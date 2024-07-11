//! Raw client
//!
//! This module contains the definition of the raw client that wraps the transport method

use std::borrow::Borrow;
use std::collections::{BTreeMap, BTreeSet, HashMap, VecDeque};
use std::io::{BufRead, BufReader, Read, Write};
use std::mem::drop;
use std::net::{TcpStream, ToSocketAddrs};
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::mpsc::{channel, Receiver, Sender};
use std::sync::{Arc, Mutex, TryLockError};
use std::time::Duration;

#[allow(unused_imports)]
use log::{debug, error, info, trace, warn};

use tapyrus::consensus::encode::deserialize;
use tapyrus::hex::{DisplayHex, FromHex};
use tapyrus::{MalFixTxid, Script};

#[cfg(feature = "use-openssl")]
use openssl::ssl::{SslConnector, SslMethod, SslStream, SslVerifyMode};

#[cfg(all(
    any(feature = "default", feature = "use-rustls"),
    not(feature = "use-openssl")
))]
use rustls::{
    pki_types::ServerName,
    pki_types::{Der, TrustAnchor},
    ClientConfig, ClientConnection, RootCertStore, StreamOwned,
};

#[cfg(any(feature = "default", feature = "proxy"))]
use crate::socks::{Socks5Stream, TargetAddr, ToTargetAddr};

use stream::ClonableStream;

use api::ElectrumApi;
use batch::Batch;
use types::*;

macro_rules! impl_batch_call {
    ( $self:expr, $data:expr, $call:ident ) => {{
        impl_batch_call!($self, $data, $call, )
    }};

    ( $self:expr, $data:expr, $call:ident, apply_deref ) => {{
        impl_batch_call!($self, $data, $call, *)
    }};

    ( $self:expr, $data:expr, $call:ident, $($apply_deref:tt)? ) => {{
        let mut batch = Batch::default();
        for i in $data {
            batch.$call($($apply_deref)* i.borrow());
        }

        let resp = $self.batch_call(&batch)?;
        let mut answer = Vec::new();

        for x in resp {
            answer.push(serde_json::from_value(x)?);
        }

        Ok(answer)
    }};
}

/// A trait for [`ToSocketAddrs`](https://doc.rust-lang.org/std/net/trait.ToSocketAddrs.html) that
/// can also be turned into a domain. Used when an SSL client needs to validate the server's
/// certificate.
pub trait ToSocketAddrsDomain: ToSocketAddrs {
    /// Returns the domain, if present
    fn domain(&self) -> Option<&str> {
        None
    }
}

impl ToSocketAddrsDomain for &str {
    fn domain(&self) -> Option<&str> {
        self.splitn(2, ':').next()
    }
}

impl ToSocketAddrsDomain for (&str, u16) {
    fn domain(&self) -> Option<&str> {
        self.0.domain()
    }
}

#[cfg(any(feature = "default", feature = "proxy"))]
impl ToSocketAddrsDomain for TargetAddr {
    fn domain(&self) -> Option<&str> {
        match self {
            TargetAddr::Ip(_) => None,
            TargetAddr::Domain(domain, _) => Some(domain.as_str()),
        }
    }
}

macro_rules! impl_to_socket_addrs_domain {
    ( $ty:ty ) => {
        impl ToSocketAddrsDomain for $ty {}
    };
}

impl_to_socket_addrs_domain!(std::net::SocketAddr);
impl_to_socket_addrs_domain!(std::net::SocketAddrV4);
impl_to_socket_addrs_domain!(std::net::SocketAddrV6);
impl_to_socket_addrs_domain!((std::net::IpAddr, u16));
impl_to_socket_addrs_domain!((std::net::Ipv4Addr, u16));
impl_to_socket_addrs_domain!((std::net::Ipv6Addr, u16));

/// Instance of an Electrum client
///
/// A `Client` maintains a constant connection with an Electrum server and exposes methods to
/// interact with it. It can also subscribe and receive notifictations from the server about new
/// blocks or activity on a specific *scriptPubKey*.
///
/// The `Client` is modeled in such a way that allows the external caller to have full control over
/// its functionality: no threads or tasks are spawned internally to monitor the state of the
/// connection.
///
/// More transport methods can be used by manually creating an instance of this struct with an
/// arbitray `S` type.
#[derive(Debug)]
pub struct RawClient<S>
where
    S: Read + Write,
{
    stream: Mutex<ClonableStream<S>>,
    buf_reader: Mutex<BufReader<ClonableStream<S>>>,

    last_id: AtomicUsize,
    waiting_map: Mutex<HashMap<usize, Sender<ChannelMessage>>>,

    headers: Mutex<VecDeque<RawHeaderNotification>>,
    script_notifications: Mutex<HashMap<ScriptHash, VecDeque<ScriptStatus>>>,

    #[cfg(feature = "debug-calls")]
    calls: AtomicUsize,
}

impl<S> From<S> for RawClient<S>
where
    S: Read + Write,
{
    fn from(stream: S) -> Self {
        let stream: ClonableStream<_> = stream.into();

        Self {
            buf_reader: Mutex::new(BufReader::new(stream.clone())),
            stream: Mutex::new(stream),

            last_id: AtomicUsize::new(0),
            waiting_map: Mutex::new(HashMap::new()),

            headers: Mutex::new(VecDeque::new()),
            script_notifications: Mutex::new(HashMap::new()),

            #[cfg(feature = "debug-calls")]
            calls: AtomicUsize::new(0),
        }
    }
}

/// Transport type used to establish a plaintext TCP connection with the server
pub type ElectrumPlaintextStream = TcpStream;
impl RawClient<ElectrumPlaintextStream> {
    /// Creates a new plaintext client and tries to connect to `socket_addr`.
    pub fn new<A: ToSocketAddrs>(
        socket_addrs: A,
        timeout: Option<Duration>,
    ) -> Result<Self, Error> {
        let stream = match timeout {
            Some(timeout) => {
                let stream = connect_with_total_timeout(socket_addrs, timeout)?;
                stream.set_read_timeout(Some(timeout))?;
                stream.set_write_timeout(Some(timeout))?;
                stream
            }
            None => TcpStream::connect(socket_addrs)?,
        };

        Ok(stream.into())
    }
}

fn connect_with_total_timeout<A: ToSocketAddrs>(
    socket_addrs: A,
    mut timeout: Duration,
) -> Result<TcpStream, Error> {
    // Use the same algorithm as curl: 1/2 on the first host, 1/4 on the second one, etc.
    // https://curl.se/mail/lib-2014-11/0164.html

    let mut errors = Vec::new();

    let addrs = socket_addrs
        .to_socket_addrs()?
        .enumerate()
        .collect::<Vec<_>>();
    for (index, addr) in &addrs {
        if *index < addrs.len() - 1 {
            timeout = timeout.div_f32(2.0);
        }

        info!(
            "Trying to connect to {} (attempt {}/{}) with timeout {:?}",
            addr,
            index + 1,
            addrs.len(),
            timeout
        );
        match TcpStream::connect_timeout(addr, timeout) {
            Ok(socket) => return Ok(socket),
            Err(e) => {
                warn!("Connection error: {:?}", e);
                errors.push(e.into());
            }
        }
    }

    Err(Error::AllAttemptsErrored(errors))
}

#[cfg(feature = "use-openssl")]
/// Transport type used to establish an OpenSSL TLS encrypted/authenticated connection with the server
pub type ElectrumSslStream = SslStream<TcpStream>;
#[cfg(feature = "use-openssl")]
impl RawClient<ElectrumSslStream> {
    /// Creates a new SSL client and tries to connect to `socket_addr`. Optionally, if
    /// `validate_domain` is `true`, validate the server's certificate.
    pub fn new_ssl<A: ToSocketAddrsDomain + Clone>(
        socket_addrs: A,
        validate_domain: bool,
        timeout: Option<Duration>,
    ) -> Result<Self, Error> {
        debug!(
            "new_ssl socket_addrs.domain():{:?} validate_domain:{} timeout:{:?}",
            socket_addrs.domain(),
            validate_domain,
            timeout
        );
        if validate_domain {
            socket_addrs.domain().ok_or(Error::MissingDomain)?;
        }
        match timeout {
            Some(timeout) => {
                let stream = connect_with_total_timeout(socket_addrs.clone(), timeout)?;
                stream.set_read_timeout(Some(timeout))?;
                stream.set_write_timeout(Some(timeout))?;
                Self::new_ssl_from_stream(socket_addrs, validate_domain, stream)
            }
            None => {
                let stream = TcpStream::connect(socket_addrs.clone())?;
                Self::new_ssl_from_stream(socket_addrs, validate_domain, stream)
            }
        }
    }

    /// Create a new SSL client using an existing TcpStream
    pub fn new_ssl_from_stream<A: ToSocketAddrsDomain>(
        socket_addrs: A,
        validate_domain: bool,
        stream: TcpStream,
    ) -> Result<Self, Error> {
        let mut builder =
            SslConnector::builder(SslMethod::tls()).map_err(Error::InvalidSslMethod)?;
        // TODO: support for certificate pinning
        if validate_domain {
            socket_addrs.domain().ok_or(Error::MissingDomain)?;
        } else {
            builder.set_verify(SslVerifyMode::NONE);
        }
        let connector = builder.build();

        let domain = socket_addrs.domain().unwrap_or("NONE").to_string();

        let stream = connector
            .connect(&domain, stream)
            .map_err(Error::SslHandshakeError)?;

        Ok(stream.into())
    }
}

#[cfg(all(
    any(feature = "default", feature = "use-rustls"),
    not(feature = "use-openssl")
))]
mod danger {
    use raw_client::ServerName;
    use rustls::client::danger::ServerCertVerified;
    use rustls::pki_types::CertificateDer;
    use rustls::pki_types::UnixTime;
    use rustls::Error;

    #[derive(Debug)]
    pub struct NoCertificateVerification {}

    impl rustls::client::danger::ServerCertVerifier for NoCertificateVerification {
        fn verify_server_cert(
            &self,
            _end_entity: &CertificateDer,
            _intermediates: &[CertificateDer],
            _server_name: &ServerName,
            _ocsp_response: &[u8],
            _now: UnixTime,
        ) -> Result<ServerCertVerified, Error> {
            Ok(ServerCertVerified::assertion())
        }

        fn verify_tls12_signature(
            &self,
            _message: &[u8],
            _cert: &CertificateDer<'_>,
            _dss: &rustls::DigitallySignedStruct,
        ) -> Result<rustls::client::danger::HandshakeSignatureValid, Error> {
            Ok(rustls::client::danger::HandshakeSignatureValid::assertion())
        }

        fn verify_tls13_signature(
            &self,
            _message: &[u8],
            _cert: &CertificateDer<'_>,
            _dss: &rustls::DigitallySignedStruct,
        ) -> Result<rustls::client::danger::HandshakeSignatureValid, Error> {
            Ok(rustls::client::danger::HandshakeSignatureValid::assertion())
        }

        fn supported_verify_schemes(&self) -> Vec<rustls::SignatureScheme> {
            vec![]
        }
    }
}

#[cfg(all(
    any(feature = "default", feature = "use-rustls"),
    not(feature = "use-openssl")
))]
/// Transport type used to establish a Rustls TLS encrypted/authenticated connection with the server
pub type ElectrumSslStream = StreamOwned<ClientConnection, TcpStream>;
#[cfg(all(
    any(feature = "default", feature = "use-rustls"),
    not(feature = "use-openssl")
))]
impl RawClient<ElectrumSslStream> {
    /// Creates a new SSL client and tries to connect to `socket_addr`. Optionally, if
    /// `validate_domain` is `true`, validate the server's certificate.
    pub fn new_ssl<A: ToSocketAddrsDomain + Clone>(
        socket_addrs: A,
        validate_domain: bool,
        timeout: Option<Duration>,
    ) -> Result<Self, Error> {
        debug!(
            "new_ssl socket_addrs.domain():{:?} validate_domain:{} timeout:{:?}",
            socket_addrs.domain(),
            validate_domain,
            timeout
        );
        if validate_domain {
            socket_addrs.domain().ok_or(Error::MissingDomain)?;
        }
        match timeout {
            Some(timeout) => {
                let stream = connect_with_total_timeout(socket_addrs.clone(), timeout)?;
                stream.set_read_timeout(Some(timeout))?;
                stream.set_write_timeout(Some(timeout))?;
                Self::new_ssl_from_stream(socket_addrs, validate_domain, stream)
            }
            None => {
                let stream = TcpStream::connect(socket_addrs.clone())?;
                Self::new_ssl_from_stream(socket_addrs, validate_domain, stream)
            }
        }
    }

    /// Create a new SSL client using an existing TcpStream
    pub fn new_ssl_from_stream<A: ToSocketAddrsDomain>(
        socket_addr: A,
        validate_domain: bool,
        tcp_stream: TcpStream,
    ) -> Result<Self, Error> {
        use std::convert::TryFrom;

        let builder = ClientConfig::builder();

        let config = if validate_domain {
            socket_addr.domain().ok_or(Error::MissingDomain)?;

            let store = webpki_roots::TLS_SERVER_ROOTS
                .into_iter()
                .map(|t| TrustAnchor {
                    subject: Der::from_slice(t.subject),
                    subject_public_key_info: Der::from_slice(t.spki),
                    name_constraints: t.name_constraints.map(|nc| Der::from_slice(nc)),
                })
                .collect::<RootCertStore>();

            // TODO: cert pinning
            builder.with_root_certificates(store).with_no_client_auth()
        } else {
            builder
                .dangerous()
                .with_custom_certificate_verifier(std::sync::Arc::new(
                    danger::NoCertificateVerification {},
                ))
                .with_no_client_auth()
        };

        let domain = socket_addr.domain().unwrap_or("NONE").to_string();
        let session = ClientConnection::new(
            std::sync::Arc::new(config),
            ServerName::try_from(domain.clone())
                .map_err(|_| Error::InvalidDNSNameError(domain.clone()))?,
        )
        .map_err(Error::CouldNotCreateConnection)?;
        let stream = StreamOwned::new(session, tcp_stream);

        Ok(stream.into())
    }
}

#[cfg(any(feature = "default", feature = "proxy"))]
/// Transport type used to establish a connection to a server through a socks proxy
pub type ElectrumProxyStream = Socks5Stream;
#[cfg(any(feature = "default", feature = "proxy"))]
impl RawClient<ElectrumProxyStream> {
    /// Creates a new socks client and tries to connect to `target_addr` using `proxy_addr` as a
    /// socks proxy server. The DNS resolution of `target_addr`, if required, is done
    /// through the proxy. This allows to specify, for instance, `.onion` addresses.
    pub fn new_proxy<T: ToTargetAddr>(
        target_addr: T,
        proxy: &crate::Socks5Config,
        timeout: Option<Duration>,
    ) -> Result<Self, Error> {
        let mut stream = match proxy.credentials.as_ref() {
            Some(cred) => Socks5Stream::connect_with_password(
                &proxy.addr,
                target_addr,
                &cred.username,
                &cred.password,
                timeout,
            )?,
            None => Socks5Stream::connect(&proxy.addr, target_addr, timeout)?,
        };
        stream.get_mut().set_read_timeout(timeout)?;
        stream.get_mut().set_write_timeout(timeout)?;

        Ok(stream.into())
    }

    #[cfg(any(feature = "use-openssl", feature = "use-rustls"))]
    /// Creates a new TLS client that connects to `target_addr` using `proxy_addr` as a socks proxy
    /// server. The DNS resolution of `target_addr`, if required, is done through the proxy. This
    /// allows to specify, for instance, `.onion` addresses.
    pub fn new_proxy_ssl<T: ToTargetAddr>(
        target_addr: T,
        validate_domain: bool,
        proxy: &crate::Socks5Config,
        timeout: Option<Duration>,
    ) -> Result<RawClient<ElectrumSslStream>, Error> {
        let target = target_addr.to_target_addr()?;

        let mut stream = match proxy.credentials.as_ref() {
            Some(cred) => Socks5Stream::connect_with_password(
                &proxy.addr,
                target_addr,
                &cred.username,
                &cred.password,
                timeout,
            )?,
            None => Socks5Stream::connect(&proxy.addr, target.clone(), timeout)?,
        };
        stream.get_mut().set_read_timeout(timeout)?;
        stream.get_mut().set_write_timeout(timeout)?;

        RawClient::new_ssl_from_stream(target, validate_domain, stream.into_inner())
    }
}

#[derive(Debug)]
enum ChannelMessage {
    Response(serde_json::Value),
    WakeUp,
    Error(Arc<std::io::Error>),
}

impl<S: Read + Write> RawClient<S> {
    // TODO: to enable this we have to find a way to allow concurrent read and writes to the
    // underlying transport struct. This can be done pretty easily for TcpStream because it can be
    // split into a "read" and a "write" object, but it's not as trivial for other types. Without
    // such thing, this causes a deadlock, because the reader thread takes a lock on the
    // `ClonableStream` before other threads can send a request to the server. They will block
    // waiting for the reader to release the mutex, but this will never happen because the server
    // didn't receive any request, so it has nothing to send back.
    // pub fn reader_thread(&self) -> Result<(), Error> {
    //     self._reader_thread(None).map(|_| ())
    // }

    fn _reader_thread(&self, until_message: Option<usize>) -> Result<serde_json::Value, Error> {
        let mut raw_resp = String::new();
        let resp = match self.buf_reader.try_lock() {
            Ok(mut reader) => {
                trace!(
                    "Starting reader thread with `until_message` = {:?}",
                    until_message
                );

                if let Some(until_message) = until_message {
                    // If we are trying to start a reader thread but the corresponding sender is
                    // missing from the map, exit immediately. This can happen with batch calls,
                    // since the sender is shared for all the individual queries in a call. We
                    // might have already received a response for that id, but we don't know it
                    // yet. Exiting here forces the calling code to fallback to the sender-receiver
                    // method, and it should find a message there waiting for it.
                    if self.waiting_map.lock()?.get(&until_message).is_none() {
                        return Err(Error::CouldntLockReader);
                    }
                }

                // Loop over every message
                loop {
                    raw_resp.clear();

                    if let Err(e) = reader.read_line(&mut raw_resp) {
                        let error = Arc::new(e);
                        for (_, s) in self.waiting_map.lock().unwrap().drain() {
                            s.send(ChannelMessage::Error(error.clone()))?;
                        }
                        return Err(Error::SharedIOError(error));
                    }
                    trace!("<== {}", raw_resp);

                    let resp: serde_json::Value = serde_json::from_str(&raw_resp)?;

                    // Normally there is and id, but it's missing for spontaneous notifications
                    // from the server
                    let resp_id = resp["id"]
                        .as_str()
                        .and_then(|s| s.parse().ok())
                        .or_else(|| resp["id"].as_u64().map(|i| i as usize));
                    match resp_id {
                        Some(resp_id) if until_message == Some(resp_id) => {
                            // We have a valid id and it's exactly the one we were waiting for!
                            trace!(
                                "Reader thread {} received a response for its request",
                                resp_id
                            );

                            // Remove ourselves from the "waiting map"
                            let mut map = self.waiting_map.lock()?;
                            map.remove(&resp_id);

                            // If the map is not empty, we select a random thread to become the
                            // new reader thread.
                            if let Some(err) = map.values().find_map(|sender| {
                                sender
                                    .send(ChannelMessage::WakeUp)
                                    .map_err(|err| {
                                        warn!("Unable to wake up a thread, trying some other");
                                        err
                                    })
                                    .err()
                            }) {
                                error!("All the threads has failed, giving up");
                                return Err(err)?;
                            }

                            break Ok(resp);
                        }
                        Some(resp_id) => {
                            // We have an id, but it's not our response. Notify the thread and
                            // move on
                            trace!("Reader thread received response for {}", resp_id);

                            if let Some(sender) = self.waiting_map.lock()?.remove(&resp_id) {
                                sender.send(ChannelMessage::Response(resp))?;
                            } else {
                                warn!("Missing listener for {}", resp_id);
                            }
                        }
                        None => {
                            // No id, that's probably a notification.
                            let mut resp = resp;

                            if let Some(ref method) = resp["method"].take().as_str() {
                                self.handle_notification(method, resp["params"].take())?;
                            } else {
                                warn!("Unexpected response: {:?}", resp);
                            }
                        }
                    }
                }
            }
            Err(TryLockError::WouldBlock) => {
                // If we "WouldBlock" here it means that there's already a reader thread
                // running somewhere.
                Err(Error::CouldntLockReader)
            }
            Err(TryLockError::Poisoned(e)) => Err(e)?,
        };

        let resp = resp?;
        if let Some(err) = resp.get("error") {
            Err(Error::Protocol(err.clone()))
        } else {
            Ok(resp)
        }
    }

    fn call(&self, req: Request) -> Result<serde_json::Value, Error> {
        // Add our listener to the map before we send the request, to make sure we don't get a
        // reply before the receiver is added
        let (sender, receiver) = channel();
        self.waiting_map.lock()?.insert(req.id, sender);

        let mut raw = serde_json::to_vec(&req)?;
        trace!("==> {}", String::from_utf8_lossy(&raw));

        raw.extend_from_slice(b"\n");
        let mut stream = self.stream.lock()?;
        stream.write_all(&raw)?;
        stream.flush()?;
        drop(stream); // release the lock

        self.increment_calls();

        let mut resp = match self.recv(&receiver, req.id) {
            Ok(resp) => resp,
            e @ Err(_) => {
                // In case of error our sender could still be left in the map, depending on where
                // the error happened. Just in case, try to remove it here
                self.waiting_map.lock()?.remove(&req.id);
                return e;
            }
        };
        Ok(resp["result"].take())
    }

    fn recv(
        &self,
        receiver: &Receiver<ChannelMessage>,
        req_id: usize,
    ) -> Result<serde_json::Value, Error> {
        loop {
            // Try to take the lock on the reader. If we manage to do so, we'll become the reader
            // thread until we get our reponse
            match self._reader_thread(Some(req_id)) {
                Ok(response) => break Ok(response),
                Err(Error::CouldntLockReader) => {
                    match receiver.recv()? {
                        // Received our response, returning it
                        ChannelMessage::Response(received) => break Ok(received),
                        ChannelMessage::WakeUp => {
                            // We have been woken up, this means that we should try becoming the
                            // reader thread ourselves
                            trace!("WakeUp for {}", req_id);

                            continue;
                        }
                        ChannelMessage::Error(e) => {
                            warn!("Received ChannelMessage::Error");

                            break Err(Error::SharedIOError(e));
                        }
                    }
                }
                e @ Err(_) => break e,
            }
        }
    }

    fn handle_notification(&self, method: &str, result: serde_json::Value) -> Result<(), Error> {
        match method {
            "blockchain.headers.subscribe" => self.headers.lock()?.append(
                &mut serde_json::from_value::<Vec<RawHeaderNotification>>(result)?
                    .into_iter()
                    .collect(),
            ),
            "blockchain.scripthash.subscribe" => {
                let unserialized: ScriptNotification = serde_json::from_value(result)?;
                let mut script_notifications = self.script_notifications.lock()?;

                let queue = script_notifications
                    .get_mut(&unserialized.scripthash)
                    .ok_or(Error::NotSubscribed(unserialized.scripthash))?;

                queue.push_back(unserialized.status);
            }
            _ => info!("received unknown notification for method `{}`", method),
        }

        Ok(())
    }

    pub(crate) fn internal_raw_call_with_vec(
        &self,
        method_name: &str,
        params: Vec<Param>,
    ) -> Result<serde_json::Value, Error> {
        let req = Request::new_id(
            self.last_id.fetch_add(1, Ordering::SeqCst),
            &method_name,
            params,
        );
        let result = self.call(req)?;

        Ok(result)
    }

    #[inline]
    #[cfg(feature = "debug-calls")]
    fn increment_calls(&self) {
        self.calls.fetch_add(1, Ordering::SeqCst);
    }

    #[inline]
    #[cfg(not(feature = "debug-calls"))]
    fn increment_calls(&self) {}
}

impl<T: Read + Write> ElectrumApi for RawClient<T> {
    fn raw_call(
        &self,
        method_name: &str,
        params: impl IntoIterator<Item = Param>,
    ) -> Result<serde_json::Value, Error> {
        self.internal_raw_call_with_vec(method_name, params.into_iter().collect())
    }

    fn batch_call(&self, batch: &Batch) -> Result<Vec<serde_json::Value>, Error> {
        let mut raw = Vec::new();

        let mut missing_responses = BTreeSet::new();
        let mut answers = BTreeMap::new();

        // Add our listener to the map before we send the request, Here we will clone the sender
        // for every request id, so that we only have to monitor one receiver.
        let (sender, receiver) = channel();

        for (method, params) in batch.iter() {
            let req = Request::new_id(
                self.last_id.fetch_add(1, Ordering::SeqCst),
                &method,
                params.to_vec(),
            );
            missing_responses.insert(req.id);

            self.waiting_map.lock()?.insert(req.id, sender.clone());

            raw.append(&mut serde_json::to_vec(&req)?);
            raw.extend_from_slice(b"\n");
        }

        if missing_responses.is_empty() {
            return Ok(vec![]);
        }

        trace!("==> {}", String::from_utf8_lossy(&raw));

        let mut stream = self.stream.lock()?;
        stream.write_all(&raw)?;
        stream.flush()?;
        drop(stream); // release the lock

        self.increment_calls();

        for req_id in missing_responses.iter() {
            match self.recv(&receiver, *req_id) {
                Ok(mut resp) => answers.insert(req_id, resp["result"].take()),
                Err(e) => {
                    // In case of error our sender could still be left in the map, depending on where
                    // the error happened. Just in case, try to remove it here
                    warn!("got error for req_id {}: {:?}", req_id, e);
                    warn!("removing all waiting req of this batch");
                    let mut guard = self.waiting_map.lock()?;
                    for req_id in missing_responses.iter() {
                        guard.remove(req_id);
                    }
                    return Err(e);
                }
            };
        }

        Ok(answers.into_iter().map(|(_, r)| r).collect())
    }

    fn block_headers_subscribe_raw(&self) -> Result<RawHeaderNotification, Error> {
        let req = Request::new_id(
            self.last_id.fetch_add(1, Ordering::SeqCst),
            "blockchain.headers.subscribe",
            vec![],
        );
        let value = self.call(req)?;

        Ok(serde_json::from_value(value)?)
    }

    fn block_headers_pop_raw(&self) -> Result<Option<RawHeaderNotification>, Error> {
        Ok(self.headers.lock()?.pop_front())
    }

    fn block_header_raw(&self, height: usize) -> Result<Vec<u8>, Error> {
        let req = Request::new_id(
            self.last_id.fetch_add(1, Ordering::SeqCst),
            "blockchain.block.header",
            vec![Param::Usize(height)],
        );
        let result = self.call(req)?;

        Ok(Vec::<u8>::from_hex(
            result
                .as_str()
                .ok_or_else(|| Error::InvalidResponse(result.clone()))?,
        )?)
    }

    fn block_headers(&self, start_height: usize, count: usize) -> Result<GetHeadersRes, Error> {
        let req = Request::new_id(
            self.last_id.fetch_add(1, Ordering::SeqCst),
            "blockchain.block.headers",
            vec![Param::Usize(start_height), Param::Usize(count)],
        );
        let result = self.call(req)?;

        let mut deserialized: GetHeadersRes = serde_json::from_value(result)?;
        for i in 0..deserialized.count {
            let (start, end) = (i * 80, (i + 1) * 80);
            deserialized
                .headers
                .push(deserialize(&deserialized.raw_headers[start..end])?);
        }
        deserialized.raw_headers.clear();

        Ok(deserialized)
    }

    fn estimate_fee(&self, number: usize) -> Result<f64, Error> {
        let req = Request::new_id(
            self.last_id.fetch_add(1, Ordering::SeqCst),
            "blockchain.estimatefee",
            vec![Param::Usize(number)],
        );
        let result = self.call(req)?;

        result
            .as_f64()
            .ok_or_else(|| Error::InvalidResponse(result.clone()))
    }

    fn relay_fee(&self) -> Result<f64, Error> {
        let req = Request::new_id(
            self.last_id.fetch_add(1, Ordering::SeqCst),
            "blockchain.relayfee",
            vec![],
        );
        let result = self.call(req)?;

        result
            .as_f64()
            .ok_or_else(|| Error::InvalidResponse(result.clone()))
    }

    fn script_subscribe(&self, script: &Script) -> Result<Option<ScriptStatus>, Error> {
        let script_hash = script.to_electrum_scripthash();
        let mut script_notifications = self.script_notifications.lock()?;

        if script_notifications.contains_key(&script_hash) {
            return Err(Error::AlreadySubscribed(script_hash));
        }

        script_notifications.insert(script_hash, VecDeque::new());
        drop(script_notifications);

        let req = Request::new_id(
            self.last_id.fetch_add(1, Ordering::SeqCst),
            "blockchain.scripthash.subscribe",
            vec![Param::String(script_hash.to_hex())],
        );
        let value = self.call(req)?;

        Ok(serde_json::from_value(value)?)
    }

    fn batch_script_subscribe<'s, I>(&self, scripts: I) -> Result<Vec<Option<ScriptStatus>>, Error>
    where
        I: IntoIterator + Clone,
        I::Item: Borrow<&'s Script>,
    {
        {
            let mut script_notifications = self.script_notifications.lock()?;

            for script in scripts.clone() {
                let script_hash = script.borrow().to_electrum_scripthash();
                if script_notifications.contains_key(&script_hash) {
                    return Err(Error::AlreadySubscribed(script_hash));
                }
                script_notifications.insert(script_hash, VecDeque::new());
            }
        }
        impl_batch_call!(self, scripts, script_subscribe)
    }

    fn script_unsubscribe(&self, script: &Script) -> Result<bool, Error> {
        let script_hash = script.to_electrum_scripthash();
        let mut script_notifications = self.script_notifications.lock()?;

        if !script_notifications.contains_key(&script_hash) {
            return Err(Error::NotSubscribed(script_hash));
        }

        let req = Request::new_id(
            self.last_id.fetch_add(1, Ordering::SeqCst),
            "blockchain.scripthash.unsubscribe",
            vec![Param::String(script_hash.to_hex())],
        );
        let value = self.call(req)?;
        let answer = serde_json::from_value(value)?;

        script_notifications.remove(&script_hash);

        Ok(answer)
    }

    fn script_pop(&self, script: &Script) -> Result<Option<ScriptStatus>, Error> {
        let script_hash = script.to_electrum_scripthash();

        match self.script_notifications.lock()?.get_mut(&script_hash) {
            None => Err(Error::NotSubscribed(script_hash)),
            Some(queue) => Ok(queue.pop_front()),
        }
    }

    fn script_get_balance(&self, script: &Script) -> Result<GetBalanceRes, Error> {
        let params = vec![Param::String(script.to_electrum_scripthash().to_hex())];
        let req = Request::new_id(
            self.last_id.fetch_add(1, Ordering::SeqCst),
            "blockchain.scripthash.get_balance",
            params,
        );
        let result = self.call(req)?;

        Ok(serde_json::from_value(result)?)
    }
    fn batch_script_get_balance<'s, I>(&self, scripts: I) -> Result<Vec<GetBalanceRes>, Error>
    where
        I: IntoIterator + Clone,
        I::Item: Borrow<&'s Script>,
    {
        impl_batch_call!(self, scripts, script_get_balance)
    }

    fn script_get_history(&self, script: &Script) -> Result<Vec<GetHistoryRes>, Error> {
        let params = vec![Param::String(script.to_electrum_scripthash().to_hex())];
        let req = Request::new_id(
            self.last_id.fetch_add(1, Ordering::SeqCst),
            "blockchain.scripthash.get_history",
            params,
        );
        let result = self.call(req)?;

        Ok(serde_json::from_value(result)?)
    }
    fn batch_script_get_history<'s, I>(&self, scripts: I) -> Result<Vec<Vec<GetHistoryRes>>, Error>
    where
        I: IntoIterator + Clone,
        I::Item: Borrow<&'s Script>,
    {
        impl_batch_call!(self, scripts, script_get_history)
    }

    fn script_list_unspent(&self, script: &Script) -> Result<Vec<ListUnspentRes>, Error> {
        let params = vec![Param::String(script.to_electrum_scripthash().to_hex())];
        let req = Request::new_id(
            self.last_id.fetch_add(1, Ordering::SeqCst),
            "blockchain.scripthash.listunspent",
            params,
        );
        let result = self.call(req)?;
        let mut result: Vec<ListUnspentRes> = serde_json::from_value(result)?;

        // This should not be necessary, since the protocol documentation says that the txs should
        // be "in blockchain order" (https://electrumx.readthedocs.io/en/latest/protocol-methods.html#blockchain-scripthash-listunspent).
        // However, elects seems to be ignoring this at the moment, so we'll sort again here just
        // to make sure the result is consistent.
        result.sort_unstable_by_key(|k| (k.height, k.tx_pos));
        Ok(result)
    }

    fn batch_script_list_unspent<'s, I>(
        &self,
        scripts: I,
    ) -> Result<Vec<Vec<ListUnspentRes>>, Error>
    where
        I: IntoIterator + Clone,
        I::Item: Borrow<&'s Script>,
    {
        impl_batch_call!(self, scripts, script_list_unspent)
    }

    fn transaction_get_raw(&self, txid: &MalFixTxid) -> Result<Vec<u8>, Error> {
        let params = vec![Param::String(format!("{:x}", txid))];
        let req = Request::new_id(
            self.last_id.fetch_add(1, Ordering::SeqCst),
            "blockchain.transaction.get",
            params,
        );
        let result = self.call(req)?;

        Ok(Vec::<u8>::from_hex(
            result
                .as_str()
                .ok_or_else(|| Error::InvalidResponse(result.clone()))?,
        )?)
    }

    fn batch_transaction_get_raw<'t, I>(&self, txids: I) -> Result<Vec<Vec<u8>>, Error>
    where
        I: IntoIterator + Clone,
        I::Item: Borrow<&'t MalFixTxid>,
    {
        let txs_string: Result<Vec<String>, Error> = impl_batch_call!(self, txids, transaction_get);
        txs_string?
            .iter()
            .map(|s| Ok(Vec::<u8>::from_hex(s)?))
            .collect()
    }

    fn batch_block_header_raw<'s, I>(&self, heights: I) -> Result<Vec<Vec<u8>>, Error>
    where
        I: IntoIterator + Clone,
        I::Item: Borrow<u32>,
    {
        let headers_string: Result<Vec<String>, Error> =
            impl_batch_call!(self, heights, block_header, apply_deref);
        headers_string?
            .iter()
            .map(|s| Ok(Vec::<u8>::from_hex(s)?))
            .collect()
    }

    fn batch_estimate_fee<'s, I>(&self, numbers: I) -> Result<Vec<f64>, Error>
    where
        I: IntoIterator + Clone,
        I::Item: Borrow<usize>,
    {
        impl_batch_call!(self, numbers, estimate_fee, apply_deref)
    }

    fn transaction_broadcast_raw(&self, raw_tx: &[u8]) -> Result<MalFixTxid, Error> {
        let params = vec![Param::String(raw_tx.to_lower_hex_string())];
        let req = Request::new_id(
            self.last_id.fetch_add(1, Ordering::SeqCst),
            "blockchain.transaction.broadcast",
            params,
        );
        let result = self.call(req)?;

        Ok(serde_json::from_value(result)?)
    }

    fn transaction_get_merkle(
        &self,
        txid: &MalFixTxid,
        height: usize,
    ) -> Result<GetMerkleRes, Error> {
        let params = vec![Param::String(format!("{:x}", txid)), Param::Usize(height)];
        let req = Request::new_id(
            self.last_id.fetch_add(1, Ordering::SeqCst),
            "blockchain.transaction.get_merkle",
            params,
        );
        let result = self.call(req)?;

        Ok(serde_json::from_value(result)?)
    }

    fn server_features(&self) -> Result<ServerFeaturesRes, Error> {
        let req = Request::new_id(
            self.last_id.fetch_add(1, Ordering::SeqCst),
            "server.features",
            vec![],
        );
        let result = self.call(req)?;

        Ok(serde_json::from_value(result)?)
    }

    fn ping(&self) -> Result<(), Error> {
        let req = Request::new_id(
            self.last_id.fetch_add(1, Ordering::SeqCst),
            "server.ping",
            vec![],
        );
        self.call(req)?;

        Ok(())
    }

    #[cfg(feature = "debug-calls")]
    fn calls_made(&self) -> Result<usize, Error> {
        Ok(self.calls.load(Ordering::SeqCst))
    }
}

#[cfg(test)]
mod test {
    use crate::utils;
    use std::str::FromStr;
    use tapyrus::hex::DisplayHex;

    use super::RawClient;
    use api::ElectrumApi;

    fn get_test_server() -> String {
        std::env::var("TEST_ELECTRUM_SERVER").unwrap_or("electrum.blockstream.info:50001".into())
    }

    #[test]
    #[ignore] // TODO: Parsing error
    fn test_server_features_simple() {
        let client = RawClient::new(get_test_server(), None).unwrap();

        let resp = client.server_features().unwrap();
        assert_eq!(
            resp.genesis_hash,
            [
                0, 0, 0, 0, 0, 25, 214, 104, 156, 8, 90, 225, 101, 131, 30, 147, 79, 247, 99, 174,
                70, 162, 166, 193, 114, 179, 241, 182, 10, 140, 226, 111
            ],
        );
        assert_eq!(resp.hash_function, Some("sha256".into()));
        assert_eq!(resp.pruning, None);
    }
    #[test]
    fn test_relay_fee() {
        let client = RawClient::new(get_test_server(), None).unwrap();

        let resp = client.relay_fee().unwrap();
        assert_eq!(resp, 0.00001);
    }

    #[test]
    #[ignore] // TODO: esplora with testnet always returns error.
    fn test_estimate_fee() {
        let client = RawClient::new(get_test_server(), None).unwrap();

        let resp = client.estimate_fee(10).unwrap();
        assert!(resp > 0.0);
    }

    #[test]
    #[ignore]
    fn test_block_header() {
        let client = RawClient::new(get_test_server(), None).unwrap();

        let resp = client.block_header(0).unwrap();
        assert_eq!(resp.version, tapyrus::block::Version::ONE);
        assert_eq!(resp.time, 1231006505);
    }

    #[test]
    fn test_block_header_raw() {
        let client = RawClient::new(get_test_server(), None).unwrap();

        let resp = client.block_header_raw(0).unwrap();
        assert_eq!(
            resp,
            vec![
                1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                0, 0, 0, 0, 0, 0, 0, 0, 68, 204, 24, 27, 208, 233, 92, 91, 153, 154, 19, 209, 252,
                13, 25, 63, 168, 34, 58, 249, 117, 17, 173, 32, 152, 33, 117, 85, 168, 65, 179, 81,
                143, 24, 236, 37, 54, 240, 187, 157, 109, 72, 52, 252, 199, 18, 233, 86, 56, 64,
                254, 159, 8, 157, 185, 232, 254, 137, 11, 255, 184, 33, 101, 132, 159, 82, 186, 94,
                1, 33, 3, 102, 38, 38, 144, 203, 223, 100, 129, 50, 206, 12, 8, 137, 98, 198, 54,
                17, 18, 88, 35, 100, 237, 225, 32, 243, 120, 10, 183, 52, 56, 252, 75, 64, 43, 30,
                217, 153, 105, 32, 245, 122, 66, 95, 111, 151, 151, 85, 124, 14, 115, 208, 201,
                251, 175, 222, 188, 170, 121, 107, 19, 110, 9, 70, 255, 169, 141, 146, 143, 129,
                48, 182, 165, 114, 248, 61, 163, 149, 48, 177, 55, 132, 238, 183, 0, 116, 101, 182,
                115, 170, 149, 9, 22, 25, 231, 238, 32, 133
            ]
        );
    }

    #[test]
    #[ignore]
    fn test_block_headers() {
        let client = RawClient::new(get_test_server(), None).unwrap();

        let resp = client.block_headers(0, 4).unwrap();
        assert_eq!(resp.count, 4);
        assert_eq!(resp.max, 2016);
        assert_eq!(resp.headers.len(), 4);

        assert_eq!(resp.headers[0].time, 1231006505);
    }

    #[test]
    #[ignore] // TODO: fix parsing getbalance result
    fn test_script_get_balance() {
        use std::str::FromStr;

        let client = RawClient::new(get_test_server(), None).unwrap();

        // Realistically nobody will ever spend from this address, so we can expect the balance to
        // increase over time
        let addr = tapyrus::Address::from_str("1AQ2CtG3jho78SrEzKe3vf6dxcEkJt5nzA")
            .unwrap()
            .assume_checked();
        let resp = client.script_get_balance(&addr.script_pubkey()).unwrap();
        assert!(resp.confirmed >= 213091301265);
    }

    #[test]
    fn test_script_get_history() {
        use std::str::FromStr;

        use tapyrus::MalFixTxid;

        let client = RawClient::new(get_test_server(), None).unwrap();

        // Mt.Gox hack address
        let addr = tapyrus::Address::from_str("1AQ2CtG3jho78SrEzKe3vf6dxcEkJt5nzA")
            .unwrap()
            .assume_checked();
        let resp = client.script_get_history(&addr.script_pubkey()).unwrap();

        assert!(resp.len() >= 328);
        assert_eq!(
            resp[0].tx_hash,
            MalFixTxid::from_str(
                "e4801aa4d2ac8912958236e10558dddb1e32a886c6186d7f4146365563f47db1"
            )
            .unwrap()
        );
    }

    #[test]
    fn test_script_list_unspent() {
        use std::str::FromStr;
        use tapyrus::MalFixTxid;

        let client = RawClient::new(get_test_server(), None).unwrap();

        let addr = tapyrus::Address::from_str("1AQ2CtG3jho78SrEzKe3vf6dxcEkJt5nzA")
            .unwrap()
            .assume_checked();
        let resp = client.script_list_unspent(&addr.script_pubkey()).unwrap();

        assert!(resp.len() >= 9);
        let txid = "4167e7e458b494d35572c62a2d47933a09e0cde17b211006f06574e7b7825f75";
        let txid = MalFixTxid::from_str(txid).unwrap();
        let txs: Vec<_> = resp.iter().filter(|e| e.tx_hash == txid).collect();
        assert_eq!(txs.len(), 1);
        assert_eq!(txs[0].value, 1250000000);
        assert_eq!(txs[0].height, 459159);
        assert_eq!(txs[0].tx_pos, 0);
    }

    #[test]
    fn test_batch_script_list_unspent() {
        use std::str::FromStr;

        let client = RawClient::new(get_test_server(), None).unwrap();

        // Testnet signer network pay-to-address
        let script_1 = tapyrus::Address::from_str("1AQ2CtG3jho78SrEzKe3vf6dxcEkJt5nzA")
            .unwrap()
            .assume_checked()
            .script_pubkey();

        let resp = client
            .batch_script_list_unspent(vec![script_1.as_script()])
            .unwrap();
        assert_eq!(resp.len(), 1);
        assert!(resp[0].len() >= 9);
    }

    #[test]
    #[ignore] // TODO: esplora with testnet always returns error.
    fn test_batch_estimate_fee() {
        let client = RawClient::new(get_test_server(), None).unwrap();

        let resp = client.batch_estimate_fee(vec![10, 20]).unwrap();
        assert_eq!(resp.len(), 2);
        assert!(resp[0] > 0.0);
        assert!(resp[1] > 0.0);
    }

    #[test]
    fn test_transaction_get() {
        use tapyrus::{transaction, MalFixTxid};

        let client = RawClient::new(get_test_server(), None).unwrap();

        let resp = client
            .transaction_get(
                &MalFixTxid::from_str(
                    "11f03b025e513d434f1ca79f22ca4343af97f2264d9551888a436bca1c0984ba",
                )
                .unwrap(),
            )
            .unwrap();
        assert_eq!(resp.version, transaction::Version::ONE);
        assert_eq!(resp.lock_time.to_consensus_u32(), 0);
    }

    #[test]
    fn test_transaction_get_raw() {
        use tapyrus::MalFixTxid;

        let client = RawClient::new(get_test_server(), None).unwrap();

        let resp = client
            .transaction_get_raw(
                &MalFixTxid::from_str(
                    "e40ceaf649597e5dc0fb3f55eb052caea0f386fc06854c063dc88a3de8fcc13c",
                )
                .unwrap(),
            )
            .unwrap();
        assert_eq!(
            resp.to_lower_hex_string(),
            "010000000100000000000000000000000000000000000000000000000000000000000000008301070006038301070101ffffffff01c680814a000000001976a9146713b478d99432aac667b7d8e87f9d06edca03bb88ac00000000"
        )
    }

    #[test]
    #[ignore]
    fn test_transaction_get_merkle() {
        use tapyrus::MalFixTxid;

        let client = RawClient::new(get_test_server(), None).unwrap();

        let txid = MalFixTxid::from_str(
            "1f7ff3c407f33eabc8bec7d2cc230948f2249ec8e591bcf6f971ca9366c8788d",
        )
        .unwrap();
        let resp = client.transaction_get_merkle(&txid, 630000).unwrap();
        assert_eq!(resp.block_height, 630000);
        assert_eq!(resp.pos, 68);
        assert_eq!(resp.merkle.len(), 12);
        assert_eq!(
            resp.merkle[0],
            [
                34, 65, 51, 64, 49, 139, 115, 189, 185, 246, 70, 225, 168, 193, 217, 195, 47, 66,
                179, 240, 153, 24, 114, 215, 144, 196, 212, 41, 39, 155, 246, 25
            ]
        );

        // Check we can verify the merkle proof validity, but fail if we supply wrong data.
        let block_header = client.block_header(resp.block_height).unwrap();
        assert!(utils::validate_merkle_proof(
            &txid,
            &block_header.merkle_root,
            &resp
        ));

        let mut fail_resp = resp.clone();
        fail_resp.pos = 13;
        assert!(!utils::validate_merkle_proof(
            &txid,
            &block_header.merkle_root,
            &fail_resp
        ));

        let fail_block_header = client.block_header(resp.block_height + 1).unwrap();
        assert!(!utils::validate_merkle_proof(
            &txid,
            &fail_block_header.merkle_root,
            &resp
        ));
    }

    #[test]
    fn test_ping() {
        let client = RawClient::new(get_test_server(), None).unwrap();
        client.ping().unwrap();
    }

    #[test]
    #[ignore]
    fn test_block_headers_subscribe() {
        let client = RawClient::new(get_test_server(), None).unwrap();
        let resp = client.block_headers_subscribe().unwrap();

        assert!(resp.height >= 639000);
    }

    #[test]
    fn test_script_subscribe() {
        use std::str::FromStr;

        let client = RawClient::new(get_test_server(), None).unwrap();

        // Mt.Gox hack address
        let addr = tapyrus::Address::from_str("1FeexV6bAHb8ybZjqQMjJrcCrHGW9sb6uF")
            .unwrap()
            .assume_checked();

        // Just make sure that the call returns Ok(something)
        client.script_subscribe(&addr.script_pubkey()).unwrap();
    }

    #[test]
    fn test_request_after_error() {
        let client = RawClient::new(get_test_server(), None).unwrap();

        assert!(client.transaction_broadcast_raw(&[0x00]).is_err());
        // assert!(client.server_features().is_ok());
        assert!(client.ping().is_ok());
    }

    #[test]
    fn test_raw_call() {
        use types::Param;

        let client = RawClient::new(get_test_server(), None).unwrap();

        let params = vec![
            Param::String(
                "e40ceaf649597e5dc0fb3f55eb052caea0f386fc06854c063dc88a3de8fcc13c".to_string(),
            ),
            Param::Bool(false),
        ];

        let resp = client
            .raw_call("blockchain.transaction.get", params)
            .unwrap();

        assert_eq!(
            resp,
            "010000000100000000000000000000000000000000000000000000000000000000000000008301070006038301070101ffffffff01c680814a000000001976a9146713b478d99432aac667b7d8e87f9d06edca03bb88ac00000000"
        )
    }
}
