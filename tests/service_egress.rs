//! `urn:shacl:validate` never reaches the network, in any build (ledger #1099, #1083).
//!
//! The claim: rudof_rdf enables `oxigraph/http-client` on every native target, so in THIS
//! crate's own default build (and in every host linking it, by feature unification) oxigraph's
//! `SparqlEvaluator::new()` installs its HTTP service handler. rudof evaluates a shape's
//! `sh:sparql [ sh:select … ]` with exactly that constructor, once per focus node, so
//! `SERVICE <http://…>` in a shapes graph was an outbound request with no `urn:cap:net:*`
//! anywhere near it. The cli re-pin arc (ikigai-rs/ikigai-cli#435) saw it connect.
//!
//! ★ No test-only feature is needed to reproduce it here, unlike ikigai-store PR 28: the
//! default native build IS the affected build (`cargo tree -i oxigraph -e features` names
//! `http-client` through rudof_rdf). [`control_rudof_itself_reaches_the_stub`] proves the
//! client is live in the build under test, by sending rudof's own query entry point a
//! `SERVICE`; if it ever stops connecting, the refusals below prove nothing and must be
//! re-derived.
//!
//! rudof builds its evaluator privately (`OxigraphInMemory::query_select`), so no refusing
//! handler can be installed on it: the check before rudof sees the text is the guard.
//!
//! Every request goes to a stub on 127.0.0.1 with an ephemeral port, never a real host.

use futures::executor::block_on;
use ikigai_core::{ArgRef, Capability, Error, Iri, Kernel, Request, Verb};
use std::io::{Read, Write};
use std::net::{SocketAddr, TcpListener, TcpStream};
use std::sync::{Arc, Mutex};

/// A plain-HTTP stub that records the request line of every connection it is sent, and
/// answers each with an empty SPARQL result set (so a client that does reach it finishes).
struct Stub {
    addr: SocketAddr,
    seen: Arc<Mutex<Vec<String>>>,
}

/// The first bytes of the connection [`Stub::requests`] makes itself. Accepts are served in
/// backlog order, so once the stub has answered this one, every connection made before it has
/// been recorded: the negative assertions need no sleep and cannot race.
const SENTINEL: &[u8] = b"SENTINEL\r\n";

impl Stub {
    fn start() -> Stub {
        let listener = TcpListener::bind("127.0.0.1:0").unwrap();
        let addr = listener.local_addr().unwrap();
        let seen = Arc::new(Mutex::new(Vec::new()));
        let record = Arc::clone(&seen);
        std::thread::spawn(move || {
            for stream in listener.incoming() {
                let Ok(mut stream) = stream else { continue };
                let head = read_head(&mut stream);
                if head.as_bytes().starts_with(SENTINEL) {
                    let _ = stream.write_all(b"ok");
                    continue;
                }
                record
                    .lock()
                    .unwrap()
                    .push(head.lines().next().unwrap_or("").to_string());
                let body = r#"{"head":{"vars":["s"]},"results":{"bindings":[]}}"#;
                let _ = write!(
                    stream,
                    "HTTP/1.1 200 OK\r\nContent-Type: application/sparql-results+json\r\n\
                     Content-Length: {}\r\nConnection: close\r\n\r\n{body}",
                    body.len()
                );
            }
        });
        Stub { addr, seen }
    }

    fn url(&self) -> String {
        format!("http://{}/sparql", self.addr)
    }

    /// Every request line the stub has been sent, after a sentinel round trip.
    fn requests(&self) -> Vec<String> {
        let mut sentinel = TcpStream::connect(self.addr).unwrap();
        sentinel.write_all(SENTINEL).unwrap();
        let mut ack = Vec::new();
        sentinel.read_to_end(&mut ack).unwrap();
        assert_eq!(ack, b"ok", "the stub did not answer its sentinel");
        self.seen.lock().unwrap().clone()
    }
}

/// Read up to the end of the request headers (or the sentinel line), enough to log it.
fn read_head(stream: &mut TcpStream) -> String {
    let mut head = Vec::new();
    let mut byte = [0u8; 1];
    while stream.read(&mut byte).map(|n| n == 1).unwrap_or(false) {
        head.push(byte[0]);
        if head == SENTINEL || head.len() > 64 * 1024 {
            break;
        }
        if head.ends_with(b"\r\n\r\n") {
            // Drain a body too, or closing with it unread resets the client's connection.
            let text = String::from_utf8_lossy(&head).to_ascii_lowercase();
            let length = text
                .lines()
                .find_map(|l| l.strip_prefix("content-length:"))
                .and_then(|n| n.trim().parse::<usize>().ok())
                .unwrap_or(0);
            let mut body = vec![0u8; length];
            let _ = stream.read_exact(&mut body);
            break;
        }
    }
    String::from_utf8_lossy(&head).into_owned()
}

const HEAD: &str = "@prefix sh: <http://www.w3.org/ns/shacl#> .\n\
                    @prefix xsd: <http://www.w3.org/2001/XMLSchema#> .\n\
                    @prefix owl: <http://www.w3.org/2002/07/owl#> .\n\
                    @prefix ex: <http://example.org/> .\n";

const DATA: &str = "@prefix ex: <http://example.org/> .\n\
                    ex:a a ex:Person ; ex:p ex:b .\n";

/// A node shape on `ex:Person` with one `sh:sparql` whose `sh:select` is `select`.
fn select_shape(select: &str) -> String {
    format!(
        "{HEAD}ex:S a sh:NodeShape ; sh:targetClass ex:Person ;\n  \
         sh:sparql [ sh:select \"\"\"{select}\"\"\" ] .\n"
    )
}

/// `text` with every character a SPARQL `IRIREF` forbids written as a Turtle `\uXXXX` escape,
/// so it can sit inside `<…>` in a Turtle document. rudof parses Turtle LENIENTLY, which does
/// not validate an IRI after unescaping it, so the forbidden characters survive into the term.
fn escaped_iri(text: &str) -> String {
    text.chars()
        .map(|c| match c {
            '<' | '>' | '"' | '{' | '}' | '|' | '^' | '`' | '\\' | '\0'..=' ' => {
                format!("\\u{:04X}", c as u32)
            }
            c => c.to_string(),
        })
        .collect()
}

/// An IRI that, rendered by rudof into `VALUES ?this { <…> }`, closes the `VALUES`, runs a
/// `SERVICE`, and reopens a `VALUES` the rest of the query closes.
fn breakout_iri(url: &str) -> String {
    escaped_iri(&format!(
        "http://example.org/x> }} SERVICE <{url}> {{ ?s ?p ?o }} VALUES ?q {{ <http://example.org/y"
    ))
}

/// What a case must answer, besides never reaching the stub.
#[derive(Clone, Copy, Debug)]
enum Expect {
    /// A typed refusal naming this argument, before anything is evaluated.
    Refused(&'static str),
    /// A report: there is nothing here to refuse (rudof never evaluates the text, or the term
    /// cannot leave its token).
    Report,
    /// rudof's own reader rejects the graph (it re-validates a triple's plain IRIs), so it never
    /// reaches the validator at all.
    ParseError,
}
use Expect::*;

/// The same breakout for the SUBJECT of a triple term, which rudof renders as
/// `<<( <subject> <predicate> <object> )>>`: it closes the triple term as well.
fn triple_subject_breakout_iri(url: &str) -> String {
    escaped_iri(&format!(
        "http://example.org/x> <http://example.org/q> <http://example.org/r> )>> }} \
         SERVICE <{url}> {{ ?s ?p ?o }} VALUES ?q {{ <<( <http://example.org/y"
    ))
}

/// One case: its name, `(data, shapes)`, and what it must answer.
type Case = (&'static str, String, String, Expect);

/// Every route by which a `urn:shacl:validate` call could put a `SERVICE` in front of rudof's
/// evaluator, plus the SHACL-SPARQL texts rudof 0.3.24 does not evaluate at all, which must stay
/// silent (a tripwire for a rudof release that starts evaluating them).
fn cases(url: &str) -> Vec<Case> {
    let service = format!("SERVICE <{url}> {{ ?s ?p ?o }}");
    vec![
        // The claim's own shape: a node shape's `sh:select`.
        (
            "select",
            DATA.into(),
            select_shape(&format!("SELECT $this WHERE {{ $this a ?t . {service} }}")),
            Refused("shapes"),
        ),
        // SILENT: by the spec a failure answers nothing bound, so only a door check is typed.
        (
            "select-silent",
            DATA.into(),
            select_shape(&format!(
                "SELECT $this WHERE {{ $this a ?t . SERVICE SILENT <{url}> {{ ?s ?p ?o }} }}"
            )),
            Refused("shapes"),
        ),
        // One level down, where only a walk of the whole algebra sees it.
        (
            "select-nested",
            DATA.into(),
            select_shape(&format!(
                "SELECT $this WHERE {{ $this a ?t FILTER EXISTS {{ OPTIONAL {{ {service} }} }} }}"
            )),
            Refused("shapes"),
        ),
        // In a sub-select.
        (
            "select-subselect",
            DATA.into(),
            select_shape(&format!(
                "SELECT $this WHERE {{ $this a ?t {{ SELECT ?s WHERE {{ {service} }} }} }}"
            )),
            Refused("shapes"),
        ),
        // A property shape's `sh:select`, with `$PATH` rendered in.
        (
            "property-path",
            DATA.into(),
            format!(
                "{HEAD}ex:S a sh:NodeShape ; sh:targetClass ex:Person ;\n  \
                 sh:property [ sh:path ex:p ;\n    \
                 sh:sparql [ sh:select \"\"\"SELECT $this ?value WHERE {{ $this $PATH ?value . {service} }}\"\"\" ] ] .\n"
            ),
            Refused("shapes"),
        ),
        // A `sh:prefixes` declaration whose PREFIX NAME carries the whole query: rudof writes it
        // into the header unescaped, and the `sh:select` is a comment. No `sh:select` literal
        // anywhere contains the word.
        (
            "prefix-name",
            DATA.into(),
            format!(
                "{HEAD}ex:S a sh:NodeShape ; sh:targetClass ex:Person ;\n  \
                 sh:sparql [ sh:prefixes ex:decls ; sh:select \"# nothing\" ] .\n\
                 ex:decls sh:declare [ sh:prefix \"\"\"a: <http://example.org/a/> SELECT $this WHERE {{ {service} }} #\"\"\" ;\n  \
                 sh:namespace \"http://example.org/b/\"^^xsd:anyURI ] .\n"
            ),
            Refused("shapes"),
        ),
        // The focus node is written into `VALUES ?this { … }` with oxrdf's `Display`. A plain
        // subject or object IRI holding `>` is rejected by rudof's reader...
        (
            "data-focus-iri",
            format!(
                "@prefix ex: <http://example.org/> .\n<{}> a ex:Person .\n",
                breakout_iri(url)
            ),
            select_shape("SELECT $this WHERE { $this a ?t }"),
            ParseError,
        ),
        (
            "shapes-target-node",
            DATA.into(),
            format!(
                "{HEAD}ex:S a sh:NodeShape ; sh:targetNode <{}> ;\n  \
                 sh:sparql [ sh:select \"\"\"SELECT $this WHERE {{ OPTIONAL {{ $this a ?t }} }}\"\"\" ] .\n",
                breakout_iri(url)
            ),
            ParseError,
        ),
        // ... but a literal's DATATYPE IRI is not re-validated: from the SHAPES graph through
        // `sh:targetNode`, ...
        (
            "shapes-target-literal-datatype",
            DATA.into(),
            format!(
                "{HEAD}ex:S a sh:NodeShape ; sh:targetNode \"v\"^^<{}> ;\n  \
                 sh:sparql [ sh:select \"\"\"SELECT $this WHERE {{ OPTIONAL {{ $this a ?t }} }}\"\"\" ] .\n",
                breakout_iri(url)
            ),
            Refused("shapes"),
        ),
        // ... from the DATA graph, a value reached by `sh:targetObjectsOf`, ...
        (
            "data-literal-datatype",
            format!(
                "@prefix ex: <http://example.org/> .\nex:a ex:p \"v\"^^<{}> .\n",
                breakout_iri(url)
            ),
            format!(
                "{HEAD}ex:S a sh:NodeShape ; sh:targetObjectsOf ex:p ;\n  \
                 sh:sparql [ sh:select \"\"\"SELECT $this WHERE {{ OPTIONAL {{ ?s ?p $this }} }}\"\"\" ] .\n"
            ),
            Refused("data"),
        ),
        // ... and nor is an IRI inside an RDF 1.2 triple term, written as `<<( … )>>`.
        (
            "data-triple-term",
            format!(
                "@prefix ex: <http://example.org/> .\nex:a ex:p <<( <{}> ex:q ex:r )>> .\n",
                triple_subject_breakout_iri(url)
            ),
            format!(
                "{HEAD}ex:S a sh:NodeShape ; sh:targetObjectsOf ex:p ;\n  \
                 sh:sparql [ sh:select \"\"\"SELECT $this WHERE {{ OPTIONAL {{ ?s ?p $this }} }}\"\"\" ] .\n"
            ),
            Refused("data"),
        ),
        // A literal focus node's LEXICAL FORM: oxrdf escapes its quotes, so it cannot break
        // out. Not refused (nothing to refuse), and must not connect.
        (
            "shapes-target-literal-lexical",
            DATA.into(),
            format!(
                "{HEAD}ex:S a sh:NodeShape ; sh:targetNode \"\"\"x\" }} {service} VALUES ?q {{ \"y\"\"\" ;\n  \
                 sh:sparql [ sh:select \"\"\"SELECT $this WHERE {{ OPTIONAL {{ $this a ?t }} }}\"\"\" ] .\n"
            ),
            Report,
        ),
        // `FROM <url>`: oxigraph reads it as the name of a graph in the store, never a fetch.
        (
            "from",
            DATA.into(),
            select_shape(&format!("SELECT $this FROM <{url}> WHERE {{ $this a ?t }}")),
            Report,
        ),
        // SHACL-SPARQL that rudof 0.3.24 does not parse at all: a SPARQL-based target, an ASK
        // validator in a SPARQL-based constraint component, and `owl:imports` (followed inside
        // the shapes graph for prefixes, never fetched).
        (
            "sparql-target",
            DATA.into(),
            format!(
                "{HEAD}ex:S a sh:NodeShape ;\n  \
                 sh:target [ a sh:SPARQLTarget ; sh:select \"\"\"SELECT ?this WHERE {{ {service} }}\"\"\" ] ;\n  \
                 sh:property [ sh:path ex:p ; sh:minCount 1 ] .\n"
            ),
            Report,
        ),
        (
            "constraint-component-ask",
            DATA.into(),
            format!(
                "{HEAD}ex:C a sh:ConstraintComponent ;\n  \
                 sh:parameter [ sh:path ex:flag ] ;\n  \
                 sh:validator [ a sh:SPARQLAskValidator ; sh:ask \"\"\"ASK {{ {service} }}\"\"\" ] .\n\
                 ex:S a sh:NodeShape ; sh:targetClass ex:Person ; ex:flag true .\n"
            ),
            Report,
        ),
        (
            "owl-imports",
            DATA.into(),
            format!(
                "{HEAD}<urn:shapes> owl:imports <{url}> .\n\
                 ex:S a sh:NodeShape ; sh:targetClass ex:Person ;\n  \
                 sh:sparql [ sh:prefixes ex:decls ; sh:select \"\"\"SELECT $this WHERE {{ $this a ?t }}\"\"\" ] .\n\
                 ex:decls owl:imports <{url}> .\n"
            ),
            Report,
        ),
    ]
}

/// The control: rudof's own query entry point, the one `validate` calls, DOES reach the stub
/// in the build under test. Without this, zero connections below could mean "no HTTP client
/// was compiled in" rather than "refused".
#[test]
fn control_rudof_itself_reaches_the_stub() {
    use rudof_rdf::rdf_core::query::QueryRDF;
    use rudof_rdf::rdf_core::RDFFormat;
    use rudof_rdf::rdf_impl::ReaderMode;
    use sparql_service::RdfData;

    let stub = Stub::start();
    let mut data =
        RdfData::from_str(DATA, &RDFFormat::Turtle, None, &ReaderMode::default()).unwrap();
    data.check_store().unwrap();
    let query = format!(
        "SELECT ?s WHERE {{ SERVICE <{}> {{ ?s ?p ?o }} }}",
        stub.url()
    );
    let _ = data.query_select(&query);
    assert_eq!(
        stub.requests().len(),
        1,
        "rudof's evaluator no longer reaches the network in this build, so the egress tests in \
         this file reproduce nothing: re-derive them (has rudof_rdf dropped oxigraph/http-client?)"
    );
}

/// Every case, run through the library entry point: none reaches the stub, and each one that
/// carries a `SERVICE` rudof would evaluate is refused as `InvalidArgument` naming its input.
/// (Run with `--nocapture` to see each case's connection count and answer.)
#[test]
fn no_shapes_or_data_graph_reaches_the_network() {
    let stub = Stub::start();
    let mut wrong = Vec::new();
    for (name, data, shapes, expect) in cases(&stub.url()) {
        let before = stub.requests().len();
        let result = ikigai_shacl::validate_report(&data, &shapes);
        let connections = stub.requests().len() - before;
        let outcome = match &result {
            Ok(report) => format!("Ok(conforms={})", report.conforms),
            Err(e) => format!("Err({e})"),
        };
        eprintln!("{name}: {connections} connection(s), {outcome}");
        if connections != 0 {
            wrong.push(format!("{name}: reached the stub {connections} time(s)"));
        }
        match (expect, &result) {
            (Refused(arg), Err(Error::InvalidArgument { name: got, detail })) => {
                if got != arg || !detail.contains("SERVICE") {
                    wrong.push(format!("{name}: refused as `{got}`: {detail}"));
                }
            }
            (Report, Ok(_)) => {}
            (ParseError, Err(Error::Endpoint(e))) if e.contains("parse error") => {}
            (expect, _) => wrong.push(format!("{name}: expected {expect:?}, got {outcome}")),
        }
    }
    assert!(wrong.is_empty(), "{}", wrong.join("\n"));
}

/// The claim's own case through the endpoint, under the root capability: the kernel door is
/// the same code, and is refused the same way.
#[test]
fn the_endpoint_refuses_service_under_root() {
    let stub = Stub::start();
    let kernel = Kernel::new(Arc::new(ikigai_shacl::space()));
    let shapes = select_shape(&format!(
        "SELECT $this WHERE {{ $this a ?t . SERVICE <{}> {{ ?s ?p ?o }} }}",
        stub.url()
    ));
    let request = Request::new(Verb::Source, Iri::parse("urn:shacl:validate").unwrap())
        .with_arg("data", ArgRef::Inline(DATA.as_bytes().to_vec()))
        .with_arg("shapes", ArgRef::Inline(shapes.into_bytes()));
    let result = block_on(kernel.issue(request, &Capability::root()));
    assert!(
        matches!(&result, Err(Error::InvalidArgument { name, .. }) if name == "shapes"),
        "{:?}",
        result.map(|r| String::from_utf8_lossy(&r.bytes).into_owned())
    );
    assert_eq!(stub.requests(), Vec::<String>::new());
}
