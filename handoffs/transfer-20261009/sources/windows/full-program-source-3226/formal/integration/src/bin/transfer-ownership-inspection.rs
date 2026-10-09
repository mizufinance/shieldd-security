//! Bounded first ownership-loop metadata; ordinary/repeated full-row parity.
use commonware_codec::Encode;
use commonware_cryptography::blake3::CoreBlake3;
use commonware_cryptography::zk::circuit::CircuitIdx;
use commonware_cryptography::zk::pari::InputLayout;
use serde_json::{json, Value};
use shieldd_sdk_circuits::{catalogue, proof::Family, scalar::inspection::Observed};
use std::{
    fs::{File, OpenOptions},
    io::{BufReader, BufWriter, Read, Write},
    path::{Path, PathBuf},
};

fn packet_blake3(bytes: &[u8]) -> String {
    let mut hasher = CoreBlake3::new();
    hasher.update(bytes);
    hasher.finalize().to_hex().to_string()
}

fn index(i: &CircuitIdx) -> Value {
    match i {
        CircuitIdx::Constant(i) => json!([0, i]),
        CircuitIdx::Witness(i) => json!([1, i]),
        CircuitIdx::Node(i) => json!([2, i]),
    }
}
fn observed(v: &Observed) -> Value {
    match v {
        Observed::Source(i) => json!({"source":index(i)}),
        Observed::Native(v) => json!({"native":hex::encode(v.encode())}),
    }
}
fn pair(p: &[Observed; 2]) -> Value {
    json!(p.iter().map(observed).collect::<Vec<_>>())
}
struct RowSpool {
    path: PathBuf,
    layout: InputLayout,
    domain: usize,
    digest: [u8; 32],
    public: usize,
    blocks: Vec<usize>,
    rows: usize,
}
impl Drop for RowSpool {
    fn drop(&mut self) {
        let _ = std::fs::remove_file(&self.path);
    }
}
impl RowSpool {
    fn new(compiled: &catalogue::Compiled) -> anyhow::Result<Self> {
        let suffix = std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)?
            .as_nanos();
        let path = std::env::temp_dir().join(format!(
            "shieldd-ownership-{}-{suffix}.rows",
            std::process::id()
        ));
        let file = OpenOptions::new()
            .write(true)
            .create_new(true)
            .open(&path)?;
        let relation = &compiled.relation;
        let spool = Self {
            path,
            layout: compiled.layout.clone(),
            domain: relation.domain_size(),
            digest: *relation.digest(),
            public: relation.public_inputs(),
            blocks: relation.blocks().to_vec(),
            rows: relation.inspect_rows().len(),
        };
        let mut writer = BufWriter::new(file);
        for (a, b) in relation.inspect_rows() {
            for terms in [a, b] {
                writer.write_all(&u64::try_from(terms.len())?.to_be_bytes())?;
                for (column, coefficient) in terms {
                    writer.write_all(&column.to_be_bytes())?;
                    writer.write_all(&coefficient.encode())?;
                }
            }
        }
        writer.flush()?;
        writer.get_ref().sync_all()?;
        Ok(spool)
    }
    fn shape(&self) -> Value {
        json!({"schema":"shieldd-transfer-ordered-spool-v1", "domain_size":self.domain,
            "relation_digest":hex::encode(self.digest),"full_rows":self.rows,
            "public_inputs":self.public,"blocks":self.blocks,
            "source_public":self.layout.public().iter().map(index).collect::<Vec<_>>(),
            "source_blocks":self.layout.blocks().iter().map(|block|
                block.iter().map(index).collect::<Vec<_>>()).collect::<Vec<_>>()})
    }
    fn persist(&self, prefix: &str, compilation: &str) -> anyhow::Result<()> {
        let mut source = BufReader::new(File::open(&self.path)?);
        let mut target = OpenOptions::new()
            .write(true)
            .create_new(true)
            .open(packet_path(prefix, "rows"))?;
        std::io::copy(&mut source, &mut target)?;
        target.sync_all()?;
        let mut shape = self.shape();
        shape["compilation"] = json!(compilation);
        write_packet_json(prefix, "shape.json", &shape)
    }
    fn compare(&self, compiled: &catalogue::Compiled) -> anyhow::Result<()> {
        let relation = &compiled.relation;
        anyhow::ensure!(
            self.layout == compiled.layout
                && self.domain == relation.domain_size()
                && self.digest == *relation.digest()
                && self.public == relation.public_inputs()
                && self.blocks == relation.blocks()
                && self.rows == relation.inspect_rows().len(),
            "ownership relation shape/digest mismatch"
        );
        let mut reader = BufReader::new(File::open(&self.path)?);
        for (row, (a, b)) in relation.inspect_rows().enumerate() {
            let mut actual = Vec::new();
            for terms in [a, b] {
                actual.extend_from_slice(&u64::try_from(terms.len())?.to_be_bytes());
                for (column, coefficient) in terms {
                    actual.extend_from_slice(&column.to_be_bytes());
                    actual.extend_from_slice(&coefficient.encode());
                }
            }
            let mut expected = vec![0; actual.len()];
            reader.read_exact(&mut expected)?;
            anyhow::ensure!(
                actual == expected,
                "ownership ordered row mismatch at {row}"
            );
        }
        let mut trailing = [0];
        anyhow::ensure!(
            reader.read(&mut trailing)? == 0,
            "ownership row spool trailing bytes"
        );
        Ok(())
    }
}
fn packet_path(prefix: &str, suffix: &str) -> PathBuf {
    PathBuf::from(format!("{prefix}.{suffix}"))
}
fn write_packet_json(prefix: &str, suffix: &str, value: &Value) -> anyhow::Result<()> {
    let file = OpenOptions::new()
        .write(true)
        .create_new(true)
        .open(packet_path(prefix, suffix))?;
    let mut writer = BufWriter::new(file);
    serde_json::to_writer(&mut writer, value)?;
    writer.write_all(b"\n")?;
    writer.flush()?;
    writer.get_ref().sync_all()?;
    Ok(())
}
fn read_packet_json(prefix: &str, suffix: &str) -> anyhow::Result<Value> {
    let file = File::open(packet_path(prefix, suffix))?;
    anyhow::ensure!(
        file.metadata()?.len() <= 8 * 1024 * 1024,
        "spool JSON size bound"
    );
    Ok(serde_json::from_reader(BufReader::new(file))?)
}
fn ensure_original_shape(shape: &Value) -> anyhow::Result<()> {
    anyhow::ensure!(
        shape["schema"] == "shieldd-transfer-ordered-spool-v1"
            && shape["domain_size"] == 262144
            && shape["full_rows"] == 200770
            && shape["public_inputs"] == 1
            && shape["blocks"] == json!([1])
            && shape["relation_digest"]
                == "16e7b009b763be55ca21f423f4f97e8c132b40b6adbcd06f6a3be17f2d0ef236",
        "spool original Transfer identity/shape mismatch"
    );
    let public = shape["source_public"]
        .as_array()
        .ok_or_else(|| anyhow::anyhow!("spool public sources absent"))?;
    let blocks = shape["source_blocks"]
        .as_array()
        .ok_or_else(|| anyhow::anyhow!("spool block sources absent"))?;
    anyhow::ensure!(
        public.len() == 1
            && blocks.len() == 1
            && blocks[0].as_array().is_some_and(|b| b.len() == 1),
        "spool source layout shape mismatch"
    );
    Ok(())
}
fn compare_framed_rows(
    left: &Path,
    right: &Path,
    rows: usize,
    domain: usize,
) -> anyhow::Result<()> {
    let mut left = BufReader::new(File::open(left)?);
    let mut right = BufReader::new(File::open(right)?);
    for row in 0..rows {
        for axis in 0..2 {
            let mut a = [0u8; 8];
            let mut b = [0u8; 8];
            left.read_exact(&mut a)?;
            right.read_exact(&mut b)?;
            anyhow::ensure!(a == b, "spool row {row} axis {axis} term count mismatch");
            let count = usize::try_from(u64::from_be_bytes(a))?;
            anyhow::ensure!(count <= domain, "spool term count bound");
            for term in 0..count {
                let mut a = [0u8; 36];
                let mut b = [0u8; 36];
                left.read_exact(&mut a)?;
                right.read_exact(&mut b)?;
                anyhow::ensure!(a == b, "spool row {row} axis {axis} term {term} mismatch");
            }
        }
    }
    let mut trailing = [0];
    anyhow::ensure!(
        left.read(&mut trailing)? == 0 && right.read(&mut trailing)? == 0,
        "spool row trailing bytes"
    );
    Ok(())
}
fn spool_identity(path: &Path, shape: &Value) -> anyhow::Result<String> {
    use commonware_cryptography::blake3::CoreBlake3;
    let mut hasher = CoreBlake3::new();
    hasher.update(b"_COMMONWARE_CRYPTOGRAPHY_ZK_PARI_RELATION_DIGEST");
    let domain = shape["domain_size"]
        .as_u64()
        .ok_or_else(|| anyhow::anyhow!("spool domain absent"))?;
    let rows = shape["full_rows"]
        .as_u64()
        .ok_or_else(|| anyhow::anyhow!("spool row count absent"))?;
    hasher.update(&domain.to_be_bytes());
    hasher.update(&rows.to_be_bytes());
    let hash_sources = |hasher: &mut CoreBlake3, value: &Value| -> anyhow::Result<()> {
        let sources = value
            .as_array()
            .ok_or_else(|| anyhow::anyhow!("spool source array absent"))?;
        hasher.update(&u64::try_from(sources.len())?.to_be_bytes());
        for source in sources {
            let source = source
                .as_array()
                .ok_or_else(|| anyhow::anyhow!("spool source pair absent"))?;
            anyhow::ensure!(source.len() == 2, "spool source pair shape");
            let tag = source[0]
                .as_u64()
                .ok_or_else(|| anyhow::anyhow!("spool source tag absent"))?;
            let index = source[1]
                .as_u64()
                .ok_or_else(|| anyhow::anyhow!("spool source index absent"))?;
            anyhow::ensure!(tag <= 2, "spool source tag bound");
            hasher.update(&[u8::try_from(tag)?]);
            hasher.update(&u32::try_from(index)?.to_be_bytes());
        }
        Ok(())
    };
    hash_sources(&mut hasher, &shape["source_public"])?;
    let blocks = shape["source_blocks"]
        .as_array()
        .ok_or_else(|| anyhow::anyhow!("spool source blocks absent"))?;
    hasher.update(&u64::try_from(blocks.len())?.to_be_bytes());
    for block in blocks {
        hash_sources(&mut hasher, block)?;
    }
    let modulus = hex::decode("73eda753299d7d483339d80809a1d80553bda402fffe5bfeffffffff00000001")?;
    let mut reader = BufReader::new(File::open(path)?);
    for row in 0..rows {
        for label in [b"A", b"B"] {
            hasher.update(label);
            let mut count = [0u8; 8];
            reader.read_exact(&mut count)?;
            let size = u64::from_be_bytes(count);
            anyhow::ensure!(size <= domain, "spool term count bound at {row}");
            hasher.update(&count);
            let mut previous = None;
            for _ in 0..size {
                let mut term = [0u8; 36];
                reader.read_exact(&mut term)?;
                let column = u32::from_be_bytes(term[..4].try_into()?);
                anyhow::ensure!(
                    u64::from(column) < domain
                        && previous.is_none_or(|p| column > p)
                        && term[4..].iter().any(|&b| b != 0)
                        && &term[4..] < modulus.as_slice(),
                    "spool noncanonical term at {row}"
                );
                previous = Some(column);
                hasher.update(&term);
            }
        }
    }
    let mut trailing = [0];
    anyhow::ensure!(reader.read(&mut trailing)? == 0, "spool row trailing bytes");
    Ok(hex::encode(hasher.finalize().as_bytes()))
}
fn qualified_metadata(
    first: &str,
    ordinary1: &str,
    ordinary2: &str,
    repeated: &str,
) -> anyhow::Result<Value> {
    let prefixes = [first, ordinary1, ordinary2, repeated];
    let paths = prefixes
        .iter()
        .map(|prefix| std::fs::canonicalize(packet_path(prefix, "rows")))
        .collect::<std::io::Result<Vec<_>>>()?;
    for i in 0..paths.len() {
        anyhow::ensure!(
            !paths[..i].contains(&paths[i]),
            "qualification needs four distinct compilation spools"
        );
    }
    let mut shapes = prefixes
        .iter()
        .map(|prefix| read_packet_json(prefix, "shape.json"))
        .collect::<anyhow::Result<Vec<_>>>()?;
    for (shape, kind) in shapes
        .iter_mut()
        .zip(["observer", "ordinary", "ordinary", "observer"])
    {
        ensure_original_shape(shape)?;
        anyhow::ensure!(
            shape["compilation"] == kind,
            "spool compilation kind mismatch"
        );
        shape
            .as_object_mut()
            .ok_or_else(|| anyhow::anyhow!("spool shape is not object"))?
            .remove("compilation");
    }
    anyhow::ensure!(
        shapes.iter().all(|shape| shape == &shapes[0]),
        "spool full source/shape mismatch"
    );
    anyhow::ensure!(
        spool_identity(&paths[0], &shapes[0])? == shapes[0]["relation_digest"].as_str().unwrap(),
        "spool bytes/source layout do not match declared original relation digest"
    );
    for path in &paths[1..] {
        compare_framed_rows(&paths[0], path, 200770, 262144)?;
    }
    let mut pending = read_packet_json(first, "pending.json")?;
    let repeat = read_packet_json(repeated, "pending.json")?;
    anyhow::ensure!(pending == repeat, "repeated observer JSON mismatch");
    anyhow::ensure!(
        pending["ordinary_full_ordered_rows_equal"] == false
            && pending["relation_digest"] == shapes[0]["relation_digest"]
            && pending["domain_size"] == shapes[0]["domain_size"]
            && pending["full_rows"] == shapes[0]["full_rows"]
            && pending["constant_copy"] == 200692,
        "pending observer identity/shape/parity mismatch"
    );
    match pending["schema"].as_str() {
        Some("shieldd-transfer-authorization-roles-v1") => {}
        Some("shieldd-transfer-fixed-spend-v1") |
        Some("shieldd-transfer-note-spend-v1") |
        Some("shieldd-transfer-note-hash-block-v1") |
        Some("shieldd-transfer-note-hash-pages-v1") |
        Some("shieldd-transfer-note-t4-pages-v1") => {
            if pending["schema"] == "shieldd-transfer-note-hash-pages-v1" {
                qualify_note_hash_pages(first,repeated,&pending)?;
            }
            if pending["schema"] == "shieldd-transfer-note-t4-pages-v1" {
                qualify_note_t4_pages(first,repeated,&pending)?;
            }
            anyhow::ensure!(
                pending["repeated_observations_equal"] == false,
                "pending fixed repeat flag mismatch"
            );
            pending["repeated_observations_equal"] = json!(true);
        }
        _ => anyhow::bail!("unsupported pending observer schema"),
    }
    pending["ordinary_full_ordered_rows_equal"] = json!(true);
    Ok(pending)
}
fn qualify_spools(
    first: &str,
    ordinary1: &str,
    ordinary2: &str,
    repeated: &str,
) -> anyhow::Result<()> {
    let metadata = qualified_metadata(first, ordinary1, ordinary2, repeated)?;
    println!("{}", serde_json::to_string(&metadata)?);
    Ok(())
}
fn main() -> anyhow::Result<()> {
    let args: Vec<_> = std::env::args().skip(1).collect();
    if args.len() == 2 && args[0] == "full-program-spool" {
        return capture_full_program(&args[1]);
    }
    if args.len() == 2 && args[0] == "note-t4-pages-spool" {
        return capture_note_t4_pages(&args[1]);
    }
    if args.len() == 2 && args[0] == "note-hash-pages-spool" {
        return capture_note_hash_pages(&args[1]);
    }
    if args.len() == 6 && args[0] == "note-hash-spool" {
        return capture_note_hash(&args[1],args[2].parse()?,&args[3],args[4].parse()?,args[5].parse()?);
    }
    if args.len() == 2 && args[0] == "note-spend-spool" {
        return capture_note_spend(&args[1]);
    }
    if args.len() == 2 && args[0] == "roles-spool" {
        return capture_roles(Some(&args[1]));
    }
    if args.len() == 2 && args[0] == "ordinary-spool" {
        let compiled = catalogue::compile(Family::Transfer)?;
        let spool = RowSpool::new(&compiled)?;
        drop(compiled);
        ensure_original_shape(&spool.shape())?;
        return spool.persist(&args[1], "ordinary");
    }
    if args.len() == 4 && args[0] == "fixed-spend-spool" {
        return capture_fixed_spend(args[1].parse()?, args[2].parse()?, Some(&args[3]));
    }
    if args.len() == 5 && args[0] == "qualify-spools" {
        return qualify_spools(&args[1], &args[2], &args[3], &args[4]);
    }
    if args == ["roles"] {
        return capture_roles(None);
    }
    anyhow::ensure!(
        args.is_empty() || args.len() == 2 || args.len() == 3,
        "expected optional window-start window-count [rnk-dh]"
    );
    let (start, count) = if args.is_empty() {
        (0, 16)
    } else {
        (args[0].parse()?, args[1].parse()?)
    };
    if args.len() == 3 && args[2] == "rnk-hash" {
        anyhow::ensure!(
            count == 1,
            "RNK hash capture selects exactly one permutation"
        );
        return capture_hash(start);
    }
    if args.len() == 3 && args[2] == "fixed-spend" {
        return capture_fixed_spend(start, count, None);
    }
    let rnk_dh = args.len() == 3;
    anyhow::ensure!(
        !rnk_dh || args[2] == "rnk-dh",
        "unknown variable-loop occurrence"
    );
    let inspect = if rnk_dh {
        catalogue::inspect_transfer_rnk_dh
    } else {
        catalogue::inspect_transfer_ownership
    };
    eprintln!(
        "capture selected authorization variable loop windows {start}..{}",
        start + count
    );
    let catalogue::OwnershipInspection {
        compiled,
        report,
        reduction,
        ivk_handles,
        selected,
        expressions,
        constant_copy,
        nodes,
        window_start,
        window_count,
    } = inspect(start, count)?;
    anyhow::ensure!(
        compiled.relation.public_inputs() == 1
            && compiled.relation.blocks() == [1]
            && compiled.layout.public().len() == 1
            && compiled.layout.blocks().len() == 1
            && compiled.layout.blocks()[0].len() == 1,
        "Transfer shape changed"
    );
    eprintln!("spool full ordered captured rows and release relation");
    let spool = RowSpool::new(&compiled)?;
    drop(compiled);
    for _ in 0..2 {
        eprintln!("ordinary full ordered relation comparison");
        let ordinary = catalogue::compile(Family::Transfer)?;
        spool.compare(&ordinary)?;
    }
    eprintln!("repeat ownership capture");
    let repeated = inspect(start, count)?;
    spool.compare(&repeated.compiled)?;
    anyhow::ensure!(
        repeated.report == report
            && repeated.reduction == reduction
            && repeated.ivk_handles == ivk_handles
            && repeated.selected == selected
            && repeated.expressions == expressions
            && repeated.nodes == nodes
            && repeated.constant_copy == constant_copy,
        "ownership repeat mismatch"
    );
    drop(repeated);
    let mut metadata = json!({
        "schema":"shieldd-transfer-ownership-v1", "family":"transfer",
        "scope":"bounded first ownership variable-loop observation; source/row/group joins open",
        "relation_digest":hex::encode(spool.digest), "domain_size":spool.domain,
        "full_rows":spool.rows, "constant_copy":constant_copy,
        "ivk_handles":ivk_handles.iter().map(index).collect::<Vec<_>>(),
        "remainder":index(&reduction.remainder),
        "remainder_bits":reduction.remainder_bits.iter().map(index).collect::<Vec<_>>(),
        "window_start":window_start, "window_count":window_count,
        "total_windows":126,
        "base":pair(&report.base), "twice":pair(&report.twice), "triple":pair(&report.triple),
        "bits":report.bits.iter().map(index).collect::<Vec<_>>(),
        "output":pair(&report.output), "target":report.target.as_ref().map(pair),
        "windows":report.windows[start..start+count].iter().map(|w|w.iter().map(pair).collect::<Vec<_>>()).collect::<Vec<_>>(),
        "window_bits":report.window_bits[start..start+count].iter().map(|b|b.iter().map(index).collect::<Vec<_>>()).collect::<Vec<_>>(),
        "quotients":report.quotients[..2].iter().chain(report.quotients[2+3*start..2+3*(start+count)].iter())
            .map(|q|q.iter().map(observed).collect::<Vec<_>>()).collect::<Vec<_>>(),
        "expressions":selected.iter().zip(&expressions).map(|(source,terms)|json!({
            "source":index(source), "terms":terms.iter().map(|(column,coefficient)|
                json!([column,hex::encode(coefficient.encode())])).collect::<Vec<_>>() })).collect::<Vec<_>>(),
        "nodes":nodes.iter().map(|(node,multiply,left,right)|json!({
            "index":node,"multiply":multiply,"left":index(left),"right":index(right)})).collect::<Vec<_>>()
    });
    if rnk_dh {
        metadata["schema"] = json!("shieldd-transfer-rnk-dh-v1");
        metadata["scope"] = json!("bounded RNK-DH variable-loop observation; hash references are boundary-only; source/row/group joins open");
        metadata.as_object_mut().unwrap().remove("target");
        metadata["nonidentity_inverse"] = observed(report.nonidentity_inverse.as_ref().unwrap());
        let bindings = report.rnk.as_ref().unwrap();
        metadata["rnk_bindings"] = json!({
            "inputs":bindings.inputs.iter().map(observed).collect::<Vec<_>>(),
            "hash":observed(&bindings.hash), "commitment":observed(&bindings.commitment),
            "regulated":observed(&bindings.regulated), "registered":observed(&bindings.registered),
            "effective_nk":observed(&bindings.effective_nk)
        });
    }
    println!("{}", serde_json::to_string(&metadata)?);
    Ok(())
}

fn capture_fixed_spend(start: usize, count: usize, spill: Option<&str>) -> anyhow::Result<()> {
    eprintln!(
        "capture bounded spend fixed-loop windows {start}..{}",
        start + count
    );
    let catalogue::FixedSpendInspection {
        compiled,
        report,
        canonical_endpoint,
        canonical_steps,
        selected,
        expressions,
        constant_copy,
    } = catalogue::inspect_transfer_fixed_spend(start, count)?;
    anyhow::ensure!(
        compiled.relation.public_inputs() == 1
            && compiled.relation.blocks() == [1]
            && compiled.layout.public().len() == 1
            && compiled.layout.blocks().len() == 1
            && compiled.layout.blocks()[0].len() == 1,
        "Transfer shape changed"
    );
    let spool = RowSpool::new(&compiled)?;
    anyhow::ensure!(
        hex::encode(spool.digest)
            == "16e7b009b763be55ca21f423f4f97e8c132b40b6adbcd06f6a3be17f2d0ef236"
            && spool.domain == 262144
            && spool.rows == 200770
            && constant_copy == 200692,
        "fixed capture differs from original Transfer relation identity/shape"
    );
    drop(compiled);
    if let Some(prefix) = spill {
        spool.persist(prefix, "observer")?;
    }
    if spill.is_none() {
        for _ in 0..2 {
            eprintln!("ordinary full ordered relation comparison");
            let ordinary = catalogue::compile(Family::Transfer)?;
            spool.compare(&ordinary)?;
        }
        eprintln!("repeat bounded fixed-loop capture");
        let repeated = catalogue::inspect_transfer_fixed_spend(start, count)?;
        spool.compare(&repeated.compiled)?;
        anyhow::ensure!(
            repeated.report == report
                && repeated.canonical_endpoint == canonical_endpoint
                && repeated.canonical_steps == canonical_steps
                && repeated.selected == selected
                && repeated.expressions == expressions
                && repeated.constant_copy == constant_copy,
            "fixed spend repeat mismatch"
        );
        drop(repeated);
    }
    let metadata = json!({
        "schema":"shieldd-transfer-fixed-spend-v1", "family":"transfer",
        "scope":"bounded actual ascending fixed-window arithmetic and LCs; canonical randomizer/native semantic joins open",
        "relation_digest":hex::encode(spool.digest), "domain_size":spool.domain,
        "full_rows":spool.rows, "constant_copy":constant_copy,
        "ordinary_full_ordered_rows_equal":spill.is_none(), "repeated_observations_equal":spill.is_none(),
        "window_start":report.window_start, "window_count":report.window_count, "total_windows":126,
        "randomizer":observed(&report.randomizer), "generator":pair(&report.generator),
        "bits":report.bits.iter().map(index).collect::<Vec<_>>(), "output":pair(&report.output),
        "canonical":{"endpoint":index(&canonical_endpoint),
            "steps":canonical_steps.iter().map(|step|step.iter().map(observed).collect::<Vec<_>>()).collect::<Vec<_>>()},
        "windows":report.windows.iter().map(|window| json!({
            "bits":window.bits.iter().map(index).collect::<Vec<_>>(),
            "table":window.table.iter().map(pair).collect::<Vec<_>>(),
            "points":window.points.iter().map(pair).collect::<Vec<_>>(),
            "arithmetic":window.arithmetic.iter().map(observed).collect::<Vec<_>>(),
            "quotient":window.quotient.iter().map(observed).collect::<Vec<_>>()
        })).collect::<Vec<_>>(),
        "expressions":selected.iter().zip(&expressions).map(|(source, terms)| json!({
            "source":index(source), "terms":terms.iter().map(|(column, coefficient)|
                json!([column, hex::encode(coefficient.encode())])).collect::<Vec<_>>()
        })).collect::<Vec<_>>()
    });
    if let Some(prefix) = spill {
        write_packet_json(prefix, "pending.json", &metadata)?;
    } else {
        println!("{}", serde_json::to_string(&metadata)?);
    }
    Ok(())
}

fn capture_roles(spill: Option<&str>) -> anyhow::Result<()> {
    eprintln!("capture Transfer caller/spend authorization boundary roles");
    let catalogue::TransferRoleInspection {
        compiled,
        report,
        rnk,
        ivk_handles,
        selected,
        expressions,
        constant_copy,
    } = catalogue::inspect_transfer_roles()?;
    anyhow::ensure!(
        compiled.relation.public_inputs() == 1
            && compiled.relation.blocks() == [1]
            && compiled.layout.public().len() == 1
            && compiled.layout.blocks().len() == 1
            && compiled.layout.blocks()[0].len() == 1,
        "Transfer shape changed"
    );
    let spool = RowSpool::new(&compiled)?;
    drop(compiled);
    if let Some(prefix) = spill {
        ensure_original_shape(&spool.shape())?;
        anyhow::ensure!(
            constant_copy == 200692,
            "original Transfer constant-copy changed"
        );
        spool.persist(prefix, "observer")?;
    }
    if spill.is_none() {
        for _ in 0..2 {
            eprintln!("ordinary full ordered relation comparison");
            let ordinary = catalogue::compile(Family::Transfer)?;
            spool.compare(&ordinary)?;
        }
        eprintln!("repeat Transfer authorization role capture");
        let repeated = catalogue::inspect_transfer_roles()?;
        spool.compare(&repeated.compiled)?;
        anyhow::ensure!(
            repeated.report == report
                && repeated.rnk == rnk
                && repeated.ivk_handles == ivk_handles
                && repeated.selected == selected
                && repeated.expressions == expressions
                && repeated.constant_copy == constant_copy,
            "authorization roles repeat mismatch"
        );
        drop(repeated);
    }
    let a = &report.caller;
    let s = &report.spend;
    let metadata = json!({
        "schema":"shieldd-transfer-authorization-roles-v1","family":"transfer",
        "scope":"existing caller/spend authorization boundaries and LCs only; source/row/native semantic joins open",
        "relation_digest":hex::encode(spool.digest),"domain_size":spool.domain,
        "full_rows":spool.rows,"constant_copy":constant_copy,"ordinary_full_ordered_rows_equal":spill.is_none(),
        "ivk_handles":ivk_handles.iter().map(index).collect::<Vec<_>>(),
        "caller":{"regulated":observed(&a.regulated),"asset":observed(&a.asset),
            "leaf_ring":pair(&a.leaf_ring),"fixed_ring":pair(&a.fixed_ring),"selected_ring":pair(&a.selected_ring),
            "address":a.address.iter().map(observed).collect::<Vec<_>>(),"rnk_dh":pair(&a.rnk_dh),
            "registered_rnk":observed(&a.registered_rnk),"ak":pair(&a.ak),
            "nk":observed(&a.nk),"effective_nk":observed(&a.effective_nk)},
        "spend":{"ak":pair(&s.ak),"randomizer":observed(&s.randomizer),
            "bits":s.bits.iter().map(index).collect::<Vec<_>>(),"generator":pair(&s.generator),
            "contribution":pair(&s.contribution),"computed":pair(&s.computed),"rk":pair(&s.rk)},
        "rnk_bindings":{"inputs":rnk.inputs.iter().map(observed).collect::<Vec<_>>(),
            "hash":observed(&rnk.hash),"commitment":observed(&rnk.commitment),
            "regulated":observed(&rnk.regulated),"registered":observed(&rnk.registered),
            "effective_nk":observed(&rnk.effective_nk)},
        "expressions":selected.iter().zip(&expressions).map(|(source,terms)|json!({
            "source":index(source),"terms":terms.iter().map(|(column,coefficient)|
                json!([column,hex::encode(coefficient.encode())])).collect::<Vec<_>>()
        })).collect::<Vec<_>>()
    });
    if let Some(prefix) = spill {
        write_packet_json(prefix, "pending.json", &metadata)?;
    } else {
        println!("{}", serde_json::to_string(&metadata)?);
    }
    Ok(())
}

fn capture_hash(block: usize) -> anyhow::Result<()> {
    eprintln!("capture RNK/commitment permutation {block}");
    let catalogue::RnkHashInspection {
        compiled,
        block,
        hashes,
        rnk,
        ivk_handles,
        selected,
        expressions,
        constant_copy,
        nodes,
    } = catalogue::inspect_transfer_rnk_hash(block)?;
    anyhow::ensure!(
        compiled.relation.public_inputs() == 1
            && compiled.relation.blocks() == [1]
            && compiled.layout.public().len() == 1
            && compiled.layout.blocks().len() == 1
            && compiled.layout.blocks()[0].len() == 1,
        "Transfer shape changed"
    );
    let spool = RowSpool::new(&compiled)?;
    drop(compiled);
    for _ in 0..2 {
        eprintln!("ordinary full ordered relation comparison");
        let ordinary = catalogue::compile(Family::Transfer)?;
        spool.compare(&ordinary)?;
    }
    eprintln!("repeat selected hash permutation capture");
    let repeated = catalogue::inspect_transfer_rnk_hash(block)?;
    spool.compare(&repeated.compiled)?;
    anyhow::ensure!(
        repeated.block == block
            && repeated.hashes == hashes
            && repeated.rnk == rnk
            && repeated.ivk_handles == ivk_handles
            && repeated.selected == selected
            && repeated.expressions == expressions
            && repeated.nodes == nodes
            && repeated.constant_copy == constant_copy,
        "RNK hash repeat mismatch"
    );
    drop(repeated);
    let metadata = json!({
        "schema":"shieldd-transfer-rnk-hash-block-v1","family":"transfer",
        "scope":"one existing permutation cone; before states are after absorption; other boundaries have LCs only; semantic joins open",
        "relation_digest":hex::encode(spool.digest),"domain_size":spool.domain,
        "full_rows":spool.rows,"constant_copy":constant_copy,
        "ordinary_full_ordered_rows_equal":true,"block":block,
        "ivk_handles":ivk_handles.iter().map(index).collect::<Vec<_>>(),
        "hashes":hashes.iter().map(|hash|json!({"domain":hash.domain,
            "inputs":hash.inputs.iter().map(observed).collect::<Vec<_>>(),"output":observed(&hash.output),
            "blocks":hash.blocks.iter().map(|block|json!({
                "before":block.before.iter().map(observed).collect::<Vec<_>>(),
                "after":block.after.iter().map(observed).collect::<Vec<_>>()
            })).collect::<Vec<_>>()
        })).collect::<Vec<_>>(),
        "rnk_bindings":{"inputs":rnk.inputs.iter().map(observed).collect::<Vec<_>>(),
            "hash":observed(&rnk.hash),"commitment":observed(&rnk.commitment),
            "regulated":observed(&rnk.regulated),"registered":observed(&rnk.registered),
            "effective_nk":observed(&rnk.effective_nk)},
        "expressions":selected.iter().zip(&expressions).map(|(source,terms)|json!({
            "source":index(source),"terms":terms.iter().map(|(column,coefficient)|
                json!([column,hex::encode(coefficient.encode())])).collect::<Vec<_>>()
        })).collect::<Vec<_>>(),
        "nodes":nodes.iter().map(|(node,multiply,left,right)|json!({
            "index":node,"multiply":multiply,"left":index(left),"right":index(right)
        })).collect::<Vec<_>>()
    });
    println!("{}", serde_json::to_string(&metadata)?);
    Ok(())
}

#[cfg(test)]
mod tests {
    #[test]
    fn framed_comparison_observes_semantic_failures() {
        use super::*;
        let suffix = std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap()
            .as_nanos();
        let directory = std::env::temp_dir().join(format!(
            "shieldd-framed-test-{}-{suffix}",
            std::process::id()
        ));
        std::fs::create_dir(&directory).unwrap();
        let left = directory.join("left.rows");
        let right = directory.join("right.rows");
        let row = |column: u32| {
            let mut value = 1u64.to_be_bytes().to_vec();
            value.extend_from_slice(&column.to_be_bytes());
            value.extend_from_slice(&[0u8; 31]);
            value.push(1);
            value.extend_from_slice(&0u64.to_be_bytes());
            value
        };
        let mut bytes = row(3);
        bytes.extend(row(4));
        std::fs::write(&left, &bytes).unwrap();
        std::fs::write(&right, &bytes).unwrap();
        compare_framed_rows(&left, &right, 2, 8).unwrap();
        let mut reordered = row(4);
        reordered.extend(row(3));
        let mut changed = bytes.clone();
        changed[43] = 2;
        let mut trailing = bytes.clone();
        trailing.push(0);
        for invalid in [
            reordered,
            changed,
            bytes[..bytes.len() - 1].to_vec(),
            trailing,
        ] {
            std::fs::write(&right, invalid).unwrap();
            assert!(compare_framed_rows(&left, &right, 2, 8).is_err());
        }
        let shape = json!({"domain_size":8,"full_rows":2,"source_public":[[1,0]],"source_blocks":[[[1,1]]]});
        let digest = spool_identity(&left, &shape).unwrap();
        let mut changed_shape = shape.clone();
        changed_shape["source_public"] = json!([[1, 2]]);
        assert_ne!(digest, spool_identity(&left, &changed_shape).unwrap());
        let mut noncanonical = bytes.clone();
        noncanonical[12..44].fill(0);
        std::fs::write(&right, noncanonical).unwrap();
        assert!(spool_identity(&right, &shape).is_err());
        std::fs::remove_dir_all(directory).unwrap();
    }
    use super::*;
    use commonware_cryptography::{
        bls12381::primitives::group::Scalar,
        zk::{
            circuit::{self, Var},
            pari::Relation,
        },
    };
    fn tiny() -> catalogue::Compiled {
        let (c, returned) = circuit::build(|ctx| {
            let x = Var::witness(ctx, |_| Scalar::from(3));
            let y = Var::witness(ctx, |_| Scalar::from(4));
            (x.clone() * &y).assert_eq(&Var::native(Scalar::from(12)));
            vec![x, y]
        });
        let layout = InputLayout::new(vec![returned[0]], vec![vec![returned[1]]]).unwrap();
        let relation = Relation::compile(&c, &layout).unwrap();
        catalogue::Compiled {
            family: Family::Transfer,
            relation,
            layout,
        }
    }
    #[test]
    fn exact_ordered_spool_rejects_corruption_truncation_and_trailing_bytes() {
        let compiled = tiny();
        let spool = RowSpool::new(&compiled).unwrap();
        spool.compare(&compiled).unwrap();
        let original = std::fs::read(&spool.path).unwrap();
        let mut offset = 0;
        let mut ranges = Vec::new();
        for _ in 0..spool.rows {
            let start = offset;
            for _ in 0..2 {
                let count =
                    u64::from_be_bytes(original[offset..offset + 8].try_into().unwrap()) as usize;
                offset += 8 + count * 36;
            }
            ranges.push(start..offset);
        }
        assert_eq!(offset, original.len());
        assert!(ranges.len() > 1);
        let last = ranges.len() - 1;
        assert_ne!(
            &original[ranges[0].clone()],
            &original[ranges[last].clone()]
        );
        let mut reordered = original[ranges[last].clone()].to_vec();
        for range in &ranges[1..last] {
            reordered.extend_from_slice(&original[range.clone()]);
        }
        reordered.extend_from_slice(&original[ranges[0].clone()]);
        std::fs::write(&spool.path, &reordered).unwrap();
        assert!(spool
            .compare(&compiled)
            .unwrap_err()
            .to_string()
            .contains("ownership ordered row mismatch"));
        let mut corrupted = original.clone();
        let last = corrupted.len() - 1;
        corrupted[last] ^= 1;
        std::fs::write(&spool.path, &corrupted).unwrap();
        assert!(spool
            .compare(&compiled)
            .unwrap_err()
            .to_string()
            .contains("ownership ordered row mismatch"));
        std::fs::write(&spool.path, &original[..original.len() - 1]).unwrap();
        let truncated = spool.compare(&compiled).unwrap_err();
        assert_eq!(
            truncated.downcast_ref::<std::io::Error>().unwrap().kind(),
            std::io::ErrorKind::UnexpectedEof
        );
        let mut trailing = original.clone();
        trailing.push(0);
        std::fs::write(&spool.path, &trailing).unwrap();
        assert_eq!(
            spool.compare(&compiled).unwrap_err().to_string(),
            "ownership row spool trailing bytes"
        );
        std::fs::write(&spool.path, &original).unwrap();
        spool.compare(&compiled).unwrap();
        let path = spool.path.clone();
        drop(spool);
        assert!(!path.exists());
    }
}

// Included in the EXISTING formal-owned spool exporter in a fresh source stage.
// New dispatch: ["note-spend-spool", prefix] => capture_note_spend(prefix).
// The existing ordinary spill / full ordered compare / repeat qualifier must
// run in separate processes before flags can become true. This emits PENDING.
fn capture_note_spend(prefix: &str) -> anyhow::Result<()> {
    let catalogue::NoteSpendInspection {
        compiled,
        report,
        selected,
        expressions,
        constant_copy,
        nodes,
    } = catalogue::inspect_transfer_note_spend()?;
    let spool = RowSpool::new(&compiled)?;
    ensure_original_shape(&spool.shape())?;
    anyhow::ensure!(constant_copy == 200692, "note-spend constant copy changed");
    spool.persist(prefix, "observer")?;
    drop(compiled);
    let spends = report.spends.iter().map(|spend| {
        let shared = &spend.shared;
        let optional = spend.optional.as_ref().map(|o| json!({
            "domain":o.domain, "slot":o.slot, "seed":observed(&o.seed),
            "synthetic":observed(&o.synthetic), "selected":observed(&o.selected),
            "products":o.products.iter().map(|p|p.iter().map(observed).collect::<Vec<_>>()).collect::<Vec<_>>()
        }));
        json!({"shared":{"asset":observed(&shared.asset),
            "address":shared.address.iter().map(observed).collect::<Vec<_>>(),
            "nk":observed(&shared.nk), "randomizer":observed(&shared.randomizer), "anchor":observed(&shared.anchor)},
            "note":spend.note.iter().map(observed).collect::<Vec<_>>(),
            "commitment":observed(&spend.commitment), "position":observed(&spend.position),
            "amount_bits":spend.amount_bits.iter().map(index).collect::<Vec<_>>(),
            "position_bits":spend.position_bits.iter().map(index).collect::<Vec<_>>(),
            "real_nullifier":observed(&spend.real_nullifier), "computed_anchor":observed(&spend.computed_anchor),
            "nullifier":observed(&spend.nullifier), "dummy":observed(&spend.dummy), "optional":optional})
    }).collect::<Vec<_>>();
    let metadata = json!({"schema":"shieldd-transfer-note-spend-v1", "family":"transfer",
        "scope":"two current Transfer spend source roles and branch LCs; hash/tree/range/native joins open",
        "relation_digest":hex::encode(spool.digest), "domain_size":spool.domain,
        "full_rows":spool.rows, "constant_copy":constant_copy,
        "ordinary_full_ordered_rows_equal":false, "repeated_observations_equal":false,
        "spends":spends,
        "expressions":selected.iter().zip(&expressions).map(|(source,terms)|json!({
            "source":index(source), "terms":terms.iter().map(|(column,coefficient)|
                json!([column,hex::encode(coefficient.encode())])).collect::<Vec<_>>() })).collect::<Vec<_>>(),
        "nodes":nodes.iter().map(|(node,multiply,left,right)|json!({
            "index":node,"multiply":multiply,"left":index(left),"right":index(right)})).collect::<Vec<_>>()});
    write_packet_json(prefix, "pending.json", &metadata)
}

// Include in the existing ownership spool runner in a NEW stage only.
fn capture_note_hash(
    prefix: &str,
    slot: usize,
    role: &str,
    level: usize,
    block: usize,
) -> anyhow::Result<()> {
    use shieldd_sdk_circuits::hash::note_inspection::Role;
    let target = match (role, level) {
        ("commitment", 0) => Role::Commitment,
        ("nullifier", 0) => Role::Nullifier,
        ("dummy", 0) => Role::Dummy,
        ("state", level) if level < 24 => Role::StateLevel(level),
        _ => anyhow::bail!("invalid note hash role/level"),
    };
    let catalogue::NoteHashInspection {
        compiled,
        spends: _,
        hash,
        selected,
        expressions,
        constant_copy,
        nodes,
    } = catalogue::inspect_transfer_note_hash(slot, target, block)?;
    let spool = RowSpool::new(&compiled)?;
    ensure_original_shape(&spool.shape())?;
    anyhow::ensure!(constant_copy == 200692, "note hash constant copy changed");
    spool.persist(prefix, "observer")?;
    drop(compiled);
    let metadata = json!({"schema":"shieldd-transfer-note-hash-block-v1","family":"transfer",
        "scope":"one input-note permutation cone and two note source LCs; tree wiring and native joins open",
        "relation_digest":hex::encode(spool.digest),"domain_size":spool.domain,"full_rows":spool.rows,
        "constant_copy":constant_copy,"ordinary_full_ordered_rows_equal":false,"repeated_observations_equal":false,
        "slot":slot,"role":role,"level":level,"block":block,
        "hash":{"domain":hash.domain,"inputs":hash.inputs.iter().map(observed).collect::<Vec<_>>(),
            "output":observed(&hash.output),"blocks":hash.blocks.iter().map(|b|json!({
                "before":b.before.iter().map(observed).collect::<Vec<_>>(),
                "after":b.after.iter().map(observed).collect::<Vec<_>>() })).collect::<Vec<_>>()},
        "expressions":selected.iter().zip(&expressions).map(|(source,terms)|json!({"source":index(source),
            "terms":terms.iter().map(|(column,coefficient)|json!([column,hex::encode(coefficient.encode())])).collect::<Vec<_>>() })).collect::<Vec<_>>(),
        "nodes":nodes.iter().map(|(node,multiply,left,right)|json!({"index":node,"multiply":multiply,
            "left":index(left),"right":index(right)})).collect::<Vec<_>>()});
    write_packet_json(prefix, "pending.json", &metadata)
}

// Existing spool runner only, NEW stage. Ordinary2+repeat qualification remains
// in qualified_metadata; this adds exact bounded page-byte checks to that path.
fn capture_note_hash_pages(prefix: &str) -> anyhow::Result<()> {
    use shieldd_sdk_circuits::hash::note_inspection::Role;
    let mut count = 0;
    let (compiled, constant_copy) = catalogue::inspect_transfer_note_hash_pages(
        |ordinal, page| {
            anyhow::ensure!(
                ordinal == count && count < 55,
                "note hash page callback order/overflow"
            );
            let (role, level) = match page.hash.role {
                Role::Commitment => ("commitment", 0),
                Role::Nullifier => ("nullifier", 0),
                Role::Dummy => ("dummy", 0),
                Role::StateLevel(level) => ("state", level),
            };
            let body = json!({"slot":page.hash.slot,"role":role,"level":level,"block":page.hash.block,
            "hash":{"domain":page.hash.domain,"inputs":page.hash.inputs.iter().map(observed).collect::<Vec<_>>(),
                "output":observed(&page.hash.output),"blocks":page.hash.blocks.iter().map(|b|json!({
                    "before":b.before.iter().map(observed).collect::<Vec<_>>(),
                    "after":b.after.iter().map(observed).collect::<Vec<_>>() })).collect::<Vec<_>>()},
            "expressions":page.selected.iter().zip(&page.expressions).map(|(source,terms)|json!({"source":index(source),
                "terms":terms.iter().map(|(column,coefficient)|json!([column,hex::encode(coefficient.encode())])).collect::<Vec<_>>() })).collect::<Vec<_>>(),
            "nodes":page.nodes.iter().map(|(node,multiply,left,right)|json!({"index":node,"multiply":multiply,
                "left":index(left),"right":index(right)})).collect::<Vec<_>>()});
            anyhow::ensure!(
                serde_json::to_vec(&body)?.len() <= 4 * 1024 * 1024,
                "note hash page JSON exceeds4MiB"
            );
            write_packet_json(prefix, &format!("page{ordinal}.observations.json"), &body)?;
            // The owned page cone/LCs and JSON are dropped before the next callback.
            count += 1;
            Ok(())
        },
    )?;
    anyhow::ensure!(
        count == 55 && constant_copy == 200692,
        "incomplete note hash page run/copy"
    );
    let spool = RowSpool::new(&compiled)?;
    ensure_original_shape(&spool.shape())?;
    spool.persist(prefix, "observer")?;
    drop(compiled);
    let mut pages = Vec::new();
    for ordinal in 0..55 {
        let mut body = read_packet_json(prefix, &format!("page{ordinal}.observations.json"))?;
        let object = body
            .as_object_mut()
            .ok_or_else(|| anyhow::anyhow!("note hash page not object"))?;
        for (key,value) in [
            ("schema",json!("shieldd-transfer-note-hash-block-v1")),("family",json!("transfer")),
            ("scope",json!("one input-note permutation cone and two note source LCs; tree wiring and native joins open")),
            ("relation_digest",json!(hex::encode(spool.digest))),("domain_size",json!(spool.domain)),
            ("full_rows",json!(spool.rows)),("constant_copy",json!(constant_copy)),
            ("ordinary_full_ordered_rows_equal",json!(false)),("repeated_observations_equal",json!(false))] {
            object.insert(key.into(),value);
        }
        write_packet_json(prefix, &format!("page{ordinal}.pending.json"), &body)?;
        let bytes = read_note_hash_page(prefix, ordinal)?;
        pages.push(
            json!({"ordinal":ordinal,"slot":body["slot"],"role":body["role"],"level":body["level"],
            "block":body["block"],"blake3":packet_blake3(&bytes)}),
        );
    }
    // Only successful completion creates this manifest. Partial callback files
    // cannot enter the ordinary/repeat qualifier without it.
    write_packet_json(
        prefix,
        "pending.json",
        &json!({"schema":"shieldd-transfer-note-hash-pages-v1","family":"transfer",
        "scope":"55 bounded input-note permutation pages from one lowering; tree wiring/native joins open",
        "relation_digest":hex::encode(spool.digest),"domain_size":spool.domain,"full_rows":spool.rows,"constant_copy":constant_copy,
        "ordinary_full_ordered_rows_equal":false,"repeated_observations_equal":false,"pages":pages}),
    )
}
fn read_note_hash_page(prefix: &str, ordinal: usize) -> anyhow::Result<Vec<u8>> {
    let file = File::open(format!("{prefix}.page{ordinal}.pending.json"))?;
    let mut bytes = Vec::new();
    file.take(4 * 1024 * 1024 + 1).read_to_end(&mut bytes)?;
    anyhow::ensure!(
        !bytes.is_empty() && bytes.len() <= 4 * 1024 * 1024,
        "note hash page byte bound"
    );
    Ok(bytes)
}
fn qualify_note_hash_pages(first: &str, repeated: &str, pending: &Value) -> anyhow::Result<()> {
    let pages = pending["pages"]
        .as_array()
        .ok_or_else(|| anyhow::anyhow!("missing note hash page inventory"))?;
    anyhow::ensure!(pages.len() == 55, "note hash manifest page count");
    for (ordinal, descriptor) in pages.iter().enumerate() {
        let slot = if ordinal >= 27 { 1usize } else { 0usize };
        let offset = if slot == 0 { ordinal } else { ordinal - 27 };
        let (role, level, block) = match offset {
            0..=1 => ("commitment", 0, offset),
            2 => ("nullifier", 0, 0),
            3..=26 => ("state", offset - 3, 0),
            27 if slot == 1 => ("dummy", 0, 0),
            _ => anyhow::bail!("invalid native note hash page inventory"),
        };
        anyhow::ensure!(
            descriptor.as_object().map(|d| d.len()) == Some(6)
                && descriptor["slot"] == slot
                && descriptor["role"] == role
                && descriptor["level"] == level
                && descriptor["block"] == block,
            "note hash native role inventory mismatch"
        );
        anyhow::ensure!(
            descriptor["ordinal"] == ordinal,
            "note hash page inventory ordering"
        );
        let bytes = read_note_hash_page(first, ordinal)?;
        let repeat = read_note_hash_page(repeated, ordinal)?;
        anyhow::ensure!(bytes == repeat, "repeated note hash page bytes mismatch");
        anyhow::ensure!(
            descriptor["blake3"] == packet_blake3(&bytes),
            "note hash page digest mismatch"
        );
        let page: Value = serde_json::from_slice(&bytes)?;
        for key in ["slot", "role", "level", "block"] {
            anyhow::ensure!(
                descriptor[key] == page[key],
                "note hash page descriptor mismatch"
            );
        }
        anyhow::ensure!(
            page["schema"] == "shieldd-transfer-note-hash-block-v1"
                && page["ordinary_full_ordered_rows_equal"] == false
                && page["repeated_observations_equal"] == false,
            "note hash page pending schema/flags mismatch"
        );
        for key in [
            "relation_digest",
            "domain_size",
            "full_rows",
            "constant_copy",
        ] {
            anyhow::ensure!(
                page[key] == pending[key],
                "note hash page/manifest identity mismatch"
            );
        }
    }
    Ok(())
}

// NEW combined stage, existing spool runner. One lowerer, 55 hash+1 tree page.
fn capture_note_t4_pages(prefix: &str) -> anyhow::Result<()> {
    use shieldd_sdk_circuits::hash::note_inspection::Role;
    let mut count = 0;
    let (compiled, copy) = catalogue::inspect_transfer_note_t4_pages(|ordinal, page| {
        anyhow::ensure!(
            ordinal == count && count < 56,
            "combined page callback order/overflow"
        );
        let body = match page {
            catalogue::NoteT4Page::Hash(page) => {
                let (role, level) = match page.hash.role {
                    Role::Commitment => ("commitment", 0),
                    Role::Nullifier => ("nullifier", 0),
                    Role::Dummy => ("dummy", 0),
                    Role::StateLevel(level) => ("state", level),
                };
                json!({"schema":"shieldd-transfer-note-hash-block-v1","family":"transfer",
                    "scope":"one input-note permutation cone and two note source LCs; tree wiring and native joins open",
                    "slot":page.hash.slot,"role":role,"level":level,"block":page.hash.block,
                    "hash":{"domain":page.hash.domain,"inputs":page.hash.inputs.iter().map(observed).collect::<Vec<_>>(),
                        "output":observed(&page.hash.output),"blocks":page.hash.blocks.iter().map(|b|json!({
                            "before":b.before.iter().map(observed).collect::<Vec<_>>(),"after":b.after.iter().map(observed).collect::<Vec<_>>() })).collect::<Vec<_>>()},
                    "expressions":page.selected.iter().zip(&page.expressions).map(|(source,terms)|json!({"source":index(source),
                        "terms":terms.iter().map(|(column,coefficient)|json!([column,hex::encode(coefficient.encode())])).collect::<Vec<_>>() })).collect::<Vec<_>>(),
                    "nodes":page.nodes.iter().map(|(node,multiply,left,right)|json!({"index":node,"multiply":multiply,"left":index(left),"right":index(right)})).collect::<Vec<_>>()})
            }
            catalogue::NoteT4Page::Tree(page) => {
                let note_handles = page.spends.selected();
                let note_expressions=page.selected.iter().zip(&page.expressions).filter(|(source,_)|note_handles.contains(source))
                    .map(|(source,terms)|json!({"source":index(source),"terms":terms.iter().map(|(column,coefficient)|json!([column,hex::encode(coefficient.encode())])).collect::<Vec<_>>() })).collect::<Vec<_>>();
                let spends=page.spends.spends.iter().map(|spend| {
                    let shared=&spend.shared;
                    let optional=spend.optional.as_ref().map(|o|json!({"domain":o.domain,"slot":o.slot,"seed":observed(&o.seed),
                        "synthetic":observed(&o.synthetic),"selected":observed(&o.selected),"products":o.products.iter().map(|p|p.iter().map(observed).collect::<Vec<_>>()).collect::<Vec<_>>()}));
                    json!({"shared":{"asset":observed(&shared.asset),"address":shared.address.iter().map(observed).collect::<Vec<_>>(),
                        "nk":observed(&shared.nk),"randomizer":observed(&shared.randomizer),"anchor":observed(&shared.anchor)},
                        "note":spend.note.iter().map(observed).collect::<Vec<_>>(),"commitment":observed(&spend.commitment),"position":observed(&spend.position),
                        "amount_bits":spend.amount_bits.iter().map(index).collect::<Vec<_>>(),"position_bits":spend.position_bits.iter().map(index).collect::<Vec<_>>(),
                        "real_nullifier":observed(&spend.real_nullifier),"computed_anchor":observed(&spend.computed_anchor),"nullifier":observed(&spend.nullifier),
                        "dummy":observed(&spend.dummy),"optional":optional})
                }).collect::<Vec<_>>();
                json!({"schema":"shieldd-transfer-note-tree-v1","family":"transfer",
                    "scope":"48 current note-only state levels and six source products each; actual rows/native joins open",
                    "domain":1,"depth":24,"levels":page.levels.iter().zip(page.products).map(|(level,products)|json!({
                        "slot":level.slot,"level":level.level,"node":observed(&level.node),"low":observed(&level.low),"high":observed(&level.high),
                        "siblings":level.siblings.iter().map(observed).collect::<Vec<_>>(),"swaps":level.swaps.iter().map(observed).collect::<Vec<_>>(),
                        "children":level.children.iter().map(observed).collect::<Vec<_>>(),"output":observed(&level.output),
                        "products":products.iter().map(|p|p.iter().map(observed).collect::<Vec<_>>()).collect::<Vec<_>>() })).collect::<Vec<_>>(),
                    "expressions":page.selected.iter().zip(&page.expressions).map(|(source,terms)|json!({"source":index(source),
                        "terms":terms.iter().map(|(column,coefficient)|json!([column,hex::encode(coefficient.encode())])).collect::<Vec<_>>() })).collect::<Vec<_>>(),
                    "spend":{"schema":"shieldd-transfer-note-spend-v1","family":"transfer",
                        "scope":"two current Transfer spend source roles and branch LCs; hash/tree/range/native joins open","spends":spends,
                        "expressions":note_expressions,"nodes":page.spend_nodes.iter().map(|(node,multiply,left,right)|json!({
                            "index":node,"multiply":multiply,"left":index(left),"right":index(right)})).collect::<Vec<_>>()}})
            }
        };
        anyhow::ensure!(
            serde_json::to_vec(&body)?.len() <= 4 * 1024 * 1024,
            "combined note page JSON exceeds4MiB"
        );
        write_packet_json(prefix, &format!("page{ordinal}.observations.json"), &body)?;
        count += 1;
        Ok(())
    })?;
    anyhow::ensure!(
        count == 56 && copy == 200692,
        "incomplete combined note pages/copy"
    );
    let spool = RowSpool::new(&compiled)?;
    ensure_original_shape(&spool.shape())?;
    spool.persist(prefix, "observer")?;
    drop(compiled);
    let identity = json!({"relation_digest":hex::encode(spool.digest),"domain_size":spool.domain,"full_rows":spool.rows,"constant_copy":copy,
        "ordinary_full_ordered_rows_equal":false,"repeated_observations_equal":false});
    let mut pages = Vec::new();
    for ordinal in 0..56 {
        let mut body = read_packet_json(prefix, &format!("page{ordinal}.observations.json"))?;
        for (key, value) in identity.as_object().unwrap() {
            body.as_object_mut()
                .unwrap()
                .insert(key.clone(), value.clone());
        }
        if ordinal == 55 {
            for (key, value) in identity.as_object().unwrap() {
                body["spend"]
                    .as_object_mut()
                    .unwrap()
                    .insert(key.clone(), value.clone());
            }
        }
        write_packet_json(prefix, &format!("page{ordinal}.pending.json"), &body)?;
        let bytes = read_note_hash_page(prefix, ordinal)?;
        pages.push(if ordinal<55 {json!({"ordinal":ordinal,"slot":body["slot"],"role":body["role"],"level":body["level"],"block":body["block"],
            "blake3":packet_blake3(&bytes)})}else{json!({"ordinal":55,"slot":0,"role":"tree","level":0,"block":0,
            "blake3":packet_blake3(&bytes)})});
    }
    let mut manifest = identity;
    let object = manifest.as_object_mut().unwrap();
    object.insert("schema".into(), json!("shieldd-transfer-note-t4-pages-v1"));
    object.insert("family".into(), json!("transfer"));
    object.insert("scope".into(),json!("55 hash pages plus one two-spend/48-tree LC page from one lowering; native/kernel joins open"));
    object.insert("pages".into(), json!(pages));
    write_packet_json(prefix, "pending.json", &manifest)
}
fn qualify_note_t4_pages(first: &str, repeated: &str, pending: &Value) -> anyhow::Result<()> {
    let pages = pending["pages"]
        .as_array()
        .ok_or_else(|| anyhow::anyhow!("missing56 note pages"))?;
    anyhow::ensure!(pages.len() == 56, "combined note page count");
    let mut hash_manifest = pending.clone();
    hash_manifest["pages"] = json!(&pages[..55]);
    qualify_note_hash_pages(first, repeated, &hash_manifest)?;
    let descriptor = &pages[55];
    anyhow::ensure!(
        descriptor.as_object().map(|d| d.len()) == Some(6)
            && descriptor["ordinal"] == 55
            && descriptor["slot"] == 0
            && descriptor["role"] == "tree"
            && descriptor["level"] == 0
            && descriptor["block"] == 0,
        "combined tree page descriptor"
    );
    let bytes = read_note_hash_page(first, 55)?;
    let repeat = read_note_hash_page(repeated, 55)?;
    anyhow::ensure!(
        bytes == repeat && descriptor["blake3"] == packet_blake3(&bytes),
        "combined tree page repeat/digest mismatch"
    );
    let page: Value = serde_json::from_slice(&bytes)?;
    anyhow::ensure!(
        page["schema"] == "shieldd-transfer-note-tree-v1"
            && page["domain"] == 1
            && page["depth"] == 24
            && page["levels"].as_array().map(|v| v.len()) == Some(48)
            && page["spend"]["schema"] == "shieldd-transfer-note-spend-v1",
        "combined tree/spend page shape mismatch"
    );
    for part in [&page, &page["spend"]] {
        anyhow::ensure!(
            part["ordinary_full_ordered_rows_equal"] == false
                && part["repeated_observations_equal"] == false,
            "combined page pending flags"
        );
        for key in [
            "relation_digest",
            "domain_size",
            "full_rows",
            "constant_copy",
        ] {
            anyhow::ensure!(part[key] == pending[key], "combined page identity mismatch");
        }
    }
    Ok(())
}

fn capture_full_program(prefix: &str) -> anyhow::Result<()> {
    let path = packet_path(prefix, "program.jsonl");
    let file = OpenOptions::new().write(true).create_new(true).open(&path)?;
    let mut writer = BufWriter::new(file);
    let compiled = catalogue::inspect_transfer_program(|circuit, layout| {
        let (witnesses, constants, nodes, assertions) = circuit.inspect_program_counts();
        // Bounded per-record streaming: the complete graph is not duplicated in
        // a JSON Value or a second Vec. Declared counts and end record are exact.
        serde_json::to_writer(&mut writer, &json!({
            "schema": "shieldd-transfer-source-program-v1", "family": "transfer",
            "witnesses": witnesses, "constants": constants, "nodes": nodes,
            "assertions": assertions, "field_modulus":
                "52435875175126190479447740508185965837690552500527637822603658699938581184513",
            "coefficient_encoding": "canonical-big-endian-32",
            "source_public": layout.public().iter().map(index).collect::<Vec<_>>(),
            "source_blocks": layout.blocks().iter().map(|block|
                block.iter().map(index).collect::<Vec<_>>()).collect::<Vec<_>>()
        }))?;
        writer.write_all(b"\n")?;
        for ordinal in 0..constants {
            let value = circuit.inspect_program_constant(ordinal)
                .ok_or_else(|| anyhow::anyhow!("complete program constant missing"))?;
            serde_json::to_writer(&mut writer, &json!({"constant": ordinal,
                "value": hex::encode(value.encode())}))?;
            writer.write_all(b"\n")?;
        }
        for ordinal in 0..nodes {
            let (multiply, left, right) = circuit.inspect_program_node(ordinal)
                .ok_or_else(|| anyhow::anyhow!("complete program node missing"))?;
            serde_json::to_writer(&mut writer, &json!({"node": ordinal,
                "operation": if multiply {"mul"} else {"add"},
                "left": index(&left), "right": index(&right)}))?;
            writer.write_all(b"\n")?;
        }
        for ordinal in 0..assertions {
            let (left, right) = circuit.inspect_program_assertion(ordinal)
                .ok_or_else(|| anyhow::anyhow!("complete program assertion missing"))?;
            serde_json::to_writer(&mut writer, &json!({"assertion": ordinal,
                "left": index(&left), "right": index(&right)}))?;
            writer.write_all(b"\n")?;
        }
        serde_json::to_writer(&mut writer, &json!({"end": true,
            "constants": constants, "nodes": nodes, "assertions": assertions}))?;
        writer.write_all(b"\n")?;
        Ok(())
    })?;
    writer.flush()?;
    writer.get_ref().sync_all()?;
    let spool = RowSpool::new(&compiled)?;
    drop(compiled);
    ensure_original_shape(&spool.shape())?;
    spool.persist(prefix, "full-program-ordinary-compiler")
    // Whole rows, repeat source program, and an independent ordinary replay
    // remain mandatory. Neither this output nor a matching hash is a proof.
}
