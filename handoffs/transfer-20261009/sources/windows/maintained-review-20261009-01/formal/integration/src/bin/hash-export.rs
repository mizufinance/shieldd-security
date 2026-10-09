use commonware_codec::Encode;
use commonware_cryptography::{
    bls12381::primitives::group::Scalar,
    zk::{
        circuit::{build, Circuit, CircuitIdx, CircuitSource, Var},
        pari::{CompiledExpression, InputLayout, Relation},
    },
};
use commonware_math::algebra::{Additive, Ring};
use serde_json::{json, Value};
use shieldd_sdk_circuits::{catalogue, hash::Parameters, map::Generators, proof::Family, transfer};
use std::collections::{BTreeMap, BTreeSet};
use std::fs::{File, OpenOptions};
use std::io::{self, BufReader, BufWriter, Read, Seek, Write};
use std::path::PathBuf;

// A direct, complete comparison uses bounded buffers rather than retaining two
// compiled Transfer relations. The disposable stream is never proof evidence.
struct ParitySpool {
    path: PathBuf,
    file: Option<File>,
}

impl ParitySpool {
    fn new() -> io::Result<Self> {
        let stamp = std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .expect("system clock precedes Unix epoch")
            .as_nanos();
        let path = std::env::temp_dir().join(format!(
            "shieldd-relation-parity-{}-{stamp}.bin",
            std::process::id()
        ));
        let file = OpenOptions::new()
            .read(true)
            .write(true)
            .create_new(true)
            .open(&path)?;
        Ok(Self {
            path,
            file: Some(file),
        })
    }

    fn file(&mut self) -> &mut File {
        self.file.as_mut().expect("owned parity file")
    }
}

impl Drop for ParitySpool {
    fn drop(&mut self) {
        drop(self.file.take());
        // Best-effort cleanup is also attempted on any rejected comparison.
        let _ = std::fs::remove_file(&self.path);
    }
}

fn stream_identity(
    output: &mut impl Write,
    circuit: &Circuit<Scalar>,
    layout: &InputLayout,
    relation: &Relation,
) -> io::Result<()> {
    fn count(output: &mut impl Write, value: usize) -> io::Result<()> {
        output.write_all(&u64::try_from(value).expect("count fits u64").to_le_bytes())
    }
    fn source(output: &mut impl Write, value: CircuitIdx) -> io::Result<()> {
        let (tag, index) = match value {
            CircuitIdx::Constant(index) => (0, index),
            CircuitIdx::Witness(index) => (1, index),
            CircuitIdx::Node(index) => (2, index),
        };
        output.write_all(&[tag])?;
        output.write_all(&index.to_le_bytes())
    }
    output.write_all(b"shieldd-ordinary-observed-parity-v1\0")?;
    count(output, relation.domain_size())?;
    count(output, relation.public_inputs())?;
    count(output, relation.committed_inputs())?;
    count(output, relation.blocks().len())?;
    for &block in relation.blocks() {
        count(output, block)?;
    }
    count(output, layout.public().len())?;
    for &index in layout.public() {
        source(output, index)?;
    }
    count(output, layout.blocks().len())?;
    for block in layout.blocks() {
        count(output, block.len())?;
        for &index in block {
            source(output, index)?;
        }
    }
    // Circuit constant identities are contiguous by the pinned source API.
    // Include even constants folded away from the emitted arithmetic rows.
    let mut constants = 0u32;
    while circuit
        .source_value(CircuitIdx::Constant(constants))
        .is_some()
    {
        constants = constants.checked_add(1).expect("constant count fits u32");
    }
    output.write_all(&constants.to_le_bytes())?;
    for index in 0..constants {
        let Some(CircuitSource::Constant(value)) =
            circuit.source_value(CircuitIdx::Constant(index))
        else {
            panic!("source constant API mismatch");
        };
        output.write_all(value.encode().as_ref())?;
    }
    count(output, relation.constraints().len())?;
    for (a, b) in relation.constraints() {
        for terms in [a, b] {
            count(output, terms.len())?;
            for (column, coefficient) in terms {
                output.write_all(&column.to_le_bytes())?;
                output.write_all(coefficient.encode().as_ref())?;
            }
        }
    }
    Ok(())
}

struct CompareStream<R> {
    ordinary: R,
    compared_bytes: u64,
}

impl<R: Read> CompareStream<R> {
    fn finish(mut self) -> io::Result<u64> {
        let mut trailing = [0u8; 1];
        if self.ordinary.read(&mut trailing)? != 0 {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                "ordinary/observed relation stream length mismatch",
            ));
        }
        Ok(self.compared_bytes)
    }
}

impl<R: Read> Write for CompareStream<R> {
    fn write(&mut self, observed: &[u8]) -> io::Result<usize> {
        let mut expected = [0u8; 64];
        for chunk in observed.chunks(expected.len()) {
            self.ordinary.read_exact(&mut expected[..chunk.len()])?;
            if &expected[..chunk.len()] != chunk {
                return Err(io::Error::new(
                    io::ErrorKind::InvalidData,
                    "ordinary/observed full relation mismatch",
                ));
            }
        }
        self.compared_bytes += u64::try_from(observed.len()).expect("buffer fits u64");
        Ok(observed.len())
    }

    fn flush(&mut self) -> io::Result<()> {
        Ok(())
    }
}

fn source_id(index: CircuitIdx) -> String {
    match index {
        CircuitIdx::Constant(i) => format!("c{i}"),
        CircuitIdx::Witness(i) => format!("w{i}"),
        CircuitIdx::Node(i) => format!("n{i}"),
    }
}

fn terms(values: &[(u32, Scalar)]) -> Vec<Value> {
    values
        .iter()
        .map(|(column, coefficient)| json!([column, hex::encode(coefficient.encode())]))
        .collect()
}

// A boundary may itself be a computed node (for example the RNK commitment's
// input is the prior RNK hash output). Its exact original definition remains
// recorded, but its children are outside this call's dependency cone.
fn cone(
    circuit: &Circuit<Scalar>,
    inputs: &[CircuitIdx],
    output: CircuitIdx,
) -> (BTreeSet<CircuitIdx>, BTreeMap<String, Value>) {
    let boundaries: BTreeSet<_> = inputs.iter().copied().collect();
    assert_eq!(
        boundaries.len(),
        inputs.len(),
        "unsupported aliased hash inputs"
    );
    let mut pending = vec![output];
    pending.extend(inputs.iter().copied());
    let mut visited = BTreeSet::new();
    let mut source = BTreeMap::new();
    while let Some(index) = pending.pop() {
        if !visited.insert(index) {
            continue;
        }
        let value = match circuit
            .source_value(index)
            .expect("invalid source identity")
        {
            CircuitSource::Constant(value) => {
                json!({"kind":"constant", "value":hex::encode(value.encode())})
            }
            CircuitSource::Witness => {
                assert!(
                    boundaries.contains(&index),
                    "undeclared witness in hash cone"
                );
                json!({"kind":"witness"})
            }
            node => {
                let (kind, left, right) = match node {
                    CircuitSource::Add(left, right) => ("add", left, right),
                    CircuitSource::Mul(left, right) => ("mul", left, right),
                    _ => unreachable!(),
                };
                let CircuitIdx::Node(current) = index else {
                    unreachable!()
                };
                for child in [left, right] {
                    assert!(
                        circuit.source_value(child).is_some(),
                        "invalid source dependency"
                    );
                    if let CircuitIdx::Node(prior) = child {
                        assert!(prior < current, "forward or cyclic source dependency");
                    }
                    if !boundaries.contains(&index) {
                        pending.push(child);
                    }
                }
                json!({"kind":kind, "left":source_id(left), "right":source_id(right)})
            }
        };
        source.insert(source_id(index), value);
    }
    (visited, source)
}

fn source_constant(circuit: &Circuit<Scalar>, index: CircuitIdx, expected: &Scalar) -> bool {
    matches!(circuit.source_value(index), Some(CircuitSource::Constant(value)) if value == expected)
}

fn source_one_minus(circuit: &Circuit<Scalar>, index: CircuitIdx, input: CircuitIdx) -> bool {
    let Some(CircuitSource::Add(left, right)) = circuit.source_value(index) else {
        return false;
    };
    let minus_one = Scalar::zero() - &Scalar::one();
    [(left, right), (right, left)]
        .into_iter()
        .any(|(one, negative)| {
            source_constant(circuit, one, &Scalar::one())
                && matches!(circuit.source_value(negative), Some(CircuitSource::Mul(a, b))
                if (a == input && source_constant(circuit, b, &minus_one))
                    || (b == input && source_constant(circuit, a, &minus_one)))
        })
}

// Retain only six named existing terminal products and their exact original
// assertions. Pari materializes product output, then separately asserts 0/1;
// retaining operands alone misses the terminal assertion's output column.
// This observes existing source IDs: it never allocates a value or assertion.
fn terminal_product(
    circuit: &Circuit<Scalar>,
    role: &str,
    left: CircuitIdx,
    right: CircuitIdx,
    complement_right: bool,
    target: Scalar,
    requested: &mut BTreeSet<CircuitIdx>,
) -> Value {
    let mut matches = Vec::new();
    for (index, (a, b)) in circuit.source_assertions().enumerate() {
        for (product, equal) in [(a, b), (b, a)] {
            if !source_constant(circuit, equal, &target) {
                continue;
            }
            let Some(CircuitSource::Mul(x, y)) = circuit.source_value(product) else {
                continue;
            };
            let right_matches = |value| {
                if complement_right {
                    source_one_minus(circuit, value, right)
                } else {
                    value == right
                }
            };
            if (x == left && right_matches(y)) || (y == left && right_matches(x)) {
                matches.push((index, product, equal));
            }
        }
    }
    assert_eq!(
        matches.len(),
        1,
        "missing/ambiguous original terminal product: {role}"
    );
    let (index, product, equal) = matches[0];
    let (indices, source) = cone(circuit, &[left, right], product);
    requested.extend(indices);
    requested.insert(equal);
    json!({"role":role,"inputs":[source_id(left),source_id(right)],
        "complement_right":complement_right,"target":hex::encode(target.encode()),
        "product":source_id(product),"asserted_equal":source_id(equal),
        "assertion_index":index,"source":source})
}

fn main() {
    let arguments: Vec<_> = std::env::args().skip(1).collect();
    let (include_scalar, include_group, completion_stream) = match arguments.as_slice() {
        [] => (false, false, None),
        [argument] if argument == "--scalar-observation" => (true, false, None),
        [argument] if argument == "--ownership-observation" => (true, true, None),
        [argument, flag, path]
            if argument == "--ownership-observation" && flag == "--completion-support-stream" =>
        {
            (true, true, Some(PathBuf::from(path)))
        }
        _ => panic!("expected an observation mode, optionally ownership --completion-support-stream PATH"),
    };
    let catalogue::Witness::Transfer(witness) = catalogue::template(Family::Transfer) else {
        unreachable!()
    };
    let parameters = Parameters::load().unwrap();
    let generators = Generators::derive(&parameters);
    let mut calls = Vec::new();
    let mut ownership_roles = Vec::new();
    let mut note_hash_roles = Vec::new();
    let mut scalar_roles = BTreeMap::new();
    let mut scalar_steps = Vec::new();
    let mut group_roles = BTreeMap::new();
    let (circuit, selected) = build(|ctx| {
        let (mut retained, observed) =
            transfer::constrain_observed(ctx, &parameters, &generators, &witness, &Scalar::zero());
        assert_eq!(retained.len(), 2);
        if include_group {
            let subgroup = observed
                .authorization
                .ak_subgroup
                .as_ref()
                .expect("actual ak subgroup handles");
            for (role, value) in [
                ("coefficient_d", &subgroup.d),
                ("point.x", &subgroup.point.x),
                ("point.y", &subgroup.point.y),
                ("preimage.x", &subgroup.preimage.x),
                ("preimage.y", &subgroup.preimage.y),
                ("curve.left", &subgroup.curve.left),
                ("curve.right", &subgroup.curve.right),
                ("point.inverse", &observed.authorization.ak_inverse),
            ] {
                group_roles.insert(role.to_owned(), retained.len());
                retained.push(value.clone());
            }
            assert_eq!(subgroup.doublings.len(), 3);
            for (index, step) in subgroup.doublings.iter().enumerate() {
                for (role, value) in [
                    ("before.x", &step.before.x),
                    ("before.y", &step.before.y),
                    ("after.x", &step.after.x),
                    ("after.y", &step.after.y),
                    ("inverse", &step.inverse),
                    ("denominator", &step.denominator),
                ] {
                    group_roles.insert(format!("double{index}.{role}"), retained.len());
                    retained.push(value.clone());
                }
            }
        }
        if include_scalar {
            let reduction = observed
                .authorization
                .reduction
                .as_ref()
                .expect("actual reduction handles");
            for (role, value) in [
                ("value", &reduction.value),
                ("quotient", &reduction.quotient),
                ("remainder", &reduction.remainder),
                ("ivk", &observed.authorization.ivk),
                ("ivk_inverse", &observed.authorization.ivk_inverse),
            ] {
                scalar_roles.insert(role.to_owned(), retained.len());
                retained.push(value.clone());
            }
            assert_eq!(reduction.quotient_bits.len(), 4);
            assert_eq!(reduction.remainder_bits.len(), 252);
            for (name, bits) in [
                ("quotient", &reduction.quotient_bits),
                ("remainder", &reduction.remainder_bits),
            ] {
                for (i, bit) in bits.iter().enumerate() {
                    scalar_roles.insert(format!("{name}.bit{i}"), retained.len());
                    retained.push(bit.var().clone());
                }
            }
            let order = Scalar::from_limbs(shieldd_sdk_circuits::scalar::ORDER);
            let last = -Scalar::one() - &(order.clone() * &Scalar::from(8));
            for (name, bits, comparison, maximum) in [
                (
                    "quotient",
                    &reduction.quotient_bits,
                    &reduction.quotient_bound,
                    Scalar::from(8),
                ),
                (
                    "remainder",
                    &reduction.remainder_bits,
                    &reduction.remainder_bound,
                    order - &Scalar::one(),
                ),
                (
                    "last",
                    &reduction.remainder_bits,
                    &reduction.last_bound,
                    last,
                ),
            ] {
                assert_eq!(comparison.steps.len(), bits.len());
                let encoded = maximum.encode();
                for (i, step) in comparison.steps.iter().enumerate() {
                    assert!(
                        step.left.var() == bits[i].var(),
                        "comparison input role drift"
                    );
                    let right = u64::from(encoded[31 - i / 8] >> (i % 8) & 1);
                    assert!(
                        step.right.var() == &Var::native(Scalar::from(right)),
                        "comparison bound must be literal"
                    );
                    if i == 0 {
                        assert!(
                            step.lower == Var::native(Scalar::one()),
                            "comparison initial prefix must be literal one"
                        );
                    } else {
                        assert!(
                            step.lower == comparison.steps[i - 1].output,
                            "comparison prefix identity drift"
                        );
                    }
                    scalar_roles.insert(format!("{name}.comparison{i}"), retained.len());
                    let output = retained.len();
                    retained.push(step.output.clone());
                    scalar_steps.push((name.to_owned(), i, right, output));
                }
                assert!(
                    comparison.within.var()
                        == &comparison.steps.last().expect("nonempty comparison").output,
                    "comparison result identity drift"
                );
            }
        }
        let action = &observed.spend_authorization;
        for (role, value) in [
            (
                "authorization.effective_nk",
                observed.authorization.effective_nk.clone(),
            ),
            ("action.ak.x", action.ak.x.clone()),
            ("action.ak.y", action.ak.y.clone()),
            ("action.randomizer", action.randomizer.clone()),
            ("action.computed_rk.x", action.computed_rk.x.clone()),
            ("action.computed_rk.y", action.computed_rk.y.clone()),
            ("action.rk.x", action.rk.x.clone()),
            ("action.rk.y", action.rk.y.clone()),
            ("statement.rk.x", observed.statement.rk.x.clone()),
            ("statement.rk.y", observed.statement.rk.y.clone()),
        ] {
            ownership_roles.push((role.to_owned(), retained.len()));
            retained.push(value);
        }
        for (slot, spend) in observed.spends.into_iter().enumerate() {
            for (role, value) in [
                ("position", spend.position.clone()),
                ("real_nullifier", spend.real_nullifier.clone()),
            ] {
                ownership_roles.push((format!("spend{slot}.{role}"), retained.len()));
                retained.push(value);
            }
            for (kind, hash) in [
                ("commitment", spend.note_commitment),
                ("nullifier", spend.nullifier_hash),
            ] {
                let start = retained.len();
                let arity = hash.inputs.len();
                retained.extend(hash.inputs);
                retained.push(hash.output);
                note_hash_roles.push((slot, kind, hash.domain, start, arity));
            }
        }
        for (role, hash) in [
            ("authorization.ivk", observed.authorization.viewing_key),
            ("authorization.rnk", observed.authorization.regulated_key),
            (
                "authorization.rnk_commitment",
                observed.authorization.regulated_commitment,
            ),
        ] {
            let start = retained.len();
            let arity = hash.inputs.len();
            retained.extend(hash.inputs);
            retained.push(hash.output);
            calls.push((role.to_owned(), hash.domain, start, arity));
        }
        retained
    });
    // Only the original claim and blinding are selected: retained handles must
    // not change fusion, layout, constraints or key shape.
    let layout = InputLayout::new(vec![selected[0]], vec![vec![selected[1]]]).unwrap();
    // Extend the same actual source observations to both input-note hashes.
    // Their descriptors below remain an independently checked caller-role join.
    for &(slot, kind, domain, start, arity) in &note_hash_roles {
        calls.push((format!("spend{slot}.{kind}"), domain, start, arity));
    }
    let mut requested = BTreeSet::new();
    // Retain caller-role identities as well; identity is not a substitute for
    // the still-required group, note-hash and signature semantics.
    requested.extend(selected.iter().skip(2).copied());
    let mut call_data = Vec::new();
    for (role, domain, start, arity) in calls {
        let inputs = &selected[start..start + arity];
        let output = selected[start + arity];
        let (indices, source) = cone(&circuit, inputs, output);
        requested.extend(indices);
        call_data.push(json!({
            "role":role, "domain":domain, "inputs":inputs.iter().copied().map(source_id).collect::<Vec<_>>(),
            "output":source_id(output), "source":source,
        }));
    }
    let mut scalar_step_data = Vec::new();
    for (name, i, right, output_index) in scalar_steps {
        let bit_name = if name == "last" { "remainder" } else { &name };
        let left = selected[scalar_roles[&format!("{bit_name}.bit{i}")]];
        let mut boundaries = vec![left];
        let lower = if i == 0 {
            None
        } else {
            let previous = selected[scalar_roles[&format!("{name}.comparison{}", i - 1)]];
            boundaries.push(previous);
            Some(source_id(previous))
        };
        let output = selected[output_index];
        let (indices, source) = cone(&circuit, &boundaries, output);
        requested.extend(indices);
        scalar_step_data.push(json!({"comparison":name,"index":i,"left":source_id(left),
            "right_literal":right,"lower":lower,"initial_literal":if i==0 {Some(1)}else{None},
            "output":source_id(output),"source":source}));
    }
    let mut terminal_products = Vec::new();
    if include_scalar {
        terminal_products.push(terminal_product(
            &circuit,
            "scalar.last_guard",
            selected[scalar_roles["quotient.bit3"]],
            selected[scalar_roles["last.comparison251"]],
            true,
            Scalar::zero(),
            &mut requested,
        ));
        terminal_products.push(terminal_product(
            &circuit,
            "scalar.ivk_inverse",
            selected[scalar_roles["ivk_inverse"]],
            selected[scalar_roles["ivk"]],
            false,
            Scalar::one(),
            &mut requested,
        ));
    }
    if include_group {
        terminal_products.push(terminal_product(
            &circuit,
            "group.point_inverse",
            selected[group_roles["point.x"]],
            selected[group_roles["point.inverse"]],
            false,
            Scalar::one(),
            &mut requested,
        ));
        for index in 0..3 {
            terminal_products.push(terminal_product(
                &circuit,
                &format!("group.double{index}_inverse"),
                selected[group_roles[&format!("double{index}.denominator")]],
                selected[group_roles[&format!("double{index}.inverse")]],
                false,
                Scalar::one(),
                &mut requested,
            ));
        }
    }
    let scalar_data = if include_scalar {
        Some(json!({"subject":"actual IVK canonical reduction",
            "roles":scalar_roles.into_iter().map(|(role,index)|(role,source_id(selected[index]))).collect::<BTreeMap<_,_>>(),
            "comparisons":scalar_step_data}))
    } else {
        None
    };
    let group_data = if include_group {
        let get = |role: &str| selected[group_roles[role]];
        let CircuitSource::Constant(d) = circuit
            .source_value(get("coefficient_d"))
            .expect("actual coefficient source")
        else {
            panic!("actual coefficient must be a source constant");
        };
        assert_eq!(d, &shieldd_sdk_circuits::group::coefficient_d());
        let mut cones = Vec::new();
        for role in ["curve.left", "curve.right"] {
            let inputs = [get("preimage.x"), get("preimage.y")];
            let output = get(role);
            let (indices, source) = cone(&circuit, &inputs, output);
            requested.extend(indices);
            cones.push(json!({"role":role,"inputs":inputs.map(source_id),"output":source_id(output),"source":source}));
        }
        for index in 0..3 {
            let inputs = [
                get(&format!("double{index}.before.x")),
                get(&format!("double{index}.before.y")),
            ];
            let role = format!("double{index}.denominator");
            let output = get(&role);
            let (indices, source) = cone(&circuit, &inputs, output);
            requested.extend(indices);
            cones.push(json!({"role":role,"inputs":inputs.map(source_id),"output":source_id(output),"source":source}));
            for axis in ["x", "y"] {
                let role = format!("double{index}.after.{axis}");
                let inputs = [
                    get(&format!("double{index}.before.x")),
                    get(&format!("double{index}.before.y")),
                    get(&format!("double{index}.inverse")),
                ];
                let output = get(&role);
                let (indices, source) = cone(&circuit, &inputs, output);
                requested.extend(indices);
                cones.push(json!({"role":role,"inputs":inputs.map(source_id),"output":source_id(output),"source":source}));
            }
        }
        Some(
            json!({"subject":"actual action authorization key cofactor constraint",
            "coefficient_d":hex::encode(d.encode()),
            "roles":group_roles.into_iter().map(|(role,index)|(role,source_id(selected[index]))).collect::<BTreeMap<_,_>>(),
            "cones":cones}),
        )
    } else {
        None
    };
    let requested: Vec<_> = requested.into_iter().collect();
    let mut parity = ParitySpool::new().expect("create owned disposable parity stream");
    let ordinary = if include_scalar {
        // Exercise the actual non-observing constructor as well: its optional
        // trace path must not change the relation or original input ownership.
        let (plain, inputs) = build(|ctx| {
            transfer::constrain(ctx, &parameters, &generators, &witness, &Scalar::zero())
        });
        assert_eq!(inputs.len(), 2);
        let plain_layout = InputLayout::new(vec![inputs[0]], vec![vec![inputs[1]]]).unwrap();
        assert_eq!(plain_layout, layout, "ordinary/observed typed input layout");
        let ordinary = Relation::compile(&plain, &plain_layout).unwrap();
        let mut output = BufWriter::new(parity.file());
        stream_identity(&mut output, &plain, &plain_layout, &ordinary)
            .expect("stream ordinary full relation");
        output.flush().expect("flush ordinary full relation");
        ordinary
    } else {
        let ordinary = Relation::compile(&circuit, &layout).unwrap();
        let mut output = BufWriter::new(parity.file());
        stream_identity(&mut output, &circuit, &layout, &ordinary)
            .expect("stream ordinary full relation");
        output.flush().expect("flush ordinary full relation");
        ordinary
    };
    let ordinary_identity = (
        *ordinary.digest(),
        ordinary.domain_size(),
        ordinary.public_inputs(),
        ordinary.blocks().to_vec(),
    );
    drop(ordinary);
    let (relation, observed) = Relation::compile_observed(&circuit, &layout, &requested).unwrap();
    assert_eq!(relation.digest(), &ordinary_identity.0);
    assert_eq!(relation.domain_size(), ordinary_identity.1);
    assert_eq!(relation.public_inputs(), ordinary_identity.2);
    assert_eq!(relation.blocks(), ordinary_identity.3);
    parity
        .file()
        .rewind()
        .expect("rewind ordinary full relation");
    let mut comparison = CompareStream {
        ordinary: BufReader::new(parity.file()),
        compared_bytes: 0,
    };
    stream_identity(&mut comparison, &circuit, &layout, &relation)
        .expect("compare observed full ordered relation");
    let full_relation_compared_bytes = comparison
        .finish()
        .expect("check exact ordinary stream end");
    if let Some(path) = &completion_stream {
        // Persist exactly the ordinary stream already compared through exact
        // EOF. The caller owns this create-new diagnostic path and its cleanup.
        // No relation handle, constraint or compiler observation is added.
        parity.file().rewind().expect("rewind verified completion stream");
        let mut destination = OpenOptions::new().write(true).create_new(true)
            .open(path).expect("create new completion stream");
        let copied = io::copy(parity.file(), &mut destination)
            .expect("copy verified completion stream");
        assert_eq!(copied, full_relation_compared_bytes);
        destination.sync_all().expect("sync completion stream");
    }
    drop(parity);
    assert_eq!(observed.len(), requested.len());
    let mut columns = BTreeSet::new();
    let expressions: Vec<_> = observed
        .iter()
        .zip(&requested)
        .map(|(item, requested)| {
            assert_eq!(item.index, *requested);
            let (kind, values) = match &item.expression {
                CompiledExpression::Linear(values) => ("linear", values),
                CompiledExpression::Square(values) => ("square", values),
            };
            columns.extend(
                values
                    .iter()
                    .filter_map(|(column, _)| (*column != 0).then_some(*column)),
            );
            json!({"source":source_id(item.index), "kind":kind, "terms":terms(values)})
        })
        .collect();
    // This is candidate-row extraction only. The kernel certificate must check
    // the exact local rows needed by every source operation, including product
    // auxiliaries and the outlined-one link. Full membership uses this exporter
    // as part of the explicit extraction TCB; a digest is not a semantic proof.
    let rows: Vec<_> = relation
        .constraints()
        .enumerate()
        .filter_map(|(index, (a, b))| {
            a.iter()
                .chain(b)
                .any(|(column, _)| *column == 0 || columns.contains(column))
                .then(|| json!({"index":index, "a":terms(a), "b":terms(b)}))
        })
        .collect();
    // Fixed actual E9 terminal output/auxiliary/inverse columns, plus the
    // outlined-one copy. Every original constraint is traversed; the separate
    // parser must reconstruct this complete occurrence table from the stream.
    let completion_support = completion_stream.as_ref().map(|_| {
        let columns = [1985u32, 1986, 1987, 1988, 2253, 49925, 49926,
            49945, 49946, 49965, 49966, 49979, 49980, 51409, 51410,
            51411, 51412, 201313];
        let occurrences: Vec<_> = relation.constraints().enumerate()
            .filter_map(|(index, (a, b))| {
                let present: Vec<_> = columns.iter().copied().filter(|wanted|
                    a.iter().chain(b).any(|(column, _)| u64::from(*wanted) == *column as u64))
                    .collect();
                (!present.is_empty()).then(|| json!({"index":index,
                    "columns":present,"a":terms(a),"b":terms(b)}))
            }).collect();
        json!({"scope":"full ordered relation column occurrences; extraction boundary, not completion",
            "columns":columns,"row_count":relation.constraints().len(),
            "stream_format":"shieldd-ordinary-observed-parity-v1",
            "stream_bytes":full_relation_compared_bytes,"rows":occurrences})
    });
    let requested_set: BTreeSet<_> = requested.iter().copied().collect();
    let assertions: Vec<_> = circuit
        .source_assertions()
        .enumerate()
        .filter_map(|(index, (left, right))| {
            (requested_set.contains(&left) || requested_set.contains(&right))
                .then(|| json!({"index":index,"left":source_id(left),"right":source_id(right)}))
        })
        .collect();
    let ownership: BTreeMap<_, _> = ownership_roles
        .into_iter()
        .map(|(role, index)| (role, source_id(selected[index])))
        .collect();
    let notes: Vec<_> = note_hash_roles.into_iter().map(|(slot, role, domain, start, arity)| {
        json!({"slot":slot,"role":role,"domain":domain,
            "inputs":selected[start..start+arity].iter().copied().map(source_id).collect::<Vec<_>>(),
            "output":source_id(selected[start+arity])})
    }).collect();
    println!(
        "{}",
        serde_json::to_string(&json!({
            "subject":"actual Transfer authorization and input-note hash dependency cones",
            "hash_scope":"authorization-and-input-notes",
            "scalar_encoding":"canonical-big-endian-32",
            "modulus_minus_one":hex::encode((-Scalar::one()).encode()),
            "relation_digest":hex::encode(relation.digest()), "domain_size":relation.domain_size(),
            "ordinary_relation_digest":hex::encode(ordinary_identity.0),
            "ordinary_observed_identity_equal":true,
            "ordinary_observed_full_ordered_equal":true,
            "ordinary_observed_comparison":"direct canonical stream: complete ordered constraints/LCs, all source constants, typed layout and dimensions; exact EOF",
            "ordinary_observed_compared_bytes":full_relation_compared_bytes,
            "ordinary_constructor_checked":include_scalar,
            "row_count":relation.constraints().len(), "public_inputs":relation.public_inputs(),
            "committed_blocks":relation.blocks(), "layout":format!("{:?}",layout),
            "calls":call_data, "expressions":expressions, "rows":rows,
            "ownership":ownership, "note_hashes":notes,
            "scalar_reduction":scalar_data, "terminal_products":terminal_products,
            "group_subgroup":group_data,
            "touching_source_assertions":assertions,
            "source_assertion_count":circuit.source_assertions().len(),
            "completion_support":completion_support,
        }))
        .unwrap()
    );
}

#[cfg(test)]
mod parity_tests {
    use super::*;
    use std::io::Cursor;

    fn compare(ordinary: &[u8], observed: &[u8]) -> io::Result<u64> {
        let mut comparison = CompareStream {
            ordinary: Cursor::new(ordinary),
            compared_bytes: 0,
        };
        comparison.write_all(observed)?;
        comparison.finish()
    }

    #[test]
    fn exact_parity_stream_rejects_mutation_and_both_length_directions() {
        let ordinary: Vec<u8> = (0..191).collect();
        assert_eq!(compare(&ordinary, &ordinary).unwrap(), 191);
        for index in [0, 63, 64, 128, 190] {
            let mut observed = ordinary.clone();
            observed[index] ^= 1;
            assert_eq!(
                compare(&ordinary, &observed).unwrap_err().kind(),
                io::ErrorKind::InvalidData
            );
        }
        assert_eq!(
            compare(&ordinary, &ordinary[..190]).unwrap_err().kind(),
            io::ErrorKind::InvalidData
        );
        assert_eq!(
            compare(&ordinary[..190], &ordinary).unwrap_err().kind(),
            io::ErrorKind::UnexpectedEof
        );
    }
}
