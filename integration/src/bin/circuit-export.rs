use commonware_codec::Encode;
use commonware_cryptography::{
    bls12381::primitives::group::Scalar,
    zk::{
        circuit::{CircuitIdx, Var, build},
        pari::{InputLayout, Relation},
    },
};
use commonware_math::algebra::{Additive, Ring};
use serde_json::json;

fn main() {
    let (circuit, indices) = build(|ctx| {
        let value = Var::witness(ctx, |_| Scalar::zero());
        let commitment = Var::witness(ctx, |_| Scalar::zero());
        let bits = shieldd_sdk_circuits::range::decompose(ctx, &value, 128);
        // Return indices for inspection; only the first two are selected in layout.
        let mut out = vec![value, commitment];
        out.extend(bits.into_iter().map(|bit| bit.into_var()));
        out
    });
    let layout = InputLayout::new(vec![indices[0]], vec![vec![indices[1]]]).unwrap();
    let relation = Relation::compile(&circuit, &layout).unwrap();
    let column = |index: CircuitIdx| match index {
        CircuitIdx::Witness(i) => relation.witness_column(i).unwrap(),
        _ => panic!("expected original witness"),
    };
    let rows: Vec<_> = relation
        .constraints()
        .map(|(a, b)| {
            let terms = |xs: &[(u32, Scalar)]| {
                xs.iter()
                    .map(|(i, c)| json!([i, hex::encode(c.encode())]))
                    .collect::<Vec<_>>()
            };
            json!({"a":terms(a),"b":terms(b)})
        })
        .collect();
    println!(
        "{}",
        serde_json::to_string_pretty(&json!({
            "subject":"range::decompose(128), isolated actual runtime constructor",
            "scalar_encoding":"canonical-big-endian-32",
            "modulus_minus_one":hex::encode((-Scalar::one()).encode()),
            "relation_digest":hex::encode(relation.digest()),
            "domain_size":relation.domain_size(), "public_inputs":relation.public_inputs(),
            "committed_blocks":relation.blocks(), "value_column":column(indices[0]),
            "commitment_column":column(indices[1]),
            "bit_columns":indices[2..].iter().copied().map(column).collect::<Vec<_>>(),
            "rows":rows
        }))
        .unwrap()
    );
}
