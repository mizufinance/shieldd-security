//! Export complete, small relations exercising the patched compiler's auxiliary columns.
use commonware_codec::Encode;
use commonware_cryptography::{
    bls12381::primitives::group::Scalar,
    zk::{
        circuit::{CircuitIdx, Var, build},
        pari::{InputLayout, Relation},
    },
};
use commonware_math::algebra::{Additive, Ring};
use serde_json::{Value, json};

fn inspect(relation: &Relation, witnesses: &[CircuitIdx]) -> Value {
    let columns: Vec<_> = witnesses
        .iter()
        .map(|index| match index {
            CircuitIdx::Witness(index) => relation.witness_column(*index).unwrap(),
            _ => panic!("fixture mapping must identify an original witness"),
        })
        .collect();
    let rows: Vec<_> = relation
        .constraints()
        .map(|(a, b)| {
            let terms = |xs: &[(u32, Scalar)]| {
                xs.iter()
                    .map(|(column, value)| json!([column, hex::encode(value.encode())]))
                    .collect::<Vec<_>>()
            };
            json!({"a": terms(a), "b": terms(b)})
        })
        .collect();
    json!({
        "relation_digest": hex::encode(relation.digest()),
        "domain_size": relation.domain_size(),
        "public_inputs": relation.public_inputs(),
        "committed_blocks": relation.blocks(),
        "witness_columns": columns,
        "rows": rows,
    })
}

fn outlined_constant() -> Value {
    let (circuit, selected) = build(|ctx| {
        let x = Var::witness(ctx, |_| Scalar::from(7u64));
        let y = x.clone() + &Var::constant(ctx, Scalar::from(11u64));
        (y.clone() * &y).assert_eq(&Var::constant(ctx, Scalar::from(324u64)));
        vec![y, x]
    });
    let layout = InputLayout::new(vec![selected[0]], vec![vec![selected[1]]]).unwrap();
    let relation = Relation::compile(&circuit, &layout).unwrap();
    let mut fixture = inspect(&relation, &[selected[1]]);
    fixture["kind"] = json!("outlined_constant");
    fixture
}

fn deferred_squares(reverse: bool, folded: bool) -> Value {
    let (circuit, selected) = build(|ctx| {
        let x = Var::witness(ctx, |_| Scalar::zero());
        let y = Var::witness(ctx, |_| Scalar::one());
        let factor = if folded {
            x.clone() + &Var::constant(ctx, Scalar::zero())
        } else {
            x.clone()
        };
        let x_squared = x.clone() * &factor;
        let y_squared = y.clone() * &y;
        if reverse {
            y_squared.assert_eq(&x_squared);
        } else {
            x_squared.assert_eq(&y_squared);
        }
        vec![x, y]
    });
    let layout = InputLayout::new(vec![selected[0]], vec![vec![selected[1]]]).unwrap();
    let relation = Relation::compile(&circuit, &layout).unwrap();
    let mut fixture = inspect(&relation, &selected);
    fixture["kind"] = json!("deferred_squares");
    fixture["reverse"] = json!(reverse);
    fixture["folded"] = json!(folded);
    fixture
}

fn main() {
    let mut fixtures = vec![outlined_constant()];
    for reverse in [false, true] {
        for folded in [false, true] {
            fixtures.push(deferred_squares(reverse, folded));
        }
    }
    println!(
        "{}",
        serde_json::to_string_pretty(&json!({
            "schema": "shieldd.compiler-controls.v1",
            "scalar_encoding": "canonical-big-endian-32",
            "modulus_minus_one": hex::encode((-Scalar::one()).encode()),
            "fixtures": fixtures,
        }))
        .unwrap()
    );
}
