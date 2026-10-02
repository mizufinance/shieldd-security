use serde_json::json;
use shieldd_sdk_circuits::{catalogue, proof::Family};

fn main() {
    let compiled = catalogue::compile(Family::Transfer).expect("compile original Transfer");
    println!(
        "{}",
        json!({
            "relation_digest": hex::encode(compiled.relation.digest()),
            "domain_size": compiled.relation.domain_size(),
            "public_inputs": compiled.relation.public_inputs(),
            "committed_blocks": compiled.relation.blocks(),
            "layout": format!("{:?}", compiled.layout),
        })
    );
}
