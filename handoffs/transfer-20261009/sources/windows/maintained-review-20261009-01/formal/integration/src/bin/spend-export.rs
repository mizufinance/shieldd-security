//! Ordinary clean-head Transfer metadata and original selected input handles.
//!
//! The historical spend observer API is unavailable at PR160. This exporter
//! calls the actual public catalogue compiler without instrumentation, key setup
//! or witness evaluation. It exports no internal spend mapping or raw rows.
use commonware_cryptography::zk::circuit::CircuitIdx;
use serde_json::{Value, json};
use shieldd_sdk_circuits::{catalogue, proof::Family, transfer};
use std::io::{self, Write};

fn source(index: CircuitIdx) -> Value {
    match index {
        CircuitIdx::Constant(index) => json!({"kind":"constant", "index":index}),
        CircuitIdx::Witness(index) => json!({"kind":"witness", "index":index}),
        CircuitIdx::Node(index) => json!({"kind":"node", "index":index}),
    }
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let compiled = catalogue::compile(Family::Transfer)?;
    assert_eq!(compiled.family, Family::Transfer);
    assert_eq!(transfer::STATEMENT_FIELDS, 64);
    let relation = &compiled.relation;
    let public = compiled.layout.public();
    let blocks = compiled.layout.blocks();
    assert_eq!(public.len(), 1);
    assert_eq!(blocks.len(), 1);
    assert_eq!(blocks[0].len(), 1);
    assert_eq!(relation.public_inputs(), 1);
    assert_eq!(relation.blocks(), &[1]);
    assert_eq!(relation.committed_inputs(), 1);
    let families: Vec<_> = Family::ALL.iter().map(|family| {
        json!({"id":*family as u8, "label":family.label()})
    }).collect();
    let ids: Vec<_> = Family::ALL.iter().map(|family| *family as u8).collect();
    assert_eq!(ids, vec![1, 2, 3, 4, 5, 6, 9]);
    let record = json!({
        "schema_version":1,
        "subject":"ordinary Transfer relation metadata and selected input handles",
        "constructor":"catalogue::compile(Family::Transfer)",
        "relation_digest":hex::encode(relation.digest()),
        "domain_size":relation.domain_size(),
        "public_inputs":relation.public_inputs(),
        "committed_blocks":relation.blocks(),
        "public_handles":public.iter().copied().map(source).collect::<Vec<_>>(),
        "committed_handles":blocks.iter().map(|block| {
            block.iter().copied().map(source).collect::<Vec<_>>()
        }).collect::<Vec<_>>(),
        "statement_fields":transfer::STATEMENT_FIELDS,
        "families":families,
        "spend_mapping":"OPEN: no internal observation API at the clean runtime pin",
        "raw_rows":"NOT_EXPORTED: relation row access is private at the clean runtime pin",
        "limits":"External source/host/build receipts must establish the exact runtime identity. CircuitIdx handles are source identities, not semantic witness proofs or compiled column indices. Metadata and family enumeration do not qualify raw rows, statement hash, keys, setup, witness/proof acceptance, whole-family semantics or runtime effects."
    });
    let mut output = io::BufWriter::new(io::stdout().lock());
    serde_json::to_writer_pretty(&mut output, &record)?;
    output.write_all(b"\n")?;
    output.flush()?;
    Ok(())
}
