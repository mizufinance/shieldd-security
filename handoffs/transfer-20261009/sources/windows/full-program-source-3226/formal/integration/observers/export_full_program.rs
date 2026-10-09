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
