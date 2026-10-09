// Fresh-only include in transfer-ownership-inspection.rs; shares its strict
// original shape guard and four-spool row-by-row/repeated-observation qualifier.
fn capture_rk_subgroup(prefix: &str) -> anyhow::Result<()> {
    let catalogue::RkSubgroupInspection { compiled, report, selected, expressions,
        constant_copy, nodes } = catalogue::inspect_transfer_rk_subgroup()?;
    let spool = RowSpool::new(&compiled)?;
    ensure_original_shape(&spool.shape())?;
    anyhow::ensure!(constant_copy == 200692, "RK original constant-copy shape");
    drop(compiled);
    spool.persist(prefix, "observer")?;
    let metadata = json!({
        "schema":"shieldd-transfer-rk-subgroup-v1", "family":"transfer",
        "scope":"bounded RK cofactor/on-curve/nonidentity source observation; row and native joins open",
        "relation_digest":hex::encode(spool.digest), "domain_size":spool.domain,
        "full_rows":spool.rows, "constant_copy":constant_copy,
        "ordinary_full_ordered_rows_equal":false, "repeated_observations_equal":false,
        "inputs":report.inputs.iter().map(index).collect::<Vec<_>>(),
        "curve":report.curve.iter().map(index).collect::<Vec<_>>(),
        "doubles":report.doubles.iter().map(|p|p.iter().map(index).collect::<Vec<_>>()).collect::<Vec<_>>(),
        "spans":report.spans, "nonidentity":report.nonidentity.iter().map(index).collect::<Vec<_>>(),
        "nonidentity_product":index(&report.nonidentity_product),
        "expressions":selected.iter().zip(&expressions).map(|(source,terms)|json!({
            "source":index(source), "terms":terms.iter().map(|(column,coefficient)|
                json!([column,hex::encode(coefficient.encode())])).collect::<Vec<_>>()
        })).collect::<Vec<_>>(),
        "nodes":nodes.iter().map(|(node,multiply,left,right)|json!({
            "index":node,"multiply":multiply,"left":index(left),"right":index(right)
        })).collect::<Vec<_>>()
    });
    write_packet_json(prefix, "pending.json", &metadata)?;
    Ok(())
}
