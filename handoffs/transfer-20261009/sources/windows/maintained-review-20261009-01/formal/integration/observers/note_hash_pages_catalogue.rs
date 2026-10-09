// Included inside catalogue.rs after note_hash_catalogue.rs, future stage only.
#[cfg(feature = "formal-observer")]
pub struct NoteHashPage<'a> {
    pub hash: &'a crate::hash::note_inspection::Report,
    pub selected: &'a [circuit::CircuitIdx],
    pub expressions: Vec<Vec<(u32, Scalar)>>,
    pub nodes: Vec<(u32, bool, circuit::CircuitIdx, circuit::CircuitIdx)>,
}
#[cfg(feature = "formal-observer")]
pub fn inspect_transfer_note_hash_pages(
    mut consume: impl FnMut(usize, NoteHashPage<'_>) -> Result<()>,
) -> Result<(Compiled, u32)> {
    let _hash_capture = crate::hash::note_inspection::begin_all()?;
    let _spend_capture = crate::note::spend_inspection::begin()?;
    let p = Parameters::load()?;
    let g = Generators::derive(&p);
    let w = template(Family::Transfer);
    let (c, returned) = circuit::build(|ctx| w.constrain(ctx, &p, &g, &Scalar::zero()));
    anyhow::ensure!(returned.len() == 2, "Transfer return roles changed");
    let layout = InputLayout::new(vec![returned[0]], vec![vec![returned[1]]])?;
    let spends = crate::note::spend_inspection::take()?;
    let hashes = crate::hash::note_inspection::take_all()?;
    let mut jobs = Vec::new();
    for hash in hashes {
        validate_note_hash_roles(&spends, &hash)?;
        for block in 0..hash.blocks.len() {
            let mut job = hash.clone();
            job.block = block;
            jobs.push(job);
        }
    }
    anyhow::ensure!(jobs.len() == 55, "two-note55 permutation inventory changed");
    // Only compact handles survive this pass. No cone/LC page is retained.
    let pages = jobs
        .iter()
        .map(|hash| note_hash_page_cone(&c, &spends, hash).map(|(selected, _)| selected))
        .collect::<Result<Vec<_>>>()?;
    let (relation, constant_copy) = Relation::compile_inspected_pages::<_, _, anyhow::Error>(
        &c,
        &layout,
        55,
        pages.iter().map(Vec::as_slice),
        |ordinal, selected, expressions| {
            let hash = &jobs[ordinal];
            let (expected, nodes) = note_hash_page_cone(&c, &spends, hash)?;
            anyhow::ensure!(
                expected.as_slice() == selected,
                "paged source handle inventory changed"
            );
            consume(
                ordinal,
                NoteHashPage {
                    hash,
                    selected,
                    expressions,
                    nodes,
                },
            )
        },
    )?;
    Ok((
        Compiled {
            family: Family::Transfer,
            relation,
            layout,
        },
        constant_copy,
    ))
}
