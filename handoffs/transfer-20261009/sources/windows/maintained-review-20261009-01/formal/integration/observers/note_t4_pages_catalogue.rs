// NEW combined stage: 55 hash pages plus one compact two-spend/48-tree page.
#[cfg(feature = "formal-observer")]
pub struct NoteTreePage<'a> {
    pub spends: &'a crate::note::spend_inspection::Report,
    pub levels: &'a [crate::tree::note_inspection::Level],
    pub products: &'a [Vec<[crate::scalar::inspection::Observed; 3]>],
    pub selected: &'a [circuit::CircuitIdx],
    pub expressions: Vec<Vec<(u32, Scalar)>>,
    pub spend_nodes: Vec<(u32, bool, circuit::CircuitIdx, circuit::CircuitIdx)>,
}
#[cfg(feature = "formal-observer")]
pub enum NoteT4Page<'a> {
    Hash(NoteHashPage<'a>),
    Tree(NoteTreePage<'a>),
}
#[cfg(feature = "formal-observer")]
pub fn inspect_transfer_note_t4_pages(
    mut consume: impl FnMut(usize, NoteT4Page<'_>) -> Result<()>,
) -> Result<(Compiled, u32)> {
    use crate::scalar::inspection::Observed;
    use circuit::CircuitIdx;
    use std::collections::BTreeSet;
    let _hash_capture = crate::hash::note_inspection::begin_all()?;
    let _spend_capture = crate::note::spend_inspection::begin()?;
    let _tree_capture = crate::tree::note_inspection::begin()?;
    let p = Parameters::load()?;
    let g = Generators::derive(&p);
    let w = template(Family::Transfer);
    let (c, returned) = circuit::build(|ctx| w.constrain(ctx, &p, &g, &Scalar::zero()));
    anyhow::ensure!(returned.len() == 2, "Transfer return roles changed");
    let layout = InputLayout::new(vec![returned[0]], vec![vec![returned[1]]])?;
    let spends = crate::note::spend_inspection::take()?;
    let hashes = crate::hash::note_inspection::take_all()?;
    let levels = crate::tree::note_inspection::take()?;
    let mut jobs = Vec::new();
    for hash in hashes {
        validate_note_hash_roles(&spends, &hash)?;
        for block in 0..hash.blocks.len() {
            let mut job = hash.clone();
            job.block = block;
            jobs.push(job);
        }
    }
    anyhow::ensure!(
        jobs.len() == 55 && levels.len() == 48,
        "combined note hash/tree inventory changed"
    );
    let products = levels
        .iter()
        .map(|level| inspect_note_tree_products(&c, level))
        .collect::<Result<Vec<_>>>()?;
    let mut tree_selected: BTreeSet<_> = spends.selected().into_iter().collect();
    for (level, products) in levels.iter().zip(&products) {
        anyhow::ensure!(
            level.low == Observed::Source(spends.spends[level.slot].position_bits[2 * level.level])
                && level.high
                    == Observed::Source(
                        spends.spends[level.slot].position_bits[2 * level.level + 1]
                    ),
            "note tree position bit roles changed"
        );
        let expected_node = if level.level == 0 {
            &spends.spends[level.slot].commitment
        } else {
            &levels[level.slot * 24 + level.level - 1].output
        };
        anyhow::ensure!(
            &level.node == expected_node,
            "note tree consecutive node source changed"
        );
        if level.level == 23 {
            anyhow::ensure!(
                level.output == spends.spends[level.slot].computed_anchor,
                "note tree final source changed"
            );
        }
        let hash = &jobs
            .iter()
            .find(|hash| {
                hash.slot == level.slot
                    && hash.role == crate::hash::note_inspection::Role::StateLevel(level.level)
            })
            .ok_or_else(|| anyhow::anyhow!("missing level hash"))?;
        anyhow::ensure!(
            hash.inputs[1..] == level.children && hash.output == level.output,
            "note tree/hash source boundary mismatch"
        );
        for value in [&level.node, &level.low, &level.high, &level.output]
            .into_iter()
            .chain(level.siblings.iter())
            .chain(level.swaps.iter())
            .chain(level.children.iter())
            .chain(products.iter().flatten())
        {
            if let Observed::Source(index) = value {
                tree_selected.insert(*index);
            }
        }
    }
    let tree_selected: Vec<_> = tree_selected.into_iter().collect();
    anyhow::ensure!(
        tree_selected.len() <= 4096,
        "combined note/tree LC page exceeds4096"
    );
    let mut spend_nodes = Vec::new();
    for product in &spends.spends[1].optional.as_ref().unwrap().products {
        let [Observed::Source(left), Observed::Source(right), Observed::Source(CircuitIdx::Node(output))] =
            product
        else {
            anyhow::bail!("optional branch product source changed")
        };
        let (multiply, a, b) = c
            .inspect_node(*output)
            .ok_or_else(|| anyhow::anyhow!("missing branch source"))?;
        anyhow::ensure!(
            multiply && a == *left && b == *right,
            "branch source operand mismatch"
        );
        spend_nodes.push((*output, multiply, a, b));
    }
    spend_nodes.sort_by_key(|node| node.0);
    let mut pages = jobs
        .iter()
        .map(|hash| note_hash_page_cone(&c, &spends, hash).map(|(selected, _)| selected))
        .collect::<Result<Vec<_>>>()?;
    pages.push(tree_selected);
    let (relation, copy) = Relation::compile_inspected_pages::<_, _, anyhow::Error>(
        &c,
        &layout,
        56,
        pages.iter().map(Vec::as_slice),
        |ordinal, selected, expressions| {
            if ordinal < 55 {
                let hash = &jobs[ordinal];
                let (expected, nodes) = note_hash_page_cone(&c, &spends, hash)?;
                anyhow::ensure!(
                    expected.as_slice() == selected,
                    "hash page source inventory changed"
                );
                consume(
                    ordinal,
                    NoteT4Page::Hash(NoteHashPage {
                        hash,
                        selected,
                        expressions,
                        nodes,
                    }),
                )
            } else {
                consume(
                    ordinal,
                    NoteT4Page::Tree(NoteTreePage {
                        spends: &spends,
                        levels: &levels,
                        products: &products,
                        selected,
                        expressions,
                        spend_nodes: spend_nodes.clone(),
                    }),
                )
            }
        },
    )?;
    Ok((
        Compiled {
            family: Family::Transfer,
            relation,
            layout,
        },
        copy,
    ))
}
