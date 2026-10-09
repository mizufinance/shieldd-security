/// The same Transfer build and ordinary compiler entry point as compile().
/// The callback only reads the already-built source program. No witness values,
/// satisfying assignment, setup material, or changed compiler lowering is used.
#[cfg(feature = "formal-observer")]
pub fn inspect_transfer_program<Consume>(mut consume: Consume) -> Result<Compiled>
where
    Consume: FnMut(&circuit::Circuit<Scalar>, &InputLayout) -> Result<()>,
{
    let p = Parameters::load()?;
    let g = Generators::derive(&p);
    let w = template(Family::Transfer);
    let (c, selected) = circuit::build(|ctx| w.constrain(ctx, &p, &g, &Scalar::zero()));
    anyhow::ensure!(selected.len() == 2, "complete Transfer program return roles changed");
    let layout = InputLayout::new(vec![selected[0]], vec![vec![selected[1]]])?;
    consume(&c, &layout)?;
    let relation = Relation::compile(&c, &layout)?;
    Ok(Compiled { family: Family::Transfer, relation, layout })
}
