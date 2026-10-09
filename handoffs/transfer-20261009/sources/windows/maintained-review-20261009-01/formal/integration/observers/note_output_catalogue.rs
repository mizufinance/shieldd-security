// Included only inside a NEW diagnostic catalogue, never an active stage.
#[cfg(feature = "formal-observer")]
pub struct NoteOutputInspection {
    pub compiled: Compiled,
    pub report: crate::note::output_inspection::Report,
    pub selected: Vec<circuit::CircuitIdx>,
    pub expressions: Vec<Vec<(u32, Scalar)>>,
    pub constant_copy: u32,
}
#[cfg(feature = "formal-observer")]
pub fn inspect_transfer_note_outputs() -> Result<NoteOutputInspection> {
    let _capture = crate::note::output_inspection::begin()?;
    let p = Parameters::load()?;let g = Generators::derive(&p);let w = template(Family::Transfer);
    let (c, returned) = circuit::build(|ctx| w.constrain(ctx,&p,&g,&Scalar::zero()));
    anyhow::ensure!(returned.len()==2,"Transfer return roles changed");
    let layout = InputLayout::new(vec![returned[0]],vec![vec![returned[1]]])?;
    let report = crate::note::output_inspection::take()?;let selected = report.selected();
    anyhow::ensure!(selected.len()<=512,"output source LC page bound");
    let (relation,expressions,constant_copy)=Relation::compile_inspected(&c,&layout,&selected)?;
    Ok(NoteOutputInspection { compiled: Compiled { family:Family::Transfer,relation,layout },
        report,selected,expressions,constant_copy })
}
