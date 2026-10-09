// Append only in a new diagnostic source child, retaining the existing74-page ABI.
#[cfg(feature="formal-observer")]
pub struct RemainingPage<'a> {
    pub report: &'a crate::transfer::remaining_inspection::Report,
    pub scope: &'a str,
    pub hash: Option<usize>,
    pub block: usize,
    pub selected: &'a [circuit::CircuitIdx],
    pub expressions: Vec<Vec<(u32,Scalar)>>,
    pub nodes: &'a [(u32,bool,circuit::CircuitIdx,circuit::CircuitIdx)],
}
#[cfg(feature="formal-observer")]
pub fn inspect_transfer_remaining_pages(scope:&str,
    mut consume:impl FnMut(usize,RemainingPage<'_>)->Result<()>,
)->Result<(Compiled,u32)> {
    use crate::scalar::inspection::Observed;
    use circuit::CircuitIdx;
    use std::collections::BTreeSet;
    anyhow::ensure!(crate::transfer::remaining_inspection::SCOPES.contains(&scope),
        "unsupported remaining component scope");
    let _capture=crate::transfer::remaining_inspection::begin()?;
    let p=Parameters::load()?;let g=Generators::derive(&p);let w=template(Family::Transfer);
    let (c,returned)=circuit::build(|ctx|w.constrain(ctx,&p,&g,&Scalar::zero()));
    anyhow::ensure!(returned.len()==2,"Transfer return roles changed");
    let report=crate::transfer::remaining_inspection::take()?;
    let layout=InputLayout::new(vec![returned[0]],vec![vec![returned[1]]])?;
    let mut roles=BTreeSet::new();
    for record in &report.records {
        if record.scope==scope || record.scope=="caller" {
            for value in &record.values {if let Observed::Source(index)=value {roles.insert(*index);}}
        }
    }
    anyhow::ensure!(!roles.is_empty() && roles.len()<=4096,"remaining role selection bound");
    let mut pages=vec![(None,0,roles.into_iter().collect::<Vec<_>>(),Vec::new())];
    for (index,hash) in report.hashes.iter().enumerate().filter(|(_,hash)|hash.scope==scope) {
        for (block,state) in hash.blocks.iter().enumerate() {
            let boundaries=hash.inputs.iter().chain(std::iter::once(&hash.output))
                .chain(hash.blocks.iter().flat_map(|b|b.before.iter().chain(&b.after))).collect::<Vec<_>>();
            let width=if hash.inputs.len()<=2{3}else{6};
            let (selected,nodes)=transfer_hash_page_cone(&c,Vec::new(),&state.before,&state.after,&boundaries,width)?;
            pages.push((Some(index),block,selected,nodes));
        }
    }
    anyhow::ensure!(pages.len()<=74,"remaining component exceeds existing74-page bound");
    let selections=pages.iter().map(|p|p.2.as_slice()).collect::<Vec<_>>();
    let (relation,copy)=Relation::compile_inspected_pages(&c,&layout,pages.len(),selections,
        |ordinal,selected,expressions| {let plan=&pages[ordinal];consume(ordinal,RemainingPage {
            report:&report,scope,hash:plan.0,block:plan.1,selected,expressions,nodes:&plan.3})})?;
    Ok((Compiled {family:Family::Transfer,relation,layout},copy))
}
