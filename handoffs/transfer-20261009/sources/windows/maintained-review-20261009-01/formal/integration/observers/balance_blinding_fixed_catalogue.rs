// Future-only fixed balance blinding pages; ordinary build/layout/lowerer order unchanged.
#[cfg(feature = "formal-observer")]
fn balance_blinding_fixed_page_cone(c:&circuit::Circuit<Scalar>,report:&crate::group::balance_blinding_fixed_inspection::Report)
    -> Result<(Vec<circuit::CircuitIdx>,Vec<(u32,bool,circuit::CircuitIdx,circuit::CircuitIdx)>)> {
    use circuit::CircuitIdx;
    use std::collections::BTreeSet;
    anyhow::ensure!((1..=16).contains(&report.window_count) && report.windows.len()==report.window_count,
        "balance blinding fixed cone page exceeds16");
    let mut boundaries=BTreeSet::new();
    for value in &report.windows[0].points[0] {
        if let crate::scalar::inspection::Observed::Source(index)=value {boundaries.insert(*index);}
    }
    if report.window_start+report.window_count<126 {
        for value in &report.output {
            if let crate::scalar::inspection::Observed::Source(index)=value {boundaries.insert(*index);}
        }
    }
    let mut selected:BTreeSet<_>=report.selected().into_iter().collect();
    let mut pending:Vec<_>=selected.iter().copied().collect();let mut visited=BTreeSet::new();let mut nodes=Vec::new();
    while let Some(index)=pending.pop() {
        if !visited.insert(index) {continue}
        anyhow::ensure!(visited.len()<=8192,"balance blinding fixed source cone exceeds8192");
        match index {
            CircuitIdx::Node(node)=>{
                let (multiply,left,right)=c.inspect_node(node).ok_or_else(||anyhow::anyhow!("invalid balance blinding fixed source node"))?;
                nodes.push((node,multiply,left,right));
                if boundaries.contains(&index) {continue}
                if multiply && !matches!(left,CircuitIdx::Constant(_)) && !matches!(right,CircuitIdx::Constant(_)) {
                    selected.extend([index,left,right]);
                }
                pending.extend([left,right]);
            }
            CircuitIdx::Constant(_)|CircuitIdx::Witness(_)=>{selected.insert(index);}
        }
    }
    nodes.sort_by_key(|node|node.0);let selected:Vec<_>=selected.into_iter().collect();
    anyhow::ensure!(selected.len()<=4096,"balance blinding fixed selected LCs exceed4096");Ok((selected,nodes))
}
#[cfg(feature = "formal-observer")]
pub struct BalanceBlindingFixedPage<'a> {
    pub report:&'a crate::group::balance_blinding_fixed_inspection::Report,
    pub selected:&'a [circuit::CircuitIdx],pub expressions:Vec<Vec<(u32,Scalar)>>,
    pub nodes:Vec<(u32,bool,circuit::CircuitIdx,circuit::CircuitIdx)>,
}
#[cfg(feature = "formal-observer")]
pub fn inspect_transfer_balance_blinding_fixed_pages(mut consume:impl FnMut(usize,BalanceBlindingFixedPage<'_>)->Result<()>)->Result<(Compiled,u32)> {
    let _capture=crate::group::balance_blinding_fixed_inspection::begin()?;
    let p=Parameters::load()?;let g=Generators::derive(&p);let w=template(Family::Transfer);
    let (c,returned)=circuit::build(|ctx|w.constrain(ctx,&p,&g,&Scalar::zero()));
    anyhow::ensure!(returned.len()==2,"Transfer return roles changed");
    let layout=InputLayout::new(vec![returned[0]],vec![vec![returned[1]]])?;
    let full=crate::group::balance_blinding_fixed_inspection::take()?;
    let jobs=[0,16,32,48,64,80,96,112].iter().map(|&start|full.page(start,std::cmp::min(16,126-start)))
        .collect::<Result<Vec<_>>>()?;drop(full);
    let selections=jobs.iter().map(|job|balance_blinding_fixed_page_cone(&c,job).map(|(selected,_)|selected)).collect::<Result<Vec<_>>>()?;
    let (relation,copy)=Relation::compile_inspected_pages::<_,_,anyhow::Error>(
        &c,&layout,8,selections.iter().map(Vec::as_slice),|ordinal,selected,expressions|{
            let report=&jobs[ordinal];let (expected,nodes)=balance_blinding_fixed_page_cone(&c,report)?;
            anyhow::ensure!(expected.as_slice()==selected,"balance blinding fixed page selection changed");
            consume(ordinal,BalanceBlindingFixedPage {report,selected,expressions,nodes})
        })?;
    Ok((Compiled {family:Family::Transfer,relation,layout},copy))
}
