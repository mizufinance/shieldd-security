// Future catalogue include: reuse the maintained bounded ordinary DAG walk.
#[cfg(feature = "formal-observer")]
pub struct RecoveryHashPage<'a> {
    pub hash:&'a crate::recovery::hash_inspection::Report,
    pub capsules:&'a [crate::recovery::capsule_inspection::Report;2],
    pub selected:&'a [circuit::CircuitIdx],pub expressions:Vec<Vec<(u32,Scalar)>>,
    pub nodes:Vec<(u32,bool,circuit::CircuitIdx,circuit::CircuitIdx)>,
}
#[cfg(feature = "formal-observer")]
fn recovery_hash_page_cone(c:&circuit::Circuit<Scalar>,
    capsules:&[crate::recovery::capsule_inspection::Report;2],hash:&crate::recovery::hash_inspection::Report,
) -> Result<(Vec<circuit::CircuitIdx>,Vec<(u32,bool,circuit::CircuitIdx,circuit::CircuitIdx)>)> {
    let mut selected=capsules.iter().flat_map(|capsule|capsule.selected()).collect::<Vec<_>>();
    selected.sort();selected.dedup();
    anyhow::ensure!(selected.len()<=1024,"recovery roles handle bound changed");
    let boundaries:Vec<_>=hash.inputs.iter().chain(std::iter::once(&hash.output)).collect();
    transfer_hash_page_cone(c,selected,&hash.before,&hash.after,&boundaries,if hash.inputs.len()<=2 {3}else{6})
}
