//! Future diagnostic recovery roles; read-only, <=1024 handles, two outputs.
//! Hash/group/scalar/native/row claims are separate required joins.
use super::Capsule;
use crate::{group::Point, scalar::inspection::Observed};
use commonware_cryptography::{bls12381::primitives::group::Scalar, zk::circuit::{BoolVar,CircuitIdx,Var}};
use std::{cell::RefCell,marker::PhantomData,rc::Rc};

#[derive(Clone,PartialEq,Eq)]
pub struct CoreHandles {
    pub payload_key:[Observed;2], pub amount:Observed, pub blinding:Observed,
    pub randomizer:Observed, pub bits:Vec<CircuitIdx>, pub seed:Observed,
    pub capsule:[Observed;7], pub commitment:Observed,
    pub computed_epk:[Observed;2], pub shared:[Observed;2],
    pub secret:Observed, pub computed_c2:Observed, pub epk_inverse:Observed,
}
#[derive(Clone,PartialEq,Eq)]
pub struct Report {
    pub core:CoreHandles, pub computed_confirmation:Observed,
    pub amount_stream:Observed, pub computed_amount:Observed,
    pub blinding_stream:Observed, pub computed_blinding:Observed, pub plaintext_inverse:Observed,
}
impl Report {
    pub fn selected(&self)->Vec<CircuitIdx> {
        let mut result=self.core.bits.clone();
        let mut add=|value:&Observed| { if let Observed::Source(index)=value {result.push(*index);} };
        for value in self.core.payload_key.iter().chain(&self.core.capsule)
            .chain(&self.core.computed_epk).chain(&self.core.shared) {add(value);}
        for value in [&self.core.amount,&self.core.blinding,&self.core.randomizer,&self.core.seed,
            &self.core.commitment,&self.core.secret,&self.core.computed_c2,&self.computed_confirmation,
            &self.amount_stream,&self.computed_amount,&self.blinding_stream,&self.computed_blinding,&self.core.epk_inverse,&self.plaintext_inverse] {add(value);}
        result.sort();result.dedup();result
    }
}
#[derive(Default)]
struct State { active:bool, invalid:bool, taken:bool, pending:Option<CoreHandles>, reports:Vec<Report> }
thread_local! {static STATE:RefCell<Option<State>>=const {RefCell::new(None)};}
pub struct Capture {_thread:PhantomData<Rc<()>>}
impl Drop for Capture {fn drop(&mut self) {STATE.with(|s|*s.borrow_mut()=None);}}
pub fn begin()->anyhow::Result<Capture> {
    STATE.with(|s| {let mut s=s.borrow_mut();anyhow::ensure!(s.is_none(),"nested recovery capture");
        *s=Some(State::default());Ok(Capture {_thread:PhantomData})})
}
pub struct Scope {active:bool,before:usize,_thread:PhantomData<Rc<()>>}
pub fn scope()->Scope {
    let (active,before)=STATE.with(|s| {let mut s=s.borrow_mut();let Some(s)=s.as_mut() else {return (false,0)};
        if s.active || s.taken || s.reports.len()>=2 || s.pending.is_some() {s.invalid=true;return (false,0)}
        s.active=true;(true,s.reports.len())});
    Scope {active,before,_thread:PhantomData}
}
impl Drop for Scope {
    fn drop(&mut self) {if !self.active {return} STATE.with(|s| {let mut s=s.borrow_mut();
        let Some(s)=s.as_mut() else {return};
        if !s.active || s.pending.is_some() || s.reports.len()!=self.before+1 {s.invalid=true;}
        s.active=false;});}
}
fn observed(value:&Var<'_,Scalar>)->Observed {
    match value.inspect_circuit_idx() {Some(index)=>Observed::Source(index),
        None=>Observed::Native(value.inspect_native().expect("invalid recovery var").clone())}
}
fn point(value:&Point<Var<'_,Scalar>>)->[Observed;2] {[observed(&value.x),observed(&value.y)]}
pub(crate) fn core<'ctx>(payload_key:&Point<Var<'ctx,Scalar>>,amount:&Var<'ctx,Scalar>,blinding:&Var<'ctx,Scalar>,
    randomizer:&Var<'ctx,Scalar>,bits:&[BoolVar<'ctx,Scalar>],seed:&Var<'ctx,Scalar>,capsule:&Capsule<Var<'ctx,Scalar>>,
    computed_epk:&Point<Var<'ctx,Scalar>>,shared:&Point<Var<'ctx,Scalar>>,secret:&Var<'ctx,Scalar>,computed_c2:&Var<'ctx,Scalar>,epk_inverse:&Var<'ctx,Scalar>) {
    STATE.with(|s| {let mut s=s.borrow_mut();let Some(s)=s.as_mut() else {return};
        if !s.active {return}
        if s.taken || s.pending.is_some() || bits.len()!=252 || s.reports.len()>=2 {s.invalid=true;return}
        let bits:Option<Vec<_>>=bits.iter().map(|b|b.var().inspect_circuit_idx()).collect();
        let Some(bits)=bits else {s.invalid=true;return};
        s.pending=Some(CoreHandles {payload_key:point(payload_key),amount:observed(amount),blinding:observed(blinding),
            randomizer:observed(randomizer),bits,seed:observed(seed),capsule:capsule.commitment_inputs().each_ref().map(observed),
            commitment:observed(&capsule.commitment),computed_epk:point(computed_epk),shared:point(shared),
            secret:observed(secret),computed_c2:observed(computed_c2),epk_inverse:observed(epk_inverse)});
    });
}
pub(crate) fn plaintext<'ctx>(amount:&Var<'ctx,Scalar>,blinding:&Var<'ctx,Scalar>,capsule:&Capsule<Var<'ctx,Scalar>>,
    seed:&Var<'ctx,Scalar>,computed_confirmation:&Var<'ctx,Scalar>,amount_stream:&Var<'ctx,Scalar>,computed_amount:&Var<'ctx,Scalar>,
    blinding_stream:&Var<'ctx,Scalar>,computed_blinding:&Var<'ctx,Scalar>,epk_inverse:&Var<'ctx,Scalar>) {
    STATE.with(|s| {let mut s=s.borrow_mut();let Some(s)=s.as_mut() else {return};
        // Input release plaintext calls outside constrain are deliberately ignored.
        if !s.active {return}
        let Some(core)=s.pending.take() else {s.invalid=true;return};
        if s.taken || s.reports.len()>=2 || core.amount!=observed(amount) || core.blinding!=observed(blinding) ||
            core.seed!=observed(seed) || core.capsule!=capsule.commitment_inputs().each_ref().map(observed) ||
            core.commitment!=observed(&capsule.commitment) {s.invalid=true;return}
        s.reports.push(Report {core,computed_confirmation:observed(computed_confirmation),amount_stream:observed(amount_stream),
            computed_amount:observed(computed_amount),blinding_stream:observed(blinding_stream),computed_blinding:observed(computed_blinding),plaintext_inverse:observed(epk_inverse)});
    });
}
pub fn take()->anyhow::Result<[Report;2]> {
    STATE.with(|s| {let mut s=s.borrow_mut();let s=s.as_mut().ok_or_else(||anyhow::anyhow!("inactive recovery capture"))?;
        anyhow::ensure!(!s.active && !s.invalid && !s.taken && s.pending.is_none() && s.reports.len()==2,
            "recovery lifecycle/order/truncation mismatch");
        let mut handles=s.reports.iter().flat_map(Report::selected).collect::<Vec<_>>();handles.sort();handles.dedup();
        anyhow::ensure!(handles.len()<=1024,"recovery role handle bound");s.taken=true;
        s.reports.clone().try_into().map_err(|_|anyhow::anyhow!("recovery fixed count mismatch"))})
}

#[cfg(test)]
mod tests {
    use super::*;
    fn report()->Report {
        let n=||Observed::Native(Scalar::from(0));
        Report {core:CoreHandles {payload_key:[n(),n()],amount:n(),blinding:n(),randomizer:n(),
            bits:(0..252).map(CircuitIdx::Witness).collect(),seed:n(),capsule:std::array::from_fn(|_|n()),
            commitment:n(),computed_epk:[n(),n()],shared:[n(),n()],secret:n(),computed_c2:n(),epk_inverse:n()},
            computed_confirmation:n(),amount_stream:n(),computed_amount:n(),blinding_stream:n(),computed_blinding:n(),plaintext_inverse:n()}
    }
    #[test]
    fn finite_scopes_truncation_and_repeat_take_refuse() {
        let capture=begin().unwrap();assert!(begin().is_err());assert!(take().is_err());
        {let _scope=scope();}assert!(take().is_err());drop(capture);
        let _capture=begin().unwrap();for _ in 0..2 {let _scope=scope();
            STATE.with(|s|s.borrow_mut().as_mut().unwrap().reports.push(report()));}
        assert_eq!(take().unwrap()[0].selected().len(),252);assert!(take().is_err());
    }
    #[test]
    fn nested_and_third_scope_poison_refuse() {
        {let _capture=begin().unwrap();let _scope=scope();let nested=scope();assert!(!nested.active);}
        let _capture=begin().unwrap();for _ in 0..2 {let _scope=scope();
            STATE.with(|s|s.borrow_mut().as_mut().unwrap().reports.push(report()));}
        assert!(!scope().active);assert!(take().is_err());
    }
}
