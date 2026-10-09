//! One balance ASSET_GENERATOR26/1 call, with width3 checkpoints and exact scope.
use crate::scalar::inspection::Observed;
use commonware_cryptography::{bls12381::primitives::group::Scalar, zk::circuit::Var};
use std::{cell::RefCell, marker::PhantomData, rc::Rc};
#[derive(Clone, PartialEq, Eq)]
pub struct Report { pub asset: Observed, pub output: Observed, pub before: Vec<Observed>, pub after: Vec<Observed> }
#[derive(Default)]
struct State { asset: Option<Observed>, before: Option<Vec<Observed>>, after: Option<Vec<Observed>>,
    output: Option<Observed>, active: bool, entered: bool, called: bool, invalid: bool, taken: bool }
thread_local! { static STATE: RefCell<Option<State>> = const { RefCell::new(None) }; }
pub struct Capture { _thread: PhantomData<Rc<()>> }
impl Drop for Capture { fn drop(&mut self) { STATE.with(|s| *s.borrow_mut()=None); } }
pub fn begin() -> anyhow::Result<Capture> { STATE.with(|s| {
    anyhow::ensure!(s.borrow().is_none(),"nested asset hash capture");*s.borrow_mut()=Some(State::default());
    Ok(Capture { _thread:PhantomData }) }) }
fn observed(value:&Var<'_,Scalar>) -> Observed { match value.inspect_circuit_idx() {
    Some(index)=>Observed::Source(index),None=>Observed::Native(value.inspect_native().expect("invalid asset hash var").clone()) } }
pub struct Scope { active: bool, _thread: PhantomData<Rc<()>> }
impl Drop for Scope { fn drop(&mut self) { if self.active { STATE.with(|s| {
    if let Some(s)=s.borrow_mut().as_mut() { s.invalid=true;s.active=false; }
}); } } }
pub fn scope(asset:&Var<'_,Scalar>) -> Scope { let active=STATE.with(|s| {
    let mut s=s.borrow_mut();let Some(s)=s.as_mut() else { return false; };
    if s.entered || s.taken { s.invalid=true;return false; }
    s.entered=true;s.active=true;s.asset=Some(observed(asset));true
});Scope { active,_thread:PhantomData } }
pub struct Call { active: bool, _thread: PhantomData<Rc<()>> }
pub(crate) fn start(domain:u8,inputs:&[Var<'_,Scalar>]) -> Call { let active=STATE.with(|s| {
    let mut s=s.borrow_mut();let Some(s)=s.as_mut() else { return false; };
    if !s.active { return false; }
    if s.called || domain!=26 || inputs.len()!=1 || Some(observed(&inputs[0]))!=s.asset {
        s.invalid=true;return false;
    }
    s.called=true;true
});Call { active,_thread:PhantomData } }
pub(crate) fn state(call:&Call,index:usize,after:bool,values:&[Var<'_,Scalar>]) {
    if !call.active { return; } STATE.with(|s| {
        let mut s=s.borrow_mut();let Some(s)=s.as_mut() else { return; };
        if index!=0 || values.len()!=3 || s.output.is_some() { s.invalid=true;return; }
        if after {
            if s.before.is_none() || s.after.is_some() { s.invalid=true;return; }
            s.after=Some(values.iter().map(observed).collect());
        } else {
            if s.before.is_some() || s.after.is_some() { s.invalid=true;return; }
            s.before=Some(values.iter().map(observed).collect());
        }
    });
}
pub(crate) fn finish(call:Call,output:&Var<'_,Scalar>) {
    if !call.active { return; } STATE.with(|s| {
        let mut s=s.borrow_mut();let Some(s)=s.as_mut() else { return; };let output=observed(output);
        if s.output.is_some() || s.after.as_ref().map(|a| &a[1])!=Some(&output) { s.invalid=true;return; }
        s.output=Some(output);
    });
}
pub fn finish_scope(mut scope:Scope,output:&Var<'_,Scalar>) {
    if !scope.active { return; } STATE.with(|s| {
        let mut s=s.borrow_mut();let Some(s)=s.as_mut() else { return; };
        if !s.active || s.output.as_ref()!=Some(&observed(output)) { s.invalid=true; }
        s.active=false;
    });scope.active=false;
}
pub fn take() -> anyhow::Result<Report> { STATE.with(|s| {
    let mut s=s.borrow_mut();let s=s.as_mut().ok_or_else(||anyhow::anyhow!("inactive asset hash capture"))?;
    anyhow::ensure!(!s.invalid && !s.active && s.entered && s.called && !s.taken &&
        s.asset.is_some() && s.output.is_some() && s.before.is_some() && s.after.is_some(),"incomplete asset hash scope");
    s.taken=true;Ok(Report { asset:s.asset.take().unwrap(),output:s.output.take().unwrap(),
        before:s.before.take().unwrap(),after:s.after.take().unwrap() }) }) }
#[cfg(test)]
mod tests {
    use super::*;
    fn values() -> Vec<Var<'static,Scalar>> { (1..=3).map(|i|Var::native(Scalar::from(i as u64))).collect() }
    #[test] fn exact_scope_order_and_repeat_refusal() {
        let capture=begin().unwrap();assert!(begin().is_err());let v=values();let scope=scope(&v[0]);
        let call=start(26,&v[..1]);state(&call,0,false,&v);state(&call,0,true,&v);finish(call,&v[1]);
        finish_scope(scope,&v[1]);let report=take().unwrap();assert!(report.asset==observed(&v[0]));
        assert!(take().is_err());drop(capture);assert!(take().is_err());
    }
    #[test] fn domain_arity_truncation_and_output_links_refuse() {
        for mode in 0..4 { let _capture=begin().unwrap();let v=values();let scope=scope(&v[0]);
            let call=start(if mode==0 {25}else{26},if mode==1 {&v[..2]}else{&v[..1]});
            state(&call,0,false,&v);if mode!=2 {state(&call,0,true,&v);}
            finish(call,&v[1]);finish_scope(scope,if mode==3 {&v[2]}else{&v[1]});assert!(take().is_err());
        }
    }
}
