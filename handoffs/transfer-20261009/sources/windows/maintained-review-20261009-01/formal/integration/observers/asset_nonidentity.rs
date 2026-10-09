//! The one existing balance generator nonidentity inverse; no Var operations.
use crate::{group::Point, scalar::inspection::Observed};
use commonware_cryptography::{bls12381::primitives::group::Scalar, zk::circuit::{CircuitIdx, Var}};
use std::{cell::RefCell, marker::PhantomData, rc::Rc};

#[derive(Clone, PartialEq, Eq)]
pub struct Report {pub asset:Observed,pub hash:Observed,pub generator:[Observed;2],pub inverse:Observed}
impl Report {
    pub fn selected(&self)->Vec<CircuitIdx> {
        let mut result=[&self.asset,&self.hash,&self.generator[0],&self.generator[1],&self.inverse]
            .into_iter().filter_map(|v|match v {Observed::Source(i)=>Some(*i),_=>None}).collect::<Vec<_>>();
        result.sort();result.dedup();result
    }
}
#[derive(Default)]
struct State {scope:Option<[Observed;4]>,report:Option<Report>,entered:usize,invalid:bool,taken:bool}
thread_local! {static STATE:RefCell<Option<State>>=const{RefCell::new(None)};}
pub struct Capture { _thread:PhantomData<Rc<()>> }
impl Drop for Capture {fn drop(&mut self){STATE.with(|s|*s.borrow_mut()=None);}}
pub fn begin()->anyhow::Result<Capture> {STATE.with(|s| {
    anyhow::ensure!(s.borrow().is_none(),"nested asset nonidentity capture");
    *s.borrow_mut()=Some(State::default());Ok(Capture{_thread:PhantomData})
})}
fn observed(v:&Var<'_,Scalar>)->Observed {match v.inspect_circuit_idx(){
    Some(i)=>Observed::Source(i),None=>Observed::Native(v.inspect_native().expect("invalid asset variable").clone())
}}
pub struct Scope {active:bool,_thread:PhantomData<Rc<()>>}
impl Drop for Scope {fn drop(&mut self){if self.active {STATE.with(|s| {
    if let Some(s)=s.borrow_mut().as_mut(){s.scope=None;}
});}}}
pub fn scope<'ctx>(asset:&Var<'ctx,Scalar>,hash:&Var<'ctx,Scalar>,generator:&Point<Var<'ctx,Scalar>>)->Scope {
    let active=STATE.with(|s| {let mut s=s.borrow_mut();let Some(s)=s.as_mut() else{return false;};
        if s.scope.is_some() || s.entered!=0 || s.taken {s.invalid=true;return false;}
        s.entered+=1;s.scope=Some([observed(asset),observed(hash),observed(&generator.x),observed(&generator.y)]);true
    });Scope{active,_thread:PhantomData}
}
pub fn record<'ctx>(x:&Var<'ctx,Scalar>,inverse:&Var<'ctx,Scalar>){STATE.with(|s| {
    let mut s=s.borrow_mut();let Some(s)=s.as_mut() else{return;};
    let Some([asset,hash,gx,gy])=s.scope.clone() else{return;};
    let inverse=observed(inverse);
    if s.taken || s.report.is_some() || observed(x)!=gx ||
        !matches!(&inverse,Observed::Source(CircuitIdx::Witness(_))) {s.invalid=true;return;}
    s.report=Some(Report{asset,hash,generator:[gx,gy],inverse});
});}
pub fn take()->anyhow::Result<Report>{STATE.with(|s| {
    let mut s=s.borrow_mut();let s=s.as_mut().ok_or_else(||anyhow::anyhow!("inactive asset nonidentity capture"))?;
    anyhow::ensure!(!s.invalid && !s.taken && s.scope.is_none() && s.entered==1,"asset nonidentity scope/count/truncation mismatch");
    let report=s.report.clone().ok_or_else(||anyhow::anyhow!("missing actual asset inverse"))?;
    anyhow::ensure!(report.selected().len()<=5,"asset nonidentity handle bound");s.taken=true;Ok(report)
})}

#[cfg(test)]
mod tests {
    use super::*;
    fn report()->Report {let w=|i|Observed::Source(CircuitIdx::Witness(i));
        Report{asset:w(1),hash:w(2),generator:[w(3),w(4)],inverse:w(5)}}
    #[test]
    fn lifecycle_refuses_truncation_nested_and_retaking() {
        {let _capture=begin().unwrap();assert!(begin().is_err());assert!(take().is_err());}
        let _capture=begin().unwrap();
        STATE.with(|s|{let mut s=s.borrow_mut();let s=s.as_mut().unwrap();s.entered=1;s.report=Some(report());});
        assert_eq!(take().unwrap().selected().len(),5);assert!(take().is_err());
    }
    #[test]
    fn open_scope_poison_and_panic_cleanup() {
        {let _capture=begin().unwrap();STATE.with(|s|{let mut s=s.borrow_mut();let s=s.as_mut().unwrap();
            let r=report();s.entered=1;s.scope=Some([r.asset.clone(),r.hash.clone(),r.generator[0].clone(),r.generator[1].clone()]);s.report=Some(r);});
            assert!(take().is_err());
            STATE.with(|s|{let mut s=s.borrow_mut();let s=s.as_mut().unwrap();s.scope=None;s.invalid=true;});assert!(take().is_err());}
        assert!(std::panic::catch_unwind(||{let _capture=begin().unwrap();panic!("owned cleanup");}).is_err());
        let _capture=begin().unwrap();
    }
}
