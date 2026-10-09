//! Future bounded recovery hash checkpoints; eight calls, one permutation each.
use super::capsule_inspection::Report as Capsule;
use crate::scalar::inspection::Observed;
use commonware_cryptography::{bls12381::primitives::group::Scalar,zk::circuit::Var};
use std::{cell::RefCell,marker::PhantomData,rc::Rc};

#[derive(Clone,Copy,PartialEq,Eq)]
pub enum Role { Secret,Confirmation,AmountStream,BlindingStream }
#[derive(Clone,PartialEq,Eq)]
pub struct Report {pub slot:usize,pub role:Role,pub domain:u8,pub inputs:Vec<Observed>,pub output:Observed,
    pub before:Vec<Observed>,pub after:Vec<Observed>}
struct Pending {role:Role,domain:u8,inputs:Vec<Observed>,before:Option<Vec<Observed>>,after:Option<Vec<Observed>>}
#[derive(Default)]
struct State {active:bool,invalid:bool,taken:bool,slots:usize,calls:usize,pending:Option<Pending>,reports:Vec<Report>}
thread_local! {static STATE:RefCell<Option<State>>=const {RefCell::new(None)};}
pub struct Capture {_thread:PhantomData<Rc<()>>}
impl Drop for Capture {fn drop(&mut self) {STATE.with(|s|*s.borrow_mut()=None);}}
pub fn begin()->anyhow::Result<Capture> {
    STATE.with(|s| {let mut s=s.borrow_mut();anyhow::ensure!(s.is_none(),"nested recovery hash capture");
        *s=Some(State::default());Ok(Capture {_thread:PhantomData})})
}
pub struct Scope {active:bool,_thread:PhantomData<Rc<()>>}
pub fn scope()->Scope {
    let active=STATE.with(|s| {let mut s=s.borrow_mut();let Some(s)=s.as_mut() else {return false};
        if s.active || s.taken || s.slots>=2 || s.pending.is_some() {s.invalid=true;return false}
        s.active=true;s.calls=0;true});Scope {active,_thread:PhantomData}
}
impl Drop for Scope {fn drop(&mut self) {if !self.active {return} STATE.with(|s| {let mut s=s.borrow_mut();
    let Some(s)=s.as_mut() else {return};if !s.active || s.calls!=4 || s.pending.is_some() || s.reports.len()!=4*(s.slots+1) {s.invalid=true;}
    s.active=false;s.slots+=1;});}}
pub struct Call {active:bool,_thread:PhantomData<Rc<()>>}
fn observed(value:&Var<'_,Scalar>)->Observed {
    match value.inspect_circuit_idx() {Some(index)=>Observed::Source(index),
        None=>Observed::Native(value.inspect_native().expect("invalid recovery hash var").clone())}
}
pub(crate) fn start(domain:u8,inputs:&[Var<'_,Scalar>])->Call {
    let active=STATE.with(|s| {let mut s=s.borrow_mut();let Some(s)=s.as_mut() else {return false};
        if !s.active {return false}
        // The existing capsule commitment is covered by the output hash lane.
        if domain==20 {if s.calls!=4 || s.pending.is_some() {s.invalid=true;}return false}
        let expected=match s.calls {0=>(Role::Secret,11,2),1=>(Role::Confirmation,21,4),
            2=>(Role::AmountStream,10,2),3=>(Role::BlindingStream,10,2),_=>{s.invalid=true;return false}};
        if s.taken || s.pending.is_some() || s.reports.len()>=8 || domain!=expected.1 || inputs.len()!=expected.2 {
            s.invalid=true;return false}
        s.calls+=1;s.pending=Some(Pending {role:expected.0,domain,inputs:inputs.iter().map(observed).collect(),before:None,after:None});true
    });Call {active,_thread:PhantomData}
}
pub(crate) fn state(call:&Call,index:usize,after:bool,values:&[Var<'_,Scalar>]) {
    if !call.active {return} STATE.with(|s| {let mut s=s.borrow_mut();let Some(s)=s.as_mut() else {return};
        let Some(p)=s.pending.as_mut() else {s.invalid=true;return};let width=if p.inputs.len()<=2 {3}else{6};
        if index!=0 || values.len()!=width || p.after.is_some() {s.invalid=true;return}
        if after {if p.before.is_none() {s.invalid=true;return}p.after=Some(values.iter().map(observed).collect());}
        else {if p.before.is_some() {s.invalid=true;return}p.before=Some(values.iter().map(observed).collect());}
    });
}
pub(crate) fn finish(call:Call,output:&Var<'_,Scalar>) {
    if !call.active {return} STATE.with(|s| {let mut s=s.borrow_mut();let Some(s)=s.as_mut() else {return};
        let Some(p)=s.pending.take() else {s.invalid=true;return};
        let (Some(before),Some(after))=(p.before,p.after) else {s.invalid=true;return};let output=observed(output);
        if after.get(1)!=Some(&output) {s.invalid=true;return}
        s.reports.push(Report {slot:s.slots,role:p.role,domain:p.domain,inputs:p.inputs,output,before,after});
    });
}
pub fn take(capsules:&[Capsule;2])->anyhow::Result<Vec<Report>> {
    STATE.with(|s| {let mut s=s.borrow_mut();let s=s.as_mut().ok_or_else(||anyhow::anyhow!("inactive recovery hash capture"))?;
        anyhow::ensure!(!s.active && !s.invalid && !s.taken && s.slots==2 && s.pending.is_none() && s.reports.len()==8,
            "recovery hash lifecycle/order/truncation mismatch");
        for slot in 0..2 {let c=&capsules[slot];let base=4*slot;
            let expected=[(Role::Secret,11,c.core.shared.to_vec(),c.core.secret.clone()),
                (Role::Confirmation,21,vec![c.core.seed.clone(),c.core.capsule[0].clone(),c.core.capsule[1].clone(),c.core.capsule[3].clone()],c.computed_confirmation.clone()),
                (Role::AmountStream,10,vec![c.core.seed.clone(),Observed::Native(Scalar::from(0))],c.amount_stream.clone()),
                (Role::BlindingStream,10,vec![c.core.seed.clone(),Observed::Native(Scalar::from(1))],c.blinding_stream.clone())];
            for (offset,(role,domain,inputs,output)) in expected.into_iter().enumerate() {let r=&s.reports[base+offset];
                anyhow::ensure!(r.slot==slot && r.role==role && r.domain==domain && r.inputs==inputs && r.output==output,
                    "recovery hash exact native role/source mismatch");}
        }
        s.taken=true;Ok(std::mem::take(&mut s.reports))})
}

#[cfg(test)]
mod tests {
    use super::*;
    fn values(width:usize)->Vec<Var<'static,Scalar>> {(0..width).map(|i|Var::native(Scalar::from(i as u64+1))).collect()}
    #[test]
    fn order_duplicate_state_and_missing_final_checkpoint_poison() {
        {let _capture=begin().unwrap();let _scope=scope();assert!(!start(21,&values(4)).active);}
        {let _capture=begin().unwrap();let _scope=scope();let call=start(11,&values(2));
            state(&call,0,false,&values(3));state(&call,0,false,&values(3));
            assert!(STATE.with(|s|s.borrow().as_ref().unwrap().invalid));}
        {let _capture=begin().unwrap();let _scope=scope();let call=start(11,&values(2));
            state(&call,0,false,&values(3));finish(call,&values(3)[1]);
            assert!(STATE.with(|s|s.borrow().as_ref().unwrap().invalid));}
    }
    #[test]
    fn exact_eight_calls_are_bounded_and_outside_calls_are_ignored() {
        let _capture=begin().unwrap();assert!(!start(21,&values(4)).active);
        for _ in 0..2 {let _scope=scope();for (domain,arity) in [(11,2),(21,4),(10,2),(10,2)] {
            let call=start(domain,&values(arity));let state_values=values(if arity==2 {3}else{6});
            state(&call,0,false,&state_values);state(&call,0,true,&state_values);finish(call,&state_values[1]);
        }assert!(!start(20,&values(7)).active);}
        assert!(STATE.with(|s| {let s=s.borrow();let s=s.as_ref().unwrap();!s.invalid && s.reports.len()==8 && s.slots==2}));
        assert!(!scope().active);
    }
}
