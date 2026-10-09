//! Future-stage output NOTE15/8 and recovery20/7 checkpoints, four calls only.
use crate::{note::output_inspection::Report as Outputs, scalar::inspection::Observed};
use commonware_cryptography::{bls12381::primitives::group::Scalar, zk::circuit::Var};
use std::{cell::RefCell, marker::PhantomData, rc::Rc};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Role { Note, Recovery }
#[derive(Clone, PartialEq, Eq)]
pub struct Block { pub before: Vec<Observed>, pub after: Vec<Observed> }
#[derive(Clone, PartialEq, Eq)]
pub struct Report {
    pub slot: usize, pub role: Role, pub block: usize, pub domain: u8,
    pub inputs: Vec<Observed>, pub output: Observed, pub blocks: Vec<Block>,
}
struct Pending {
    role: Role, domain: u8, inputs: Vec<Observed>,
    before: Option<Vec<Observed>>, blocks: Vec<Block>,
}
#[derive(Default)]
struct State {
    outputs: usize, active: bool, calls: usize, invalid: bool, taken: bool,
    pending: Option<Pending>, reports: Vec<Report>,
}
thread_local! { static STATE: RefCell<Option<State>> = const { RefCell::new(None) }; }
pub struct Capture { _thread: PhantomData<Rc<()>> }
impl Drop for Capture { fn drop(&mut self) { STATE.with(|s| *s.borrow_mut()=None); } }
pub fn begin() -> anyhow::Result<Capture> {
    STATE.with(|s| {
        let mut s=s.borrow_mut();anyhow::ensure!(s.is_none(),"nested output hash capture");
        *s=Some(State::default());Ok(Capture { _thread:PhantomData })
    })
}
pub struct OutputScope { active: bool, _thread: PhantomData<Rc<()>> }
pub fn output() -> OutputScope {
    let active=STATE.with(|s| {
        let mut s=s.borrow_mut();let Some(s)=s.as_mut() else { return false; };
        if s.active || s.outputs>=2 || s.taken { s.invalid=true;return false; }
        s.active=true;s.calls=0;true
    });
    OutputScope { active,_thread:PhantomData }
}
impl Drop for OutputScope {
    fn drop(&mut self) {
        if !self.active { return; }
        STATE.with(|s| {
            let mut s=s.borrow_mut();let Some(s)=s.as_mut() else { return; };
            if !s.active || s.calls!=2 || s.pending.is_some() || s.reports.len()!=2*(s.outputs+1) {
                s.invalid=true;
            }
            s.active=false;s.outputs+=1;
        });
    }
}
pub struct Call { active: bool, _thread: PhantomData<Rc<()>> }
fn observed(value: &Var<'_,Scalar>) -> Observed {
    match value.inspect_circuit_idx() {
        Some(index)=>Observed::Source(index),
        None=>Observed::Native(value.inspect_native().expect("invalid output hash var").clone()),
    }
}
pub(crate) fn start(domain:u8,inputs:&[Var<'_,Scalar>]) -> Call {
    let active=STATE.with(|s| {
        let mut s=s.borrow_mut();let Some(s)=s.as_mut() else { return false; };
        // Other encryption calls remain ordinary source operations in this scope.
        if !s.active || !matches!(domain,15|20) { return false; }
        let wanted=match s.calls { 0=>(Role::Note,15,8),1=>(Role::Recovery,20,7),
            _=>{s.invalid=true;return false;} };
        if s.taken || s.pending.is_some() || domain!=wanted.1 || inputs.len()!=wanted.2 || s.reports.len()>=4 {
            s.invalid=true;return false;
        }
        s.calls+=1;
        s.pending=Some(Pending { role:wanted.0,domain,inputs:inputs.iter().map(observed).collect(),
            before:None,blocks:Vec::new() });true
    });
    Call { active,_thread:PhantomData }
}
pub(crate) fn state(call:&Call,index:usize,after:bool,values:&[Var<'_,Scalar>]) {
    if !call.active { return; }
    STATE.with(|s| {
        let mut s=s.borrow_mut();let Some(s)=s.as_mut() else { return; };
        let Some(p)=s.pending.as_mut() else { s.invalid=true;return; };
        if values.len()!=6 || index!=p.blocks.len() || index>=2 { s.invalid=true;return; }
        if after {
            let Some(before)=p.before.take() else { s.invalid=true;return; };
            p.blocks.push(Block { before,after:values.iter().map(observed).collect() });
        } else if p.before.is_some() { s.invalid=true; }
        else { p.before=Some(values.iter().map(observed).collect()); }
    });
}
pub(crate) fn finish(call:Call,output:&Var<'_,Scalar>) {
    if !call.active { return; }
    STATE.with(|s| {
        let mut s=s.borrow_mut();let Some(s)=s.as_mut() else { return; };
        let Some(p)=s.pending.take() else { s.invalid=true;return; };
        let output=observed(output);
        if p.before.is_some() || p.blocks.len()!=2 || p.blocks.last().map(|b| &b.after[1])!=Some(&output) {
            s.invalid=true;return;
        }
        s.reports.push(Report { slot:s.outputs,role:p.role,block:0,domain:p.domain,
            inputs:p.inputs,output,blocks:p.blocks });
    });
}
pub fn take(outputs:&Outputs) -> anyhow::Result<Vec<Report>> {
    STATE.with(|s| {
        let mut s=s.borrow_mut();let s=s.as_mut().ok_or_else(|| anyhow::anyhow!("inactive output hash capture"))?;
        anyhow::ensure!(!s.invalid && !s.taken && !s.active && s.outputs==2 && s.pending.is_none() && s.reports.len()==4,
            "incomplete four output hash calls/scopes");
        for slot in 0..2 {
            let note=&s.reports[2*slot];let recovery=&s.reports[2*slot+1];let output=&outputs.outputs[slot];
            anyhow::ensure!(note.slot==slot && note.role==Role::Note && note.inputs.as_slice()==output.note &&
                note.output==output.computed_commitment,"output NOTE source fields/output changed");
            anyhow::ensure!(recovery.slot==slot && recovery.role==Role::Recovery && recovery.inputs.as_slice()==output.capsule,
                "output recovery commitment source fields changed");
            // The recovery hash output is a computed source node. Its equality
            // to the supplied capsule commitment is a mandatory actual row join.
        }
        s.taken=true;Ok(std::mem::take(&mut s.reports))
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    fn values(count:usize) -> Vec<Var<'static,Scalar>> {
        (0..count).map(|i|Var::native(Scalar::from(i as u64+1))).collect()
    }
    fn complete_call(domain:u8,arity:usize) {
        let call=start(domain,&values(arity));assert!(call.active);let lanes=values(6);
        for block in 0..2 { state(&call,block,false,&lanes);state(&call,block,true,&lanes); }
        finish(call,&lanes[1]);
    }
    fn outputs() -> Outputs {
        use crate::note::output_inspection::Output;
        let output=|receiver| Output { receiver,note:values(8).iter().map(observed).collect::<Vec<_>>().try_into().ok().expect("eight fixture note fields"),
            amount_bits:Vec::new(),receiver_inverse:None,computed_commitment:observed(&values(6)[1]),
            commitment:Observed::Native(Scalar::from(0)),capsule:values(7).iter().map(observed).collect::<Vec<_>>().try_into().ok().expect("seven fixture capsule fields"),
            capsule_commitment:Observed::Native(Scalar::from(0)),payload_key:std::array::from_fn(|_|Observed::Native(Scalar::from(0))) };
        Outputs { outputs:[output(true),output(false)] }
    }
    #[test]
    fn two_scopes_four_calls_and_repeat_take() {
        let capture=begin().unwrap();assert!(begin().is_err());assert!(take(&outputs()).is_err());
        for _ in 0..2 { let _scope=output();complete_call(15,8);complete_call(20,7); }
        assert_eq!(take(&outputs()).unwrap().len(),4);assert!(take(&outputs()).is_err());
        drop(capture);assert!(take(&outputs()).is_err());
    }
    #[test]
    fn wrong_order_truncated_blocks_and_source_links_refuse() {
        { let _capture=begin().unwrap();let _scope=output();assert!(!start(20,&values(7)).active); }
        { let _capture=begin().unwrap();{ let _scope=output();let call=start(15,&values(8));
            state(&call,0,false,&values(6));finish(call,&values(6)[1]); }assert!(take(&outputs()).is_err()); }
        { let _capture=begin().unwrap();for _ in 0..2 { let _scope=output();complete_call(15,8);complete_call(20,7); }
            let mut roles=outputs();roles.outputs[1].capsule[0]=Observed::Native(Scalar::from(99));assert!(take(&roles).is_err()); }
    }
}
