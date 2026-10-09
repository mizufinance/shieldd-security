//! Distinct balance VALUE_BLINDING fixed trace. Zero/identity is legal here.
//! Reads existing references only; no Var operations or eager DAG expansion.
use super::{Point,Scalar};
use crate::scalar::inspection::Observed;
use commonware_cryptography::zk::circuit::{BoolVar,CircuitIdx,Var};
use std::{cell::RefCell,marker::PhantomData,rc::Rc};

#[derive(Clone,PartialEq,Eq)]
pub struct Window {
    pub index:usize,pub table:[[Scalar;2];4],pub points:[[Observed;2];3],
    pub bits:[CircuitIdx;2],pub arithmetic:[Observed;4],pub quotient:[Observed;6],
}
#[derive(Clone,PartialEq,Eq)]
pub struct Report {
    pub window_start:usize,pub window_count:usize,pub base:[Scalar;2],
    pub blinding:Observed,pub bits:Vec<CircuitIdx>,pub output:[Observed;2],pub windows:Vec<Window>,
}
impl Report {
    pub fn page(&self,start:usize,count:usize)->anyhow::Result<Self> {
        anyhow::ensure!(self.window_start==0 && self.window_count==126 && self.windows.len()==126 &&
            start<126 && (1..=16).contains(&count) && start+count<=126,"balance blinding fixed page bounds");
        let mut page=self.clone();page.window_start=start;page.window_count=count;
        page.windows=self.windows[start..start+count].to_vec();Ok(page)
    }
    pub fn selected(&self)->Vec<CircuitIdx> {
        let mut values=self.bits.clone();
        let mut add=|value:&Observed|if let Observed::Source(index)=value {values.push(*index)};
        add(&self.blinding);for value in &self.output {add(value)}
        for window in &self.windows {
            for value in window.points.iter().flatten().chain(&window.arithmetic).chain(&window.quotient) {add(value)}
        }
        values.sort();values.dedup();values
    }
}
struct State {
    active:bool,invalid:bool,taken:bool,calls:usize,next:usize,current:Option<usize>,
    arithmetic:Option<[Observed;4]>,quotient:Option<[Observed;6]>,
    report:Option<Report>,started:bool,finished:bool,
}
impl State {fn new()->Self {Self {active:false,invalid:false,taken:false,calls:0,next:0,current:None,
    arithmetic:None,quotient:None,report:None,started:false,finished:false}}}
thread_local! {static STATE:RefCell<Option<State>>=const {RefCell::new(None)};}
pub struct Capture {_thread:PhantomData<Rc<()>>}
impl Drop for Capture {fn drop(&mut self) {STATE.with(|state|*state.borrow_mut()=None)}}
pub fn begin()->anyhow::Result<Capture> {
    STATE.with(|state|{let mut state=state.borrow_mut();anyhow::ensure!(state.is_none(),"nested balance blinding capture");
        *state=Some(State::new());Ok(Capture {_thread:PhantomData})})
}
fn observed(value:&Var<'_,Scalar>)->Observed {
    match value.inspect_circuit_idx() {Some(index)=>Observed::Source(index),
        None=>Observed::Native(value.inspect_native().expect("invalid balance blinding Var").clone())}
}
fn point(value:&Point<Var<'_,Scalar>>)->[Observed;2] {[observed(&value.x),observed(&value.y)]}
fn native(value:&Point<Scalar>)->[Scalar;2] {[value.x.clone(),value.y.clone()]}
pub struct Scope {active:bool,_thread:PhantomData<Rc<()>>}
impl Drop for Scope {fn drop(&mut self) {if self.active {STATE.with(|state|if let Some(state)=state.borrow_mut().as_mut() {
    state.invalid|=!state.active || !state.finished || state.next!=126 || state.current.is_some();state.active=false;
})}}}
pub(crate) fn scope<'ctx>(base:&Point<Scalar>,blinding:&Var<'ctx,Scalar>,bits:&[BoolVar<'ctx,Scalar>])->Option<Scope> {
    STATE.with(|state|{let mut state=state.borrow_mut();let state=state.as_mut()?;state.calls+=1;
        let handles:Option<Vec<_>>=bits.iter().map(|bit|bit.var().inspect_circuit_idx()).collect();
        state.invalid|=state.active || state.taken || state.calls!=1 || state.report.is_some() || bits.len()!=252 || handles.is_none();
        let handles=handles.unwrap_or_default();let mut distinct=handles.clone();distinct.sort();distinct.dedup();
        state.invalid|=distinct.len()!=252 || handles.iter().any(|index|!matches!(index,CircuitIdx::Witness(_)));
        state.report=Some(Report {window_start:0,window_count:126,base:native(base),blinding:observed(blinding),
            bits:handles,output:[Observed::Native(Scalar::from(0u64)),Observed::Native(Scalar::from(1u64))],windows:Vec::new()});
        state.active=true;Some(Scope {active:true,_thread:PhantomData})})
}
pub(super) fn begin_loop<'ctx>(base:&Point<Scalar>,bits:&[BoolVar<'ctx,Scalar>]) {
    STATE.with(|state|{let mut state=state.borrow_mut();let Some(state)=state.as_mut().filter(|s|s.active) else {return};
        let Some(report)=state.report.as_ref() else {state.invalid=true;return};
        let handles:Option<Vec<_>>=bits.iter().map(|bit|bit.var().inspect_circuit_idx()).collect();
        state.invalid|=state.started || state.finished || state.next!=0 || native(base)!=report.base || handles.as_ref()!=Some(&report.bits);
        state.started=true;
    })
}
fn advance(state:&mut State,index:usize) {
    state.invalid|=!state.started || state.finished || state.current.is_some() || index!=state.next || index>=126 || state.arithmetic.is_some() || state.quotient.is_some();
    state.current=Some(index);
}
pub(super) fn begin_window(index:usize) {STATE.with(|state|if let Some(state)=state.borrow_mut().as_mut().filter(|s|s.active) {advance(state,index)})}
pub(super) fn arithmetic(values:[&Var<'_,Scalar>;4]) {STATE.with(|state|if let Some(state)=state.borrow_mut().as_mut().filter(|s|s.active) {
    state.invalid|=state.current.is_none() || state.arithmetic.is_some();state.arithmetic=Some(values.map(observed));
})}
pub(super) fn quotient(values:[&Var<'_,Scalar>;6]) {STATE.with(|state|if let Some(state)=state.borrow_mut().as_mut().filter(|s|s.active) {
    state.invalid|=state.current.is_none() || state.quotient.is_some();state.quotient=Some(values.map(observed));
})}
pub(super) fn finish_window<'ctx>(base:&Point<Scalar>,twice:&Point<Scalar>,triple:&Point<Scalar>,next_base:&Point<Scalar>,
    incoming:&Point<Var<'ctx,Scalar>>,selected:&Point<Var<'ctx,Scalar>>,outgoing:&Point<Var<'ctx,Scalar>>) {
    STATE.with(|state|{let mut state=state.borrow_mut();let Some(state)=state.as_mut().filter(|s|s.active) else {return};
        let Some(index)=state.current.take() else {state.invalid=true;return};
        let (Some(arithmetic),Some(quotient))=(state.arithmetic.take(),state.quotient.take()) else {state.invalid=true;return};
        let Some(report)=state.report.as_mut() else {state.invalid=true;return};
        if state.invalid || index>=126 || report.windows.len()!=index {state.invalid=true;return}
        let points=[point(incoming),point(selected),point(outgoing)];
        state.invalid|=quotient[4..]!=points[2] || report.windows.last().is_some_and(|last|
            last.points[2]!=points[0] || last.table[3]!=native(base));
        if index==0 {state.invalid|=points[0]!=[Observed::Native(Scalar::from(0u64)),Observed::Native(Scalar::from(1u64))];}
        report.windows.push(Window {index,table:[native(base),native(twice),native(triple),native(next_base)],
            points,bits:[report.bits[2*index],report.bits[2*index+1]],arithmetic,quotient});state.next+=1;
    })
}
pub(super) fn finish_loop(output:&Point<Var<'_,Scalar>>) {STATE.with(|state|if let Some(state)=state.borrow_mut().as_mut().filter(|s|s.active) {
    state.invalid|=state.finished || state.next!=126 || state.current.is_some() || state.arithmetic.is_some() || state.quotient.is_some();
    if let Some(report)=state.report.as_mut() {state.invalid|=report.windows.last().is_none_or(|last|last.points[2]!=point(output));report.output=point(output)}
    else {state.invalid=true} state.finished=true;
})}
pub fn take()->anyhow::Result<Report> {STATE.with(|state|{let mut state=state.borrow_mut();let state=state.as_mut().ok_or_else(||anyhow::anyhow!("inactive balance blinding capture"))?;
    anyhow::ensure!(!state.active && !state.invalid && !state.taken && state.calls==1 && state.started && state.finished && state.next==126 &&
        state.current.is_none() && state.arithmetic.is_none() && state.quotient.is_none(),"balance blinding fixed lifecycle/order/truncation mismatch");
    let report=state.report.as_ref().ok_or_else(||anyhow::anyhow!("balance blinding missing report"))?;
    anyhow::ensure!(report.windows.len()==126 && report.bits.len()==252,"balance blinding incomplete trace");state.taken=true;Ok(report.clone())
})}

#[cfg(test)]
mod tests {
    use super::*;
    #[test] fn lifecycle_refuses_nested_inactive_truncated_and_duplicate_take() {
        assert!(take().is_err());let capture=begin().unwrap();assert!(begin().is_err());assert!(take().is_err());drop(capture);
        let capture=begin().unwrap();STATE.with(|state|state.borrow_mut().as_mut().unwrap().taken=true);assert!(take().is_err());drop(capture);
    }
    #[test] fn window_order_refuses_skips_and_duplicate_materialization() {
        let mut state=State::new();state.started=true;advance(&mut state,1);assert!(state.invalid);
        let mut state=State::new();state.started=true;advance(&mut state,0);advance(&mut state,0);assert!(state.invalid);
        let mut state=State::new();state.started=true;state.finished=true;advance(&mut state,126);assert!(state.invalid);
    }
    #[test] fn zero_scalar_identity_is_not_a_nonidentity_requirement() {
        let report=Report {window_start:0,window_count:126,base:[Scalar::from(1u64),Scalar::from(2u64)],
            blinding:Observed::Native(Scalar::from(0u64)),bits:Vec::new(),
            output:[Observed::Native(Scalar::from(0u64)),Observed::Native(Scalar::from(1u64))],windows:Vec::new()};
        assert_eq!(report.selected().len(),0);assert!(report.page(0,16).is_err());
    }
    #[test] fn actual_value_blinding_zero_trace_is_complete_and_satisfied() {
        use commonware_cryptography::zk::circuit::build_with_values;
        let capture=begin().unwrap();
        let generator=super::super::native_point(&shieldd_sdk_crypto::generators::VALUE_BLINDING);
        let (c,_)=build_with_values(|ctx| {
            let blinding=Var::witness(ctx,|_|Scalar::from(0u64));
            let bits=crate::scalar::canonical_bits(ctx,&blinding);
            let selected=scope(&generator,&blinding,&bits);
            let output=generator.multiply_fixed(&bits);drop(selected);
            output.assert_equal(&Point {x:Var::native(Scalar::from(0u64)),y:Var::native(Scalar::from(1u64))});
            vec![output.x,output.y]
        });
        assert!(c.is_satisfied());let report=take().unwrap();assert_eq!(report.windows.len(),126);
        assert!(report.base==native(&generator));
        assert_eq!((0..126).step_by(16).map(|start|report.page(start,std::cmp::min(16,126-start)).unwrap().windows.len()).sum::<usize>(),126);
        assert!(take().is_err());drop(capture);assert!(begin().is_ok());
    }
}
