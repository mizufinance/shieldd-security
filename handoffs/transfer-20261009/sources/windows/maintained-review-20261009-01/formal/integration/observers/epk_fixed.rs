//! Fresh-only compact fixed EPK roles. No circuit/Var operations or DAG expansion.
use super::{Point,Scalar};
use crate::scalar::inspection::Observed;
use commonware_cryptography::zk::circuit::{BoolVar,CircuitIdx,Var};
use std::{cell::RefCell,marker::PhantomData,rc::Rc};

#[derive(Clone,Copy,PartialEq,Eq)]
pub enum Lane { Recovery, Encryption }
impl Lane { pub fn slots(self)->usize { match self {Self::Recovery=>2,Self::Encryption=>4} } }
#[derive(Clone,PartialEq,Eq)]
pub struct Window {
    pub index:usize,
    /// Existing native base,twice,triple,nextBase; not circuit witnesses.
    pub table:[[Scalar;2];4],
    /// Incoming,selected,outgoing source roles.
    pub points:[[Observed;2];3],
    pub bits:[CircuitIdx;2],
    pub arithmetic:[Observed;4],
    pub quotient:[Observed;6],
}
#[derive(Clone,PartialEq,Eq)]
pub struct Report {
    pub lane:Lane,pub slot:usize,pub window_start:usize,pub window_count:usize,
    pub base:[Scalar;2],pub randomizer:Observed,pub bits:Vec<CircuitIdx>,
    pub published:[Observed;2],pub output:[Observed;2],pub inverse:Option<Observed>,pub windows:Vec<Window>,
}
impl Report {
    pub fn page(&self,start:usize,count:usize)->anyhow::Result<Self> {
        anyhow::ensure!(self.window_start==0 && self.window_count==126 && self.windows.len()==126 &&
            start<126 && (1..=16).contains(&count) && start+count<=126,"EPK fixed complete report/page bounds");
        let mut report=self.clone();report.window_start=start;report.window_count=count;
        report.windows=self.windows[start..start+count].to_vec();Ok(report)
    }
    pub fn selected(&self)->Vec<CircuitIdx> {
        let mut selected=self.bits.clone();
        let mut add=|value:&Observed|if let Observed::Source(index)=value {selected.push(*index)};
        add(&self.randomizer);if let Some(inverse)=&self.inverse {add(inverse)} for value in self.published.iter().chain(&self.output) {add(value)}
        for window in &self.windows {
            for value in window.points.iter().flatten().chain(&window.arithmetic).chain(&window.quotient) {add(value)}
        }
        selected.sort();selected.dedup();selected
    }
}
struct State {
    lane:Lane,slot:usize,calls:usize,active:bool,invalid:bool,taken:bool,
    next:usize,current:Option<usize>,arithmetic:Option<[Observed;4]>,quotient:Option<[Observed;6]>,
    report:Option<Report>,started:bool,finished:bool,
}
thread_local! {static STATE:RefCell<Option<State>>=const {RefCell::new(None)};}
struct AllState {reports:Vec<Report>,invalid:bool,taken:bool}
thread_local! {static ALL_STATE:RefCell<Option<AllState>>=const {RefCell::new(None)};}
pub fn scope_id(ordinal:usize)->Option<(Lane,usize)> {
    match ordinal {0..=1=>Some((Lane::Recovery,ordinal)),2..=5=>Some((Lane::Encryption,ordinal-2)),_=>None}
}
pub struct AllCapture {_thread:PhantomData<Rc<()>>}
impl Drop for AllCapture {fn drop(&mut self) {
    STATE.with(|s|*s.borrow_mut()=None);ALL_STATE.with(|s|*s.borrow_mut()=None);
}}
pub fn begin_all()->anyhow::Result<AllCapture> {
    anyhow::ensure!(STATE.with(|s|s.borrow().is_none()),"nested EPK fixed selected/all capture");
    ALL_STATE.with(|s|{let mut s=s.borrow_mut();anyhow::ensure!(s.is_none(),"nested EPK fixed all capture");
        *s=Some(AllState {reports:Vec::new(),invalid:false,taken:false});Ok(AllCapture {_thread:PhantomData})})
}
pub struct Capture {_thread:PhantomData<Rc<()>>}
impl Drop for Capture {fn drop(&mut self) {STATE.with(|s|*s.borrow_mut()=None)}}
pub fn begin(lane:Lane,slot:usize)->anyhow::Result<Capture> {
    anyhow::ensure!(slot<lane.slots(),"EPK fixed slot out of bounds");
    anyhow::ensure!(ALL_STATE.with(|s|s.borrow().is_none()),"nested EPK fixed all/selected capture");
    STATE.with(|s|{let mut s=s.borrow_mut();anyhow::ensure!(s.is_none(),"nested EPK fixed capture");
        *s=Some(State {lane,slot,calls:0,active:false,invalid:false,taken:false,next:0,current:None,
            arithmetic:None,quotient:None,report:None,started:false,finished:false});Ok(Capture {_thread:PhantomData})})
}
fn observed(value:&Var<'_,Scalar>)->Observed {
    match value.inspect_circuit_idx() {Some(index)=>Observed::Source(index),
        None=>Observed::Native(value.inspect_native().expect("invalid EPK fixed Var").clone())}
}
fn point(value:&Point<Var<'_,Scalar>>)->[Observed;2] {[observed(&value.x),observed(&value.y)]}
fn native(value:&Point<Scalar>)->[Scalar;2] {[value.x.clone(),value.y.clone()]}
pub struct Scope {active:bool,_thread:PhantomData<Rc<()>>}
impl Drop for Scope {fn drop(&mut self) {if self.active {STATE.with(|s|if let Some(s)=s.borrow_mut().as_mut() {
    s.invalid|=!s.active || !s.finished || s.next!=126 || s.current.is_some();s.active=false;
});ALL_STATE.with(|all|if let Some(all)=all.borrow_mut().as_mut() {
    let state=STATE.with(|s|s.borrow_mut().take());
    if let Some(s)=state {
        let valid=!s.invalid && s.started && s.finished && s.next==126 && s.arithmetic.is_none() && s.quotient.is_none() &&
            s.report.as_ref().is_some_and(|r|r.windows.len()==126 && r.bits.len()==252 && r.inverse.is_some() &&
                scope_id(all.reports.len())==Some((r.lane,r.slot)));
        all.invalid|=!valid;if valid {all.reports.push(s.report.unwrap());}
    } else {all.invalid=true}
});}}}
pub(crate) fn scope<'ctx>(lane:Lane,base:&Point<Scalar>,randomizer:&Var<'ctx,Scalar>,
    bits:&[BoolVar<'ctx,Scalar>],published:&Point<Var<'ctx,Scalar>>)->Option<Scope> {
    let all_slot=ALL_STATE.with(|all|{let mut all=all.borrow_mut();let all=all.as_mut()?;
        let expected=scope_id(all.reports.len());
        all.invalid|=all.taken || expected.is_none_or(|(expected,_)|expected!=lane) || STATE.with(|s|s.borrow().is_some());
        if all.invalid {return None} expected.map(|(_,slot)|slot)
    });
    if let Some(slot)=all_slot {STATE.with(|s|*s.borrow_mut()=Some(State {lane,slot,calls:slot,active:false,
        invalid:false,taken:false,next:0,current:None,arithmetic:None,quotient:None,report:None,started:false,finished:false}));}
    STATE.with(|s|{let mut s=s.borrow_mut();let state=s.as_mut()?;if lane!=state.lane {return None}
        let index=state.calls;state.calls+=1;
        state.invalid|=state.active || state.taken || index>=lane.slots();
        if index!=state.slot {return None}
        let handles:Option<Vec<_>>=bits.iter().map(|b|b.var().inspect_circuit_idx()).collect();
        state.invalid|=state.report.is_some() || bits.len()!=252 || handles.is_none();
        let handles=handles.unwrap_or_default();let mut distinct=handles.clone();distinct.sort();distinct.dedup();
        state.invalid|=distinct.len()!=252 || handles.iter().any(|h|!matches!(h,CircuitIdx::Witness(_)));
        state.report=Some(Report {lane,slot:index,window_start:0,window_count:126,base:native(base),
            randomizer:observed(randomizer),bits:handles,published:point(published),output:point(published),inverse:None,windows:Vec::new()});
        state.active=true;Some(Scope {active:true,_thread:PhantomData})})
}
pub(super) fn begin_loop<'ctx>(base:&Point<Scalar>,bits:&[BoolVar<'ctx,Scalar>]) {
    STATE.with(|s|{let mut s=s.borrow_mut();let Some(s)=s.as_mut().filter(|s|s.active) else {return};
        let Some(report)=s.report.as_ref() else {s.invalid=true;return};
        let handles:Option<Vec<_>>=bits.iter().map(|b|b.var().inspect_circuit_idx()).collect();
        s.invalid|=s.started || s.finished || s.next!=0 || native(base)!=report.base || handles.as_ref()!=Some(&report.bits);s.started=true;})
}
fn advance(s:&mut State,index:usize) {
    s.invalid|=!s.started || s.current.is_some() || index!=s.next || index>=126 || s.arithmetic.is_some() || s.quotient.is_some();
    s.current=Some(index);
}
pub(super) fn begin_window(index:usize) {STATE.with(|s|if let Some(s)=s.borrow_mut().as_mut().filter(|s|s.active) {advance(s,index)})}
pub(super) fn arithmetic(values:[&Var<'_,Scalar>;4]) {STATE.with(|s|if let Some(s)=s.borrow_mut().as_mut().filter(|s|s.active) {
    s.invalid|=s.current.is_none() || s.arithmetic.is_some();s.arithmetic=Some(values.map(observed));})}
pub(super) fn quotient(values:[&Var<'_,Scalar>;6]) {STATE.with(|s|if let Some(s)=s.borrow_mut().as_mut().filter(|s|s.active) {
    s.invalid|=s.current.is_none() || s.quotient.is_some();s.quotient=Some(values.map(observed));})}
pub(super) fn finish_window<'ctx>(base:&Point<Scalar>,twice:&Point<Scalar>,triple:&Point<Scalar>,next_base:&Point<Scalar>,
    incoming:&Point<Var<'ctx,Scalar>>,selected:&Point<Var<'ctx,Scalar>>,outgoing:&Point<Var<'ctx,Scalar>>) {
    STATE.with(|s|{let mut s=s.borrow_mut();let Some(s)=s.as_mut().filter(|s|s.active) else {return};
        let Some(index)=s.current.take() else {s.invalid=true;return};
        let (Some(arithmetic),Some(quotient))=(s.arithmetic.take(),s.quotient.take()) else {s.invalid=true;return};
        let Some(report)=s.report.as_mut() else {s.invalid=true;return};
        if s.invalid || index>=126 || report.windows.len()!=index {s.invalid=true;return}
        let points=[point(incoming),point(selected),point(outgoing)];
        s.invalid|=quotient[4..]!=points[2] || report.windows.last().is_some_and(|last|
            last.points[2]!=points[0] || last.table[3]!=native(base));
        report.windows.push(Window {index,table:[native(base),native(twice),native(triple),native(next_base)],
            points,bits:[report.bits[2*index],report.bits[2*index+1]],arithmetic,quotient});s.next+=1;})
}
pub(super) fn finish_loop(output:&Point<Var<'_,Scalar>>) {STATE.with(|s|if let Some(s)=s.borrow_mut().as_mut().filter(|s|s.active) {
    s.invalid|=s.finished || s.next!=126 || s.current.is_some() || s.arithmetic.is_some() || s.quotient.is_some();
    if let Some(report)=s.report.as_mut() {s.invalid|=report.windows.last().is_none_or(|w|w.points[2]!=point(output));report.output=point(output)}
    else {s.invalid=true} s.finished=true;
})}
pub(crate) fn inverse(value:&Var<'_,Scalar>) {STATE.with(|s|if let Some(s)=s.borrow_mut().as_mut().filter(|s|s.active) {
    let inverse=observed(value);
    s.invalid|=!s.finished || !matches!(inverse,Observed::Source(CircuitIdx::Witness(_)));
    if let Some(report)=s.report.as_mut() {s.invalid|=report.inverse.is_some();report.inverse=Some(inverse)} else {s.invalid=true}
})}
pub fn take()->anyhow::Result<Report> {STATE.with(|s|{let mut s=s.borrow_mut();let s=s.as_mut().ok_or_else(||anyhow::anyhow!("inactive EPK fixed capture"))?;
    anyhow::ensure!(!s.active && !s.invalid && !s.taken && s.finished && s.calls==s.lane.slots() && s.next==126 &&
        s.current.is_none() && s.arithmetic.is_none() && s.quotient.is_none(),"EPK fixed lifecycle/order/truncation mismatch");
    let report=s.report.as_ref().ok_or_else(||anyhow::anyhow!("EPK fixed missing report"))?;
    anyhow::ensure!(report.windows.len()==126 && report.bits.len()==252 && report.inverse.is_some(),"EPK fixed incomplete windows/bits");
    s.taken=true;Ok(report.clone())})}
pub fn take_all()->anyhow::Result<Vec<Report>> {
    anyhow::ensure!(STATE.with(|s|s.borrow().is_none()),"EPK fixed all unfinished scope");
    ALL_STATE.with(|s|{let mut s=s.borrow_mut();let s=s.as_mut().ok_or_else(||anyhow::anyhow!("inactive EPK fixed all capture"))?;
        anyhow::ensure!(!s.invalid && !s.taken && s.reports.len()==6 && s.reports.iter().enumerate().all(|(i,r)|
            scope_id(i)==Some((r.lane,r.slot)) && r.windows.len()==126 && r.inverse.is_some()),"EPK fixed all order/truncation/lifecycle");
        s.taken=true;Ok(s.reports.clone())})
}

#[cfg(test)]
mod tests {
    use super::*;
    use commonware_math::algebra::Field;
    #[test] fn nested_capture_and_reset() {let capture=begin(Lane::Recovery,0).unwrap();assert!(begin(Lane::Recovery,1).is_err());
        assert!(take().is_err());drop(capture);assert!(begin(Lane::Encryption,3).is_ok());assert!(begin(Lane::Recovery,2).is_err());}
    #[test] fn exact_order_and_overflow_refusal() {let _capture=begin(Lane::Recovery,0).unwrap();STATE.with(|s|{let mut s=s.borrow_mut();
        let s=s.as_mut().unwrap();advance(s,1);assert!(s.invalid);s.invalid=false;s.current=None;s.next=126;advance(s,126);assert!(s.invalid);});}
    #[test] fn complete_page_partition() {let starts:Vec<_>=(0..126).step_by(16).collect();assert_eq!(starts,[0,16,32,48,64,80,96,112]);
        let sizes:Vec<_>=starts.iter().map(|s|std::cmp::min(16,126-s)).collect();assert_eq!(sizes,[16,16,16,16,16,16,16,14]);
        assert_eq!(sizes.iter().sum::<usize>(),126);}
    #[test] fn all_capture_excludes_selected_and_refuses_truncation() {
        let capture=begin_all().unwrap();assert!(begin_all().is_err());assert!(begin(Lane::Recovery,0).is_err());
        assert!(take_all().is_err());drop(capture);let selected=begin(Lane::Encryption,0).unwrap();assert!(begin_all().is_err());drop(selected);
        assert!(begin_all().is_ok());
    }
    #[test] fn all_six_source_order_and_partition() {
        assert!(scope_id(0)==Some((Lane::Recovery,0)));assert!(scope_id(1)==Some((Lane::Recovery,1)));
        for i in 2..6 {assert!(scope_id(i)==Some((Lane::Encryption,i-2)));}assert!(scope_id(6).is_none());
        assert_eq!((0..6).flat_map(|_|(0..126).step_by(16)).count(),48);
    }
    #[test] fn all_real_fixed_scopes_complete_once_and_reset() {
        use commonware_cryptography::zk::circuit;
        let capture=begin_all().unwrap();
        let _built=circuit::build(|ctx|{
            let mut outputs=Vec::new();
            for ordinal in 0..6 {
                let (lane,_)=scope_id(ordinal).unwrap();let generator=super::super::generator();
                let randomizer=Var::witness(ctx,|_|Scalar::from(1u64));
                let bits=crate::scalar::canonical_bits(ctx,&randomizer);
                let published=Point {x:Var::witness(ctx,|_|generator.x.clone()),y:Var::witness(ctx,|_|generator.y.clone())};
                let captured=scope(lane,&generator,&randomizer,&bits,&published);
                generator.multiply_fixed(&bits).assert_equal(&published);
                let witness=published.x.inv();inverse(&witness);drop(captured);outputs.push(published.x);
            }outputs
        });
        let reports=take_all().unwrap();assert_eq!(reports.len(),6);
        assert!(reports.iter().all(|report|report.windows.len()==126 && report.inverse.is_some()));
        assert!(take_all().is_err());drop(capture);assert!(begin(Lane::Recovery,0).is_ok());
    }
    #[test] fn all_actual_wrong_first_lane_refused() {
        let _capture=begin_all().unwrap();let generator=super::super::generator();let randomizer=Var::native(Scalar::from(1u64));
        let published=Point {x:Var::native(generator.x.clone()),y:Var::native(generator.y.clone())};
        assert!(scope(Lane::Encryption,&generator,&randomizer,&[],&published).is_none());
        assert!(take_all().is_err());ALL_STATE.with(|s|assert!(s.borrow().as_ref().unwrap().invalid));
    }
}
