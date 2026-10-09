//! Bounded existing balance129 source handles; no circuit operations or cone walk.
use super::{Point, Scalar};
use crate::scalar::inspection::Observed;
use commonware_cryptography::zk::circuit::{BoolVar, CircuitIdx, Var};
use commonware_math::algebra::Additive;
use std::{cell::RefCell, marker::PhantomData, rc::Rc};

#[derive(Clone, PartialEq, Eq)]
pub struct Window {
    pub index: usize,
    /// Incoming, optimized double, optimized double, selected, outgoing.
    pub points: [[Observed; 2]; 5],
    /// First reversed window is exactly [bit128, native false].
    pub bits: [Observed; 2],
    pub quotients: [[Observed; 6]; 3],
}
#[derive(Clone, PartialEq, Eq)]
pub struct Report {
    pub window_start: usize,
    pub window_count: usize,
    pub negative: Observed,
    pub magnitude: Observed,
    pub bits: Vec<CircuitIdx>,
    pub base: [Observed; 2],
    pub twice: [Observed; 2],
    pub triple: [Observed; 2],
    pub precompute_quotients: [[Observed; 6]; 2],
    pub windows: Vec<Window>,
    pub output: [Observed; 2],
}
impl Report {
    pub fn page(&self, start: usize, count: usize) -> anyhow::Result<Self> {
        anyhow::ensure!(self.window_start == 0 && self.window_count == 65 && self.windows.len() == 65 &&
            (1..=16).contains(&count) && start < 65 && start + count <= 65,
            "balance variable complete report/page bounds");
        let mut page = self.clone();
        page.window_start = start; page.window_count = count;
        page.windows = self.windows[start..start+count].to_vec();
        Ok(page)
    }
    pub fn selected(&self) -> Vec<CircuitIdx> {
        let mut values = vec![&self.negative, &self.magnitude];
        for point in [&self.base, &self.twice, &self.triple, &self.output] { values.extend(point); }
        for quotient in &self.precompute_quotients { values.extend(quotient); }
        for window in &self.windows {
            for point in &window.points { values.extend(point); }
            values.extend(&window.bits);
            for quotient in &window.quotients { values.extend(quotient); }
        }
        let mut selected: Vec<_> = values.into_iter().filter_map(|value| match value {
            Observed::Source(index) => Some(*index), Observed::Native(_) => None,
        }).collect();
        selected.extend(&self.bits); selected.sort(); selected.dedup(); selected
    }
}
struct State {
    start: usize, count: usize, active: bool, calls: usize, invalid: bool, taken: bool,
    next_window: usize, current_window: Option<usize>, quotient_count: usize,
    window_quotients: Vec<[Observed; 6]>, precompute: Vec<[Observed; 6]>,
    report: Option<Report>,
    scope_values: Option<([Observed; 2], Observed, Observed, Vec<CircuitIdx>)>,
}
thread_local! { static STATE: RefCell<Option<State>> = const { RefCell::new(None) }; }
pub struct Capture { _thread: PhantomData<Rc<()>> }
impl Drop for Capture { fn drop(&mut self) { STATE.with(|s| *s.borrow_mut() = None); } }
pub fn begin(start: usize, count: usize) -> anyhow::Result<Capture> {
    anyhow::ensure!((1..=16).contains(&count) && start < 65 && start + count <= 65,
        "balance variable chunk outside65/16 bounds");
    STATE.with(|state| {
        let mut state = state.borrow_mut(); anyhow::ensure!(state.is_none(), "nested balance variable capture");
        *state = Some(State { start, count, active: false, calls: 0, invalid: false, taken: false,
            next_window: 0, current_window: None, quotient_count: 0, window_quotients: Vec::new(),
            precompute: Vec::new(), report: None, scope_values: None });
        Ok(Capture { _thread: PhantomData })
    })
}
/// Retain only compact existing handles for exactly65 windows. LC/cone pages
/// are still at most16 windows and are serialized/discarded during lowering.
pub fn begin_paged() -> anyhow::Result<Capture> {
    STATE.with(|state| {
        let mut state = state.borrow_mut(); anyhow::ensure!(state.is_none(), "nested balance variable capture");
        *state = Some(State { start: 0, count: 65, active: false, calls: 0, invalid: false, taken: false,
            next_window: 0, current_window: None, quotient_count: 0, window_quotients: Vec::new(),
            precompute: Vec::new(), report: None, scope_values: None });
        Ok(Capture { _thread: PhantomData })
    })
}
fn observed(value: &Var<'_, Scalar>) -> Observed {
    match value.inspect_circuit_idx() {
        Some(index) => Observed::Source(index),
        None => Observed::Native(value.inspect_native().expect("invalid balance variable Var").clone()),
    }
}
fn point(value: &Point<Var<'_, Scalar>>) -> [Observed; 2] { [observed(&value.x), observed(&value.y)] }
pub struct Scope { _thread: PhantomData<Rc<()>> }
impl Drop for Scope { fn drop(&mut self) {
    STATE.with(|s| if let Some(s) = s.borrow_mut().as_mut() { s.active = false; });
} }
pub(crate) fn scope<'ctx>(base: &Point<Var<'ctx, Scalar>>, negative: &BoolVar<'ctx, Scalar>,
    magnitude: &Var<'ctx, Scalar>, bits: &[BoolVar<'ctx, Scalar>]) -> Option<Scope> {
    STATE.with(|state| {
        let mut state = state.borrow_mut(); let state = state.as_mut()?;
        assert!(!state.active, "nested balance variable scope"); state.calls += 1;
        let handles: Option<Vec<_>> = bits.iter().map(|bit| bit.var().inspect_circuit_idx()).collect();
        state.invalid |= state.calls != 1 || state.taken || bits.len() != 129 || handles.is_none();
        state.scope_values = Some((point(base), observed(negative.var()), observed(magnitude), handles.unwrap_or_default()));
        state.active = true; Some(Scope { _thread: PhantomData })
    })
}
pub(super) fn quotient(values: [&Var<'_, Scalar>; 6]) {
    STATE.with(|state| {
        let mut state = state.borrow_mut(); let Some(state) = state.as_mut().filter(|s| s.active) else { return; };
        state.quotient_count += 1;
        if let Some(index) = state.current_window {
            if (state.start..state.start+state.count).contains(&index) {
                if state.window_quotients.len() < 3 { state.window_quotients.push(values.map(observed)); }
                else { state.invalid = true; }
            }
        } else if state.report.is_none() && state.precompute.len() < 2 {
            state.precompute.push(values.map(observed));
        } else { state.invalid = true; }
        state.invalid |= state.quotient_count > 197;
    })
}
pub(super) fn begin_loop<'ctx>(base: &Point<Var<'ctx, Scalar>>, bits: &[BoolVar<'ctx, Scalar>],
    twice: &Point<Var<'ctx, Scalar>>, triple: &Point<Var<'ctx, Scalar>>) {
    STATE.with(|state| {
        let mut state = state.borrow_mut(); let Some(state) = state.as_mut().filter(|s| s.active) else { return; };
        if state.invalid || state.report.is_some() || state.precompute.len() != 2 || state.quotient_count != 2 {
            state.invalid = true; return;
        }
        let Some((scope_base,negative,magnitude,scope_bits)) = state.scope_values.as_ref() else { state.invalid = true; return; };
        let handles: Option<Vec<_>> = bits.iter().map(|bit| bit.var().inspect_circuit_idx()).collect();
        state.invalid |= *scope_base != point(base) || handles.as_ref() != Some(scope_bits);
        let precompute_quotients = state.precompute.clone().try_into().unwrap_or_else(|_| unreachable!("checked precompute count"));
        state.report = Some(Report { window_start: state.start, window_count: state.count,
            negative: negative.clone(), magnitude: magnitude.clone(), bits: scope_bits.clone(),
            base: point(base), twice: point(twice), triple: point(triple), precompute_quotients,
            windows: Vec::new(), output: point(base) });
    })
}
pub(super) fn begin_window(index: usize) {
    STATE.with(|state| {
        let mut state = state.borrow_mut(); let Some(state) = state.as_mut().filter(|s| s.active) else { return; };
        state.invalid |= state.report.is_none() || state.current_window.is_some() || index != state.next_window || index >= 65;
        state.current_window = Some(index); state.window_quotients.clear();
    })
}
pub(super) fn finish_window<'ctx>(index: usize, pair: &[BoolVar<'ctx, Scalar>], points: [&Point<Var<'ctx, Scalar>>; 5]) {
    STATE.with(|state| {
        let mut state = state.borrow_mut(); let Some(state) = state.as_mut().filter(|s| s.active) else { return; };
        state.invalid |= state.current_window != Some(index) || state.quotient_count != 2+3*(index+1);
        state.current_window = None; state.next_window += 1;
        let expected_len = if index == 0 { 1 } else { 2 };
        if pair.len() != expected_len { state.invalid = true; return; }
        if (state.start..state.start+state.count).contains(&index) {
            if state.window_quotients.len() != 3 { state.invalid = true; return; }
            let Some(report) = state.report.as_mut() else { state.invalid = true; return; };
            if report.windows.len() >= state.count { state.invalid = true; return; }
            let low = 128-2*index;
            let high = if index == 0 { Observed::Native(Scalar::zero()) } else { Observed::Source(report.bits[low+1]) };
            let actual_low = observed(pair[0].var());
            let actual_high = pair.get(1).map(|b| observed(b.var())).unwrap_or_else(|| Observed::Native(Scalar::zero()));
            state.invalid |= actual_low != Observed::Source(report.bits[low]) || actual_high != high;
            let quotients = state.window_quotients.clone().try_into().unwrap_or_else(|_| unreachable!("checked window quotient count"));
            report.windows.push(Window { index, points: points.map(point), bits: [actual_low, actual_high], quotients });
        }
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn bounded_selection_and_lifecycle_refusal() {
        for (start,count) in [(0,0),(0,17),(65,1),(64,2),(usize::MAX,1)] {
            assert!(begin(start,count).is_err());
        }
        let capture = begin(0,16).unwrap();
        assert!(begin(0,1).is_err());
        assert!(take().is_err());
        drop(capture);
        let _ = std::panic::catch_unwind(|| {
            let _capture = begin(64,1).unwrap();
            STATE.with(|state| state.borrow_mut().as_mut().unwrap().active=true);
            let _scope = Scope { _thread: PhantomData };
            panic!("owned capture cleanup");
        });
        let _capture = begin(64,1).unwrap();
        assert!(take().is_err());
    }
    #[test]
    fn odd_pair_and_exact65_reversed_order() {
        let mut seen = Vec::new();
        for index in 0..65 {
            let low = 128-2*index;
            seen.push(low);
            if index != 0 { seen.push(low+1); }
        }
        seen.sort();
        assert_eq!(seen,(0..129).collect::<Vec<_>>());
        assert_eq!(128-2*64,0);
        assert_eq!(2+3*65,197);
    }
    #[test]
    fn paged_compact_capture_reuses_exact_lifecycle() {
        let capture=begin_paged().unwrap();
        STATE.with(|state| {
            let state=state.borrow();let state=state.as_ref().unwrap();
            assert_eq!((state.start,state.count),(0,65));
        });
        assert!(begin(0,1).is_err());assert!(begin_paged().is_err());assert!(take().is_err());
        drop(capture);
        let _capture=begin(64,1).unwrap();
        assert!(take().is_err());
    }
}
pub(super) fn finish_loop(output: &Point<Var<'_, Scalar>>) {
    STATE.with(|state| {
        let mut state = state.borrow_mut(); let Some(state) = state.as_mut().filter(|s| s.active) else { return; };
        state.invalid |= state.next_window != 65 || state.current_window.is_some() || state.quotient_count != 197;
        if let Some(report) = state.report.as_mut() { report.output = point(output); }
        else { state.invalid = true; }
    })
}
pub fn take() -> anyhow::Result<Report> {
    STATE.with(|state| {
        let mut state = state.borrow_mut(); let state = state.as_mut().ok_or_else(|| anyhow::anyhow!("absent balance variable capture"))?;
        anyhow::ensure!(!state.active && !state.invalid && !state.taken && state.calls == 1 && state.next_window == 65 &&
            state.quotient_count == 197, "balance variable lifecycle/count/overflow mismatch");
        let report = state.report.as_ref().ok_or_else(|| anyhow::anyhow!("absent balance variable report"))?;
        anyhow::ensure!(report.bits.len() == 129 && report.windows.len() == state.count && report.selected().len() <= 4096,
            "balance variable report bound mismatch");
        anyhow::ensure!(report.precompute_quotients[0][4..] == report.twice && report.precompute_quotients[1][4..] == report.triple,
            "balance variable shared quotient output mismatch");
        for (offset,window) in report.windows.iter().enumerate() {
            anyhow::ensure!(window.index == state.start+offset &&
                window.quotients[0][4..] == window.points[1] && window.quotients[1][4..] == window.points[2] &&
                window.quotients[2][4..] == window.points[4], "balance variable window quotient role mismatch");
            if offset > 0 { anyhow::ensure!(window.points[0] == report.windows[offset-1].points[4], "balance variable point chain mismatch"); }
        }
        if state.start == 0 { anyhow::ensure!(report.windows[0].points[0] == [Observed::Native(Scalar::zero()), Observed::Native(Scalar::from(1))], "balance variable initial identity mismatch"); }
        if state.start+state.count == 65 { anyhow::ensure!(report.windows.last().unwrap().points[4] == report.output, "balance variable final output mismatch"); }
        state.taken = true; Ok(report.clone())
    })
}
