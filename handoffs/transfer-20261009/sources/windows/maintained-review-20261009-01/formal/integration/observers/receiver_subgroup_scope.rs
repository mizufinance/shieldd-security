//! Fresh-only receiver scope over the existing bounded subgroup recorder.
use crate::group::inspection;
use std::{cell::RefCell, marker::PhantomData, rc::Rc};

#[derive(Default)]
struct State {
    calls: usize,
    active: Option<(usize, usize)>,
    reports: Vec<inspection::Report>,
}
thread_local! { static STATE: RefCell<Option<State>> = const { RefCell::new(None) }; }
pub struct Capture { _thread: PhantomData<Rc<()>> }
impl Drop for Capture {
    fn drop(&mut self) { STATE.with(|state| *state.borrow_mut() = None); }
}
pub fn begin() -> anyhow::Result<Capture> {
    STATE.with(|state| {
        let mut state = state.borrow_mut();
        anyhow::ensure!(state.is_none(), "nested receiver subgroup capture");
        *state = Some(State::default());
        Ok(Capture { _thread: PhantomData })
    })
}
pub struct CallScope { _thread: PhantomData<Rc<()>> }
impl Drop for CallScope {
    fn drop(&mut self) {
        STATE.with(|state| {
            if let Some(state) = state.borrow_mut().as_mut() {
                let (_, points) = state.active.take().expect("receiver scope lost");
                if !std::thread::panicking() {
                    assert_eq!(points, 3, "compliance point occurrence mismatch");
                }
            }
        });
    }
}
pub(crate) fn enter() -> Option<CallScope> {
    STATE.with(|state| {
        let mut state = state.borrow_mut();
        let state = state.as_mut()?;
        assert!(state.active.is_none() && state.calls < 2, "compliance occurrence mismatch");
        state.active = Some((state.calls, 0));
        state.calls += 1;
        Some(CallScope { _thread: PhantomData })
    })
}
pub struct PointScope {
    scope: Option<inspection::Scope>,
    capture: Option<inspection::Capture>,
    _thread: PhantomData<Rc<()>>,
}
impl Drop for PointScope {
    fn drop(&mut self) {
        drop(self.scope.take());
        if std::thread::panicking() {
            drop(self.capture.take());
            return;
        }
        let report = inspection::take().expect("receiver subgroup report incomplete");
        drop(self.capture.take());
        STATE.with(|state| {
            let mut state = state.borrow_mut();
            let state = state.as_mut().expect("receiver capture lost");
            assert!(state.reports.len() < 3, "receiver point report overflow");
            state.reports.push(report);
        });
    }
}
pub(crate) fn point_scope() -> Option<PointScope> {
    let selected = STATE.with(|state| {
        let mut state = state.borrow_mut();
        let Some(state) = state.as_mut() else { return false; };
        let (call, points) = state.active.as_mut().expect("point outside compliance call");
        assert!(*points < 3, "compliance point count overflow");
        *points += 1;
        *call == 1
    });
    if !selected { return None; }
    // The generic recorder exists only inside this one point operation. This
    // excludes earlier authorization/RK scopes without changing their hooks.
    let capture = inspection::begin().expect("overlapping subgroup recorder");
    let scope = inspection::scope().expect("receiver subgroup recorder absent");
    Some(PointScope { scope: Some(scope), capture: Some(capture), _thread: PhantomData })
}
pub fn take() -> anyhow::Result<Vec<inspection::Report>> {
    STATE.with(|state| {
        let mut state = state.borrow_mut();
        let state = state.as_mut().ok_or_else(|| anyhow::anyhow!("inactive receiver capture"))?;
        anyhow::ensure!(state.calls == 2 && state.active.is_none() && state.reports.len() == 3,
            "exact sender/receiver and receiver three-point report required");
        Ok(std::mem::take(&mut state.reports))
    })
}
