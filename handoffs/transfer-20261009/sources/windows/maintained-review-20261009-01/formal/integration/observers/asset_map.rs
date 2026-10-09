//! One exact balance asset-map boundary, source handles only, no witness values.
use super::Point;
use crate::scalar::inspection::Observed;
use commonware_cryptography::{
    bls12381::primitives::group::Scalar,
    zk::circuit::{BoolVar, CircuitIdx, Var},
};
use std::{cell::RefCell, marker::PhantomData, rc::Rc};

#[derive(Clone, PartialEq, Eq)]
pub struct Report {
    pub asset: Observed,
    pub hash: Observed,
    /// u,tv,den1,inv1,x1,gx1,x2,gx2,square,qrRoot,x,ySquared,y,s,t,plus,den,zero,inv.
    pub values: [Observed; 19],
    pub y_bits: Vec<CircuitIdx>,
    /// Rational image followed by each of the three actual doublings.
    pub cofactor: [[Observed; 2]; 4],
    pub cofactor_aux: [[Observed; 7]; 3],
    pub constraint_products: [Observed; 4],
    pub qr: [Observed; 2],
    pub canonical: [Observed; 2],
}
impl Report {
    pub fn selected(&self) -> Vec<CircuitIdx> {
        let mut result = self.y_bits.clone();
        for value in [&self.asset, &self.hash].into_iter().chain(self.values.iter())
            .chain(self.cofactor.iter().flatten()).chain(self.cofactor_aux.iter().flatten())
            .chain(self.constraint_products.iter()).chain(self.qr.iter()).chain(self.canonical.iter()) {
            if let Observed::Source(index) = value { result.push(*index); }
        }
        result.sort();
        result.dedup();
        result
    }
}
#[derive(Default)]
struct State {
    scope: Option<[Observed; 2]>,
    report: Option<Report>,
    entered: usize,
    invalid: bool,
    taken: bool,
    qr: Option<[Observed; 2]>,
    canonical: Option<(Observed, Vec<CircuitIdx>, [Observed; 2])>,
}
thread_local! {static STATE:RefCell<Option<State>>=const{RefCell::new(None)};}
pub struct Capture { _thread: PhantomData<Rc<()>> }
impl Drop for Capture {
    fn drop(&mut self) { STATE.with(|s| *s.borrow_mut() = None); }
}
pub fn begin() -> anyhow::Result<Capture> {
    STATE.with(|s| {
        anyhow::ensure!(s.borrow().is_none(), "asset-map capture already active");
        *s.borrow_mut() = Some(State::default());
        Ok(Capture { _thread: PhantomData })
    })
}
fn observed(v: &Var<'_, Scalar>) -> Observed {
    match v.inspect_circuit_idx() {
        Some(index) => Observed::Source(index),
        None => Observed::Native(v.inspect_native().expect("invalid map variable").clone()),
    }
}
pub struct Scope { active: bool, _thread: PhantomData<Rc<()>> }
impl Drop for Scope {
    fn drop(&mut self) {
        if self.active { STATE.with(|s| {
            if let Some(s) = s.borrow_mut().as_mut() { s.scope = None; }
        }); }
    }
}
pub fn scope(asset: &Var<'_, Scalar>, hash: &Var<'_, Scalar>) -> Scope {
    let active = STATE.with(|s| {
        let mut s = s.borrow_mut();
        let Some(s) = s.as_mut() else { return false; };
        if s.scope.is_some() || s.taken || s.entered != 0 { s.invalid = true; return false; }
        s.entered += 1;
        s.scope = Some([observed(asset), observed(hash)]);
        true
    });
    Scope { active, _thread: PhantomData }
}
pub(super) fn qr(squared: &Var<'_, Scalar>, selected: &Var<'_, Scalar>) {
    STATE.with(|s| {
        let mut s = s.borrow_mut();
        let Some(s) = s.as_mut() else { return; };
        if s.scope.is_none() { return; }
        if s.qr.is_some() || s.taken { s.invalid = true; return; }
        s.qr = Some([observed(squared), observed(selected)]);
    });
}
pub fn canonical(value: &Var<'_, Scalar>, bits: &[BoolVar<'_, Scalar>],
    sum: &Var<'_, Scalar>, bounded: &BoolVar<'_, Scalar>) {
    STATE.with(|s| {
        let mut s = s.borrow_mut();
        let Some(s) = s.as_mut() else { return; };
        if s.scope.is_none() { return; }
        if s.canonical.is_some() || s.taken || bits.len() != 255 { s.invalid = true; return; }
        let Some(bits) = bits.iter().map(|b| b.var().inspect_circuit_idx()).collect::<Option<Vec<_>>>()
            else { s.invalid = true; return; };
        s.canonical = Some((observed(value), bits, [observed(sum), observed(bounded.var())]));
    });
}
pub(super) fn record(values: [&Var<'_, Scalar>; 19], bits: &[BoolVar<'_, Scalar>],
    points: &[Point<Var<'_, Scalar>>], products: [&Var<'_, Scalar>; 4],
    aux: &[[Var<'_, Scalar>; 7]]) {
    STATE.with(|s| {
        let mut s = s.borrow_mut();
        let Some(s) = s.as_mut() else { return; };
        let Some([asset, hash]) = s.scope.clone() else { return; };
        if s.taken || s.report.is_some() || bits.len() != 255 || points.len() != 4 || aux.len() != 3 {
            s.invalid = true; return;
        }
        let Some(y_bits) = bits.iter().map(|b| b.var().inspect_circuit_idx()).collect::<Option<Vec<_>>>()
            else { s.invalid = true; return; };
        let values = values.map(observed);
        if values[0] != hash { s.invalid = true; return; }
        let (Some(qr), Some((value, recorded_bits, canonical))) = (s.qr.clone(), s.canonical.clone())
            else { s.invalid = true; return; };
        if value != values[12] || recorded_bits != y_bits { s.invalid = true; return; }
        let cofactor = points.iter().map(|p| [observed(&p.x), observed(&p.y)])
            .collect::<Vec<_>>().try_into().unwrap_or_else(|_| unreachable!("checked cofactor size"));
        let cofactor_aux = aux.iter().map(|a| a.each_ref().map(observed)).collect::<Vec<_>>()
            .try_into().unwrap_or_else(|_| unreachable!("checked auxiliary size"));
        s.report = Some(Report { asset, hash, values, y_bits, cofactor, cofactor_aux,
            constraint_products: products.map(observed), qr, canonical });
    });
}
pub fn take() -> anyhow::Result<Report> {
    STATE.with(|s| {
        let mut s = s.borrow_mut();
        let s = s.as_mut().ok_or_else(|| anyhow::anyhow!("inactive asset-map capture"))?;
        anyhow::ensure!(!s.invalid && !s.taken && s.scope.is_none() && s.entered == 1,
            "asset-map scope/count/overflow mismatch");
        let report = s.report.clone().ok_or_else(|| anyhow::anyhow!("missing asset-map record"))?;
        anyhow::ensure!(report.selected().len() <= 320, "asset-map selected handle bound");
        s.taken = true;
        Ok(report)
    })
}
