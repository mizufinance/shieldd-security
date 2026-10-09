//! Bounded actual receiver/change source handles. No assignments or cone walk.
use super::Note;
use crate::{encryption::Address, group::Point, recovery::Capsule, scalar::inspection::Observed};
use commonware_cryptography::{
    bls12381::primitives::group::Scalar,
    zk::circuit::{BoolVar, CircuitIdx, Var},
};
use std::{cell::RefCell, marker::PhantomData, rc::Rc};

#[derive(Clone, PartialEq, Eq)]
pub struct Output {
    pub receiver: bool,
    /// Exact native NOTE15/8 field order, including the supplied address/asset.
    pub note: [Observed; 8],
    pub amount_bits: Vec<CircuitIdx>,
    pub receiver_inverse: Option<Observed>,
    pub computed_commitment: Observed,
    pub commitment: Observed,
    /// Recovery commitment7 field order, not an assertion of hash semantics.
    pub capsule: [Observed; 7],
    pub capsule_commitment: Observed,
    pub payload_key: [Observed; 2],
}
#[derive(Clone, PartialEq, Eq)]
pub struct Report {
    pub outputs: [Output; 2],
}
impl Report {
    pub fn selected(&self) -> Vec<CircuitIdx> {
        let mut result = Vec::new();
        let mut add = |value: &Observed| {
            if let Observed::Source(index) = value { result.push(*index); }
        };
        for output in &self.outputs {
            for value in &output.note { add(value); }
            for value in &output.capsule { add(value); }
            for value in &output.payload_key { add(value); }
            for value in [&output.computed_commitment, &output.commitment, &output.capsule_commitment] {
                add(value);
            }
            if let Some(inverse) = &output.receiver_inverse { add(inverse); }
        }
        for output in &self.outputs { result.extend(&output.amount_bits); }
        result.sort();result.dedup();result
    }
}
#[derive(Default)]
struct State { outputs: Vec<Output>, invalid: bool, taken: bool }
thread_local! { static STATE: RefCell<Option<State>> = const { RefCell::new(None) }; }
pub struct Capture { _thread: PhantomData<Rc<()>> }
impl Drop for Capture {
    fn drop(&mut self) { STATE.with(|state| *state.borrow_mut() = None); }
}
pub fn begin() -> anyhow::Result<Capture> {
    STATE.with(|state| {
        let mut state = state.borrow_mut();
        anyhow::ensure!(state.is_none(), "nested note-output capture");
        *state = Some(State::default());
        Ok(Capture { _thread: PhantomData })
    })
}
fn observed(value: &Var<'_, Scalar>) -> Observed {
    match value.inspect_circuit_idx() {
        Some(index) => Observed::Source(index),
        None => Observed::Native(value.inspect_native().expect("invalid output var").clone()),
    }
}
pub(crate) fn record<'ctx>(
    receiver: bool, note: &Note<Var<'ctx, Scalar>>, asset: &Var<'ctx, Scalar>,
    address: &Address<Var<'ctx, Scalar>>, payload_key: &Point<Var<'ctx, Scalar>>,
    amount_bits: &[BoolVar<'ctx, Scalar>], receiver_inverse: Option<&Var<'ctx, Scalar>>,
    computed_commitment: &Var<'ctx, Scalar>, commitment: &Var<'ctx, Scalar>,
    capsule: &Capsule<Var<'ctx, Scalar>>,
) {
    STATE.with(|state| {
        let mut state = state.borrow_mut();let Some(state) = state.as_mut() else { return; };
        if state.taken || state.outputs.len() >= 2 || amount_bits.len() != 128 ||
            receiver != state.outputs.is_empty() || receiver != receiver_inverse.is_some() {
            state.invalid = true;return;
        }
        let bits: Option<Vec<_>> = amount_bits.iter().map(|bit| bit.var().inspect_circuit_idx()).collect();
        let Some(amount_bits) = bits else { state.invalid = true;return; };
        state.outputs.push(Output {
            receiver, note: note.fields(asset,address).each_ref().map(observed), amount_bits,
            receiver_inverse: receiver_inverse.map(observed), computed_commitment: observed(computed_commitment),
            commitment: observed(commitment), capsule: capsule.commitment_inputs().each_ref().map(observed),
            capsule_commitment: observed(&capsule.commitment), payload_key: [observed(&payload_key.x),observed(&payload_key.y)],
        });
    });
}
pub fn take() -> anyhow::Result<Report> {
    STATE.with(|state| {
        let mut state = state.borrow_mut();
        let state = state.as_mut().ok_or_else(|| anyhow::anyhow!("inactive output capture"))?;
        anyhow::ensure!(!state.invalid && !state.taken && state.outputs.len()==2,"output count/order/overflow/repeat mismatch");
        let report = Report { outputs: state.outputs.clone().try_into().map_err(|_| anyhow::anyhow!("output fixed count mismatch"))? };
        anyhow::ensure!(report.outputs[0].receiver && !report.outputs[1].receiver,"receiver/change role mismatch");
        anyhow::ensure!(report.outputs[0].receiver_inverse.is_some() && report.outputs[1].receiver_inverse.is_none(),"output inverse branch mismatch");
        anyhow::ensure!(report.outputs[0].note[2]==report.outputs[1].note[2] && report.outputs[0].payload_key==report.outputs[1].payload_key,"output shared asset/payload source mismatch");
        anyhow::ensure!(report.selected().len()<=512,"output selected source bound");
        state.taken=true;Ok(report)
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    fn output(receiver: bool) -> Output {
        let native = || Observed::Native(Scalar::from(0));
        Output {
            receiver, note: std::array::from_fn(|_| native()),
            amount_bits: (0..128).map(CircuitIdx::Witness).collect(),
            receiver_inverse: receiver.then(native), computed_commitment: native(),
            commitment: native(), capsule: std::array::from_fn(|_| native()),
            capsule_commitment: native(), payload_key: [native(),native()],
        }
    }
    fn install(outputs: Vec<Output>, invalid: bool) {
        STATE.with(|state| {
            let mut state = state.borrow_mut();let state=state.as_mut().unwrap();
            state.outputs=outputs;state.invalid=invalid;
        });
    }
    #[test]
    fn lifecycle_fixed_order_and_truncation() {
        let capture=begin().unwrap();assert!(begin().is_err());assert!(take().is_err());
        install(vec![output(true)],false);assert!(take().is_err());
        install(vec![output(true),output(false)],false);
        let report=take().unwrap();assert_eq!(report.selected().len(),128);assert!(take().is_err());
        drop(capture);assert!(take().is_err());assert!(begin().is_ok());
    }
    #[test]
    fn wrong_roles_shared_handles_and_poison_refuse() {
        let _capture=begin().unwrap();
        install(vec![output(false),output(true)],false);assert!(take().is_err());
        let mut change=output(false);change.receiver_inverse=Some(Observed::Native(Scalar::from(1)));
        install(vec![output(true),change],false);assert!(take().is_err());
        let mut change=output(false);change.note[2]=Observed::Native(Scalar::from(1));
        install(vec![output(true),change],false);assert!(take().is_err());
        install(vec![output(true),output(false)],true);assert!(take().is_err());
        install(vec![output(true),output(false),output(false)],false);assert!(take().is_err());
    }
}
