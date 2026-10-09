//! Bounded source-only current Transfer spend observer. No witness values.
use super::{Note, SpendContext};
use crate::scalar::inspection::Observed;
use commonware_cryptography::{
    bls12381::primitives::group::Scalar,
    zk::circuit::{BoolVar, CircuitIdx, Var},
};
use std::{cell::RefCell, marker::PhantomData, rc::Rc};

#[derive(Clone, PartialEq, Eq)]
pub struct Shared {
    pub asset: Observed,
    pub address: [Observed; 4],
    pub nk: Observed,
    pub randomizer: Observed,
    pub anchor: Observed,
}
#[derive(Clone, PartialEq, Eq)]
pub struct Optional {
    pub domain: u8,
    pub slot: usize,
    pub seed: Observed,
    pub synthetic: Observed,
    pub selected: Observed,
    /// Source operand/result triples. Compiler auxiliaries are NOT source vars;
    /// the ordinary-row matcher discovers their exact physical columns.
    pub products: [[Observed; 3]; 3],
}
#[derive(Clone, PartialEq, Eq)]
pub struct Spend {
    pub shared: Shared,
    pub note: [Observed; 8],
    pub commitment: Observed,
    pub position: Observed,
    pub amount_bits: Vec<CircuitIdx>,
    pub position_bits: Vec<CircuitIdx>,
    pub real_nullifier: Observed,
    pub computed_anchor: Observed,
    pub nullifier: Observed,
    pub dummy: Observed,
    pub optional: Option<Optional>,
}
#[derive(Clone, PartialEq, Eq)]
pub struct Report {
    pub spends: [Spend; 2],
}
impl Report {
    pub fn selected(&self) -> Vec<CircuitIdx> {
        let mut result = Vec::new();
        let mut add = |value: &Observed| {
            if let Observed::Source(index) = value {
                result.push(*index);
            }
        };
        for spend in &self.spends {
            for value in [
                &spend.shared.asset,
                &spend.shared.nk,
                &spend.shared.randomizer,
                &spend.shared.anchor,
            ] {
                add(value);
            }
            for value in &spend.shared.address {
                add(value);
            }
            for value in &spend.note {
                add(value);
            }
            for value in [
                &spend.commitment,
                &spend.position,
                &spend.real_nullifier,
                &spend.computed_anchor,
                &spend.nullifier,
                &spend.dummy,
            ] {
                add(value);
            }
            if let Some(optional) = &spend.optional {
                for value in [&optional.seed, &optional.synthetic, &optional.selected] {
                    add(value);
                }
                for product in &optional.products {
                    for value in product {
                        add(value);
                    }
                }
            }
        }
        for spend in &self.spends {
            result.extend(&spend.amount_bits);
            result.extend(&spend.position_bits);
        }
        result.sort();
        result.dedup();
        result
    }
}
#[derive(Default)]
struct State {
    spends: Vec<Spend>,
    invalid: bool,
    taken: bool,
}
thread_local! { static STATE: RefCell<Option<State>> = const { RefCell::new(None) }; }
pub struct Capture {
    _thread: PhantomData<Rc<()>>,
}
impl Drop for Capture {
    fn drop(&mut self) {
        STATE.with(|state| *state.borrow_mut() = None);
    }
}
pub fn begin() -> anyhow::Result<Capture> {
    STATE.with(|state| {
        let mut state = state.borrow_mut();
        anyhow::ensure!(state.is_none(), "nested note-spend capture");
        *state = Some(State::default());
        Ok(Capture {
            _thread: PhantomData,
        })
    })
}
fn observed(value: &Var<'_, Scalar>) -> Observed {
    match value.inspect_circuit_idx() {
        Some(index) => Observed::Source(index),
        None => Observed::Native(
            value
                .inspect_native()
                .expect("invalid note-spend var")
                .clone(),
        ),
    }
}
pub(crate) fn optional(
    domain: u8,
    slot: usize,
    seed: &Var<'_, Scalar>,
    synthetic: &Var<'_, Scalar>,
    selected: &Var<'_, Scalar>,
    products: [[&Var<'_, Scalar>; 3]; 3],
) -> Option<Optional> {
    STATE.with(|state| {
        state.borrow().as_ref().map(|_| Optional {
            domain,
            slot,
            seed: observed(seed),
            synthetic: observed(synthetic),
            selected: observed(selected),
            products: products.map(|product| product.map(observed)),
        })
    })
}
pub(crate) fn record<'ctx>(
    shared: &SpendContext<'ctx>,
    note: &Note<Var<'ctx, Scalar>>,
    commitment: &Var<'ctx, Scalar>,
    position: &Var<'ctx, Scalar>,
    amount_bits: &[BoolVar<'ctx, Scalar>],
    position_bits: &[BoolVar<'ctx, Scalar>],
    real_nullifier: &Var<'ctx, Scalar>,
    computed_anchor: &Var<'ctx, Scalar>,
    nullifier: &Var<'ctx, Scalar>,
    dummy: &BoolVar<'ctx, Scalar>,
    optional: Option<Optional>,
) {
    STATE.with(|state| {
        let mut state = state.borrow_mut();
        let Some(state) = state.as_mut() else {
            return;
        };
        if state.taken
            || state.spends.len() >= 2
            || amount_bits.len() != 128
            || position_bits.len() != 48
        {
            state.invalid = true;
            return;
        }
        let bits = |values: &[BoolVar<'_, Scalar>]| -> Option<Vec<_>> {
            values
                .iter()
                .map(|bit| bit.var().inspect_circuit_idx())
                .collect()
        };
        let (Some(amount_bits), Some(position_bits)) = (bits(amount_bits), bits(position_bits))
        else {
            state.invalid = true;
            return;
        };
        let address = &shared.address;
        state.spends.push(Spend {
            shared: Shared {
                asset: observed(&shared.asset),
                address: [
                    observed(&address.diversified.x),
                    observed(&address.diversified.y),
                    observed(&address.transmission.x),
                    observed(&address.transmission.y),
                ],
                nk: observed(&shared.nk),
                randomizer: observed(&shared.randomizer),
                anchor: observed(&shared.anchor),
            },
            note: note.fields(&shared.asset, address).each_ref().map(observed),
            commitment: observed(commitment),
            position: observed(position),
            amount_bits,
            position_bits,
            real_nullifier: observed(real_nullifier),
            computed_anchor: observed(computed_anchor),
            nullifier: observed(nullifier),
            dummy: observed(dummy.var()),
            optional,
        });
    });
}
pub fn take() -> anyhow::Result<Report> {
    STATE.with(|state| {
        let mut state = state.borrow_mut();
        let state = state
            .as_mut()
            .ok_or_else(|| anyhow::anyhow!("inactive note-spend capture"))?;
        anyhow::ensure!(
            !state.invalid && !state.taken && state.spends.len() == 2,
            "note-spend count/overflow/repeat mismatch"
        );
        let required = &state.spends[0];
        let optional = &state.spends[1];
        anyhow::ensure!(
            required.optional.is_none()
                && optional.optional.as_ref().is_some_and(|o| o.domain
                    == shieldd_sdk_crypto::domains::DUMMY_NULLIFIER
                    && o.slot == 1),
            "note-spend required/Transfer optional policy mismatch"
        );
        anyhow::ensure!(
            required.shared == optional.shared,
            "note-spend shared role mismatch"
        );
        anyhow::ensure!(
            required.dummy == Observed::Native(Scalar::from(0)),
            "required spend constructor must return false"
        );
        let report = Report {
            spends: state
                .spends
                .clone()
                .try_into()
                .map_err(|_| anyhow::anyhow!("note-spend fixed count mismatch"))?,
        };
        anyhow::ensure!(
            report.selected().len() <= 512,
            "note-spend selected source bound"
        );
        state.taken = true;
        Ok(report)
    })
}
