//! Future-stage companion: 48 existing note-only quaternary wiring boundaries.
use super::Tree;
use crate::scalar::inspection::Observed;
use commonware_cryptography::{bls12381::primitives::group::Scalar, zk::circuit::Var};
use std::{cell::RefCell, marker::PhantomData, rc::Rc};

#[derive(Clone, PartialEq, Eq)]
pub struct Level {
    pub slot: usize,
    pub level: usize,
    pub node: Observed,
    pub low: Observed,
    pub high: Observed,
    pub siblings: [Observed; 3],
    pub swaps: [Observed; 2],
    pub children: [Observed; 4],
    pub output: Observed,
}
#[derive(Default)]
struct State {
    levels: Vec<Level>,
    invalid: bool,
    taken: bool,
}
thread_local! {static STATE:RefCell<Option<State>>=const{RefCell::new(None)};}
pub struct Capture {
    _thread: PhantomData<Rc<()>>,
}
impl Drop for Capture {
    fn drop(&mut self) {
        STATE.with(|s| *s.borrow_mut() = None);
    }
}
pub fn begin() -> anyhow::Result<Capture> {
    STATE.with(|s| {
        anyhow::ensure!(s.borrow().is_none(), "note tree capture already active");
        *s.borrow_mut() = Some(State::default());
        Ok(Capture {
            _thread: PhantomData,
        })
    })
}
fn observed(v: &Var<'_, Scalar>) -> Observed {
    match v.inspect_circuit_idx() {
        Some(index) => Observed::Source(index),
        None => Observed::Native(v.inspect_native().expect("invalid tree variable").clone()),
    }
}
pub(super) fn record(
    kind: Tree,
    level: usize,
    node: &Var<'_, Scalar>,
    low: &Var<'_, Scalar>,
    high: &Var<'_, Scalar>,
    siblings: &[Var<'_, Scalar>; 3],
    swaps: [&Var<'_, Scalar>; 2],
    inputs: &[Var<'_, Scalar>; 5],
    output: &Var<'_, Scalar>,
) {
    if kind as u8 != 1 {
        return;
    }
    let Some(slot) = crate::hash::note_inspection::current_spend_slot() else {
        return;
    };
    STATE.with(|s| {
        let mut s = s.borrow_mut();
        let Some(s) = s.as_mut() else {
            return;
        };
        if s.taken || slot >= 2 || level >= 24 || s.levels.len() != slot * 24 + level {
            s.invalid = true;
            return;
        }
        if observed(&inputs[0]) != Observed::Native(Scalar::from(level as u64 + 1)) {
            s.invalid = true;
            return;
        }
        s.levels.push(Level {
            slot,
            level,
            node: observed(node),
            low: observed(low),
            high: observed(high),
            siblings: std::array::from_fn(|i| observed(&siblings[i])),
            swaps: std::array::from_fn(|i| observed(swaps[i])),
            children: std::array::from_fn(|i| observed(&inputs[i + 1])),
            output: observed(output),
        });
    });
}
pub fn take() -> anyhow::Result<Vec<Level>> {
    STATE.with(|s| {
        let mut s = s.borrow_mut();
        let s = s
            .as_mut()
            .ok_or_else(|| anyhow::anyhow!("no note tree capture"))?;
        anyhow::ensure!(
            !s.invalid && !s.taken && s.levels.len() == 48,
            "incomplete48 note tree levels"
        );
        s.taken = true;
        Ok(std::mem::take(&mut s.levels))
    })
}

#[cfg(test)]
mod note_tree_scope_tests {
    use super::*;
    fn record_level(level: usize) {
        let node = Var::native(Scalar::from(7u64));
        let low = Var::native(Scalar::from(0u64));
        let high = Var::native(Scalar::from(1u64));
        let siblings = std::array::from_fn(|i| Var::native(Scalar::from(i as u64 + 11)));
        let inputs = [
            Var::native(Scalar::from(level as u64 + 1)),
            node.clone(),
            siblings[0].clone(),
            siblings[1].clone(),
            siblings[2].clone(),
        ];
        record(
            Tree::State,
            level,
            &node,
            &low,
            &high,
            &siblings,
            [&low, &high],
            &inputs,
            &node,
        );
    }
    #[test]
    fn exact48_order_take_once_and_reset_on_drop() {
        {
            let _hash = crate::hash::note_inspection::begin_all().unwrap();
            let _capture = begin().unwrap();
            assert!(begin().is_err());
            for _slot in 0..2 {
                let _scope = crate::hash::note_inspection::spend();
                for level in 0..24 {
                    record_level(level);
                }
            }
            let levels = take().unwrap();
            assert_eq!(levels.len(), 48);
            assert_eq!((levels[0].slot, levels[0].level), (0, 0));
            assert_eq!((levels[47].slot, levels[47].level), (1, 23));
            assert!(take().is_err());
        }
        let _capture = begin().unwrap();
        assert!(take().is_err());
    }
    #[test]
    fn truncation_reorder_and_overflow_refused() {
        for levels in [vec![0], vec![1], (0..25).collect()] {
            let _hash = crate::hash::note_inspection::begin_all().unwrap();
            let _capture = begin().unwrap();
            let _scope = crate::hash::note_inspection::spend();
            for level in levels {
                record_level(level);
            }
            assert!(take().is_err());
        }
    }
}
