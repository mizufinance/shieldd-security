//! Fresh-stage only: one existing input-note hash permutation, no values.
use super::Scalar;
use crate::scalar::inspection::Observed;
use commonware_cryptography::zk::circuit::Var;
use std::{cell::RefCell, marker::PhantomData, rc::Rc};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Role {
    Commitment,
    Nullifier,
    Dummy,
    StateLevel(usize),
}
impl Role {
    fn index(self) -> usize {
        match self {
            Self::Commitment => 0,
            Self::Nullifier => 1,
            Self::Dummy => 26,
            Self::StateLevel(level) => 2 + level,
        }
    }
}
#[derive(Clone, PartialEq, Eq)]
pub struct Block {
    pub before: Vec<Observed>,
    pub after: Vec<Observed>,
}
#[derive(Clone, PartialEq, Eq)]
pub struct Report {
    pub slot: usize,
    pub role: Role,
    pub block: usize,
    pub domain: u8,
    pub inputs: Vec<Observed>,
    pub output: Observed,
    pub blocks: Vec<Block>,
}
struct Pending {
    slot: usize,
    role: Role,
    domain: u8,
    inputs: Vec<Observed>,
    before: Option<Vec<Observed>>,
    blocks: Vec<Block>,
}
struct State {
    batch: bool,
    reports: Vec<Report>,
    slot: usize,
    role: Role,
    block: usize,
    spends: usize,
    active: bool,
    calls: usize,
    invalid: bool,
    taken: bool,
    pending: Option<Pending>,
    report: Option<Report>,
}
thread_local! { static STATE: RefCell<Option<State>> = const { RefCell::new(None) }; }
pub struct Capture {
    _thread: PhantomData<Rc<()>>,
}
impl Drop for Capture {
    fn drop(&mut self) {
        STATE.with(|s| *s.borrow_mut() = None);
    }
}
pub fn begin(slot: usize, role: Role, block: usize) -> anyhow::Result<Capture> {
    anyhow::ensure!(
        slot < 2 && (role != Role::Dummy || slot == 1),
        "invalid input-note hash role"
    );
    anyhow::ensure!(
        !matches!(role, Role::StateLevel(level) if level >= 24),
        "invalid state level"
    );
    anyhow::ensure!(
        block < if role == Role::Commitment { 2 } else { 1 },
        "invalid hash block"
    );
    STATE.with(|s| {
        anyhow::ensure!(
            s.borrow().is_none(),
            "input-note hash capture already active"
        );
        *s.borrow_mut() = Some(State {
            batch: false,
            reports: Vec::new(),
            slot,
            role,
            block,
            spends: 0,
            active: false,
            calls: 0,
            invalid: false,
            taken: false,
            pending: None,
            report: None,
        });
        Ok(Capture {
            _thread: PhantomData,
        })
    })
}
/// Compact 53-call boundaries only; source cones are rebuilt/discarded per page.
pub fn begin_all() -> anyhow::Result<Capture> {
    let capture = begin(0, Role::Commitment, 0)?;
    STATE.with(|s| s.borrow_mut().as_mut().unwrap().batch = true);
    Ok(capture)
}
pub struct Spend {
    active: bool,
    _thread: PhantomData<Rc<()>>,
}
/// Install at the entry to constrain_spend, before any note hash is built.
pub fn spend() -> Spend {
    let active = STATE.with(|s| {
        let mut s = s.borrow_mut();
        let Some(s) = s.as_mut() else {
            return false;
        };
        if s.active || s.spends >= 2 || s.taken {
            s.invalid = true;
            return false;
        }
        s.active = true;
        s.calls = 0;
        true
    });
    Spend {
        active,
        _thread: PhantomData,
    }
}
impl Drop for Spend {
    fn drop(&mut self) {
        if !self.active {
            return;
        }
        STATE.with(|s| {
            let mut s = s.borrow_mut();
            let Some(s) = s.as_mut() else {
                return;
            };
            if !s.active || s.calls != if s.spends == 0 { 26 } else { 27 } || s.pending.is_some() {
                s.invalid = true;
            }
            s.active = false;
            s.spends += 1;
        });
    }
}
pub struct Call {
    active: bool,
    _thread: PhantomData<Rc<()>>,
}
fn observed(value: &Var<'_, Scalar>) -> Observed {
    match value.inspect_circuit_idx() {
        Some(index) => Observed::Source(index),
        None => Observed::Native(
            value
                .inspect_native()
                .expect("invalid hash variable")
                .clone(),
        ),
    }
}
pub(super) fn start(domain: u8, inputs: &[Var<'_, Scalar>]) -> Call {
    let active = STATE.with(|s| {
        let mut s = s.borrow_mut();
        let Some(s) = s.as_mut() else {
            return false;
        };
        if !s.active {
            return false;
        }
        let index = s.calls;
        s.calls += 1;
        let (wanted, arity) = match index {
            0 => (15, 8),
            1 => (7, 3),
            2..=25 => (1, 5),
            26 if s.spends == 1 => (22, 3),
            _ => {
                s.invalid = true;
                return false;
            }
        };
        if s.taken || s.pending.is_some() || domain != wanted || inputs.len() != arity {
            s.invalid = true;
            return false;
        }
        if index >= 2
            && index <= 25
            && observed(&inputs[0]) != Observed::Native(Scalar::from((index - 1) as u64))
        {
            s.invalid = true;
            return false;
        }
        if index == 26 && observed(&inputs[2]) != Observed::Native(Scalar::from(1u64)) {
            s.invalid = true;
            return false;
        }
        if !s.batch && (s.spends != s.slot || index != s.role.index()) {
            return false;
        }
        if s.report.is_some() || s.reports.len() >= 53 {
            s.invalid = true;
            return false;
        }
        s.pending = Some(Pending {
            slot: s.spends,
            role: match index {
                0 => Role::Commitment,
                1 => Role::Nullifier,
                2..=25 => Role::StateLevel(index - 2),
                26 => Role::Dummy,
                _ => unreachable!(),
            },
            domain,
            inputs: inputs.iter().map(observed).collect(),
            before: None,
            blocks: Vec::new(),
        });
        true
    });
    Call {
        active,
        _thread: PhantomData,
    }
}
pub(super) fn state(call: &Call, index: usize, after: bool, values: &[Var<'_, Scalar>]) {
    if !call.active {
        return;
    }
    STATE.with(|s| {
        let mut s = s.borrow_mut();
        let Some(s) = s.as_mut() else {
            return;
        };
        let Some(p) = s.pending.as_mut() else {
            s.invalid = true;
            return;
        };
        let count = if p.domain == 15 { 2 } else { 1 };
        if values.len() != 6 || index != p.blocks.len() || index >= count {
            s.invalid = true;
            return;
        }
        if after {
            let Some(before) = p.before.take() else {
                s.invalid = true;
                return;
            };
            p.blocks.push(Block {
                before,
                after: values.iter().map(observed).collect(),
            });
        } else if p.before.is_some() {
            s.invalid = true;
        } else {
            p.before = Some(values.iter().map(observed).collect());
        }
    });
}
pub(super) fn finish(call: Call, output: &Var<'_, Scalar>) {
    if !call.active {
        return;
    }
    STATE.with(|s| {
        let mut s = s.borrow_mut();
        let Some(s) = s.as_mut() else {
            return;
        };
        let Some(p) = s.pending.take() else {
            s.invalid = true;
            return;
        };
        let count = if p.domain == 15 { 2 } else { 1 };
        if p.before.is_some()
            || p.blocks.len() != count
            || p.blocks.last().map(|b| &b.after[1]) != Some(&observed(output))
        {
            s.invalid = true;
            return;
        }
        let report = Report {
            slot: p.slot,
            role: p.role,
            block: s.block,
            domain: p.domain,
            inputs: p.inputs,
            output: observed(output),
            blocks: p.blocks,
        };
        if s.batch {
            s.reports.push(report);
        } else {
            s.report = Some(report);
        }
    });
}
pub fn take() -> anyhow::Result<Report> {
    STATE.with(|s| {
        let mut s = s.borrow_mut();
        let s = s
            .as_mut()
            .ok_or_else(|| anyhow::anyhow!("no note hash capture"))?;
        anyhow::ensure!(
            !s.batch && !s.invalid && !s.taken && !s.active && s.spends == 2 && s.pending.is_none(),
            "incomplete two input-note hash scopes"
        );
        let report = s
            .report
            .take()
            .ok_or_else(|| anyhow::anyhow!("missing selected note hash"))?;
        s.taken = true;
        Ok(report)
    })
}
pub fn take_all() -> anyhow::Result<Vec<Report>> {
    STATE.with(|s| {
        let mut s = s.borrow_mut();
        let s = s
            .as_mut()
            .ok_or_else(|| anyhow::anyhow!("no note hash capture"))?;
        anyhow::ensure!(
            s.batch
                && !s.invalid
                && !s.taken
                && !s.active
                && s.spends == 2
                && s.pending.is_none()
                && s.reports.len() == 53,
            "incomplete53 input-note hash calls"
        );
        s.taken = true;
        Ok(std::mem::take(&mut s.reports))
    })
}
/// Read-only note scope identity for the separate tree-wiring companion.
pub fn current_spend_slot() -> Option<usize> {
    STATE.with(|s| {
        s.borrow()
            .as_ref()
            .filter(|s| s.active && !s.taken)
            .map(|s| s.spends)
    })
}

#[cfg(test)]
mod note_hash_scope_tests {
    use super::*;
    fn values(count: usize) -> Vec<Var<'static, Scalar>> {
        (0..count)
            .map(|i| Var::native(Scalar::from(i as u64 + 1)))
            .collect()
    }
    fn complete_call(domain: u8, arity: usize, level: usize) {
        let mut inputs = values(arity);
        if domain == 1 {
            inputs[0] = Var::native(Scalar::from(level as u64 + 1));
        }
        if domain == 22 {
            inputs[2] = Var::native(Scalar::from(1u64));
        }
        let lanes = values(6);
        let call = start(domain, &inputs);
        assert!(call.active);
        for block in 0..if domain == 15 { 2 } else { 1 } {
            state(&call, block, false, &lanes);
            state(&call, block, true, &lanes);
        }
        finish(call, &lanes[1]);
    }
    fn complete_spends() {
        for slot in 0..2 {
            let _scope = spend();
            complete_call(15, 8, 0);
            complete_call(7, 3, 0);
            for level in 0..24 {
                complete_call(1, 5, level);
            }
            if slot == 1 {
                complete_call(22, 3, 0);
            }
        }
    }
    #[test]
    fn all53_calls55_blocks_and_take_once() {
        let _capture = begin_all().unwrap();
        assert!(begin_all().is_err());
        complete_spends();
        let reports = take_all().unwrap();
        assert_eq!(reports.len(), 53);
        assert_eq!(reports.iter().map(|r| r.blocks.len()).sum::<usize>(), 55);
        assert_eq!(reports[0].role, Role::Commitment);
        assert_eq!(reports[26].slot, 1);
        assert_eq!(reports[52].role, Role::Dummy);
        assert!(take_all().is_err());
    }
    #[test]
    fn truncated_or_reordered_scopes_and_wrong_level_are_refused() {
        {
            let _capture = begin_all().unwrap();
            {
                let _scope = spend();
                complete_call(15, 8, 0);
            }
            assert!(take_all().is_err());
        }
        {
            let _capture = begin_all().unwrap();
            let _scope = spend();
            assert!(!start(7, &values(3)).active);
            assert!(take_all().is_err());
        }
        {
            let _capture = begin_all().unwrap();
            let _scope = spend();
            complete_call(15, 8, 0);
            complete_call(7, 3, 0);
            let mut inputs = values(5);
            inputs[0] = Var::native(Scalar::from(2u64));
            assert!(!start(1, &inputs).active);
            assert!(take_all().is_err());
        }
    }
}
