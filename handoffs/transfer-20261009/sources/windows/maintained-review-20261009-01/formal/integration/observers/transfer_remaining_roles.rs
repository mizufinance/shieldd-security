//! Fresh child only: source handles and bounded hash checkpoints, never values.
use crate::scalar::inspection::Observed;
use commonware_cryptography::{bls12381::primitives::group::Scalar, zk::circuit::Var};
use std::{cell::RefCell, marker::PhantomData, rc::Rc};

pub const SCOPES: [&str; 8] = ["sender", "receiver", "volume", "encryption",
    "audit-sender", "audit-receiver", "routing", "statement"];
#[derive(Clone, PartialEq, Eq)]
pub struct Record { pub scope: &'static str, pub tag: &'static str, pub ordinal: usize, pub values: Vec<Observed> }
#[derive(Clone, PartialEq, Eq)]
pub struct Block { pub before: Vec<Observed>, pub after: Vec<Observed> }
#[derive(Clone, PartialEq, Eq)]
pub struct Hash { pub scope: &'static str, pub domain: u8, pub inputs: Vec<Observed>,
    pub output: Observed, pub blocks: Vec<Block> }
#[derive(Clone, PartialEq, Eq)]
pub struct Report { pub records: Vec<Record>, pub hashes: Vec<Hash> }
struct Pending { scope: &'static str, domain: u8, inputs: Vec<Observed>,
    before: Option<Vec<Observed>>, blocks: Vec<Block> }
#[derive(Default)]
struct State { scopes: Vec<&'static str>, visits: Vec<&'static str>, records: Vec<Record>,
    hashes: Vec<Hash>, pending: Option<Pending>, invalid: bool, taken: bool }
thread_local! { static STATE: RefCell<Option<State>> = const { RefCell::new(None) }; }
pub struct Capture { _thread: PhantomData<Rc<()>> }
impl Drop for Capture { fn drop(&mut self) { STATE.with(|s| *s.borrow_mut() = None); } }
pub fn begin() -> anyhow::Result<Capture> {
    STATE.with(|s| { let mut s=s.borrow_mut();anyhow::ensure!(s.is_none(),"nested remaining capture");
        *s=Some(State::default());Ok(Capture {_thread:PhantomData}) })
}
pub struct Scope { active: bool, name: &'static str, _thread: PhantomData<Rc<()>> }
pub fn scope(name: &'static str) -> Scope {
    let active=STATE.with(|s| { let mut s=s.borrow_mut();let Some(s)=s.as_mut() else{return false};
        let allowed=SCOPES.contains(&name) && !s.visits.contains(&name) && s.pending.is_none()
            && !s.taken && (s.scopes.is_empty() ||
                (s.scopes==["encryption"] && matches!(name,"audit-sender"|"audit-receiver")));
        if !allowed {s.invalid=true;return false}
        s.scopes.push(name);s.visits.push(name);true });
    Scope {active,name,_thread:PhantomData}
}
impl Drop for Scope { fn drop(&mut self) { if !self.active{return}
    STATE.with(|s| { let mut s=s.borrow_mut();let Some(s)=s.as_mut() else{return};
        if s.pending.is_some() || s.scopes.pop()!=Some(self.name){s.invalid=true;} }); } }
fn observed(v:&Var<'_,Scalar>)->Observed {
    match v.inspect_circuit_idx() {Some(i)=>Observed::Source(i),
        None=>Observed::Native(v.inspect_native().expect("invalid remaining source var").clone())}
}
pub fn values(tag:&'static str, values:&[&Var<'_,Scalar>]) {
    indexed(tag,0,values)
}
pub fn indexed(tag:&'static str, ordinal:usize, values:&[&Var<'_,Scalar>]) {
    STATE.with(|s| {let mut s=s.borrow_mut();let Some(s)=s.as_mut() else{return};
        let scope=s.scopes.last().copied().unwrap_or("caller");
        if s.taken || values.is_empty() || values.len()>1024 || s.records.len()>=128
            || ordinal>31 || s.records.iter().any(|r|r.scope==scope && r.tag==tag && r.ordinal==ordinal){s.invalid=true;return}
        s.records.push(Record {scope,tag,ordinal,values:values.iter().map(|v|observed(v)).collect()}); });
}
pub fn tree_level(ordinal:usize,values:&[&Var<'_,Scalar>]) {
    let active=STATE.with(|s|s.borrow().as_ref().and_then(|s|s.scopes.last().copied())
        .map(|scope|matches!(scope,"sender"|"receiver"|"volume")).unwrap_or(false));
    if active {indexed("tree-level",ordinal,values);}
}
pub struct Call {active:bool,_thread:PhantomData<Rc<()>>}
pub(crate) fn start(domain:u8, inputs:&[Var<'_,Scalar>])->Call {
    let active=STATE.with(|s| {let mut s=s.borrow_mut();let Some(s)=s.as_mut() else{return false};
        let Some(scope)=s.scopes.last().copied() else{return false};
        if s.pending.is_some() || s.taken || inputs.is_empty() || inputs.len()>64 || s.hashes.len()>=128 {
            s.invalid=true;return false}
        s.pending=Some(Pending {scope,domain,inputs:inputs.iter().map(observed).collect(),
            before:None,blocks:Vec::new()});true});Call {active,_thread:PhantomData}
}
pub(crate) fn state(call:&Call, block:usize, after:bool, values:&[Var<'_,Scalar>]) {
    if !call.active{return} STATE.with(|s| {let mut s=s.borrow_mut();let Some(s)=s.as_mut() else{return};
        let Some(p)=s.pending.as_mut() else{s.invalid=true;return};
        let width=if p.inputs.len()<=2{3}else{6};
        if block!=p.blocks.len() || values.len()!=width || block>=13 {s.invalid=true;return}
        let values=values.iter().map(observed).collect();
        if after {let Some(before)=p.before.take() else{s.invalid=true;return};
            p.blocks.push(Block {before,after:values});}
        else {if p.before.is_some(){s.invalid=true;return}p.before=Some(values);}
    });
}
pub(crate) fn finish(call:Call, output:&Var<'_,Scalar>) {
    if !call.active{return} STATE.with(|s| {let mut s=s.borrow_mut();let Some(s)=s.as_mut() else{return};
        let Some(p)=s.pending.take() else{s.invalid=true;return};
        let rate=if p.inputs.len()<=2{2}else{5};let blocks=p.inputs.len().div_ceil(rate);
        let output=observed(output);
        if p.before.is_some() || p.blocks.len()!=blocks ||
            p.blocks.last().and_then(|b|b.after.get(1))!=Some(&output){s.invalid=true;return}
        s.hashes.push(Hash {scope:p.scope,domain:p.domain,inputs:p.inputs,output,blocks:p.blocks});
    });
}
pub fn expected_hashes(scope:&str)->Vec<(u8,usize)> {
    match scope {
        "sender"|"receiver"=>std::iter::once((19,9)).chain(std::iter::repeat_n((3,5),16)).collect(),
        "volume"=>std::iter::once((4,5)).chain(std::iter::once((5,4)))
            .chain(std::iter::repeat_n((1,5),24))
            .chain([(6,3),(7,3),(5,4),(9,3),(8,3)]).collect(),
        "encryption"=>std::iter::repeat_n((14,2),5).chain(std::iter::once((12,4)))
            .chain(std::iter::repeat_n((10,2),4)).chain([(11,2),(13,4),(10,2),(11,2),(13,4),(10,2)])
            .chain([(11,2),(10,2),(10,2),(10,2),(11,2),(10,2),(10,2),(10,2)]).collect(),
        "audit-sender"|"audit-receiver"=>vec![(35,4)],
        "routing"=>vec![(33,3),(30,2),(30,2),(32,1),(31,2),(31,2)],
        "statement"=>vec![(34,64)],_=>Vec::new(),
    }
}
// Exact tag/ordinal/width inventory from the reviewed current source hooks.
// Handle equality here is syntactic shared-input identity, not a field/group proof.
pub fn record_shapes() -> Vec<(&'static str,&'static str,usize,usize)> {
    let mut wanted=vec![("caller","shared",0,8),("caller","registry-leaf",0,14),
        ("caller","auth-roots",0,7),("caller","note-slots",0,8),
        ("caller","external",0,2),("caller","balance",0,2)];
    for scope in ["sender","receiver"] {
        wanted.extend([(scope,"membership",0,5),(scope,"computed-root",0,1),
            (scope,"lifecycle-bits",0,131),
            (scope,if scope=="sender" {"sender-binding"} else {"receiver-binding"},0,8)]);
        wanted.extend((0..16).map(|i|(scope,"tree-level",i,14)));
    }
    wanted.extend([("volume","shared",0,12),("volume","context-bool",0,2),
        ("volume","day-index",0,1),("volume","timestamp-bits",0,64),("volume","day-bits",0,48),
        ("volume","second-within",0,1),("volume","prior-bits",0,128),("volume","successor-bits",0,128),
        ("volume","controls",0,13),("volume","candidate-bits",0,128),("volume","limit-bits",0,128),
        ("volume","second-bits",0,17),("volume","volume-output",0,5)]);
    wanted.extend((0..24).map(|i|("volume","tree-level",i,14)));
    wanted.extend([("encryption","shared",0,24),("encryption","audit-output",0,6),
        ("encryption","published44",0,44),("encryption","metadata-equality-endpoints",0,20)]);
    wanted.extend((0..4).map(|i|("encryption","ephemeral-bits",i,252)));
    for scope in ["audit-sender","audit-receiver"] {
        wanted.extend([(scope,"randomness-bits",0,252),(scope,"binding",0,10)]);
    }
    wanted.extend([("routing","shared",0,7),("routing","precision-values",0,2),
        ("routing","regulated-prefix",0,32),("routing","unregulated-prefix",0,32),
        ("routing","active-prefix",0,32),("routing","flags",0,7),("routing","routing-output",0,4)]);
    for slot in 0..2 { wanted.extend([("routing","public-bits",slot,32),
        ("routing","route-bits",slot,255),("routing","random-bits",slot,255)]); }
    wanted.extend([("statement","ordered64",0,64),("statement","interface",0,2)]);
    wanted.sort();wanted
}
fn role<'a>(records:&'a [Record],scope:&str,tag:&str,ordinal:usize)->anyhow::Result<&'a [Observed]> {
    records.iter().find(|r|r.scope==scope && r.tag==tag && r.ordinal==ordinal)
        .map(|r|r.values.as_slice()).ok_or_else(||anyhow::anyhow!("missing remaining role {scope}/{tag}/{ordinal}"))
}
fn joins(records:&[Record],hashes:&[Hash])->anyhow::Result<()> {
    let mut shapes=records.iter().map(|r|(r.scope,r.tag,r.ordinal,r.values.len())).collect::<Vec<_>>();
    shapes.sort();anyhow::ensure!(shapes==record_shapes(),"remaining exact role inventory changed");
    let at=|scope,tag,ordinal|role(records,scope,tag,ordinal);
    let shared=at("caller","shared",0)?;let leaf=at("caller","registry-leaf",0)?;
    let auth=at("caller","auth-roots",0)?;let notes=at("caller","note-slots",0)?;
    let sender=at("sender","sender-binding",0)?;let receiver=at("receiver","receiver-binding",0)?;
    let volume=at("volume","shared",0)?;let control=at("volume","controls",0)?;
    let vo=at("volume","volume-output",0)?;let encryption=at("encryption","shared",0)?;
    let routing=at("routing","shared",0)?;let ro=at("routing","routing-output",0)?;
    anyhow::ensure!(volume[0]==shared[4] && volume[2..6]==sender[..4] && volume[6]==shared[3]
        && volume[7]==notes[6] && volume[8]==leaf[9] && volume[9]==shared[0]
        && volume[10]==auth[0] && volume[11]==shared[5],"volume current caller inputs changed");
    anyhow::ensure!(at("caller","external",0)?[1]==shared[7],"external regulated input changed");
    anyhow::ensure!(encryption[0]==vo[4] && encryption[1]==shared[5] && encryption[2]==shared[3]
        && encryption[3]==notes[6] && encryption[11..15]==sender[..4]
        && encryption[15..19]==receiver[..4] && encryption[23]==shared[4],"encryption caller inputs changed");
    anyhow::ensure!(routing[0]==shared[7] && routing[1]==notes[7] && routing[2..4]==sender[2..4]
        && routing[4..6]==receiver[2..4] && routing[6]==shared[5],"routing caller/change slot changed");
    anyhow::ensure!(control[2]==vo[3] && control[6]==vo[2] && control[12]==vo[4]
        && at("volume","context-bool",0)?[0]==vo[3],"volume output/context aliases changed");
    for (scope,binding) in [("audit-sender",sender),("audit-receiver",receiver)] {
        let values=at(scope,"binding",0)?;
        anyhow::ensure!(values[..4]==binding[..4] && values[4..6]==encryption[9..11],"ownership address/checking caller changed");
        let hash=hashes.iter().find(|h|h.scope==scope).ok_or_else(||anyhow::anyhow!("missing ownership hash"))?;
        anyhow::ensure!(hash.inputs==values[..4],"ownership fingerprint hash input changed");
    }
    for (scope,binding) in [("sender",sender),("receiver",receiver)] {
        let member=at(scope,"membership",0)?;
        anyhow::ensure!(member[2]==shared[3] && member[3]==shared[2] && member[4]==shared[7],"compliance caller gate inputs changed");
        let hs=hashes.iter().filter(|h|h.scope==scope).collect::<Vec<_>>();
        let expected=binding[..4].iter().chain(std::iter::once(&shared[3])).chain(binding[4..].iter()).collect::<Vec<_>>();
        anyhow::ensure!(hs[0].inputs.iter().collect::<Vec<_>>()==expected && hs[0].output==member[0],"compliance leaf source binding changed");
        for level in 0..16 {
            let tree=at(scope,"tree-level",level)?;
            anyhow::ensure!(tree[0]==hs[level].output && tree[8..12]==hs[level+1].inputs[1..5]
                && tree[12]==hs[level+1].output && tree[13]==member[1],"compliance ordered tree source edge changed");
        }
        anyhow::ensure!(at(scope,"computed-root",0)?[0]==hs[16].output,"compliance root source changed");
    }
    let hs=hashes.iter().filter(|h|h.scope=="volume").collect::<Vec<_>>();
    anyhow::ensure!(hs[0].inputs[..4]==sender[..4] && hs[0].inputs[4]==shared[3],"volume subject hash input changed");
    for level in 0..24 {
        let tree=at("volume","tree-level",level)?;
        anyhow::ensure!(tree[0]==hs[level+1].output && tree[8..12]==hs[level+2].inputs[1..5]
            && tree[12]==hs[level+2].output,"volume ordered tree source edge changed");
    }
    for index in [26,27,29,30] {
        anyhow::ensure!(hs[index].inputs[0]==auth[0],"volume hash uses wrong raw NK");
    }
    let published=at("encryption","published44",0)?;
    let metadata=at("encryption","audit-output",0)?;
    anyhow::ensure!(metadata[..4]==published[26..30]
        && metadata[4]==published[30] && metadata[5]==published[35],"published metadata output aliases changed");
    // These are independently allocated witnesses with source assert_eq rows.
    // Capture each endpoint without asserting the desired field equality here.
    let endpoints=at("encryption","metadata-equality-endpoints",0)?;
    for i in 0..5 {
        anyhow::ensure!(endpoints[2*i]==published[26+i] && endpoints[2*i+1]==encryption[19+i],
            "published/shared policy equality endpoints changed");
    }
    anyhow::ensure!(endpoints[10]==published[35] && endpoints[11]==encryption[6],"epoch equality endpoints changed");
    let eh=hashes.iter().filter(|h|h.scope=="encryption").collect::<Vec<_>>();
    for i in 0..4 {
        anyhow::ensure!(endpoints[12+2*i]==published[31+i] && endpoints[13+2*i]==eh[i+1].output,
            "salt hash/equality endpoints changed");
    }
    for (scope,start) in [("audit-sender",36),("audit-receiver",40)] {
        anyhow::ensure!(at(scope,"binding",0)?[6..10]==published[start..start+4],"published ownership slot changed");
    }
    let balance=at("caller","balance",0)?;
    let mut ordered=auth[4..6].to_vec();ordered.push(shared[0].clone());
    ordered.extend_from_slice(&notes[2..6]);ordered.extend_from_slice(balance);
    ordered.extend_from_slice(&ro[1..3]);ordered.push(ro[0].clone());ordered.extend_from_slice(&vo[..4]);
    ordered.extend_from_slice(&notes[..2]);ordered.extend_from_slice(&shared[1..3]);
    ordered.extend_from_slice(&published[..4]);
    for (core,ext) in [(4,14),(9,20)] {
        ordered.extend_from_slice(&published[core..core+3]);ordered.push(published[core+4].clone());
        ordered.extend_from_slice(&published[ext..ext+6]);
    }
    ordered.push(shared[4].clone());ordered.push(published[7].clone());ordered.push(published[12].clone());
    ordered.extend_from_slice(&published[26..30]);ordered.extend_from_slice(&published[31..44]);
    let fields=at("statement","ordered64",0)?;
    anyhow::ensure!(ordered.len()==64 && ordered==fields,"current Transfer64 projection/slot ordering changed");
    anyhow::ensure!(at("statement","interface",0)?[1]==shared[6],"committed balance blinding alias changed");
    anyhow::ensure!(hashes.iter().find(|h|h.scope=="statement").map(|h|h.inputs.as_slice())==Some(fields),
        "statement hash is not the exact observed ordered64 list");
    Ok(())
}
pub fn take()->anyhow::Result<Report> {
    STATE.with(|s| {let mut s=s.borrow_mut();let s=s.as_mut().ok_or_else(||anyhow::anyhow!("inactive remaining capture"))?;
        anyhow::ensure!(!s.invalid && !s.taken && s.scopes.is_empty() && s.pending.is_none(),"remaining lifecycle/truncation mismatch");
        anyhow::ensure!(s.visits==["sender","receiver","volume","encryption","audit-sender","audit-receiver","routing","statement"],
            "remaining component order/multiplicity changed");
        for scope in SCOPES {let actual=s.hashes.iter().filter(|h|h.scope==scope)
            .map(|h|(h.domain,h.inputs.len())).collect::<Vec<_>>();
            anyhow::ensure!(actual==expected_hashes(scope),"remaining exact hash scope/domain/arity changed: {scope}");}
        joins(&s.records,&s.hashes)?;
        s.taken=true;Ok(Report {records:std::mem::take(&mut s.records),hashes:std::mem::take(&mut s.hashes)})
    })
}
