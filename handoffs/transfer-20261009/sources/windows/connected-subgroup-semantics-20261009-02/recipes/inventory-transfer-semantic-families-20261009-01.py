from pathlib import Path
import hashlib, json, re, subprocess, sys

repo = Path('C:/src/shieldd-transfer-windows-publication-20261009')
runtime = Path('C:/src/shieldd-pr160-844389ee')
rust = runtime / 'crates/crypto/circuits/src'
formal = repo / 'handoffs/transfer-20261009/sources/windows/maintained-review-20261009-01/formal/circuits/ShielddSecurity'
assert subprocess.check_output(['git','-C',str(runtime),'rev-parse','HEAD'], text=True).strip() == '844389ee069e1fb2e576708842d0b389b4d9a44a'
subprocess.run(['git','-C',str(runtime),'diff','--quiet','HEAD','--'],check=True)
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
files = {}
for name in ['transfer','registry','compliance','authorization','note','volume','encryption','routing','balance','audit','recovery','encoding','range','scalar','hash','group','map','tree']:
    p = rust / (name + '.rs')
    lines = p.read_text().splitlines()
    functions = [{'name':m.group(1),'line':i+1} for i,line in enumerate(lines)
                 if (m := re.search(r'\bfn\s+(\w+)\b',line))]
    files[name] = {'path':str(p.relative_to(runtime)).replace('\\','/'),'sha256':sha(p),
                   'function_declarations':functions,'function_lines_are_locators_not_extracted_graph_ranges':True}
for name in ['poseidon381','poseidon381-wide']:
    p = runtime / ('crates/crypto/primitives/params/' + name + '.json')
    files[name] = {'path':str(p.relative_to(runtime)).replace('\\','/'),'sha256':sha(p)}

def family(name, source, ports, assertions, join):
    return {'name':name,'source_files':source,'witness_and_port_boundary':ports,
            'assertion_boundary':assertions,'numeric_graph_node_range':None,
            'numeric_assertion_range':None,'original_row_indices':None,
            'status':'SOURCE_REVIEW_AND_CANDIDATE_FOUNDATIONS_ONLY; concrete full-graph instance OPEN',
            'remaining_semantic_join':join}
families = [
family('Poseidon permutation and sponge',['hash'],
 'Width3 for arity<=2, otherwise width6. State0=256*arity+domain; other state words zero. Absorb chunks of WIDTH-1 into words1 onward; empty input permutes once; output state1. No fresh witness inside hash.',
 '65 rounds, ARK each word; x^5 all words rounds0..3,61..64, otherwise word0; MDS ordered dot products. Caller binds returned digest.',
 'Exact pinned ARK/MDS/field constant lift, symbolic round/sponge recurrence and extracted compiler certificates; domain, arity, input order and consumer output binding.'),
family('Shared-inverse Edwards addition and subgroup',['group'],
 'Point.add uses one inverse of product of two denominators. witness_subgroup allocates targetxy, preimagexy and three shared inverse hints (7 raw fields).',
 'Preimage curve equation, three inverse equations, two target coordinate equalities. Nonidentity is separate x-inverse constraint.',
 'Only first registry DK instance is checked below. Repeated instances need exact port rebinding and original-row coverage; deployed full curve/codec/order remain explicit obligations.'),
family('Affine quotient windows and scalar multiplication',['group','scalar'],
 'window helpers use two quotient operations per point, unlike shared-inverse add. Radix4 variable precomputes twice/triple then reverses two-bit chunks, doubles twice/adds. Fixed windows use increasing native weighted bases; odd final high bit false.',
 'Each actual quotient equation plus selector Boolean rows, scalar reconstruction and canonical bound. Denominator nonzero follows from model/curve premises, not quotient equation alone.',
 'Exact source window matcher, native fixed tables and SDK curve/codec alignment. Frozen720-DH-module chain is separate foundation evidence; no proved replacement for its concrete checks.'),
family('Boolean, zero, ranges, comparisons and scalar reduction',['range','scalar','encoding'],
 'is_zero allocates Bool+inverse. decompose allocates width Boolean bits. Bounded comparison allocates borrow,difference and difference bits. Canonical scalar252bits<=r-1; canonical field255bits<=p-1; reduction quotient4bits and remainder252bits.',
 'v*inverse=1-zero and v*zero=0; bit weighted reconstruction; comparator recurrences; quotient<=8, remainder<r, field equation and final quotient8 bound prevent wrap.',
 'Instantiate exact node/assertion/row support and independent integer/byte decoding; arbitrary characteristic fields do not supply a canonical codec.'),
family('Quaternary Merkle paths',['tree'],
 'Path position plus three sibling fields per level; two position bits per level. State24levels/compliance16levels. Reused position bits still reconstruct exact position.',
 'Two selectors order four children; hash input has level word then4children (arity5); output root alone is not membership until caller equality/gate.',
 'Symbolic level recurrence, exact hash instances, path witness order and caller gate; no global interval inferred from Rust call locators.'),
family('Elligator and derived generators',['map'],
 'QR branch Bool, QR root,yroot,canonical ybits,exceptional-zero flag,rational inverse then three shared-inverse cofactor doubles. Native QR/sqrt/parity use canonical bytes.',
 'Root squares/branch equations, sign parity, denominator*inverse=1-zero, denominator*zero=0,inverse*zero=0; caller uses mapped output.',
 'Deterministic native branch and exceptional case, concrete field sqrt/parity/parameters and source matcher. Subgroup template does not establish map uniqueness.'),
family('Registry membership and regulated gap',['registry','audit','tree'],
 'Leaf value,nextIndex,nextValue; DK subgroup,daily limit,route policy,ring subgroup,ringId,policyId,permission,resource,audit epoch and two audit subgroup keys; depth16path.',
 'PARAMS hash4, RING hash6, AUDIT_KEYS hash5, RING combine2, LEAF hash5; root anchor; regulated asset equality; unregulated strict gap; epoch64bits and gated forbidden audit-key equalities.',
 'First DK closed slice; remaining digests/keys/gap/root/policy selection and exact row coverage open. Regulated issuer nonidentity is checked after Transfer selection.'),
family('Sender and receiver compliance',['compliance'],
 'Each address diversified/transmission/rnkDH has subgroup+nonidentity, plus rnk commitment/lifecycle and depth16path. Lifecycle131bits.',
 'COMPLIANCE_LEAF9fields; regulated root=anchor; regulated status bits0=1,1/2=0,upper64bits67..130zero; middle64 generation preserved.',
 'Six subgroup rebinding instances, lifecycle bit ranges/gates and hash/path consumer joins.'),
family('Authorization IVK/RNK and randomized key',['authorization','note'],
 'AK subgroup/preimage/nonidentity, NK, IVK hash3/reduction252bits/nonzero; diversified*IVK=transmission and rnkDH*IVK; randomizer252bits, fixed generator multiple+AK, RK subgroup/nonidentity.',
 'RNK hash9 and commitment hash1 with regulated commitment equality; shared address/ring/nonzero checks. Randomized key xy equality binds computed value.',
 'Owned SDK admission/generator/scalar/codec contracts, exact source scalar/window/hash/add/RK instance and independent subgroup admission.'),
family('Notes, nullifiers and padding',['note','tree'],
 'Two spends: note3fields,amount128bits,position48bits,path,nullifier; second has dummyBool/seed. Two outputs: note3fields,commitment,capsule; first output amount inverse.',
 'NOTE hash8, nullifier hash3, State24path. Required membership/nullifier equality; optional real membership gate, selected nullifier and dummy amount0. Outputs digest equality and capsule commitment=note recovery.',
 'Exact domains/fixed padding slot1, branch semantics, shared addresses/asset/NK/randomizer and output consumer joins.'),
family('Volume state transition',['volume','transfer'],
 'useReal/startsNewDay Booleans,context1or2,timestamp64/day48/second17,subject,prior/successor amounts128,limit128,blindings and State24continuationpath.',
 'Timestamp decomposition seconds<=86399; ordinary/regulated/external eligibility; gated subject/state/successor/limit constraints; real/pad nullifier and commitment selection. Transfer also (context-1)*external=0.',
 'Both allocated branches retained even when gated; exact subject/domain/path/NK/nonce/day and fee/external semantics; no inactive-cone omission without proof.'),
family('Audit ownership and Transfer encryption',['audit','encryption','encoding'],
 'Two ownership ciphertexts raw Rxy/Cxy+randomness252bits; four tier EPKxy/c2/ciphertexts and core confirmations; metadata5policyfields,epoch4salts. Four ephemeral252bit scalars; five variable DH products incl unconditional detection.',
 'EPK=fixed generator multiple,nonidentity; selected flagged detection/payload DH, stream/detection/confirmation equalities; ownership fingerprint hash4/map+checking DH=C; metadata shared equalities. Published derived coordinates are not subgroup witness allocations.',
 'Exact DH/window/hash/map/address-packing instances and all tier/metadata/statement ports. Existing serial DH checks do not close full Transfer graph consumer joins.'),
family('Recovery capsules',['recovery','note'],
 'Each output allocates commitment,EPKxy,c2,salt,confirmation,encrypted amount/blinding plus seed and randomizer252bits. Transfer uses witness_fields, not standalone Capsule.witness subgroup allocation.',
 'Fixed generator=EPK/nonidentity; payload DH, seed+secret=c2; confirmation hash4,stream2 amount/blinding,commitment hash7; note recovery equality.',
 'Two exact constructor instances, canonical scalar/EPK/DH/plaintext/digest consumers; release relation does not claim knowledge of encryption secret.'),
family('Routing tags',['routing','encoding','range'],
 'Two precisions0..32 one-hot,asOfHeight,parameterSet,public tags32bits; canonical route/permutation/random hashes255bits. Shared nonce; permutation lowbit swaps sender/receiver slots.',
 'Precision order, parameter hash3 equality, per-slot32selected bit equalities with relevance and active prefix masks; slot0/slot1 statement binding.',
 'Exact canonical/hash/one-hot/mask/select source instance; preserve corrected routing slot order, shared nonce and change relevance.'),
family('Balance commitment',['balance','map','group'],
 'Four amount128bits,sum129bits,signBool,magnitude129bits; asset generator hash1/map,variable magnitude multiple and fixed canonical252bit blinding multiple.',
 'Signed difference reconstruction,asset generator nonidentity,sign x-negation and shared-inverse sum; resulting xy bound in statement. Circuit does not assert net difference zero.',
 'Signed integer/range semantics, exact generator/map/odd-window/blinding native joins and consumer statement coordinates.'),
family('Header, statement and compiler boundary',['transfer'],
 'Raw0..7 header: anchors3,asset,timestamp,nonce,blinding,regulatedBool. Statement64fields; final raw22734 claimed digest. Returned claimed/blinding; compiler fixed0=1 andcopy200692=1.',
 'Final hash(STATEMENT_DOMAIN,64ordered fields)=claimed; compiled public input roles and fixed/copy rows separate. Four local header-carrier expected rows have scoped evidence.',
 'Complete role legality, all64field ports, statement domain/sponging, topological and full original-row coverage/LocalRowSoundness; full Transfer theorem remains open.')]

patterns = {'concrete_zmod_codec':r'CanonicalField\s*\(ZMod', 'concrete_zmod_modulus':r'ZMod\s+Scalar\.modulus',
 'prime_fact':r'Fact\s*[^\n]*Prime', 'modulus_prime':r'modulus_prime',
 'standard_model_constructor':r'StandardCurveModel[^\n]*(?::=|where)'}
search = {name:[] for name in patterns}
roster = {}
for p in sorted(formal.glob('*.lean')):
    roster[p.name] = sha(p)
    for line_number,line in enumerate(p.read_text(encoding='utf-8-sig').splitlines(),1):
        for name,pattern in patterns.items():
            if re.search(pattern,line): search[name].append({'file':p.name,'line':line_number,'text':line})
owned = [
 {'obligation':'Full deployed StandardCurveModel and global (8*r)-annihilation',
  'existing':'GroupWindows StandardCurveModel specifies full on-curve coverage, coordinate injection,identity,addition. Group.cofactor_image_annihilated proves generic implication under GLOBAL order. Concrete successor uses equivalent nativeEight coordinate lemma.',
  'open':'No concrete deployed full-group instance/order evidence identified. SubgroupPoint alone cannot supply coverage of torsion points.'},
 {'obligation':'NoUnitSquare fixed d and imaginary squared=-1',
  'existing':'Group.denominators_nonzero derives completeness from these explicit parameters. Parent numeric d=-10240/10241 comparison is data only.',
  'open':'No checked concrete nonsquare/imaginary witness identified; cannot assume for arbitrary extensions of characteristic p.'},
 {'obligation':'Concrete prime field, canonical decoder and BEWrite',
  'existing':'TransferReduction.CanonicalField is explicit bounded decode+roundtrip. GroupByteCodec.canonicalWrite supplies mathematical byte writer for any codec; reader_join proves indexing agreement. ShielddScalarReader derives owned reader operations from explicit upstream Backend.',
  'open':'Math writer is not native FFI agreement; concrete field/primality and Scalar encoding/reader contracts still require evidence. Avoid brute-force255bit norm_num. If prime proof required, bounded kernel Lucas/Pratt certificate route is a candidate, not a checked result.'},
 {'obligation':'Scalar::from_limbs(INVERSE_EIGHT)',
  'existing':'GroupNativeCofactor.inverse_eight_equation and inverse_eight_bound checked; exact little-endian limb numerical values compared with source.',
  'open':'Native from_limbs interpretation remains a source/primitive contract. Numeric agreement alone supplies no codec refinement.'},
 {'obligation':'SDK subgroup admission, coordinates and generator',
  'existing':'ShielddNativeSdk.Upstream explicitly quantifies subgroup promotion,fallible decoding,encoding,affine meaning,group operations and SPEND_AUTH; owned wrappers are derived. GroupNativeAuthorization coordinate reader keeps independent BERead/CoordinateBytes contracts.',
  'open':'No concrete implementation satisfying those full upstream contracts identified. Completion requires independent r-annihilated initial point; output desired subgroupness is not an admission premise.'}]
result = {'runtime_sha':'844389ee069e1fb2e576708842d0b389b4d9a44a','parent_commit':'d7d44ca82712a35a3e40d68af7ae89b25b128ce6',
 'kind':'SOURCE_REVIEW_INVENTORY; no new proof/runtime/model-check/control credit', 'files':files,
 'checked_instance':{'name':'first registry DK only','source_witness_ids':[11,12,13,14,15,16,17],
  'source_arithmetic_ids_inclusive':[1,58],'local_nodes':80,'local_inputs':[0,6],
  'local_constants':[7,21],'local_arithmetic':[22,79],
  'local_assertion_pairs':[[25,28],[13,37],[17,54],[21,71],[0,76],[1,79]],
  'original_row_indices':list(range(64))+list(range(177955,177961))+[200769],
  'proof_receipt':'handoffs/transfer-20261009/receipts/windows/connected-subgroup-concrete-20261009-01.json',
  'coverage02_successor':'PENDING_ACTUAL_CHECK; separate receipt required',
  'other_instance_status':'Reusable typed matcher exists; no other original global node/row/assertion instance checked by this inventory.'},
 'macro_families':families,'owned_instance_obligations':owned,
 'evidence_references':{str(p.relative_to(repo)).replace('\\','/'):{'sha256':sha(p),'kind':kind}
   for p,kind in [
     (repo/'handoffs/transfer-20261009/receipts/mac/mac-transfer-profile01/profile-result01.json','DATA_PROFILE_ONLY; no family semantic attribution'),
     (repo/'handoffs/transfer-20261009/reviews/subgroup-pinned-constants-parent.json','NUMERIC_SOURCE_DATA_COMPARISON_ONLY; no codec/group proof'),
     (repo/'handoffs/transfer-20261009/receipts/windows/subgroup-arithmetic-20261009-01.json','SCOPED_KERNEL_ARITHMETIC_AND_QUALIFIED_DEPENDENCIES'),
     (repo/'handoffs/transfer-20261009/receipts/windows/connected-subgroup-concrete-20261009-01.json','SCOPED_KERNEL71ROW_JOIN; no concrete deployed instances')]},
 'bounded_search_evidence':{'scope':str(formal),'files_scanned':len(roster),
  'roster_sha256':hashlib.sha256(json.dumps(roster,sort_keys=True).encode()).hexdigest(),
  'patterns':patterns,'matches':search,
  'standard_model_matches_disposition':'Four matches inspected: generic model definition and parameterized SDK/game contract structures; none is a concrete deployed model construction.',
  'limitation':'Absence only for these textual searches; no repository-wide nonexistence theorem.'},
 'next_checked_block':{'recommended':'One width6 Poseidon65-round permutation, then first registry PARAMS arity4 hash consumer.',
  'basis':'Qualitative inference from pervasive source hash calls and fullgraph large add/constant-scale profile. Profile does not attribute90percent to Poseidon; no family percentage or exact hash node interval claimed.',
  'reuse':'Symbolic ARK/Sbox/MDS round recurrence and sponge absorption; then Merkle level hash5, commitments/encryption/statement hash consumers.',
  'required_extraction':['Stable source call identifier/domain/arity and ordered raw input ports','Each round state ports and exact source-node predecessor mapping','Exact constants matched to pinned parameter files','Output state1 consumer and original assertion IDs','Materialized/nonmaterialized compiler events and complete original-row mappings','Witness allocation boundaries/external ports/topological/fixed/copy obligations'],
  'bounded_pilot':'First prove one symbolic round and bounded extracted matcher instance; measure finite Lean memory/time before65round composition. No million-literal LC expansion or escalation on timeout.',
  'alternative':'Rebind subgroup matcher to next ring/address instance for smaller immediate row closure; division-window family needs its own matcher because it is not the17-node shared-inverse doubling block.'},
 'queued_owned_instance_research':{
   'affine_group':{'entry':'https://isa-afp.org/entries/Edwards_Elliptic_Curves_Group.html',
     'provided_release_snapshot':'https://isa-afp.org/release/afp-Edwards_Elliptic_Curves_Group-2026-02-06.tar.gz',
     'primary_entry_checked':'Entry dated February16,2023 describes integer polynomial associativity checked by polynomial division.',
     'mapping_provenance':'Parent and Opus SOURCE REVIEW ONLY: AFP(x,y)=(our y,our x),c=-1,same d; no Lean instance credit.',
     'certificate_correction':'Lines61..180 provide denominator rearrangements. Ideal-membership cofactors r1/r2/r3 are existential via algebra, not exported cleared-numerator certificates.',
     'candidate_port':'Opaque intermediate-point row-form associativity with explicit integer cofactors, then OnCurve subtype AddCommGroup and covering/injective model; reuse existing denominator and closure lemmas. Avoid giant quotient field_simp.',
     'global_order':'Separate unproved cardinality/order obligation','new_dependency_imported':False,'kernel_credit':0},
   'prime_field_data':{'provenance':'Parent-provided untrusted Python candidate; not yet published in this baton.',
     'recursive_lucas_candidate_sha256':'20d3da8789fc847a4e5450c430321b52350e79f7533bcd43ff48695ffa4c862d',
     'candidate_certificates':38,'root_base':7,
     'claimed_p_minus_one_factorization':'2^32*3*11*19*10177*125527*859267*906349^2*2508409*2529403*52437899*254760293^2',
     'claimed_imaginary':3465144826073652318776269530687742778270252468765361963008,
     'claimed_modular_checks':'imaginary^2=-1 modp; fixed d^((p-1)/2)=-1 modp',
     'candidate_next_task':'Kernel-check bounded recursive Lucas certificates and modular identities, then derive concrete field/nonsquare/root instance. Native codec and global group order remain separate.',
     'kernel_credit':0,'primality_credit':0,'field_instance_credit':0}},
 'global_open':['Fullgraph semantic partition/checked coverage','Concrete field/curve/codec/SDK instances','Full Transfer constructive completeness and arbitrary-assignment soundness','Runtime verifier/development registry and state/durable-store refinement'],
 'native_successors':'UNRUN','full_transfer':'OPEN'}
out = repo / 'handoffs/transfer-20261009/reviews/windows-semantic-family-inventory-20261009-01.json'
assert not out.exists() or '--refresh-review' in sys.argv
out.write_bytes((json.dumps(result,indent=2)+'\n').encode())
print(json.dumps({'path':str(out),'sha256':sha(out),'families':len(families),'search_files':len(roster)}))
