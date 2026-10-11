"""Source-shaped all-slot ordered typed nullifier projection installs concrete model inputs."""
import hashlib,json,re
from pathlib import Path
ROOT=Path(__file__).resolve().parent; DIAG=ROOT.parent
assert not (ROOT/'prepare.py').exists() and not (ROOT/'handwritten').exists()
runtime=Path('C:/src/shieldd-pr160-844389ee')
def pin(p):
    p=Path(p); b=p.read_bytes()
    return {'path':str(p),'bytes':len(b),'sha256':hashlib.sha256(b).hexdigest()}
files={name:runtime/relative for name,relative in {
    'action':'crates/core/component/shielded-pool/src/transfer/action.rs',
    'execute':'crates/core/component/shielded-pool/src/component/action_handler/transfer.rs',
    'effects':'crates/core/component/shielded-pool/src/component/action_handler/note_reshape.rs',
    'nullifier':'crates/core/component/sct/src/nullifier.rs'}.items()}
text={name:p.read_text() for name,p in files.items()}
patterns={
 'action':[r'pub struct TransferInputBody\s*\{\s*pub nullifier: Nullifier,',r'pub inputs: Vec<TransferInputBody>,'],
 'execute':[r'note_reshape::execute_proof_bound_effects\(\s*&mut state,\s*&transfer\.body\.inputs,\s*&transfer\.body\.outputs,\s*\|input\| input\.nullifier,\s*\|output\| &output\.note_payload,\s*\)'],
 'effects':[r'let nullifiers = inputs\s*\.iter\(\)\s*\.map\(input_nullifier\)\s*\.collect::<Vec<Nullifier>>\(\);',r'state\.nullify_all\(&nullifiers, source\.into\(\)\)\.await\?;'],
 'nullifier':[r'pub struct Nullifier\(pub Fq\);',r'pub fn to_bytes\(&self\) -> \[u8; 32\]\s*\{\s*self\.0\.to_bytes\(\)\s*\}']}
matches={}
for name,expressions in patterns.items():
    matches[name]=[]
    for expression in expressions:
        found=list(re.finditer(expression,text[name]))
        assert len(found)==1,(name,expression,len(found))
        match=found[0]
        matches[name].append({'expression':expression,'start_line':text[name][:match.start()].count('\n')+1,'matched_source':match.group()})
(ROOT/'context').mkdir()
(ROOT/'context/source-projection-shape.json').write_text(json.dumps({'kind':'EXACT_TRANSFER_ALL_SLOT_TYPED_NULLIFIER_PROJECTION_SOURCE_SHAPE',
    'runtime_sha':'844389ee069e1fb2e576708842d0b389b4d9a44a','runtime_sources':[pin(p) for p in files.values()],
    'matched_shapes':matches,'scope':'Exact source type/accessor/all-slot ordered map/batch insertion/byte-forwarding shape, no filters or private-padding suppression in matched iterator. Static source association only; Rust iterator/map/collect/Nullifier/Scalar/byte/compiler/native trace semantics remain explicit. No native/proof/control/certification credit for this JSON.'},indent=2,sort_keys=True)+'\n')
source='''import ShielddSecurity.TransferScalarByteEquality01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferSourceTypedInputProjection01
open TransferWholeReaderRefusal01 (Config)
open TransferScalarLittleEndianBytes01 (scalarKey)
open TransferScalarMontgomeryValue01 (montgomeryValue)
open TransferBoundedNativeCodec01 (nullifierModulus)
/-! Exact all-slot source-shaped map of Transfer input nullifier fields, followed
by the finite four-word scalar serializer. Concrete configuration installation
derives typed input projection and canonical key bounds; every slot is kept
in source order, without a caller-provided desired key vector/range premise.
Action-input and nullifier-word selectors describe the actual runtime binding
interface. Checked pinned source accessor/iterator/batch/byte-forwarding shape
does not prove Rust/native iterator/field/Scalar/codec/compiler trace semantics. -/

def typedWords {I A : Type} (inputs : A → List I) (wordOf : I → Vector UInt64 4) (action : A) : List (Vector UInt64 4) :=
  (inputs action).map wordOf

def sourceKeys {I A : Type} (inputs : A → List I) (wordOf : I → Vector UInt64 4) (action : A) : List Nat :=
  (inputs action).map (fun input => scalarKey (wordOf input))

def installTypedInputs {O E K X Tree A I : Type} (config : Config O E K X Tree A)
    (inputs : A → List I) (wordOf : I → Vector UInt64 4) : Config O E K X Tree A :=
  {config with inputs := sourceKeys inputs wordOf}

theorem installed_config_inputs_are_exact_ordered_typed_scalar_projection {O E K X Tree A I : Type}
    (config : Config O E K X Tree A) (inputs : A → List I) (wordOf : I → Vector UInt64 4) (action : A) :
    (installTypedInputs config inputs wordOf).inputs action = (typedWords inputs wordOf action).map scalarKey := by
  change (inputs action).map (fun input => scalarKey (wordOf input)) = ((inputs action).map wordOf).map scalarKey
  rw [List.map_map]

theorem source_keys_are_exact_ordered_mathematical_montgomery_values {I A : Type}
    (inputs : A → List I) (wordOf : I → Vector UInt64 4) (action : A) :
    sourceKeys inputs wordOf action = (inputs action).map (fun input => montgomeryValue (wordOf input)) := by
  exact List.map_congr_left (fun input _ =>
    TransferScalarMontgomeryValue01.fixed_four_word_typed_serializer_has_exact_canonical_montgomery_value (wordOf input))

theorem installed_config_derives_every_input_key_in_canonical_nullifier_domain {O E K X Tree A I : Type}
    (config : Config O E K X Tree A) (inputs : A → List I) (wordOf : I → Vector UInt64 4) (action : A) :
    ∀ key ∈ (installTypedInputs config inputs wordOf).inputs action, key < nullifierModulus := by
  intro key inside
  change key ∈ (inputs action).map (fun input => scalarKey (wordOf input)) at inside
  obtain ⟨input, _, projected⟩ := List.mem_map.mp inside
  rw [← projected]
  exact TransferScalarLittleEndianBytes01.fixed_four_word_source_scalar_projection_is_canonical (wordOf input)

'''
names=re.findall(r'^(?:def|theorem) ([A-Za-z0-9_]+)',source,re.M)
assert len(names)==6
for name in names:
    source+='set_option pp.all true in\n#check @'+name+'\n#print axioms '+name+'\n'
source+='end ShielddSecurity.TransferSourceTypedInputProjection01\n'
(ROOT/'handwritten').mkdir()
(ROOT/'handwritten/TransferSourceTypedInputProjection01.lean').write_text(source)
s=(DIAG/'transfer-scalar-byte-equality-20261011-01/prepare.py').read_text()
def replace(a,b,count=1):
    global s
    assert s.count(a)==count,(a,s.count(a))
    s=s.replace(a,b)
replace("UPSTREAM = DIAG / 'transfer-scalar-padded-carry-20261011-03'", "UPSTREAM = DIAG / 'transfer-scalar-byte-equality-20261011-01'")
replace("POOL = DIAG / 'transfer-scalar-byte-equality-owned-floor-20261011-01'", "POOL = DIAG / 'transfer-source-typed-input-projection-owned-floor-20261011-01'")
replace("MODULE = 'TransferScalarByteEquality01'", "MODULE = 'TransferSourceTypedInputProjection01'")
s=s.replace("'runs/01-TransferScalarPaddedCarry01/stdout.txt'", "'runs/01-TransferScalarByteEquality01/stdout.txt'",1)
replace('assert len(current) == 6','assert len(current) == 4')
replace("records.append(('TransferScalarPaddedCarry01'", "records.append(('TransferScalarByteEquality01'")
replace("    'handwritten/TransferScalarPaddedCarry01.lean', 'project/ShielddSecurity/TransferScalarPaddedCarry01.lean']]", "    'handwritten/TransferScalarByteEquality01.lean', 'project/ShielddSecurity/TransferScalarByteEquality01.lean']]")
replace('assert len(records) == 90 and len(audits) == 848','assert len(records) == 91 and len(audits) == 852')
replace("'objects': 90", "'objects': 91")
s=s.replace('ninety-module','ninety-one-module').replace('848 inherited','852 inherited')
replace("'imports': ['ShielddSecurity.TransferScalarPaddedCarry01']", "'imports': ['ShielddSecurity.TransferScalarByteEquality01']")
replace('assert len(names) == 4','assert len(names) == 6')
replace("'fresh_audits': 4", "'fresh_audits': 6")
start=s.index('\nmapping = ');end=s.index('\ndomain = ',start)
scope='Concrete configuration installs source-shaped all-slot ordered Transfer input nullifier projection through finite four-word scalar serialization. Typed projection, exact ordered mathematical Montgomery values and canonical key bounds are derived without desired key vector/range premises. Six complete reports: three definitions/three theorems. Exact pinned Transfer input Nullifier field, body input iterator/accessor, all-slot map/collect before nullify_all and Nullifier byte-forwarding source shapes checked separately. Runtime action/field-to-word selectors and Rust iterator/Scalar/byte/codec/compiler/native trace semantics remain explicit. Zero native/control/certification credit.'
s=s[:start]+"\nmapping = {'runtime_sha': prior_mapping['runtime_sha'], 'runtime_sources': list(runtime_rows.values()),\n    'interfaces': prior_mapping['interfaces'] + ["+repr(scope)+"], 'scope': "+repr(scope)+"}"+s[end:]
anchor="mapping_file = ROOT / 'source-mapping.json'"
assert s.count(anchor)==1
s=s.replace(anchor,"mapping['action_projection_source_association'] = pin(ROOT/'context/source-projection-shape.json')\nprojectionAssociation = json.loads(Path(mapping['action_projection_source_association']['path']).read_bytes())\nfor row in projectionAssociation['runtime_sources']:\n    assert row['path'] not in runtime_rows or runtime_rows[row['path']] == row\n    runtime_rows[row['path']] = row\nmapping['runtime_sources'] = list(runtime_rows.values())\n"+anchor,1)
s=s.replace("plan['pins'] += wordContext +", "plan['pins'] += [mapping['action_projection_source_association']]\nplan['pins'] += wordContext +",1)
start=s.index("plan['source_repairs'] = ");end=s.index("\nplan['artifact_policy']",start)
s=s[:start]+"plan['source_repairs'] = 'Fresh concrete source-shaped ordered all-slot typed input configuration on exact 852-report/91-module qualified ancestry. Canonical range and mathematical projection derived from finite scalar serialization; actual action/word selector binding and Rust semantics remain explicit. All guards unchanged, no ancestor replay.'"+s[end:]
s=s.replace('SOURCE_SCALAR_TYPED_BYTE_KEY_VALUE_EQUALITY','SOURCE_TRANSFER_CONCRETE_TYPED_INPUT_PROJECTION')
s=s.replace('SCALAR_BYTE_EQUALITY_COMPLETE_NINETY_MODULE_CLOSURE_SELF_REVIEWED_UNRUN','SOURCE_TYPED_INPUT_PROJECTION_COMPLETE_NINETY_ONE_MODULE_CLOSURE_SELF_REVIEWED_UNRUN')
s=s.replace("'inherited_audits': 848", "'inherited_audits': 852")
(ROOT/'prepare.py').write_text(s)
print({'fresh_audits':6,'inherited_reports':852,'owned_modules':91,'native_correspondence_still_open':True})
