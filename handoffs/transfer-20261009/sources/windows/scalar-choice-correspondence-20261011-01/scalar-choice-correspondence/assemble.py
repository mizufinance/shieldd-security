"""Seal the successfully-loaded SCT branch and exact manager callback join."""
import hashlib
import importlib.util
import io
import json
import tarfile
from pathlib import Path

ROOT = Path(__file__).resolve().parent
DIAG = ROOT.parent
CURRENT = DIAG / 'transfer-scalar-choice-correspondence-20261012-01'
CHECKPOINT = DIAG / 'transfer-scalar-choice-correspondence-checkpoint-20261012-01'
MODULE = 'TransferScalarChoiceCorrespondence01'

def pin(p):
    p = Path(p)
    data = p.read_bytes()
    return {'path': str(p), 'bytes': len(data), 'sha256': hashlib.sha256(data).hexdigest()}

def dump(p, obj):
    p.write_bytes((json.dumps(obj, indent=2, sort_keys=True) + '\n').encode())

archive = ROOT / 'portable-windows-scalar-choice-correspondence-endpoint01.tar.xz'
assert not archive.exists() and not (ROOT / 'manifest.json').exists()
spec = importlib.util.spec_from_file_location('sct_complete_auditor', CURRENT / 'execute_bounded.py')
m = importlib.util.module_from_spec(spec)
spec.loader.exec_module(m)
plan = json.loads((CURRENT / 'plan.json').read_bytes())
events = [json.loads(s) for s in (CURRENT / 'events.jsonl').read_text().splitlines()]
assert len(events) == 2 and events[-1]['result']['status'] == 'passed'
stdout = CURRENT / ('runs/01-' + MODULE + '/stdout.txt')
fresh = m.audit(stdout.read_text(), plan['targets'][0]['audit_names'])
assert len(fresh) == 6 and fresh == events[-1]['result']['audits']
declaration_kinds = __import__('re').findall(r'^(def|theorem|structure|inductive) ', m.code_only((CURRENT / ('handwritten/' + MODULE + '.lean')).read_text()), __import__('re').M)
assert len(declaration_kinds) == len(fresh)
assert declaration_kinds.count('inductive') == 0 and declaration_kinds.count('def') == 1 and declaration_kinds.count('theorem') == 5
assert pin(stdout) == events[-1]['result']['stdout']
for obj in events[-1]['result']['objects']:
    assert pin(obj['path']) == obj
pool = json.loads(Path(plan['owned_import_pool']['path']).read_bytes())
assert pool['objects'] == 207 and len(pool['inherited_public_reports']) == 1467
manager_endpoint = DIAG / 'transfer-scalar-inverse-correctness-endpoint-20261012-04'
manager_archive = manager_endpoint / 'portable-windows-scalar-inverse-correctness-endpoint01.tar.xz'
assert pin(manager_archive)['sha256'] == 'c1cf8c43c246819d4ef31db22beef07b482fddccf0bb3c13ef8036f6b774a428'
with tarfile.open(manager_archive, 'r:xz') as tar:
    manager_review = json.loads(tar.extractfile('review.json').read())
    manager_reference = json.loads(tar.extractfile('context/inherited-reference.json').read())
    manager_pool = json.loads(tar.extractfile('context/owned-composition-review.json').read())
    manager_plan = json.loads(tar.extractfile('qualified/plan.json').read())
    manager_events = [json.loads(s) for s in tar.extractfile('qualified/events.jsonl').read().decode().splitlines()]
    manager_stdout = tar.extractfile('reports/fresh-6-complete-declarations.txt').read().decode()
    manager_reports = m.audit(manager_stdout, manager_plan['targets'][0]['audit_names'])
assert len(manager_reports) == 6 and manager_reports == manager_review['fresh_audits'] == manager_events[-1]['result']['audits']
combined_reports = {**manager_pool['inherited_public_reports'], **manager_reports}
manager_selected = manager_pool['selected'] + [{'module': 'TransferScalarInverseCorrectness01',
    'source': manager_plan['targets'][0]['source'], 'object': manager_events[-1]['result']['objects'][0]}]
assert len(combined_reports)==1422 and len(manager_selected)==203
dependency_packages=[]
for dirname,filename,module,count,wanted in [
 ('transfer-scalar-pow-bit-integer-endpoint-20261012-03','scalar-pow-bit-integer','TransferScalarPowBitInteger01',6,'32b7290c2eed3d3501e7824a6a8ef647d55d967fd9bffee4620d27f5501973c3'),
 ('transfer-scalar-pow-field-endpoint-20261012-08','scalar-pow-field','TransferScalarPowField01',6,'2b6c2bd99648d804315ce27ffe86696d6f3911cf0bb381d0d15504ac180bd231'),
 ('transfer-scalar-choice-masks-endpoint-20261012-06','scalar-choice-masks','TransferScalarChoiceMasks01',21,'074bf306301458f5571f6cbf57739e48354160f4bed07afae545f7460f5cea1c'),
 ('transfer-scalar-constant-equality-endpoint-20261012-04','scalar-constant-equality','TransferScalarConstantEquality01',12,'ce16a3943bbe7f4f8977234e8cd6656288ae343b1f73495615e7115246c6ebac')]:
 endpoint=DIAG/dirname;carrier=endpoint/('portable-windows-'+filename+'-endpoint01.tar.xz')
 assert pin(carrier)['sha256']==wanted
 with tarfile.open(carrier,'r:xz') as tar:
  qplan=json.loads(tar.extractfile('qualified/plan.json').read())
  qevents=[json.loads(line) for line in tar.extractfile('qualified/events.jsonl').read().decode().splitlines()]
  qreview=json.loads(tar.extractfile('review.json').read())
  qpool=json.loads(tar.extractfile('context/owned-composition-review.json').read())
  qreference=json.loads(tar.extractfile('context/inherited-reference.json').read())
  report_name='reports/fresh-%d-complete-declarations.txt'%count
  qstdout=tar.extractfile(report_name).read().decode()
  qreports=m.audit(qstdout,qplan['targets'][0]['audit_names'])
  assert len(qevents)==2 and qevents[-1]['result']['status']=='passed'
  assert len(qreports)==count and qreports==qevents[-1]['result']['audits']==qreview['fresh_audits']
  assert json.loads((endpoint/'review.json').read_bytes())==qreview
  for name,report in qpool['inherited_public_reports'].items():assert combined_reports[name]==report
  known={row['module']:row for row in manager_selected}
  for row in qpool['selected']:
   assert known[row['module']]['source']==row['source'] and known[row['module']]['object']==row['object']
  assert set(combined_reports).isdisjoint(qreports);combined_reports.update(qreports)
  manager_selected.append({'module':module,'source':qplan['targets'][0]['source'],'object':qevents[-1]['result']['objects'][0]})
  dependency_packages.append({'module':module,'count':count,'archive':pin(carrier),'manifest':pin(endpoint/'manifest.json'),'review':pin(endpoint/'review.json'),'reference':qreference,'plan':qplan,'events':qevents,'report_name':report_name})
assert len(combined_reports)==1467 and combined_reports==pool['inherited_public_reports'] and len(manager_selected)==207

archive_source_cache={}
def original_lean_sources(carrier):
    key=carrier['path']
    if key not in archive_source_cache:
        assert pin(key)==carrier
        with tarfile.open(key,'r:xz') as tar:
            archive_source_cache[key]={name:tar.extractfile(name).read() for name in tar.getnames()
                if name.endswith('.lean') and name.startswith(('source/ShielddSecurity/','generated-source/ShielddSecurity/','handwritten-source/ShielddSecurity/'))}
    return archive_source_cache[key]
for selected in pool['selected']:
    original = next(r for r in manager_selected if r['module'] == selected['module'])
    assert selected['source'] == original['source'] and selected['object'] == original['object']
    for k in ['source', 'object', 'copy']:
        assert pin(selected[k]['path']) == selected[k]
    carriers = [pin(manager_archive)] + [item['archive'] for item in dependency_packages]
    def collect_archive_refs(value):
        if isinstance(value, dict):
            if 'archive' in value and isinstance(value['archive'], dict) and 'path' in value['archive']:
                carriers.append(value['archive'])
            for nested in value.values():
                collect_archive_refs(nested)
        elif isinstance(value, list):
            for nested in value:
                collect_archive_refs(nested)
    collect_archive_refs(manager_reference)
    for item in dependency_packages:collect_archive_refs(item['reference'])
    member = 'source/ShielddSecurity/' + selected['module'] + '.lean'
    found = False
    for carrier in {r['path']: r for r in carriers}.values():
        originals=original_lean_sources(carrier)
        candidates=[name for name in originals if name.endswith('/ShielddSecurity/'+selected['module']+'.lean')]
        for name in candidates:
            if originals[name]==Path(selected['source']['path']).read_bytes():
                found=True;break
        if found:break
    assert found, selected['module']
def core_floor_refs(value):
    if isinstance(value, dict):
        if 'core_floor' in value:
            yield value['core_floor']['original']
        for nested in value.values():
            yield from core_floor_refs(nested)
    elif isinstance(value, list):
        for nested in value:
            yield from core_floor_refs(nested)
assert manager_plan['external_floor']==plan['external_floor']
reference = {'scalar_inverse_correctness': {'archive': pin(manager_archive), 'manifest': pin(manager_endpoint / 'manifest.json'),
    'status': 'LOCALLY_QUALIFIED_AND_FULLY_TRANSPORTED; PARENT_ACCEPTANCE_SEPARATE', 'imported_complete_reports': len(manager_reports)},
    'ancestors': manager_reference, 'complete_owned_modules': pool['objects'], 'inherited_complete_reports': len(pool['inherited_public_reports']),
    'all_inherited_source_object_and_full_report_identities_verified': True,
    'scope': 'Exact two-hundred-three-module whole/current pending/durable reader/source capacity/block/seal/prepare/finite codec/writer/intent/participants/boundary staging/keys/reader/authenticated snapshot/recovery/durable write closure, with 1422 original inherited complete reports; original recovery selected once without replay; shared StateDelta and seventeen Readback reports included once. No ancestors replayed here.'}
reference['scope']='Complete203-module first owned root and1422 original complete reports: whole qualified inverse/prime/word branch reused once. Original field48-module packet unchanged; no ancestors replayed.'
reference['scalar_dependencies']=[{key:item[key] for key in ['module','count','archive','manifest','review','reference']} for item in dependency_packages]
reference['scope']='Complete207-module1467-report first import root: original inverse/prime and exact bit/power/masks/equality branches merged with matching shared source/object/full-report identities, no ancestor replay. Every full original sealed qualification/history archive remains referenced by exact identity.'
dump(ROOT / 'inherited-reference.json', reference)
records, payload = [], []

def add(p, name, role):
    p = Path(p)
    assert name not in {n for n, _ in payload}
    payload.append((name, p.read_bytes()))
    records.append({'archive_path': name, 'original': pin(p), 'role': role})

for name in ['prepare.py', 'prepare_recipe.py', 'execute_bounded.py', 'plan.json', 'review.json', 'source-mapping.json', 'events.jsonl']:
    add(CURRENT / name, 'qualified/' + name, 'exact successful source and unchanged strict guards')
add(CURRENT / ('handwritten/' + MODULE + '.lean'), 'source/ShielddSecurity/' + MODULE + '.lean', 'exact typed source word-mask/equality/power/inversion model composition')
capstone = DIAG/'transfer-capstone-plan-20261011-01/plan.json'
assert pin(capstone) in plan['pins'] and pin(capstone)['sha256']=='d6ab4913d7b42c52b32357ac04bfc3da58b7b162140c2556bba90915d40ca067'
add(capstone, 'context/handwritten-capstone-plan.json', 'planning only: explicit native temporal/poison/snapshot/ICS23/library/Host/ownership/OS/full gate obligations; zero evidence credit')

add(stdout, 'reports/fresh-6-complete-declarations.txt', 'all raw full types and permitted axioms')
add(plan['owned_import_pool']['path'], 'context/owned-composition-review.json', 'complete207-module first import root; no object bytes')
add(ROOT / 'inherited-reference.json', 'context/inherited-reference.json', 'verified1467 inherited complete reports and exact source/object identities')
for name in ['preservation_check.py', 'preservation.json']:
    add(CHECKPOINT / name, 'preservation/' + name, 'all protected/foreign/main/clean runtime identities preserved')
mapping = json.loads((CURRENT / 'source-mapping.json').read_bytes())
for key,filename in [('scalar_choice_correspondence_source_shape','scalar-choice-correspondence-shape.json'),('scalar_inverse_correctness_source_shape','scalar-inverse-correctness-shape.json')]:
    row=mapping[key];assert pin(row['path'])==row and row in plan['pins']
    add(row['path'],'context/'+filename,'exact public constants/qualified Lucas/order source identities; mathematical field interpretation, native binding separate')
row=mapping['scalar_invert_field_source_shape']
assert pin(row['path'])==row and row in plan['pins']
add(row['path'],'context/scalar-invert-field-shape.json','exact qualified word machine/source instance/mathematical operation sources; symbolic field exponent simulation, Fermat/native caller separate')
row=mapping['scalar_field_values_source_shape']
assert pin(row['path'])==row and row in plan['pins']
add(row['path'],'context/scalar-field-values-shape.json','exact qualified word operation source contracts and mathematical scope; modular proof derives field values, native compiler/caller binding separate')
row=mapping['scalar_extended_family_source_shape']
assert pin(row['path'])==row and row in plan['pins']
add(row['path'],'context/scalar-extended-family-shape.json','exact cached u64/random64-byte/conditional selection source bodies and explicit represented/excluded constructor inventory; static association only')
row=mapping['scalar_public_constants_source_shape']
assert pin(row['path'])==row and row in plan['pins']
add(row['path'],'context/scalar-public-constants-shape.json','exact cached five public PrimeField literal/binding blocks checked against source words; static association only')
row=mapping['scalar_invert_chain_source_shape']
assert pin(row['path'])==row and row in plan['pins']
add(row['path'],'context/scalar-invert-chain-shape.json','exact cached source85 ordered statements/initialized register parsing/finite exponent crosscheck; generator source preserved; static source association separate from field inverse and native compiler/caller proof')
row=mapping['scalar_invert_machine_source_shape']
assert pin(row['path'])==row and row in plan['pins']
add(row['path'],'context/scalar-invert-machine-shape.json','exact authenticated cached source inversion addition chain and repeated-square helper; generic symbolic machine only, exact source instance/inverse/native binding separate')
row=mapping['scalar_pow_invariant_source_shape']
assert pin(row['path'])==row and row in plan['pins']
add(row['path'],'context/scalar-pow-invariant-shape.json','exact authenticated cached ZERO/ONE/R and reverse word/bit pow, pow_vartime and repeated-square source helper; static association only, exponent/native Choice/compiler/caller separate')
row=mapping['scalar_square_product_source_shape']
assert pin(row['path'])==row and row in plan['pins']
add(row['path'],'context/scalar-square-product-shape.json','exact authenticated cached optimized square MAC/shift/ADC/final reduction body; static association only')
row=mapping['scalar_square_diagonal_source_shape']
assert pin(row['path'])==row and row in plan['pins']
add(row['path'],'context/scalar-square-diagonal-shape.json','exact authenticated cached four diagonal MAC/ADC pairs and remaining square body; static association only')
row=mapping['scalar_square_shift_source_shape']
assert pin(row['path'])==row and row in plan['pins']
add(row['path'],'context/scalar-square-shift-shape.json','exact authenticated cached seven adjacent source shift assignments and remaining square body; static association only')
row=mapping['scalar_square_cross_source_shape']
assert pin(row['path'])==row and row in plan['pins']
add(row['path'],'context/scalar-square-cross-shape.json','exact authenticated cached six shrinking MAC row source and remaining square body; static association only')
row=mapping['scalar_input_family_source_shape']
assert pin(row['path'])==row and row in plan['pins']
add(row['path'],'context/scalar-input-family-shape.json','exact authenticated cached32-byte Choice/CtOption/R2 source body and explicit represented/excluded family inventory; static association only, native binding separate')
row=mapping['scalar_wide_byte_input_source_shape']
assert pin(row['path'])==row and row in plan['pins']
add(row['path'],'context/scalar-wide-byte-input-shape.json','exact authenticated cached eight ordered8-byte LE source slices/from_u512 call; static identity only, native slice/array/primitive/compiler/caller correspondence separate')
row=mapping['scalar_wide_constructor_source_shape']
assert pin(row['path'])==row and row in plan['pins']
add(row['path'],'context/scalar-wide-constructor-shape.json','exact authenticated cached R3 literal/eight word low-high split/two mul R2/R3 then add source body; static identity only, Rust/compiler/caller correspondence separate')
row=mapping['scalar_program_family_source_shape']
assert pin(row['path'])==row and row in plan['pins']
add(row['path'],'context/scalar-program-family-shape.json','exact authenticated cached from_raw/R2 and add/sub/mul/neg/double bodies; static association only, native family/caller/compiler binding separate')
row=mapping['scalar_canonical_neg_source_shape']
assert pin(row['path'])==row and row in plan['pins']
add(row['path'],'context/scalar-canonical-neg-shape.json','exact authenticated cached four SBB/MODULUS-self OR-zero wrapping-subtract mask source body; static identity only, Rust/compiler/caller correspondence separate')
row=mapping['scalar_canonical_sub_source_shape']
assert pin(row['path'])==row and row in plan['pins']
add(row['path'],'context/scalar-canonical-sub-shape.json','exact authenticated cached four SBB/four masked ADC source body; static identity only, Rust/compiler/caller correspondence separate')
row=mapping['scalar_canonical_add_source_shape']
assert pin(row['path'])==row and row in plan['pins']
add(row['path'],'context/scalar-canonical-add-shape.json','exact authenticated cached four ADC/sub-modulus source body; static identity only, Rust/compiler/caller correspondence separate')
row=mapping['checked_word_accepted_source_shape']
assert pin(row['path'])==row and row in plan['pins']
add(row['path'],'context/checked-word-accepted-source-shape.json','exact source ordered getter then iter/copied/collect and writer prepare call shapes; static association only, native vector/Copy/Scalar/compiler bindings separate')
row=mapping['fresh_snapshot_source_shape']
assert pin(row['path'])==row and row in plan['pins']
add(row['path'],'context/source-fresh-snapshot-shape.json','exact Snapshot object None/StateDelta new live default leaf/no layers/cache default declarations; static association, no durable/ICS23/native semantic credit')
row=mapping['checked_word_seal_source_shape']
assert pin(row['path'])==row and row in plan['pins']
add(row['path'],'context/checked-word-seal-shape.json','exact checked read/default/refusal/ordered-field put source shape, static association only')
row=mapping['sct_pending_read_source_shape']
assert pin(row['path']) == row and row in plan['pins']
add(row['path'],'context/sct-pending-read-shape.json','exact source typed enum/default/ordered clone/isSealed/ensureSealed cases; absence passes ensure while isSealed false; static association only')
row=mapping['checked_pending_put_source_shape']
assert pin(row['path']) == row and row in plan['pins']
add(row['path'],'context/checked-pending-put-shape.json','exact source inner Any TypeId read and mismatch panic before boxed pending object insert; static association only')
row=mapping['saturating_capacity_source_shape']
assert pin(row['path']) == row and row in plan['pins']
add(row['path'],'context/saturating-capacity-shape.json','exact source pending length saturating_add comparison and consensus32768 literal; static association only')
row=mapping['checked_pending_read_source_shape']
assert pin(row['path']) == row and row in plan['pins']
add(row['path'],'context/checked-pending-read-shape.json','exact source getter downcast-before-Clone leaf/layer/parent branches and pending absence default; static association only')
row = mapping['r2_decoder_payload_source_shape']
assert pin(row['path']) == row and row in plan['pins']
add(row['path'], 'context/r2-decoder-payload-shape.json', 'exact pinned R2 literal and decoder multiplication/CtOption static source association; native binding separate')
row = mapping['wide_reduction_source_shape']
assert pin(row['path']) == row and row in plan['pins']
add(row['path'], 'context/wide-reduction-shape.json', 'exact four4MAC/upperADC groups with deferredcarry; static source only')
row = mapping['wide_product_source_shape']
assert pin(row['path']) == row and row in plan['pins']
add(row['path'], 'context/wide-product-shape.json', 'exact16 MAC retained-row/carry static source association; primitive/compiler/final wide reduction binding separate')
row = mapping['scalar_decode_source_shape']
assert pin(row['path']) == row and row in plan['pins']
add(row['path'], 'context/scalar-decoder-shape.json', 'four exact LE word reads/four SBB/low choice bit shape; static source only; R2 conversion separate')
row = mapping['corrected_finalization_source_order']
assert pin(row['path']) == row and row in plan['pins']
add(row['path'], 'context/corrected-finalization-call-order.json', 'fresh reordered inventory follows authenticated source call positions; static association only')
row = mapping['fixed_finalization_source_association']
assert pin(row['path']) == row and row in plan['pins']
add(row['path'], 'context/fixed-finalization-source-association.json', 'exact known returned SCT/compact finishing call-order association, not exhaustive native trace proof')
row = mapping['known_finalization_source_association']
assert pin(row['path']) == row and row in plan['pins']
add(row['path'], 'context/known-finalization-source-association.json', 'six exact source literals and known put/delete call shapes; static association, no exhaustive native trace proof')
row = mapping['action_projection_source_association']
assert pin(row['path']) == row and row in plan['pins']
add(row['path'], 'context/action-projection-source-association.json', 'exact input field/all-slot ordered iterator map/batch and Nullifier byte-forwarding shapes; static association only')
row = mapping['serializer_byte_source_association']
assert pin(row['path']) == row and row in plan['pins']
add(row['path'], 'context/serializer-byte-source-association.json', 'exact pinned array and four ordered LE byte slices; shape only, not native primitive or trace semantics')
row = mapping['serializer_wrapper_source_association']
assert pin(row['path']) == row and row in plan['pins']
add(row['path'], 'context/serializer-wrapper-source-association.json', 'exact constants/zero-high-limbs/four rounds/final subtraction structure, no semantic or native credit')

for row in mapping['word_primitive_context']:
    assert pin(row['path']) == row and row in plan['pins']
    add(row['path'], 'context/word-primitive-context/' + Path(row['path']).name, 'raw pinned registry source and authenticated cached crate association, not semantic proof')

runtime_rows = {row['path']: row for row in mapping['runtime_sources']}
for producer in ['transfer-nullifier-batch-source-20261011-02', 'transfer-raw-effects-source-20261011-04']:
    association_file = DIAG / producer / 'source-mapping.json'
    association_pin = pin(association_file)
    assert association_pin in plan['pins']
    association = json.loads(association_file.read_bytes())
    assert association['runtime_sha'] == mapping['runtime_sha']
    add(association_file, 'context/ancestor-source-associations/' + producer + '.json', 'unchanged source association already pinned in the qualified plan; not semantic proof')
    for row in association['runtime_sources']:
        assert pin(row['path']) == row
        assert row['path'] not in runtime_rows or runtime_rows[row['path']] == row
        runtime_rows[row['path']] = row
    for interface in association.get('interfaces', []):
        if interface not in mapping['interfaces']:
            mapping['interfaces'].append(interface)
mapping['runtime_sources'] = list(runtime_rows.values())
for row in mapping['runtime_sources']:
    assert pin(row['path']) == row
    relative = Path(row['path']).relative_to(Path('C:/src/shieldd-pr160-844389ee')).as_posix()
    add(row['path'], 'runtime/' + relative, 'exact pinned Ordinary payload/SCT/current-volume source; semantic interfaces explicit')
add(DIAG.parent.parent / 'shieldd.lock', 'context/shieldd.lock', 'exact full runtime SHA')
add(ROOT / 'prepare_assembly.py', 'prepare_assembly.py', 'exact assembly derivation source')
correspondenceContext=json.loads((CURRENT/'context/scalar-choice-correspondence-shape.json').read_text())
for key in ['source_choice_masks','source_constant_equality','source_pow_field','source_inverse_correctness']:
 row=correspondenceContext[key];assert row in plan['pins'] and pin(row['path'])==row
 add(row['path'],'context/original-'+Path(row['path']).name,'exact original qualified source-model association; native correspondence remains separate')
for item in dependency_packages:
 prefix='dependency-qualification/'+item['module']+'/'
 with tarfile.open(item['archive']['path'],'r:xz') as tar:
  manifest=json.loads(tar.extractfile('manifest.json').read())
  original_rows={row['archive_path']:row['original'] for row in manifest['entries']}
  selected_names=['qualified/'+name for name in ['prepare.py','prepare_recipe.py','execute_bounded.py','plan.json','review.json','source-mapping.json','events.jsonl']]
  selected_names += ['source/ShielddSecurity/'+item['module']+'.lean',item['report_name']]
  for name in selected_names:
   row=original_rows[name];path=Path(row['path']);raw=tar.extractfile(name).read()
   assert pin(path)==row and raw==path.read_bytes()
   add(path,prefix+name,'exact original successful qualification source/full types/axioms/runner and unchanged physical guards; all complete original histories linked by exact sealed archive identity')
  add(item['manifest']['path'],prefix+'manifest.json','full original archive member manifest; histories preserved in the referenced full original archive')
  add(item['review']['path'],prefix+'review.json','full exact original qualification review')
priorAssembly=DIAG/'transfer-scalar-choice-correspondence-endpoint-20261012-01'
assert not (priorAssembly/'manifest.json').exists() and not list(priorAssembly.glob('*.tar.xz'))
for name in ['prepare_assembly.py','assemble.py']:
 add(priorAssembly/name,'history/unrun-assembly01/'+name,'exact original unrun assembly; inherited status/schema labels corrected before sealing, proof unchanged and not replayed')
add(Path(__file__), 'assemble.py', 'exact assembly source')
review = {'status': 'SOURCE_WORD_MASK_POWER_AND_EQUALITY_FLAG_INVERSE_COMPOSITION_QUALIFIED',
    'fresh_sources': 1, 'fresh_definition_audits': declaration_kinds.count('def'), 'fresh_structure_audits': declaration_kinds.count('structure') + declaration_kinds.count('inductive'), 'fresh_theorem_audits': declaration_kinds.count('theorem'),
    'fresh_complete_public_audits': len(fresh), 'fresh_audits': fresh, 'inherited_complete_public_audits': len(pool['inherited_public_reports']),
    'inherited_reference': reference, 'compiler_result': events[-1]['result'], 'plan': pin(CURRENT / 'plan.json'),
    'interfaces': mapping['interfaces'], 'runtime_sha': mapping['runtime_sha'],
    'native_test_credit': 0, 'negative_control_credit': 0, 'rejected_attempts': 0, 'withdrawn_unrun_sources': 0, 'unprepared_setup_failures': 0, 'rejected_proof_credit': 0,
    'certification': False, 'full_transfer': 'OPEN',
    'scope': mapping['scope'] + ' Six complete declarations:one definition/five theorems. Exact original207-module1467-report dependency union, original successful qualification sources/types/axioms/guards and full original archive/history identities retained. No ancestor replay or native result inferred from hashes.'}
dump(ROOT / 'review.json', review)
add(ROOT / 'review.json', 'review.json', 'complete current audit and explicit load/clone/tree/panic limits')
manifest = {'schema': 'transfer-scalar-choice-correspondence-endpoint-v1', 'entries': records,
    'fresh_audits': len(fresh), 'inherited_audits': len(pool['inherited_public_reports']), 'inherited_reference': reference,
    'object_bytes_in_archive': 0, 'toolchain_bytes_in_archive': 0,
    'native_test_credit': 0, 'negative_control_credit': 0, 'certification': False, 'scope': review['scope']}
data = (json.dumps(manifest, indent=2, sort_keys=True) + '\n').encode()
(ROOT / 'manifest.json').write_bytes(data)
payload.append(('manifest.json', data))
with tarfile.open(archive, 'w:xz', preset=6) as tar:
    for name, data in sorted(payload):
        info = tarfile.TarInfo(name)
        info.size, info.mode, info.mtime = len(data), 0o644, 0
        tar.addfile(info, io.BytesIO(data))
with tarfile.open(archive, 'r:xz') as tar:
    assert len(tar.getmembers()) == len(payload)
    assert all(tar.extractfile(name).read() == data for name, data in payload)
assert all(pin(r['original']['path']) == r['original'] for r in records)
print(json.dumps({'archive': pin(archive), 'manifest': pin(ROOT / 'manifest.json'), 'review': pin(ROOT / 'review.json'),
    'entries': len(records), 'members': len(payload), 'fresh_audits': len(fresh), 'inherited_audits': len(pool['inherited_public_reports']),
    'native_test_credit': 0, 'certification': False}))
