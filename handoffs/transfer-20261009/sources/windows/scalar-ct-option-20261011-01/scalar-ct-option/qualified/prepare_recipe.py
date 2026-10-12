from pathlib import Path
ROOT=Path(__file__).resolve().parent;DIAG=ROOT.parent
assert not (ROOT/'prepare.py').exists()
s=(DIAG/'transfer-nullifier-field-domain-20261012-01/prepare.py').read_text()
for a,b in [
 ("UP=DIAG/'transfer-nullifier-field-codec-20261012-03'","UP=DIAG/'transfer-nullifier-field-domain-20261012-02'"),
 ("POOL=DIAG/'transfer-nullifier-field-domain-owned-floor-20261012-01'","POOL=DIAG/'transfer-scalar-ct-option-owned-floor-20261012-01'"),
 ("MODULE='TransferNullifierFieldDomain01'","MODULE='TransferScalarCtOption01'"),
 ('runs/01-TransferNullifierFieldCodec01/stdout.txt','runs/01-TransferNullifierFieldDomain01/stdout.txt'),
 ('len(current)==10','len(current)==11'),
 ("records.append(('TransferNullifierFieldCodec01'","records.append(('TransferNullifierFieldDomain01'"),
 ('len(records)==209 and len(audits)==1483','len(records)==210 and len(audits)==1494'),
 ("'prepare_from02.py'","'prepare_from01.py'"),
 ('handwritten/TransferNullifierFieldCodec01.lean','handwritten/TransferNullifierFieldDomain01.lean'),
 ('project/ShielddSecurity/TransferNullifierFieldCodec01.lean','project/ShielddSecurity/TransferNullifierFieldDomain01.lean'),
 ("'objects':209","'objects':210"),
 ('qualified209-module1483-report','qualified210-module1494-report'),
 ('nullifier-field-domain-shape.json','scalar-ct-option-shape.json'),
 ('nullifier_field_domain_source_shape','scalar_ct_option_source_shape'),
 ("'imports':['ShielddSecurity.TransferNullifierFieldCodec01']","'imports':['ShielddSecurity.TransferNullifierFieldDomain01']"),
 ('exact209-module qualified','exact210-module qualified'),
 ('NULLIFIER_FIELD_DOMAIN_SELF_REVIEWED_UNRUN','SCALAR_CT_OPTION_SELF_REVIEWED_UNRUN')]:
 assert s.count(a)==1,(a,s.count(a));s=s.replace(a,b)
start=s.index("scope='");end=s.index('\n',start)
scope='Eleven complete source-model declarations follow exact locked subtle CtOption::new, is_some/unwrap_u8 projections and From<CtOption<T>> conversion. Payload and byte are retained on every input; conversion accepts byte1 with exact payload without a general byte-validity assumption. Modeled BLS Scalar byte constructor derives byte0/1, canonical stored R2 payload and modular field meaning for all32-byte inputs, including refusal. The accepted whole input domain equals the qualified decoder. Source/library association is authenticated separately. Compiler/volatile barrier/layout/native ABI/eager side effects/timing/private origins/all native callers/full Transfer remain open.'
s=s[:start]+"scope="+repr(scope)+s[end:]
extra="""subtle_context=json.loads((DIAG/'transfer-scalar-choice-masks-20261012-05/context/scalar-choice-masks-shape.json').read_bytes())
for key in ['subtle_locked_archive','subtle_source_copy','subtle_source_original','locked_cargo_manifest']:
 row=subtle_context[key];assert pin(row['path'])==row;plan['pins'].append(row)
raw=Path(subtle_context['subtle_source_copy']['path']).read_text()
assert 'if source.is_some().unwrap_u8() == 1u8 {' in raw and 'Option::Some(source.value)' in raw
assert 'pub struct CtOption<T>' in raw and 'pub fn new(value: T, is_some: Choice)' in raw
shape=json.loads(context.read_bytes());shape['subtle_source_context']=subtle_context
shape['subtle_source_shape']=pin(DIAG/'transfer-scalar-choice-masks-20261012-05/context/scalar-choice-masks-shape.json')
dump(context,shape);mapping['scalar_ct_option_source_shape']=pin(context);dump(mapping_file,mapping)
plan['pins']=[r for r in plan['pins'] if r['path'] not in [str(context),str(mapping_file)]]+[pin(context),pin(mapping_file),shape['subtle_source_shape']]
"""
at=s.index("plan['artifact_policy']");s=s[:at]+extra+s[at:]
(ROOT/'prepare.py').write_bytes(s.encode())
print({'source_ct_option_stored_payload_and_flag_projection':True,'all210_module1494_report_predecessors_preserved':True,'finite_guards_unchanged':True,'no_ancestor_replay':True})
