"""Independent canonical original-field retention/publication and metadata correction review."""
from pathlib import Path
import argparse,json,hashlib,re,difflib
J=Path(__file__).resolve().parent;cases={'canonical-source-word-retention':('TransferCanonicalSourceWordRetention01',3,0,3),'canonical-source-publication':('TransferCanonicalSourcePublication01',5,2,3)};p=argparse.ArgumentParser();p.add_argument('label',choices=cases);a=p.parse_args();M,N,nd,nt=cases[a.label];D=J/('windows-'+a.label+'-review01');P=D/'packet01';S=P/'source/ShielddSecurity'/(M+'.lean');s=S.read_text()
def read(p):return json.loads(p.read_text())
def pin(p):
 b=p.read_bytes();return dict(path=str(p),bytes=len(b),sha256=hashlib.sha256(b).hexdigest())
plan=read(P/'qualified/plan.json');target=plan['targets'][0]['source'];assert len(S.read_bytes())==target['bytes']and hashlib.sha256(S.read_bytes()).hexdigest()==target['sha256'];assert any(z['path'].replace('\\','/').endswith('/handwritten/'+M+'.lean')and z['sha256']==target['sha256']and z['bytes']==target['bytes']for z in plan['pins'])
names=re.findall(r'^(?:def|theorem) ([A-Za-z0-9_]+)',s,re.M);assert names==re.findall(r'^#check @([^\n]+)',s,re.M)and len(names)==N;assert len(re.findall(r'^def ',s,re.M))==nd and len(re.findall(r'^theorem ',s,re.M))==nt and not(P/'unselected').exists()
old=read(P/'superseded-metadata/review.json');new=read(P/'review.json');allowed={'fresh_definition_audits','fresh_theorem_audits','metadata_correction'}
if a.label=='canonical-source-publication':allowed.add('inherited_reference')
assert set(old)<=set(new)and all(old.get(k)==v for k,v in new.items()if k not in allowed);assert old['compiler_result']==new['compiler_result']and old['fresh_audits']==new['fresh_audits'];assert new['fresh_definition_audits']==nd and new['fresh_theorem_audits']==nt and new['fresh_complete_public_audits']==N
original_manifest=read(P/'superseded-metadata/manifest.json');current_manifest=read(P/'manifest.json');previous={e['archive_path']:e['original']for e in original_manifest['entries']};current={e['archive_path']:e['original']for e in current_manifest['entries']};preserved=[]
for relative,original in previous.items():
 if relative.startswith(('source/','reports/','qualified/')):
  assert current[relative]==original;preserved.append(relative)
assert preserved and any(x.startswith('source/')for x in preserved)and any(x.startswith('reports/')for x in preserved)
history=read(P/'context/metadata-history.json');assert history==new['metadata_correction'];assert history['original_archive']['sha256']==('a73c5de332a59b0aa773caeb664400521dad3094b7b6599f31ecca29a20c6e0d'if nd==0 else'8aef5f2b045ce256cd441219bb5b046fab29b8459feda2493ca05316b41af6d1')
if nd==0:
 assert 'scalar : CanonicalScalar'in s and 'canonical_source_key_constructor_recovers_every_canonical_raw_vector'in s and 'source_key_word_encoder_recovers_entire_canonical_typed_scalar'in s and 'finite_field_list_roundtrip_follows_from_symbolic_pointwise_inverse'in s
 scope='Canonical typed source scalar, whose raw four-word representative is below the exact modulus, is recovered in full from its source key through constructed LE/R2 encoder. Raw words, proof-bearing typed scalar and exact ordered source list identity are derived; no caller inverse or desired output premise. Native private Scalar invariant/constructor/compiler/selector correspondence remains owned OPEN.'
else:
 assert 'returned : runCompleteBlock'in s and 'success : outcome.root = some root'in s and 'returned_whole_word_driver_derives_successful_checked_getter_and_exact_boundary'in s
 assert 'constructed_sealed_codec_retains_exact_original_canonical_source_fields'in s and 'stored :'in s and 'rw [stored]'in s
 scope='Returned constructed whole canonical source-driver execution plus root success derives reached sealed object retaining exact ordered original canonical fields, successful checked SCT getter, mathematical key projection, exact accepted insertions and application-root/Ready/Idle/physical-root/boundary properties. Final object/state/walk/codec inverse/canonical bound/getter/frame are consequences. Input selector produces CanonicalScalar in an explicit typed domain; older modeled driver and its primitive/host callbacks are not thereby an actual native Rust trace.'
scope+=' Original assembly metadata counters corrected from declaration kinds; complete qualification/source/object/full type/axiom reports unchanged, superseded metadata preserved, no Lean replay. Any/Clone/imbl/type/ownership/liveness/compiler/callee/OS/full native correspondence and full Transfer remain owned OPEN.'
r=dict(status='PASSED_SOURCE_HISTORY',kind='Independently reviewed canonical typed-source model and immutable metadata history; no verifier',source=pin(S),fresh_reports=N,metadata_correction=history,unchanged_original_qualification_entries=preserved,original_metadata=pin(P/'superseded-metadata/review.json'),assembly_delta=''.join(difflib.unified_diff((P/'superseded-metadata/assemble.py').read_text().splitlines(True),(P/'assemble.py').read_text().splitlines(True))),scope=scope,full_transfer='OPEN',native_execution='UNRUN');(D/'semantic-source-review01.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(dict(label=a.label,status=r['status'],reports=N,unchanged_qualification_entries=len(preserved))))
