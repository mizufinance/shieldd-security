from pathlib import Path
import json,hashlib,re
J=Path(__file__).parent;W=J.parent;D=J/'registry-candidate205-255-review01';P=W/'mac-registry-candidate205-255-kernel-result01'
def read(v):
 b=Path(v['path']).read_bytes();assert len(b)==v['bytes'] and hashlib.sha256(b).hexdigest()==v['sha256'];return b
entries=json.loads((P/'source-object-receipt01.json').read_text()); inherited=json.loads((D/'exclusions204-reference-packet01/source-object-receipt01.json').read_text())
sources={e['module']:read(e['source']).decode() for e in entries+inherited};assert len(entries)==16 and len(inherited)==1 and len(sources)==17
audit=json.loads((D/'audit-result01.json').read_text()); ref=json.loads((D/'exclusions204-original-audit01.json').read_text());assert audit['declarations']==34 and ref['declarations']==6
hist=json.loads((D/'source-history-review01.json').read_text());assert hist['attempts']==2295 and hist['failed']==156
for name in ['source-generation-review01.json','exclusions204-generation-review01.json']:assert json.loads((D/name).read_text())['status']=='PASSED'
graph=json.loads((J/'source-integration-20261011-01/mac-source-closure2537.json').read_text())['custom_sources'];assert not(set(sources)&set(graph))
imp=json.loads((D/'import-guard-review01.json').read_text());assert imp['qualified_modules']==17 and imp['complete_reports']==40 and not(set(imp['custom_associations'])-set(graph)-set(sources))
allpositions=[]
for i in range(15):
 n=f'MerkleCandidateLevel255L{i:02d}';s=sources[n];start=3146+424*i
 assert f'theorem arithmetic (base : Nat → F) : Satisfies (CapturedFullRelation58.candidate base) (MerkleGlobalBody181.arithmeticRows {i}) := by' in s
 assert f'theorem rows (base : Nat → F) : Satisfies (CapturedFullRelation58.candidate base) (MerkleFamily32Whole.rows (F:=F) {i}) :=' in s
 assert '(satisfied :' not in s and 'SatisfiesAt' not in s and '(truth :' not in s
 ranges=[tuple(map(int,x)) for x in re.findall(r'exact CapturedArithmeticSelection252.range_supported (\d+) (\d+) \(by omega\)',s)]
 blocks=[(j,start+16*j,16 if j<26 else 8)for j in range(27)]
 if i==1:blocks=[b for b in blocks if b[0]!=23];blocks=[(j,f,32 if j==22 else z)for j,f,z in blocks]
 expected=[(f,z)for j,f,z in blocks];assert ranges==expected
 assert s.count('apply CapturedArithmeticSelection252.candidate_rows base ')==len(blocks)
 for j,first,size in blocks:
  target='CapturedMerkleGlobalPilot182' if i==0 and j==0 else 'CapturedMerkleWide223Pilot' if i==1 and j==22 else f'CapturedMerkleGlobalArithmetic184L{i:02d}B{j:02d}'
  assert f'{target}.indices {target}.rows {target}.checked' in s
  assert f"change ∀ index∈List.range' {first} {size},CapturedArithmeticSelection252.Supported index" in s
  allpositions.extend(range(first,first+size))
 assert f'rw [←CapturedMerkleGlobalLevel185L{i:02d}.partition]' in s and 'apply flatten_sound' in s
 assert f'MerkleArithmeticConstruction253.body_rows base {i} CapturedMerkleGlobalLevel185L{i:02d}.copy_checked (arithmetic base)' in s
assert allpositions==list(range(3146,9506)) and len(allpositions)==6360
s=sources['RegistrySemanticSound205']
for t in ['withHash (RegistryPointSemantic200.interpret','{c with unregulatedRing:=CapturedRegistryPointDomain75.sink}','RegistryNatural193.small RegistryNatural193.wide representation','registry := recover representation rho','asset := representation.value (rho 6)','assetAnchor := representation.value (rho 4)','regulated := flag','(flagMeaning : rho 10=(if flag then 1 else 0)) (one : rho 0=1)','(representation : CanonicalRepresentation F)','(nonSquare : Group.NoUnitSquare (CapturedFirstSubgroup81.d:F))','(imaginarySquare : imaginary*imaginary = -1)','(model : Group.StandardCurveModel J (CapturedFirstSubgroup81.d:F))','(standardOrder : ∀ point : J,(8*TransferCore.scalarOrder) • point=0)','TransferSem.RegistrySem (crypto c representation model) (witness template representation rho flag)','RegistryPointSemantic200.registry_points','MerkleNaturalRoot197.anchor','RegistryConditions201.value_bounds','RegistryConditions201.unregulated_order','RegistryExclusions204.all_guards','theorem exists_flag (rho : Nat → F)','rcases CapturedRegulatedSound163.role_cases rho satisfied with zero|oneFlag']:assert t in s
# The repaired exists_flag removes only an unused one premise and obsolete extra application argument.
old=(W/'mac-registry-semantic-sound205-source02/source-root/ShielddSecurity/RegistrySemanticSound205.lean').read_text()
assert old.replace('theorem exists_flag (rho : Nat → F) (one : rho 0=1)','theorem exists_flag (rho : Nat → F)').replace('role_cases rho satisfied one','role_cases rho satisfied')==s
s=sources['RegistryExclusions204'];assert s.count('apply CapturedGlobalRegistered74.full_forbidden_pair rho one satisfied ')==5
for i in range(5):assert f'full_forbidden_pair rho one satisfied {i} (by decide)' in s
assert '(regulated : rho 10≠0)' in s and '(representation : CanonicalRepresentation F)' in s and 'theorem all_guards' in s
original=json.loads(read(inherited[0]['receipt']));assert original['status']=='passed' and original['cleanup']['clean'] and len(original['audits'])==6
assert any(x['module']=='RegistryExclusions204' for x in hist['rejected'])
scope=json.loads((P/'scope01.json').read_text()); phase=[json.loads(x)for x in read(scope['history']['complete_phase_ledger']).decode().splitlines()]; selected=json.loads((P/'ledger-prefix01.json').read_text())['events']
assert len(phase)==68 and phase[:32]==selected and [x['kind']for x in phase]==['intent','result']*34
later=[]
for index,(intent,result) in enumerate(zip(phase[::2],phase[1::2])):
 assert intent['ordinal']==2280+index
 receipt=json.loads(read(result['receipt']));assert receipt['status']=='passed' and receipt['exit']==0 and receipt['cleanup']['clean']
 assert receipt['source']==intent['source'] and receipt['module']==intent['module'] and receipt['command']==intent['command']
 read(receipt['source']);read(receipt['stdout']);assert not read(receipt['stderr']).strip()
 assert receipt['lean_seconds']<=240 and receipt['peak_group_rss']<=4294967296
 if index>=16:later.append(dict(module=receipt['module'],receipt=result['receipt'],source=receipt['source'],qualified_in_this_packet=False))
assert len(later)==18 and later[-1]['module']=='CandidateRows258P017'
admission=json.loads(read(scope['history']['preflight_refusal_admission']));assert admission['approved'] and admission['module']=='CandidateRows258P018' and admission['prior_passed']==34 and admission['prior_ledger_sha256']==scope['history']['complete_phase_ledger']['sha256']
assert not any(x.get('module')=='CandidateRows258P018'for x in phase)
claim='All fifteen later Merkle families derive independent candidate arithmetic and actual shared copy truth internally: 6360 distinct arithmetic positions3146..9505 plus shared copy200769, 428 aggregate rows/425 distinct selected positions per family. Their final types accept arbitrary base only, without fullSAT, desired row truth or desired hash premises. Registry205 composes point, natural root, conditions and five exclusions into complete MODELED RegistrySem under explicit CanonicalRepresentation, StandardCurveModel, nonsquare/imaginary-square and global standardOrder interfaces; exists_flag derives Boolean role from fullSAT only. These concrete representation/deployed SDK crypto/model/order instances remain owned OPEN. Previously unpublished exact RegistryExclusions204 original1142 is recovered and independently full-type/axiom/source/generator/import/physical reviewed, 1module6original reports, no fresh replay; its prior failed original remains in complete156-failure history. Selected new endpoint2295 is16modules34reports; combined publication17modules40reports includes recovered dependency. Complete stopped284 phase through2313 preserved:18later passed prefix modules and P018 approved admission WITHOUT intent are provenance only and not qualified here. No native or combined replay; actual legal compatible seed/all assertions/full Transfer OPEN.'
r=dict(status='PASSED',new_modules=16,new_reports=34,inherited_modules=1,inherited_reports=6,modules=17,reports=40,source_pins=[e['source']for e in entries+inherited],selected_history_attempts=2295,selected_history_failures=156,complete_phase_ledger=scope['history']['complete_phase_ledger'],separate_later_prefix=later,preflight_admission_without_intent=scope['history']['preflight_refusal_admission'],recovered_original_dependency=inherited[0],concrete_instances='OWNED_OPEN',scope=claim,full_transfer='OPEN',root_verifier_execution='NONE')
out=D/'source-semantic-review01.json';assert not out.exists();out.write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(dict(status='PASSED',new_modules=16,new_reports=34,recovered_modules=1,recovered_reports=6,later_provenance_modules=18,full_transfer='OPEN')))
