from pathlib import Path
import json,hashlib,re
J=Path(__file__).parent;W=J.parent;D=J/'candidate-fullpath258-262-review01';P=W/'mac-candidate-fullpath258-262-kernel-result01'
def read(v):
 b=Path(v['path']).read_bytes();assert len(b)==v['bytes']and hashlib.sha256(b).hexdigest()==v['sha256'];return b
es=json.loads((P/'source-object-receipt01.json').read_text());assert len(es)==60;sources={e['module']:read(e['source']).decode()for e in es}
audit=json.loads((D/'audit-result01.json').read_text());assert len(audit['modules'])==60 and audit['declarations']==253
gen=json.loads((D/'source-generation-review01.json').read_text());hist=json.loads((D/'source-history-review01.json').read_text());imp=json.loads((D/'import-guard-review01.json').read_text());assert gen['status']==hist['status']=='PASSED'and hist['attempts']==2355 and hist['failed']==156 and imp['qualified_modules']==60 and imp['complete_reports']==253
graph=json.loads((J/'source-integration-20261011-01/mac-source-closure2554.json').read_text())['custom_sources'];assert not(set(sources)&set(graph))and not(set(imp['custom_associations'])-set(graph)-set(sources))
assert {e['guard_sha256']for e in imp['execution_configs']}=={'d38270306c68c5353fe12a9433a67cf02793c1fd1be75593e2a8a40e94004d9a'}
original=json.loads((W/'mac-prefix-candidate258-source02/templates01.json').read_text())['modules'];assert len(original)==232
batch='\n'.join(sources[f'CandidateBatch262B{i:02d}']for i in range(13));positions=set();names=[]
for i in range(232):
 n=f'CandidateRows258P{i:03d}';s=original[n]['body'];first=s.index('namespace ShielddSecurity.');end=s.index('end ShielddSecurity.'+n)+len('end ShielddSecurity.'+n);body=s[first:end]
 if i<37:assert body in sources[n]
 else:assert batch.count(body)==1
 assert f'theorem rows (base : Nat → F) : Satisfies (CapturedFullRelation58.candidate base)'in body and 'SatisfiesAt'not in body and '(truth :'not in body and '(satisfied :'not in body
 ranges=[tuple(map(int,x))for x in re.findall(r'range_supported (\d+) (\d+)',body)];assert len(ranges)==1
 first,size=ranges[0];assert 0<=first<first+size<=3146;positions.update(range(first,first+size));names.append('ShielddSecurity.'+n+'.rows')
assert len(positions)==3134 and positions==set(range(3146))-set(range(2722,2734))
assert {x['name']for m in audit['modules']for x in m['audits']if x['name'].startswith('ShielddSecurity.CandidateRows258P')}==set(names)
selection=sources['CandidateMerkleSelection261']
for t in ["change index∈List.range' 2722 12++[200769] at member",'CapturedMerkleFirstSelection186.checked','CapturedArithmeticSelection252.range_supported 2722 12 (by omega)']:assert t in selection
positions.update(range(2722,2734));positions.update(range(3146,9506));assert positions==set(range(9506))
assembly=sources['CompilerCandidateAssembly259']
for t in ['theorem append_rows','theorem copy_stream','theorem copy_collection','theorem copy_packed','rowCheck p copy CapturedFullRelation58.rowAt 200770 200769 target=true','rowCheck copy CapturedFullRelation58.rowAt 200770 200769 target=true','CapturedArithmeticSelection252.copies_supported 1']:assert t in assembly
collectors={'CandidateCall04Rows259':['CapturedInitial73419Completion01.callRows','←CapturedCall04GlobalBinding168.partition'], 'CandidatePriorRows259':['CapturedPriorGlobalBinding170.headRows','CapturedPriorRows16Frame01.capturedPriorRows','←CapturedPriorGlobalBinding170.prior_partition'], 'CandidateThreeCallRows259':['TransferPoseidonThreeCallJoin15Program01.arithmeticRows','TransferPoseidonThreeCallJoin15Program01.originalRows','CompilerCandidateAssembly259.copy_packed','CapturedThreeCallGlobalBinding173.copy_checked'], 'CandidateRegistryRows259':['CapturedRegistryGlobalBinding175.arithmeticRows','RegistryWhole23.selectedRows','CapturedRegistryGlobalBinding175.copy_checked'], 'CandidateFirstMerkleRows259':['MerkleHash27Whole.selectedRows.take 412','←CapturedMerkleFirstGlobal186.partition','MerkleHash27Whole.selectedRows.drop 412','CapturedMerkleFirstGlobal186.copy_checked']}
for n,ts in collectors.items():
 s=sources[n];assert 'SatisfiesAt'not in s and '(satisfied :'not in s and '(truth :'not in s
 for t in ts:assert t in s
rest=sources['CandidateMerkleRest261'];assert '(i : Fin 15)'in rest and 'CompilerIndexedSlices183.chain_sound'in rest
for i in range(15):assert f'exact MerkleCandidateLevel255L{i:02d}.rows base'in rest
prior=sources['CandidateMerklePrior261']
for n in ['CandidatePriorRows259','CandidateThreeCallRows259','CandidateRegistryRows259','CandidateMerkleSelection261']:assert f'exact {n}.rows base' in prior
s=sources['CandidateMerkleMeaning261']
for t in ['theorem output (base : Nat → F) (one : base 0=1)','eval (CapturedFullRelation58.candidate base) MerklePath33AnchorData.output=','MerklePath33Meaning.meaning (CapturedFullRelation58.candidate base) 15','MerkleArithmeticConstruction253.candidate_zero base one','(CandidateMerklePrior261.rows base) (CandidateFirstMerkleRows259.rows base) (CandidateMerkleRest261.rows base)','(below : column<22738)','CapturedFullRelation58.candidate base column=CompilerVerifierLinks53.seeded base column','CapturedFullArithmetic52.outside _ column (Or.inl below)','MerklePath33Meaning.meaning_agrees _ _ (input_frame base) 15','theorem output_seeded (base : Nat → F) (one : base 0=1)','MerklePath33Meaning.meaning (CompilerVerifierLinks53.seeded base) 15']:assert t in s
assert 'SatisfiesAt'not in s and '(truth :'not in s and '(satisfied :'not in s and '(root :'not in s
scope=json.loads((P/'scope01.json').read_text());phase=[json.loads(x)for x in read(scope['history']['complete_phase_ledger']).decode().splitlines()];ledger=json.loads((P/'ledger-prefix01.json').read_text());assert phase==ledger['events']and len(phase)==46 and ledger['endpoint_attempt']==2355
for intent,result in zip(phase[::2],phase[1::2]):
 r=json.loads(read(result['receipt']));assert r['status']=='passed'and r['cleanup']['clean']and r['source']==intent['source']and r['module']==intent['module'];read(r['source']);read(r['stdout']);assert not read(r['stderr']).strip()
claim='Independent arithmetic candidate now has all selected arithmetic0..9505 and one distinct actual copy200769, and complete sixteen-level FIELD hash/path output. All232 checker-derived candidate proofs accept arbitrary base only;37 original physical modules retained,195 exact original namespace/theorem/proof bodies compiled in13 batches with identical preambles/headers deduplicated. Grouping changes no theorem or proof body. Six symbolic collectors combine734prior/1572Join/416registry/412first arithmetic with actual internally derived copy rows; first selection adds12 arithmetic, accepted15later families reused without compilation. Range union independently equals all9506 positions. Output field semantics requires only base0=1; all original columns below22738 retain exact seeded base, and path meaning is equal to that same seeded assignment. No fullSAT, desired row/hash/root truth, prior truth, or legal-witness premise supplies these conclusions. Legal root equality/actual anchor assertion, Boolean/word legal seed coherence, remaining assertion truths, concrete representation/SDK cryptography/native/full Transfer remain owned OPEN. Sixty newly published physical modules253 original reports comprise37 carried original prefix jobs plus23 phase286 jobs (13batches+10joins); no claim that60 jobs freshly ran in286. Complete2355history156failed and full46eventphase286 ledger preserved. Original guardd382 unchanged; map38 lossless archival independently reviewed123. No Root verifier/native/combined replay.'
r=dict(status='PASSED',modules=60,reports=253,new_modules=60,new_reports=253,inherited_modules=0,inherited_reports=0,source_pins=[e['source']for e in es],selected_history_attempts=2355,selected_history_failures=156,complete_phase_ledger=scope['history']['complete_phase_ledger'],exact_original_namespace_proofs=232,batched_original_proofs=195,current_phase_jobs=23,carried_original_prefix_jobs=37,selected_arithmetic_positions=9506,distinct_shared_copy=200769,scope=claim,full_transfer='OPEN',root_verifier_execution='NONE')
out=D/'source-semantic-review01.json';assert not out.exists();out.write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(dict(status='PASSED',modules=60,reports=253,original_proofs=232,batch_proofs_exact=195,current_phase_jobs=23,full_transfer='OPEN')))
