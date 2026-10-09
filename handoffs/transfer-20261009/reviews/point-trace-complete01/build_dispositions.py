"""Generate immutable parent acceptance and structured successful audit evidence."""
import sys
assert sys.flags.isolated and sys.flags.dont_write_bytecode and sys.flags.no_site
import hashlib,json,re
from pathlib import Path
H=Path(__file__).resolve().parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
for root,expected,count in [(H,3144,247),(H.parent/'parent-point-order-review01',113,39)]:
 F=root/'frozen';m=json.loads((F/'manifest.json').read_bytes());r=json.loads((F/'receipt.json').read_bytes());review=json.loads((root/'opus55-review.json').read_bytes());audit=json.loads((root/'packet-review01.json').read_bytes())
 assert not review['is_error'] and 'claude-opus-5-5' in review['modelUsage']
 for n,x in m['files'].items():assert sha(F/n)==x['sha256'] and (F/n).stat().st_size==x['bytes']
 records=[]
 for name,leaf in r['modules'].items():
  out=F/'review-audit-text'/(name+'.txt');assert sha(out)==leaf['stdout_sha256'];text=out.read_text()
  facts={}
  for n,axioms in leaf['audit']['axioms'].items():
   hits=re.findall(r'^@?'+re.escape(n)+r'(?:\.\{[^}]*\})?\s*:[\s\S]*?(?=^\''+re.escape(n)+r'\')',text,re.M);assert len(hits)==1
   facts[n]=dict(full_signature=hits[0].strip(),full_signature_sha256=hashlib.sha256(hits[0].strip().encode()).hexdigest(),axioms=axioms)
  records.append(dict(module=name,source_sha256=leaf['audit']['original_source_sha256'],audited_source_sha256=leaf['audit']['candidate_sha256'],successful_stdout_sha256=sha(out),actual_exit=leaf['actual_exit'],declarations=facts))
 assert len(records)==count and sum(len(x['declarations']) for x in records)==expected
 p=root/'structured-type-axiom-audit01.json';assert not p.exists();p.write_text(json.dumps(dict(schema='parent-existing-successful-output-structured-evidence-v1',producer_manifest_sha256=sha(F/'manifest.json'),modules=records,declaration_audits=expected,parent_kernel_runs=0,full_transfer='OPEN'),indent=2)+'\n')
 if root==H:
  scope='359 additional actual Point operations; all369 candidate associations DATA; exact Scalar.order annihilation and base nonidentity on same actual Point; no exported full graph-link/native/cardinality theorem'
  limits='8566 raw resource samples independently parsed; composition disk peak1485558304B; first-chain disk peak not separately sampled'
  notes='Opus receipt-head observation resolved: exact execution heads are present in receipt.batches and independently verified by parent, chain8e55fc6 and endpoint9489b75; freeze7ea375d stays distinct'
 else:
  scope='One new theorem addOrderOf same actual Point base = Scalar.order;112 inherited-primality platform audits count zero new primality mathematics'
  limits='Raw resource samples omitted; worker-derived hash-bound JSON summaries inspected; scoped disk worker peak1487296294B'
  notes='Parent append-only audit-wrapper reconstruction refusal repaired to exact preserved prerequisite audit-strip/short-name transform; no Lean source change or kernel rerun'
 p=root/'review-disposition01.json';assert not p.exists();p.write_text(json.dumps(dict(status='accepted_scoped_checkpoint',actual_Opus_model='claude-opus-5-5',effort='high',review_sha256=sha(root/'opus55-review.json'),parent_audit_sha256=sha(root/'packet-review01.json'),structured_type_axiom_sha256=sha(root/'structured-type-axiom-audit01.json'),new_declared_axioms=False,scope=scope,resource_evidence_limit=limits,resolved_review_notes=notes,accepted_math_context='Exact concrete field/Point/StandardCurveModel/primality accepted separately; native deployment remains OPEN',kernel_runs_by_parent=0,final_certification_refresh=False,full_transfer='OPEN'),indent=2)+'\n')
 print(json.dumps(dict(root=str(root),modules=count,audits=expected,status='accepted_scoped_checkpoint')))
