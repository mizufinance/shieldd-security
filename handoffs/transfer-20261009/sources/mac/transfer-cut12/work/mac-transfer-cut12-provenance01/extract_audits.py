"""Extract exact named Lean signatures, excluding preceding diagnostic text.

Provenance-only successor: existing immutable logs and receipts are read; no
Lean process, original producer file, proof source or object is changed.
"""
import argparse,hashlib,json,re,time
from pathlib import Path

PRODUCER_SHA='cf1511163550fb7e788df052bdef1837dd464f5cc7a0d6b17ab19f07f27f5a45'
ENVELOPE_SHA='288dd9601abaf54a7418e5f6ec3c0011efb742ebea827cbf31dab0902d2363ce'
def sha(path):return hashlib.sha256(path.read_bytes()).hexdigest()
def extract(text,name,expected_hash):
    signature_pattern=r'^@?'+re.escape(name)+r'\s*:[\s\S]*?(?=^\''+re.escape(name)+r'\')'
    signatures=re.findall(signature_pattern,text,re.M)
    assert len(signatures)==1,'named signature missing/duplicated: '+name
    signature=signatures[0].strip()
    digest=hashlib.sha256(signature.encode()).hexdigest()
    assert digest==expected_hash,'full signature differs from immutable receipt: '+name
    report_pattern=r"^'"+re.escape(name)+r"' (depends on axioms: \[[^\]]*\]|does not depend on any axioms)\s*$"
    reports=re.findall(report_pattern,text,re.M)
    assert len(reports)==1,'named axiom report missing/duplicated: '+name
    report=reports[0]
    if report.startswith('depends'):
        axioms=[x.strip() for x in report.removeprefix('depends on axioms: [').removesuffix(']').split(',') if x.strip()]
        assert set(axioms)<={'propext','Quot.sound','Classical.choice'},'unexpected axiom'
    return signature,report,digest
def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('--root',type=Path,required=True)
    parser.add_argument('--producer',type=Path,required=True)
    parser.add_argument('--envelope',type=Path,required=True)
    parser.add_argument('--output-dir',type=Path,required=True)
    args=parser.parse_args();started=time.monotonic()
    assert sha(args.producer)==PRODUCER_SHA and sha(args.envelope)==ENVELOPE_SHA
    producer=json.loads(args.producer.read_text());envelope=json.loads(args.envelope.read_text())
    assert envelope['producer_manifest_sha256']==PRODUCER_SHA
    original={**producer['files'],**envelope['entries']}
    def rehash_original():
        for relative,identity in original.items():
            path=args.root/relative
            assert path.is_file() and not path.is_symlink()
            assert sha(path)==identity['sha256'],'original sealed entry changed: '+relative
        assert sha(args.producer)==PRODUCER_SHA and sha(args.envelope)==ENVELOPE_SHA
    rehash_original()
    assert not args.output_dir.exists(),'successor output must be fresh'
    args.output_dir.mkdir(parents=True)
    summary_path=args.root/'outputs/mac-transfer-cut12/final-summary01.json'
    assert sha(summary_path)==producer['files'][str(summary_path.relative_to(args.root))]['sha256']
    summary=json.loads(summary_path.read_text());records=[];input_receipts=[]
    for accepted in summary['fresh']:
        receipt=args.root/accepted['receipt_path'];r=json.loads(receipt.read_text())
        assert sha(receipt)==accepted['receipt_sha256'] and r['status']=='passed'
        log=receipt.with_suffix('.log');assert sha(log)==r['log_sha256'];text=log.read_text()
        assert sorted(r['expected_signature_names'])==sorted(r['expected_axiom_names'])
        axiom_names=re.findall(r"^'([^']+)' (?:depends on axioms: \[[^\]]*\]|does not depend on any axioms)\s*$",text,re.M)
        assert sorted(axiom_names)==sorted(r['expected_axiom_names'])
        for name in r['expected_signature_names']:
            full_type,axioms,digest=extract(text,name,r['full_signature_sha256'][name])
            records.append(dict(name=name,full_type=full_type,axioms=axioms,full_type_sha256=digest,
                raw_log=str(log.relative_to(args.root)),raw_log_sha256=sha(log)))
        input_receipts.append(dict(path=str(receipt.relative_to(args.root)),sha256=sha(receipt),log_sha256=sha(log)))
    assert len(records)==61 and len({r['name'] for r in records})==61
    old_path=args.root/'outputs/mac-transfer-cut12/full-audits01.json';old=json.loads(old_path.read_text())
    assert [r['name'] for r in old]==[r['name'] for r in records]
    corrected=[]
    for previous,current in zip(old,records,strict=True):
        assert {k:v for k,v in previous.items() if k!='full_type'}=={k:v for k,v in current.items() if k!='full_type'}
        if previous['full_type']!=current['full_type']:
            corrected.append(current['name'])
            assert hashlib.sha256(previous['full_type'].encode()).hexdigest()!=previous['full_type_sha256']
    assert corrected==['ShielddSecurity.TransferCut12Proof01.legal','ShielddSecurity.TransferCut12Proof01.completed_materialized']
    result=args.output_dir/'full-audits-successor01.json';result.write_text(json.dumps(records,indent=2)+'\n')
    rehash_original()
    verification=args.output_dir/'verification01.json'
    verification.write_text(json.dumps(dict(status='passed',scope='Provenance-only exact signature extraction; no proof/Lean/object/source change',
        producer_sha256=PRODUCER_SHA,envelope_sha256=ENVELOPE_SHA,original_entry_paths_rehashed=len(original),
        original_full_audits_sha256=sha(old_path),successor_full_audits_sha256=sha(result),
        corrected_records=corrected,all_full_type_hashes_equal_receipts=True,records=61,
        all_stage_modules=7,all_stage_audits=61,root_new_closure_modules=3,root_new_closure_audits=39,
        inputs=input_receipts,executing_extractor_sha256=sha(Path(__file__)),seconds=time.monotonic()-started,kernel_runs=0),indent=2)+'\n')
    print(json.dumps(dict(status='passed',records=61,corrected=corrected,successor_sha256=sha(result),verification_sha256=sha(verification))))
if __name__=='__main__':main()
