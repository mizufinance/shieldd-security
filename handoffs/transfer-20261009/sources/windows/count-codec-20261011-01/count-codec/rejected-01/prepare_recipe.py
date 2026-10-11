"""Reuse strict narrow recipe for symbolic big-endian count codec proofs."""
from pathlib import Path
import re
ROOT=Path(__file__).resolve().parent
DIAG=ROOT.parent
assert not (ROOT/'prepare.py').exists()
s=(DIAG/'transfer-ordinary-index-count-20261011-01/prepare.py').read_text()
def replace(a,b):
    global s
    assert s.count(a)==1,a
    s=s.replace(a,b)
replace("UPSTREAM = DIAG / 'transfer-ordinary-index-read-20261011-01'", "UPSTREAM = DIAG / 'transfer-ordinary-index-count-20261011-01'")
s=s.replace('transfer-ordinary-index-count-owned-floor-20261011-01','transfer-index-count-codec-owned-floor-20261011-01')
s=s.replace("MODULE = 'TransferOrdinaryIndexCountSource01'", "MODULE = 'TransferIndexCountCodec01'")
s=s.replace('TransferOrdinaryIndexReadSource01','TransferOrdinaryIndexCountSource01')
replace('assert len(current) == 7','assert len(current) == 6')
replace('assert len(records) == 21 and len(audits) == 250','assert len(records) == 22 and len(audits) == 256')
replace("'objects': 21", "'objects': 22")
s=s.replace('Complete twenty-one-module first owned root; 250 inherited full reports.','Complete twenty-two-module first owned root; 256 inherited full reports.')
replace('assert len(names) == 6','assert len(names) == 15')
start=s.index("mapping = {'runtime_sha'")
end=s.index("\nmapping_file =",start)
s=s[:start]+"""mapping = {'runtime_sha': prior_mapping['runtime_sha'], 'runtime_sources': prior_mapping['runtime_sources'],
    'interfaces': prior_mapping['interfaces'] + ['Concrete Nat-list byte codec requires actual Vec<u8> representation; symbolic base-256 value corresponds to Rust u64 big-endian operations by the retained runtime source, without a Rust semantics theorem'],
    'scope': 'Concrete big-endian u64 count codec uses finite symbolic width recurrences. Encoding length/range, decoding range, bounded decode-encode identity and Ordinal codec roundtrip are proved for all values. For valid real-byte representations, decode failure is exactly wrong length; absent count is zero and full u64 ordinal rejects increment. The instantiated mathematical Codec can feed the qualified current-overlay/whole Ordinary count proofs. Byte representation, Rust semantics, key/proof/token/store/tree/block/durability interfaces remain separate. No unrolled constraint walks, native execution, semantic negative control or full Transfer certification.'}
""".rstrip()+s[end:]
s=s.replace('CURRENT_OVERLAY_COUNT_DERIVES_WHOLE_ORDINARY_MALFORMED_OR_OVERFLOW_REFUSAL','SYMBOLIC_BIG_ENDIAN_U64_INDEX_COUNT_CODEC')
s=s.replace('ORDINARY_INDEX_COUNT_COMPLETE_TWENTY_ONE_MODULE_CLOSURE_SELF_REVIEWED_UNRUN','INDEX_COUNT_CODEC_COMPLETE_TWENTY_TWO_MODULE_CLOSURE_SELF_REVIEWED_UNRUN')
s=s.replace("'fresh_audits': 6, 'inherited_audits': 250", "'fresh_audits': 15, 'inherited_audits': 256")
s=s.replace('complete twenty-one-module owned root','complete twenty-two-module owned root')
s=s.replace('Fresh finite source consumes actual NV reads and derives malformed/overflow refusal through the qualified whole Ordinary source.','Fresh symbolic width lemmas instantiate the mathematical u64 index-count codec through the qualified current-overlay/whole Ordinary count closure.')
(ROOT/'prepare.py').write_text(s)
f=ROOT/'handwritten/TransferIndexCountCodec01.lean'
lean=f.read_text(); names=re.findall(r'^(?:structure|inductive|def|theorem) ([A-Za-z0-9_]+)',lean,re.M)
assert len(names)==15 and '#check' not in lean
audits='\n'.join('set_option pp.all true in\n#check @'+n+'\n#print axioms '+n for n in names)
lean=lean.replace('\nend ShielddSecurity.TransferIndexCountCodec01','\n'+audits+'\n\nend ShielddSecurity.TransferIndexCountCodec01')
f.write_text(lean)
print({'fresh_audits':15,'inherited_audits':256,'owned_modules':22})
