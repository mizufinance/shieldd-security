from generation_common import *
module='TransferPoseidonWidth3Prefix10AbsorbProof01';raw=(S/'absorption-proof-template.lean.txt').read_text();text,names=audited(raw,module);metadata('absorption-proof',__file__,[save(module,text)],dict(template_sha256=sha(raw.encode()),descriptor_sha256=DESCRIPTOR_SHA))
