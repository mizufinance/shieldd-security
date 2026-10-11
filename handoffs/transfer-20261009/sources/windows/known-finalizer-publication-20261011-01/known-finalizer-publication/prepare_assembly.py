"""Fresh03 endpoint retaining setup01 and failed parser02 with exact layout repair."""
from pathlib import Path
ROOT=Path(__file__).resolve().parent; DIAG=ROOT.parent
assert not (ROOT/'assemble.py').exists()
s=(DIAG/'transfer-known-finalizer-publication-endpoint-20261011-02/assemble.py').read_text()
s=s.replace("CURRENT = DIAG / 'transfer-known-finalizer-publication-20261011-02'", "CURRENT = DIAG / 'transfer-known-finalizer-publication-20261011-03'")
s=s.replace('transfer-known-finalizer-publication-checkpoint-20261011-02','transfer-known-finalizer-publication-checkpoint-20261011-03')
a="assert (failed/'handwritten/TransferKnownFinalizerPublication01.lean').read_bytes()==(CURRENT/'handwritten/TransferKnownFinalizerPublication01.lean').read_bytes()"
assert s.count(a)==1
b="""failed02=DIAG/'transfer-known-finalizer-publication-20261011-02'
for n in ['prepare_recipe.py','recipe_source.py','prepare.py','plan.json','review.json','execute_bounded.py','source-mapping.json','events.jsonl','handwritten/TransferKnownFinalizerPublication01.lean','project/ShielddSecurity/TransferKnownFinalizerPublication01.lean','runs/01-TransferKnownFinalizerPublication01/stdout.txt']:
    assert pin(failed02/n) in plan['pins']
    add(failed02/n,'rejected-kernel/02/'+n,'record update offside parser failure; zero proof/control credit')
old=(failed02/'handwritten/TransferKnownFinalizerPublication01.lean').read_text()
assert old==(failed/'handwritten/TransferKnownFinalizerPublication01.lean').read_text()
assert old.replace('verifiable := mergeWrites delta.cache.verifiable effects.verifiable,\\n    nonverifiable','verifiable := mergeWrites delta.cache.verifiable effects.verifiable, nonverifiable')==(CURRENT/'handwritten/TransferKnownFinalizerPublication01.lean').read_text()
"""
s=s.replace(a,b)
s=s.replace("'rejected_attempts': 1, 'rejected_setup_attempts': 1, 'rejected_kernel_attempts': 0", "'rejected_attempts': 2, 'rejected_setup_attempts': 1, 'rejected_kernel_attempts': 1")
s=s.replace('fresh02 current upstream stdout match narrowed once, proof source unchanged.', 'Fresh02 current upstream stdout match narrowed once and proof source unchanged; failed02 record update parser output retained. Fresh03 one record update line-break repair only; seven intended contracts and all finite guards unchanged.')
(ROOT/'assemble.py').write_text(s)
print({'fresh_reports':7,'inherited_reports':866,'owned_modules':93,'rejected_setup':1,'rejected_kernel':1})
