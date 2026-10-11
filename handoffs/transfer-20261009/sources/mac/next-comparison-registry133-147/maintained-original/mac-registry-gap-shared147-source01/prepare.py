from pathlib import Path
W=Path('/Users/antoinecyr/Documents/Codex/2026-10-08/can/work');S=W/'mac-registry-gap-shared147-source01'
if S.exists():raise ValueError('fresh')
s=S.mkdir();old=(W/'mac-next-low-shared143-source01/template.lean').read_text();a=old.index('theorem legal_registry_global1466');decl=old[a:old.index(' := by',a)];decl=decl.replace('legal_registry_global1466','legal_registry_global1467');bodyStart=decl.index(' :\n    ((((');decl=decl[:bodyStart]+decl[bodyStart:].replace(' :\n    ((((',' :\n    ((((',1)
# Wrap existing conclusion only, preserving every earlier hypothesis and row-range conclusion.
start=decl.index(' :\n    ((((')+3;decl=decl[:start]+'('+decl[start:]+') ∧\n    SatisfiesAt (completed base initial w.registry.nextValue w.asset w.registry.value w.registry.audit.epoch w.registry.position)\n      (fun index => CapturedFullRelation58.rowAt (179421+index)) 1'
t='''import ShielddSecurity.CapturedRegistryGap146
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedRegistryGapShared147
open Compiler CompilerArithmeticTransport41 CompilerAssertionBlock51
variable {F : Type} [Field F] [CharP F p]
abbrev completed := CapturedRegistryGap146.completed (F:=F)
'''+decl+''' := by
  exact ⟨CapturedNextLowShared143.legal_registry_global1466 c w legal sinkMeaning base initial imaginary
    epoch position regulated asset registry px py cx cy nextMeaning zero binding valid nonSquare imaginarySquare,
    CapturedRegistryGap146.complete c w legal base initial regulated zero⟩
end ShielddSecurity.CapturedRegistryGapShared147
'''
(S/'template.lean').write_text(t);g=(W/'mac-lexicographic-comparison144-source05/generate.py').read_text().replace('LexicographicComparison144','CapturedRegistryGapShared147');a=g.index('audits=');b=g.index('\nt+=',a);g=g[:a]+"audits=['ShielddSecurity.CapturedRegistryGapShared147.'+n for n in ['completed','legal_registry_global1467']]"+g[b:];g=g.replace('Independent128-low-bit value and exact255-bit low/high recombination from seed bits. No target comparison/order/row truth premise.','One same assignment: all177954 actual arithmetic +1467 distinct assertions including legal Registry gap. Anchor178117 and other21349 assertion/link positions remainOPEN. Actual roles/preimage/curve/certificate premises explicit.');(S/'generate.py').write_text(g);(S/'prepare.py').write_bytes(Path(__file__).read_bytes())
