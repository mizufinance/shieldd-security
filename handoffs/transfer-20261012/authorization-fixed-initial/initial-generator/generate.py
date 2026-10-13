from pathlib import Path
import json
root=Path(__file__).resolve().parent
import argparse,os,hashlib
ap=argparse.ArgumentParser();ap.add_argument('--output',type=Path,required=True);a=ap.parse_args();assert not a.output.exists();out=a.output.with_name(a.output.name+'.pending');out.mkdir();dest=out/'source-root/ShielddSecurity';dest.mkdir(parents=True)
def showlc(t):return '['+','.join('('+str(c)+','+str(v)+')' for c,v in t)+']'
def showrows(rs):return '['+','.join('⟨'+showlc(a)+','+showlc(b)+'⟩' for a,b in rs)+']'
entries=[]
for e in json.loads((root/'entries.json').read_text()):
 entries.append('⟨'+','.join(showlc(t) for t in e['terms'])+','+str(e['position'])+','+showrows(e['rows'])+'⟩')
s='import ShielddSecurity.PointEqualityAdapter440\nimport ShielddSecurity.VariableWindowColumns449\nimport ShielddSecurity.AuthorizationFixedSelectors481B000\nset_option autoImplicit false\nset_option maxHeartbeats 900000\nset_option maxRecDepth 8192\nnoncomputable section\nnamespace ShielddSecurity.AuthorizationFixedInitialCapture498\nopen PointEqualityAdapter440\ndef entries : List Entry := ['+','.join(entries)+']\ntheorem checked : entries.all check=true := by decide +kernel\nend ShielddSecurity.AuthorizationFixedInitialCapture498\n'
for n in ['entries','checked']:s+='\nset_option pp.all true in\n#check @ShielddSecurity.AuthorizationFixedInitialCapture498.'+n+'\n#print axioms ShielddSecurity.AuthorizationFixedInitialCapture498.'+n+'\n'
s+='''
namespace ShielddSecurity.AuthorizationFixedInitialCapture498
open Compiler CompilerArithmeticTransport41 CompilerAssertionBlock51 VariableWindowColumns449
def selector : FixedSelectorAdapter480.Entry := AuthorizationFixedSelectors481B000.entries[0]
theorem selector_checked : FixedSelectorAdapter480.check selector=true :=
  List.all_eq_true.mp AuthorizationFixedSelectors481B000.checked _ (List.getElem_mem (by decide))
theorem rows_iff {F : Type} [Field F] [CharP F p] (rho : Nat → F)
    (one : rho copy=1) (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
    SatisfiesAt rho (fun i => CapturedFullRelation58.rowAt (177954+4028+i)) 2 ↔
      columnPoint rho 4019=Group.windowPoint (rho 3767) (rho 3768)
        (FixedSelectorAdapter480.base selector) (FixedSelectorAdapter480.twice selector)
        (FixedSelectorAdapter480.triple selector) := by
  have checked := List.all_eq_true.mp checked entries[0] (List.getElem_mem (by decide))
  have equivalence := PointEqualityAdapter440.equality_iff entries[0] checked rho
  have x : canonical p entries[0].expectedX=canonical p selector.outputX := by decide +kernel
  have y : canonical p entries[0].expectedY=canonical p selector.outputY := by decide +kernel
  rw [canonical_equal rho _ _ x,canonical_equal rho _ _ y] at equivalence
  have outputX : entries[0].outputX=[(4019,1)] := rfl
  have outputY : entries[0].outputY=[(4020,1)] := rfl
  rw [outputX,outputY] at equivalence
  simp only [eval,Int.cast_one,one_mul,add_zero] at equivalence
  rw [FixedSelectorAdapter480.coordinates selector selector_checked rho one arithmetic] at equivalence
  exact equivalence
end ShielddSecurity.AuthorizationFixedInitialCapture498
'''
for n in ['selector','selector_checked','rows_iff']:
 s+='\nset_option pp.all true in\n#check @ShielddSecurity.AuthorizationFixedInitialCapture498.'+n+'\n#print axioms ShielddSecurity.AuthorizationFixedInitialCapture498.'+n+'\n'
f=dest/'AuthorizationFixedInitialCapture498.lean';f.write_text(s);(out/'generation.json').write_text(json.dumps(dict(sourceSha256=hashlib.sha256(f.read_bytes()).hexdigest(),positions=[4028,4029]))+'\n');os.replace(out,a.output);print('Generated transmission equality entry')
