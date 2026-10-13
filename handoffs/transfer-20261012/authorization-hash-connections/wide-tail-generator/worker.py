from pathlib import Path
import json,sys
D=json.loads((Path(__file__).resolve().parent/'data.json').read_text());ci,bi,offset=map(int,sys.argv[2:]);ps=[x for x in D['phases']if x['call']==ci and x['block']==bi and x['round']>=2];out=(Path(sys.argv[1])/'source-root/ShielddSecurity');out.mkdir(parents=True,exist_ok=True)
for block in range(21):
 phases=ps[block*3:(block+1)*3];name=f'AuthorizationWideTail525C{ci}B{bi}B{block:02d}';imports=sorted(set(f'TransferPoseidonCall04Proof{a["round"]//8:02d}'for a in phases))
 s='import ShielddSecurity.AuthorizationPoseidonRowBridge521\nimport ShielddSecurity.CompilerWindowRenaming05\n'+''.join('import ShielddSecurity.'+n+'\n'for n in imports)+f'''set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.{name}
open Compiler CompilerAssertionBlock51 CompilerColumnRenaming05
open CapturedInitial73419Generic01 (p copy)
def ren := CompilerWindowRenaming05.swap 23076 396 {offset}
theorem fixed : ren 0=0 ∧ ren copy=copy := by decide +kernel
variable {{F : Type}} [Field F] [CharP F p]
''';audits=['fixed']
 for a in phases:
  r=a['round'];n=f'TransferPoseidonCall04R{r:02d}';cnt=len(a['indices'])-1;start=a['indices'][0]
  s+=f'''def rows{r} := CompilerColumnRenaming05.rows ren {n}.arithmeticRows.toList
theorem actual{r} : CompilerRowSlice63.check CapturedFullArithmetic52.rowAt {start} {cnt} rows{r}=true := by decide +kernel
theorem step{r} (rho : Nat → F) (one : rho 0=1) (linked : rho copy=rho 0)
    (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
    (fun i => eval rho (linear ren ({n}.after i)))=Poseidon.round
      (Poseidon.castParameters TransferPoseidonCall04Shared01.parameters) {r}
      (fun i => eval rho (linear ren ({n}.before i))) := by
  have target := CompilerRowSlice63.of_full_satisfies CapturedFullArithmetic52.rowAt 177954 {start} {cnt} rows{r} actual{r} (by decide) rho arithmetic
  have source := (satisfies_rows ren rho {n}.arithmeticRows.toList).mp target
  have copied := AuthorizationPoseidonRowBridge521.copy_satisfied (fun c => rho (ren c))
    (by simpa only [fixed.1,fixed.2] using linked)
  have sat : Satisfies (fun c => rho (ren c)) {n}.originalRows.toList := by
    change Satisfies (fun c => rho (ren c)) ({n}.arithmeticRows.toList++[AuthorizationPoseidonRowBridge521.copyRow])
    intro row member
    rcases List.mem_append.mp member with left|right
    · exact source row left
    · exact copied row right
  have result := {n}Proof.arbitrary_round_sound (fun c => rho (ren c))
    (by simpa only [fixed.1] using one) AuthorizationPoseidonPhase517.four_ne_zero sat
  simpa only [eval_linear] using result
''';audits+=['actual'+str(r),'step'+str(r)]
 s+=f'end ShielddSecurity.{name}\n'
 for n in audits:s+=f'set_option pp.all true in\n#check @ShielddSecurity.{name}.{n}\n#print axioms ShielddSecurity.{name}.{n}\n'
 (out/(name+'.lean')).write_text(s)
print('Prepared wide tail',ci,bi)
