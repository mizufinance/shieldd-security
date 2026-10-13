from pathlib import Path
import json,argparse,hashlib,os
root=Path(__file__).resolve().parent
ap=argparse.ArgumentParser();ap.add_argument('--output',type=Path,required=True);a=ap.parse_args();out=a.output.resolve();assert not out.exists();pending=out.with_name(out.name+'.pending');pending.mkdir()
rows=json.loads((root/'rows.json').read_bytes());assert len(rows)==18
p=52435875175126190479447740508185965837690552500527637822603658699938581184513
def lc(values,raw=False):
 values=sorted((200692 if col==0 else col,k) for col,k in values)
 def coeff(k):return '((p:Int)-1)' if raw and k==p-1 else str(k)
 return '['+','.join('('+str(col)+','+coeff(k)+')' for col,k in values)+']'
entries=[];before=[(200692,1),(7729,-1)]
for index in range(9):
 bit=7730+index;maximum=bool(86399>>(index+8)&1);pivot=108462+2*index;aux=pivot+1
 after=[(200692,1),(bit,-1),(pivot,1)] if maximum else [(pivot,1)]
 pair='['+','.join('⟨'+lc(r[0],True)+','+lc(r[1],True)+'⟩' for r in rows[2*index:2*index+2])+']'
 entries.append('⟨'+str(bit)+','+str(maximum).lower()+','+lc(before)+','+lc(after)+','+str(pivot)+','+str(aux)+','+pair+'⟩');before=after
text="""import ShielddSecurity.ComparisonCertificate101
import ShielddSecurity.CompilerRowSlice63
import ShielddSecurity.CapturedFullArithmetic52
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.LastSecondComparison376
open Compiler CompilerArithmeticTransport41 CompilerAssertionBlock51 ComparisonCertificate101
"""
text+='def entries : List Entry := ['+','.join(entries)+']\n'
text+='def initial : Linear := [(7729,-1),(200692,1)]\ndef actualRows : List Row := entries.flatMap Entry.rows\n'
text+='noncomputable def productionCheck : Bool := chainCheck initial entries\ntheorem production_checked : productionCheck=true := by decide +kernel\n'
text+='noncomputable def rowCheck : Bool := CompilerRowSlice63.check CapturedFullArithmetic52.rowAt 85724 18 actualRows\ntheorem rows_checked : rowCheck=true := by decide +kernel\n'
text+='theorem output_exact : output initial entries=[(7738,-1),(108478,1),(200692,1)] := by rfl\n'
text+='variable {F : Type} [Field F] [CharP F p]\ntheorem semantic (rho : Nat → F) (one : rho copy=1)\n    (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :\n    eval rho (output initial entries)=rawScan rho (eval rho initial) entries :=\n  chain_sound rho initial entries one production_checked\n    (CompilerRowSlice63.of_full_satisfies CapturedFullArithmetic52.rowAt 177954 85724 18 actualRows rows_checked (by decide) rho arithmetic)\nend ShielddSecurity.LastSecondComparison376\n'
for name in ['entries','initial','actualRows','productionCheck','production_checked','rowCheck','rows_checked','output_exact','semantic']:
 n='ShielddSecurity.LastSecondComparison376.'+name;text+='\nset_option pp.all true in\n#check @'+n+'\n#print axioms '+n+'\n'
dest=pending/'source-root/ShielddSecurity/LastSecondComparison376.lean';dest.parent.mkdir(parents=True);dest.write_text(text);(pending/'generation.json').write_text(json.dumps(dict(source_sha256=hashlib.sha256(dest.read_bytes()).hexdigest(),rows_sha256=hashlib.sha256((root/'rows.json').read_bytes()).hexdigest()))+'\n');os.replace(pending,out);print('Generated checked17-bit last-second comparison source')
