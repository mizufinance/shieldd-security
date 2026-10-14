from pathlib import Path
import json,sys,hashlib
root=Path(__file__).resolve().parent;out=Path(sys.argv[1]);out.mkdir(exist_ok=False);dest=out/'source-root/ShielddSecurity';dest.mkdir(parents=True);inventory={}
def lc(t):return '['+','.join(f'({c},{v})' for c,v in t)+']'
def rows(rs):return '['+','.join('⟨'+lc(a)+','+lc(b)+'⟩' for a,b in rs)+']'
def op(e):return '⟨'+str(e['isAdd']).lower()+',['+','.join(map(lc,e['ports']))+'],'+str(e['arithmeticStart'])+','+rows(e['arithmeticRows'])+','+str(e['assertionStart'])+','+rows(e['assertionRows'])+'⟩'
def selector(e):return '⟨['+','.join(map(lc,e['ports']))+'],'+str(e['arithmeticStart'])+','+rows(e['arithmeticRows'])+','+lc(e['outputX'])+','+lc(e['outputY'])+'⟩'
for f in json.loads((root/'families.json').read_text()):
 name='PayloadInitial572F'+str(f['family']).zfill(2);start=f['points'];bits=f['bits'];pos=f['assertions'];sel=f['entries'][0]['selector']
 s='''import ShielddSecurity.PointEqualityAdapter440
import ShielddSecurity.VariableWindowColumns449
import ShielddSecurity.PayloadBase568
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.'''+name+'''
open Compiler CompilerArithmeticTransport41 CompilerAssertionBlock51 VariableWindowColumns449
'''
 s+='def doubleEntry : VariableOperationAdapter434.Entry := '+op(f['precompute'][0])+'\n'
 s+='def tripleEntry : VariableOperationAdapter434.Entry := '+op(f['precompute'][1])+'\n'
 s+='def selector : VariableSelectorAdapter437.Entry := '+selector(sel)+'\n'
 s+='def initialEntry : PointEqualityAdapter440.Entry := ⟨'+','.join([lc([[start+4,1]]),lc([[start+5,1]]),lc(sel['outputX']),lc(sel['outputY']),str(pos+4),rows(f['initialRows'])])+'⟩\n'
 for item,adapter in [('doubleEntry','VariableOperationAdapter434'),('tripleEntry','VariableOperationAdapter434'),('selector','VariableSelectorAdapter437'),('initialEntry','PointEqualityAdapter440')]:s+=f'theorem {item}_checked : {adapter}.check {item}=true := by decide +kernel\n'
 s+=f'''variable {{F : Type}} [Field F] [CharP F p]
theorem precompute_rows_iff (rho : Nat → F) (one : rho copy=1)
    (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
    (VariableOperationAdapter434.Rows rho doubleEntry ∧ VariableOperationAdapter434.Rows rho tripleEntry) ↔
      TransferOwnership.DoubleEquations (VariableWindowJoin443.point rho PayloadBase568.baseX PayloadBase568.baseY) (columnPoint rho {start}) ∧
      TransferOwnership.AddEquations (CapturedFirstSubgroup81.d:F) (columnPoint rho {start})
        (VariableWindowJoin443.point rho PayloadBase568.baseX PayloadBase568.baseY) (columnPoint rho {start+2}) := by
  rw [VariableOperationAdapter434.equations_iff doubleEntry doubleEntry_checked rho one arithmetic,
    VariableOperationAdapter434.equations_iff tripleEntry tripleEntry_checked rho one arithmetic]
  change (TransferOwnership.DoubleEquations
    (VariableWindowJoin443.point rho PayloadBase568.baseX PayloadBase568.baseY)
    (VariableWindowJoin443.point rho [({start},1)] [({start+1},1)]) ∧
    TransferOwnership.AddEquations (CapturedFirstSubgroup81.d:F)
      (VariableWindowJoin443.point rho [({start},1)] [({start+1},1)])
      (VariableWindowJoin443.point rho PayloadBase568.baseX PayloadBase568.baseY)
      (VariableWindowJoin443.point rho [({start+2},1)] [({start+3},1)])) ↔ _
  simp only [VariableWindowJoin443.point,columnPoint,eval,Int.cast_one,one_mul,add_zero]

theorem initial_rows_iff (rho : Nat → F) (one : rho copy=1)
    (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
    SatisfiesAt rho (fun i => CapturedFullRelation58.rowAt (177954+{pos+4}+i)) 2 ↔
      columnPoint rho {start+4}=Group.windowPoint (rho {bits+250}) (rho {bits+251})
        (VariableWindowJoin443.point rho PayloadBase568.baseX PayloadBase568.baseY)
        (columnPoint rho {start}) (columnPoint rho {start+2}) := by
  have equivalence := PointEqualityAdapter440.equality_iff initialEntry initialEntry_checked rho
  have x : canonical p initialEntry.expectedX=canonical p selector.outputX := by decide +kernel
  have y : canonical p initialEntry.expectedY=canonical p selector.outputY := by decide +kernel
  rw [canonical_equal rho _ _ x,canonical_equal rho _ _ y] at equivalence
  have outputX : initialEntry.outputX=[({start+4},1)] := rfl
  have outputY : initialEntry.outputY=[({start+5},1)] := rfl
  rw [outputX,outputY] at equivalence
  rw [VariableSelectorAdapter437.coordinates selector selector_checked rho one arithmetic] at equivalence
  change (SatisfiesAt rho (fun i => CapturedFullRelation58.rowAt (177954+{pos+4}+i)) 2 ↔
    VariableWindowJoin443.point rho [({start+4},1)] [({start+5},1)]=
      Group.windowPoint (eval rho [({bits+250},1)]) (eval rho [({bits+251},1)])
        (VariableWindowJoin443.point rho PayloadBase568.baseX PayloadBase568.baseY)
        (VariableWindowJoin443.point rho [({start},1)] [({start+1},1)])
        (VariableWindowJoin443.point rho [({start+2},1)] [({start+3},1)])) at equivalence
  simpa only [VariableWindowJoin443.point,columnPoint,eval,Int.cast_one,one_mul,add_zero] using equivalence
end ShielddSecurity.{name}
'''
 audits=['doubleEntry_checked','tripleEntry_checked','selector_checked','initialEntry_checked','precompute_rows_iff','initial_rows_iff']
 for a in audits:s+=f'set_option pp.all true in\n#check @ShielddSecurity.{name}.{a}\n#print axioms ShielddSecurity.{name}.{a}\n'
 p=dest/(name+'.lean');p.write_text(s);inventory[name]=dict(sha256=hashlib.sha256(p.read_bytes()).hexdigest(),audits=audits)
(out/'generation.json').write_text(json.dumps(inventory,indent=2)+'\n');print('generated two exact payload prefix adapters; kernel checks pending')
