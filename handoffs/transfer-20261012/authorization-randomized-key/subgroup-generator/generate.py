from pathlib import Path
import argparse,json
root=Path(__file__).resolve().parent
ap=argparse.ArgumentParser();ap.add_argument('--output',type=Path,required=True);a=ap.parse_args();out=a.output.resolve();assert not out.exists();dst=out/'source-root/ShielddSecurity';dst.mkdir(parents=True)
for f in json.loads((root/'families.json').read_text()):
    name='AuthorizationRkCapture506'+f['name'];ps=f['point_start'];ar=f['arithmetic_start'];ac=f['assertion_start']
    t=f"""import ShielddSecurity.CapturedFourSubgroupConstructor88
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.{name}
open Compiler CompilerArithmeticTransport41 CompilerAssertionBlock51

def rename (column : Nat) : Nat :=
  if 14≤column ∧ column<21 then {ps}+(column-14)
  else if 22738≤column ∧ column<22802 then {22738+ar}+(column-22738)
  else column

def arithmeticRows : List Row :=
  CompilerColumnRenaming05.rows rename TransferFirstSubgroupData01.arithmeticRows.toList

def originalRows : List Row :=
  CompilerColumnRenaming05.rows rename TransferFirstSubgroupData01.originalRows.toList

noncomputable def arithmeticCheck : Bool := (List.range 64).all (fun index =>
  decide (CapturedFullArithmetic52.rowAt ({ar}+index)=arithmeticRows[index]?))
theorem arithmetic_checked : arithmeticCheck=true := by decide +kernel

theorem copy_checked : arithmeticRows[64]?=some (TransferFirstSubgroupData01.arithmeticRows[64]) := by decide +kernel

theorem length_checked : arithmeticRows.length=65 := by decide +kernel

theorem zero_fixed : rename 0=0 := by decide +kernel
theorem copy_fixed : rename copy=copy := by decide +kernel

noncomputable def assertionCheck : Bool := (List.range 6).all (fun index =>
  decide (CapturedFullRelation58.rowAt (177954+{ac}+index)=originalRows[64+index]?))
theorem assertion_checked : assertionCheck=true := by decide +kernel

variable {{F : Type}} [Field F] [CharP F p]
theorem from_arithmetic (rho : Nat → F)
    (sat : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) (linked : rho copy=rho 0) :
    Satisfies rho arithmeticRows := by
  intro row member
  obtain ⟨index,found⟩ := List.mem_iff_getElem?.mp member
  obtain ⟨before,_⟩ := List.getElem?_eq_some_iff.mp found
  rw [length_checked] at before
  by_cases arith : index<64
  · have position := of_decide_eq_true (List.all_eq_true.mp arithmetic_checked index (List.mem_range.mpr arith))
    exact sat ({ar}+index) (by omega) row (position.trans found)
  · have sameIndex : index=64 := by omega
    subst index
    have same := Option.some.inj (copy_checked.symm.trans found)
    subst row
    apply (CompilerAssertionBlock51.checked_iff copy _ _ CapturedSubgroupSelection87.copy_checked rho linked).mpr
    simpa [CompilerAssertionBlock51.Truth,CompilerAssertionBlock51.sourceLeft,CompilerAssertionBlock51.sourceRight,
      expressionValue,eval,CompilerArithmeticTransport41.copy,TransferFirstSubgroupData01.copy] using linked.symm

theorem pulled (rho : Nat → F)
    (sat : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) (linked : rho copy=rho 0) :
    Satisfies (fun column => rho (rename column)) TransferFirstSubgroupData01.arithmeticRows.toList :=
  (CompilerColumnRenaming05.satisfies_rows rename rho _).mp (from_arithmetic rho sat linked)

theorem complete (rho : Nat → F) (initial : Group.Point F) (imaginary : F)
    (zero : rho 0=1) (linked : rho copy=rho 0)
    (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954)
    (roles : CapturedFourSubgroupConstructor88.InputRoles (fun column => rho (rename column)) initial)
    (valid : Group.OnCurve (CapturedFirstSubgroup81.d:F) initial)
    (nonSquare : Group.NoUnitSquare (CapturedFirstSubgroup81.d:F)) (imaginarySquare : imaginary*imaginary=-1) :
    SatisfiesAt rho (fun index => CapturedFullRelation58.rowAt (177954+{ac}+index)) 6 := by
  have localRows := CapturedSubgroupActual86.original_from_constructed_inputs
    (fun column => rho (rename column)) initial imaginary
    (by simpa only [zero_fixed] using zero) (by simpa only [zero_fixed,copy_fixed] using linked)
    (pulled rho arithmetic linked) (CapturedFourSubgroupConstructor88.input_identity _ _ roles)
    valid nonSquare imaginarySquare
  have fullRows : Satisfies rho originalRows :=
    (CompilerColumnRenaming05.satisfies_rows rename rho _).mpr localRows
  intro index bound row found
  have position := of_decide_eq_true (List.all_eq_true.mp assertion_checked index (List.mem_range.mpr bound))
  exact fullRows row (List.mem_iff_getElem?.mpr ⟨64+index,position.symm.trans found⟩)
end ShielddSecurity.{name}

"""
    for n in ['rename','arithmeticRows','originalRows','arithmeticCheck','arithmetic_checked','copy_checked','length_checked','zero_fixed','copy_fixed','assertionCheck','assertion_checked','from_arithmetic','pulled','complete']:
        t+=f'set_option pp.all true in\n#check @ShielddSecurity.{name}.{n}\n#print axioms ShielddSecurity.{name}.{n}\n\n'
    if f['name']=='B05':
        start=t.index('def rename ');stop=t.index('noncomputable def arithmeticCheck')
        definitions=t[start:stop]
        base='import ShielddSecurity.CapturedFourSubgroupConstructor88\nset_option autoImplicit false\nset_option maxHeartbeats 900000\nset_option maxRecDepth 8192\nnoncomputable section\nnamespace ShielddSecurity.'+name+'\nopen Compiler CompilerArithmeticTransport41 CompilerAssertionBlock51\n'+definitions+'end ShielddSecurity.'+name+'\n'
        for n in ['rename','arithmeticRows','originalRows']:
            base+=f'set_option pp.all true in\n#check @ShielddSecurity.{name}.{n}\n#print axioms ShielddSecurity.{name}.{n}\n\n'
        (dst/(name+'Base.lean')).write_text(base.rstrip()+'\n')
        imports=[]
        for chunk in range(4):
            checkName=name+'Check'+str(chunk);imports.append(checkName)
            text='import ShielddSecurity.'+name+'Base\nset_option autoImplicit false\nset_option maxHeartbeats 900000\nset_option maxRecDepth 8192\nnoncomputable section\nnamespace ShielddSecurity.'+checkName+'\nopen '+name+'\n'
            text+=f'theorem checked : (List.range 16).all (fun offset => decide (CapturedFullArithmetic52.rowAt ({ar}+({16*chunk}+offset))=arithmeticRows[{16*chunk}+offset]?)) = true := by decide +kernel\n'
            text+='end ShielddSecurity.'+checkName+'\nset_option pp.all true in\n#check @ShielddSecurity.'+checkName+'.checked\n#print axioms ShielddSecurity.'+checkName+'.checked\n'
            (dst/(checkName+'.lean')).write_text(text)
        t=t[:start]+t[stop:]
        t=t.replace('import ShielddSecurity.CapturedFourSubgroupConstructor88',''.join('import ShielddSecurity.'+n+'\n' for n in imports).rstrip())
        old='theorem arithmetic_checked : arithmeticCheck=true := by decide +kernel'
        proof='theorem arithmetic_checked : arithmeticCheck=true := by\n  apply List.all_eq_true.mpr\n  intro index member\n  have bound : index<64 := List.mem_range.mp member\n'
        for chunk in range(3):
            proof+=f'  by_cases before{chunk} : index<{16*(chunk+1)}\n  · have certificate := List.all_eq_true.mp {imports[chunk]}.checked (index-{16*chunk}) (List.mem_range.mpr (by omega))\n    have position : {16*chunk}+(index-{16*chunk})=index := by omega\n    simpa only [position] using certificate\n'
        proof+=f'  have certificate := List.all_eq_true.mp {imports[3]}.checked (index-48) (List.mem_range.mpr (by omega))\n  have position : 48+(index-48)=index := by omega\n  simpa only [position] using certificate'
        assert old in t;t=t.replace(old,proof)
        for n in ['rename','arithmeticRows','originalRows']:
            t=t.replace(f'set_option pp.all true in\n#check @ShielddSecurity.{name}.{n}\n#print axioms ShielddSecurity.{name}.{n}\n\n','')
    (dst/(name+'.lean')).write_text(t.rstrip()+'\n')
import hashlib,re
inventory={}
for source in dst.glob('*.lean'):
    inventory[source.stem]=dict(sha256=hashlib.sha256(source.read_bytes()).hexdigest(),audits=re.findall(r'#check @([A-Za-z0-9_.]+)',source.read_text()))
(out/'generation.json').write_text(json.dumps(inventory,sort_keys=True)+'\n');print(json.dumps(dict(modules=len(inventory),reports=sum(len(item['audits']) for item in inventory.values()))))
