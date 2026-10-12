from pathlib import Path
import subprocess,sys
ROOT=Path(__file__).resolve().parent;DIAG=ROOT.parent
OLD=DIAG/'transfer-scalar-invert-chain-20261011-03'
assert not (ROOT/'prepare.py').exists()
deciders='''def sourceOperandDecider (defined : List Nat) (operand : InvertOperand) :
    Decidable (operandInitialized defined operand) :=
  match operand with
  | .input => .isTrue True.intro
  | .register _ => inferInstance

def sourceInstructionDecider (defined : List Nat) (instruction : InvertInstruction) :
    Decidable (instructionReadsInitialized defined instruction) :=
  match instruction with
  | .square _ source _ => sourceOperandDecider defined source
  | .multiply _ left right =>
    match sourceOperandDecider defined left, sourceOperandDecider defined right with
    | .isTrue l, .isTrue r => .isTrue ⟨l, r⟩
    | .isFalse l, _ => .isFalse (fun h => l h.1)
    | _, .isFalse r => .isFalse (fun h => r h.2)

def sourceChainDecider (defined : List Nat) : (instructions : List InvertInstruction) →
    Decidable (sourceWellFormed defined instructions)
  | [] => .isTrue True.intro
  | instruction :: rest =>
    match sourceInstructionDecider defined instruction,
        sourceChainDecider (instructionTarget instruction :: defined) rest with
    | .isTrue first, .isTrue tail => .isTrue ⟨first, tail⟩
    | .isFalse first, _ => .isFalse (fun h => first h.1)
    | _, .isFalse tail => .isFalse (fun h => tail h.2)

'''
needle='sourceWellFormed [] sourceInvertInstructions := by\n  simp only [sourceInvertInstructions, sourceWellFormed, instructionReadsInitialized, operandInitialized] <;> decide'
replacement='sourceWellFormed [] sourceInvertInstructions := by\n  letI := sourceChainDecider [] sourceInvertInstructions\n  decide'
s=(OLD/'generate_source.py').read_text();assert s.count(needle)==1
s=s.replace(needle,replacement)
assert s.count('def sourceInvertInstructions : List InvertInstruction := [')==1
s=s.replace('def sourceInvertInstructions : List InvertInstruction := [',deciders+'def sourceInvertInstructions : List InvertInstruction := [')
assert s.count('assert len(names)==9')==1;s=s.replace('assert len(names)==9','assert len(names)==12')
(ROOT/'generate_source.py').write_text(s)
subprocess.run([sys.executable,'-B',str(ROOT/'generate_source.py')],check=True)
expected=(OLD/'generated/TransferScalarInvertChain01.lean').read_text().replace(needle,replacement).replace('def sourceInvertInstructions : List InvertInstruction := [',deciders+'def sourceInvertInstructions : List InvertInstruction := [')
new=(ROOT/'generated/TransferScalarInvertChain01.lean').read_text()
audit=''
for name in ['sourceOperandDecider','sourceInstructionDecider','sourceChainDecider']:
    audit+='\nset_option pp.all true in\n#check @'+name+'\n#print axioms '+name+'\n'
expected=expected.replace('\nset_option pp.all true in\n#check @sourceInvertInstructions',audit+'\nset_option pp.all true in\n#check @sourceInvertInstructions')
assert new==expected
s=(OLD/'prepare.py').read_text().replace("POOL = DIAG / 'transfer-scalar-invert-chain-owned-floor-20261011-03'","POOL = DIAG / 'transfer-scalar-invert-chain-owned-floor-20261011-04'")
s=s.replace('assert len(names) == 9','assert len(names) == 12').replace("'fresh_audits': 9","'fresh_audits': 12").replace('Three definitions/six theorems.','Six definitions/six theorems, including small recursive operand/instruction/walk deciders.')
at=s.index("plan['artifact_policy']")
extra="""failedInvertChainThird=DIAG/'transfer-scalar-invert-chain-20261011-03'
plan['pins'] += [pin(failedInvertChainThird/n) for n in ['generate_source.py','prepare_recipe.py','prepare.py','plan.json','review.json','execute_bounded.py','source-mapping.json','events.jsonl','context/scalar-invert-chain-shape.json','generated/TransferScalarInvertChain01.lean','project/ShielddSecurity/TransferScalarInvertChain01.lean','runs/01-TransferScalarInvertChain01/stdout.txt']]
"""
s=s[:at]+extra+s[at:];(ROOT/'prepare.py').write_text(s)
print({'recursive_decider_replaces_nested_class_search':True,'unchanged_85_source_instructions_and_contracts':True,'fresh_declarations':12,'prior_raw_artifacts':35})
