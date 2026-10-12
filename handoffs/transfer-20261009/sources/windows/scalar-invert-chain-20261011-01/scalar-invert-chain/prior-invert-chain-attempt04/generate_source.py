from pathlib import Path
import hashlib,json,os,re
ROOT=Path(__file__).resolve().parent;DIAG=ROOT.parent
library=DIAG/'transfer-bounded-native-codec-20261011-02/context/runtime-library/bls12_381-0.8.0-scalar.rs'
data=library.read_bytes();sha=hashlib.sha256(data).hexdigest()
assert sha=='986f81e7fcb783a668bc4ab55721b22d497c5860cd7136e3cc600d2d9c321475'
text=data.decode();start=text.index('    pub fn invert(');end=text.index('\n    }',start)+6
body=text[start:end];begin=body.index('        let mut t0 =');finish=body.index('        CtOption::new')
chain=body[begin:finish]
instructions=[];exponents={};defined=set();lean=[]
def operand(value):
    if value=='self': return {'kind':'input'}
    index=int(value[1:]);assert index in defined,('uninitialized source operand',value)
    return {'kind':'register','index':index}
def expr(op): return '.input' if op['kind']=='input' else '(.register '+str(op['index'])+')'
def exponent(op): return 1 if op['kind']=='input' else exponents[op['index']]
for offset,line in enumerate(chain.splitlines()):
    statement=line.strip()
    if not statement: continue
    row={'original_statement':statement,'source_line':text[:start+begin].count('\n')+offset+1}
    match=re.fullmatch(r'square_assign_multi\(&mut t(\d+), (\d+)\);',statement)
    if match:
        target,count=map(int,match.groups());source=operand('t'+str(target))
        row.update(kind='square',target=target,source=source,count=count)
        result=exponent(source)*2**count
        lean.append('  .square '+str(target)+' '+expr(source)+' '+str(count))
    else:
        match=re.fullmatch(r'(?:let (?:mut )?)?t(\d+) = (self|t\d+)\.square\(\);',statement)
        if match:
            target=int(match[1]);source=operand(match[2]);count=1
            row.update(kind='square',target=target,source=source,count=count)
            result=exponent(source)*2
            lean.append('  .square '+str(target)+' '+expr(source)+' 1')
        else:
            match=re.fullmatch(r'(?:let (?:mut )?)?t(\d+) = (self|t\d+) \* &?(self|t\d+);',statement)
            if match:
                target=int(match[1]);left=operand(match[2]);right=operand(match[3])
            else:
                match=re.fullmatch(r't(\d+) \*= &?(self|t\d+);',statement)
                assert match,('unrecognized source statement',statement)
                target=int(match[1]);left=operand('t'+str(target));right=operand(match[2])
            row.update(kind='multiply',target=target,left=left,right=right)
            result=exponent(left)+exponent(right)
            lean.append('  .multiply '+str(target)+' '+expr(left)+' '+expr(right))
    defined.add(target);exponents[target]=result;instructions.append(row)
p=52435875175126190479447740508185965837690552500527637822603658699938581184513
assert exponents[0]==p-2 and len(instructions)==len(lean)
source='''import ShielddSecurity.TransferScalarInvertMachine01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferScalarInvertChain01
open TransferCanonicalWordEquality01 (CanonicalScalar)
open TransferScalarInvertMachine01
open TransferScalarPowInvariant01 (sourceZero)
open TransferScalarWordPrimitives01 (packWords)
open TransferScalarLittleEndianBytes01 (serializerBytes decodeLE)
open TransferScalarMontgomeryValue01 (montgomeryValue)
/-! Generated from the exact authenticated cached invert body. Each source
statement is retained in the generator context in original order. This
instance proves initialized reads, successful canonical payload, exact zero
refusal and a separate natural-exponent p-2 certificate. Field exponent/
inverse semantics and native Choice/compiler/caller coupling remain open. -/
def sourceOperandDecider (defined : List Nat) (operand : InvertOperand) :
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

def sourceInvertInstructions : List InvertInstruction := [
'''+',\n'.join(lean)+''']

theorem source_invert_instruction_reads_are_well_formed :
    sourceWellFormed [] sourceInvertInstructions := by
  letI := sourceChainDecider [] sourceInvertInstructions
  decide

theorem source_invert_final_result_register_is_initialized :
    0 ∈ sourceAssigned [] sourceInvertInstructions := by decide

theorem source_invert_natural_exponent_instance_is_modulus_minus_two :
    (do
      let result ← sourceExponentWalk (fun _ => none) sourceInvertInstructions
      result 0) = some (TransferBoundedNativeCodec01.nullifierModulus - 2) := by decide

def sourceInvertPayload (self : CanonicalScalar) : Option CanonicalScalar := do
  let registers ← sourceWalk self sourceInvertInstructions (fun _ => none)
  registers 0

def sourceInvert (self : CanonicalScalar) : Option CanonicalScalar :=
  if self.words = sourceZero.words then none else sourceInvertPayload self

theorem exact_source_invert_chain_derives_successful_canonical_payload (self : CanonicalScalar) :
    ∃ scalar, sourceInvertPayload self = some scalar := by
  have initial : registerInitialized (fun _ => none) [] := by
    intro index inside
    cases inside
  obtain ⟨registers, walked, initialized⟩ :=
    well_formed_symbolic_inversion_walk_derives_successful_initialized_result
      self sourceInvertInstructions (fun _ => none) [] initial source_invert_instruction_reads_are_well_formed
  obtain ⟨scalar, returned⟩ := initialized 0 source_invert_final_result_register_is_initialized
  refine ⟨scalar, ?_⟩
  change (sourceWalk self sourceInvertInstructions (fun _ => none)).bind (fun registers => registers 0) = some scalar
  rw [walked]
  exact returned

theorem exact_source_invert_zero_refusal_is_derived (self : CanonicalScalar) :
    sourceInvert self = none ↔ self.words = sourceZero.words := by
  by_cases zero : self.words = sourceZero.words
  · constructor
    · intro _
      exact zero
    · intro _
      exact if_pos zero
  · obtain ⟨scalar, returned⟩ := exact_source_invert_chain_derives_successful_canonical_payload self
    constructor
    · intro refused
      change (if self.words = sourceZero.words then none else sourceInvertPayload self) = none at refused
      rw [if_neg zero, returned] at refused
      cases refused
    · intro same
      exact False.elim (zero same)

theorem exact_returned_source_invert_derives_canonical_fields_and_exact_serialization
    (self : CanonicalScalar) :
    match sourceInvert self with
    | none => True
    | some scalar => packWords scalar.words.toList < TransferBoundedNativeCodec01.nullifierModulus ∧
        (serializerBytes scalar.words.toList).length = 32 ∧
        decodeLE (serializerBytes scalar.words.toList) < TransferBoundedNativeCodec01.nullifierModulus ∧
        decodeLE (serializerBytes scalar.words.toList) = montgomeryValue scalar.words := by
  cases sourceInvert self with
  | none => trivial
  | some scalar => exact ⟨scalar.canonical,
      TransferCheckedWordAcceptedInput01.every_original_typed_field_has_exact_32_byte_canonical_serialized_key scalar⟩
'''
names=re.findall(r'^(?:def|theorem) ([A-Za-z0-9_]+)',source,re.M)
assert len(names)==12
for name in names: source+='\nset_option pp.all true in\n#check @'+name+'\n#print axioms '+name+'\n'
source+='end ShielddSecurity.TransferScalarInvertChain01\n'
def atomic_new(path,data):
    assert not path.exists();path.parent.mkdir(parents=True,exist_ok=True)
    temp=path.with_name(path.name+'.tmp');assert not temp.exists()
    temp.write_bytes(data);os.replace(temp,path)
atomic_new(ROOT/'generated/TransferScalarInvertChain01.lean',source.encode())
context={'library':{'path':str(library),'bytes':len(data),'sha256':sha},'invert_body':body,'instructions':instructions,'register_indices':sorted(defined),'instruction_count':len(instructions),'python_exponent_crosscheck':str(exponents[0]),'scope':'Source parser and static initialized-read/exponent crosscheck only. Kernel qualification and field exponent/inverse/native correspondence separate. Generated Lean must be repaired through this generator, never edited directly.'}
atomic_new(ROOT/'context/scalar-invert-chain-shape.json',(json.dumps(context,indent=2,sort_keys=True)+'\n').encode())
print({'source_instruction_count':len(instructions),'generated_declarations':len(names),'parsed_registers':sorted(defined),'natural_exponent_crosscheck_matches_p_minus_two':True,'kernel_check':'UNRUN'})
