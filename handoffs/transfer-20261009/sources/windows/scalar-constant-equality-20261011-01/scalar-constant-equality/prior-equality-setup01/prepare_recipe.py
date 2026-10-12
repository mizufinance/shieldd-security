from pathlib import Path
import hashlib,json
ROOT=Path(__file__).resolve().parent;DIAG=ROOT.parent
OLD=DIAG/'transfer-scalar-choice-masks-20261012-01'
assert not (ROOT/'prepare.py').exists()
def pin(p):
    p=Path(p);b=p.read_bytes();return {'path':str(p),'bytes':len(b),'sha256':hashlib.sha256(b).hexdigest()}
context=json.loads((OLD/'context/scalar-choice-masks-shape.json').read_text())
for key in ['subtle_locked_archive','locked_cargo_manifest','subtle_source_original','subtle_source_copy','scalar_source']:assert pin(context[key]['path'])==context[key]
source=Path(context['subtle_source_copy']['path']).read_text()
for exact in ['let x: $t_u = self ^ other;','let y: $t_u = (x | x.wrapping_neg()) >> ($bit_width - 1);','((y ^ (1 as $t_u)) as u8).into()','(1u8 & (!self.0)).into()']:assert exact in source
scalar=Path(context['scalar_source']['path']).read_text()
assert 'CtOption::new(tmp, !self.ct_eq(&Self::zero()))' in scalar
assert 'self.0[0].ct_eq(&other.0[0])' in scalar and '& self.0[3].ct_eq(&other.0[3])' in scalar
(ROOT/'context').mkdir();(ROOT/'context/subtle-2.6.1-lib.rs').write_bytes(Path(context['subtle_source_copy']['path']).read_bytes())
context['subtle_source_copy']=pin(ROOT/'context/subtle-2.6.1-lib.rs')
context.pop('actual_Choice_from_u8_check',None)
context['scope']='Source-shaped exact locked subtle2.6.1 UInt64 xor/wrapping-neg/or/high-bit/xor1/cast equality algorithm, Scalar four equality-byte ANDs and source invert Choice NOT. Word/vector equality and flag0/1 values derived, including modeled inversion refusal precisely at mathematical zero for canonical self. No assumed equality/flag result. Rust compiler/volatile barrier/all caller origins/timing/full Transfer remain open.'
(ROOT/'context/scalar-constant-equality-shape.json').write_text(json.dumps(context,indent=2,sort_keys=True)+'\n')
s=(OLD/'prepare.py').read_text().replace("MODULE = 'TransferScalarChoiceMasks01'","MODULE = 'TransferScalarConstantEquality01'")
s=s.replace('scalar_choice_masks_source_shape','scalar_constant_equality_source_shape').replace('scalar-choice-masks-shape.json','scalar-constant-equality-shape.json')
s=s.replace('assert len(names) == 20','assert len(names) == 12').replace("'fresh_audits': 20","'fresh_audits': 12")
s=s.replace('SCALAR_CHOICE_MASKS_COMPLETE_WORD_BRANCH_SELF_REVIEWED_UNRUN','SCALAR_CONSTANT_EQUALITY_COMPLETE_WORD_BRANCH_SELF_REVIEWED_UNRUN')
(ROOT/'prepare.py').write_text(s)
print({'exact_locked_equality_and_invert_flag_source_associations_verified':True,'public_declarations':12,'same_existing163_module_word_pool_reused_readonly':True,'all_execution_guards_unchanged':True})
