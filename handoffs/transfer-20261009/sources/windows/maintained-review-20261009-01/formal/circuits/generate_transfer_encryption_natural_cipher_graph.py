"""Derive natural-number ciphertext equations from actual field assertions."""
import re
NAME='TransferEncryptionNaturalCipherGraph'
FIELD='RuntimeTransferEncryptionFieldCipherGraph'
GRAPH='RuntimeTransferEncryptionHashGraph'


def generate(cases,seeds):
    assert len(cases)==8 and seeds==[(0,12,10,8517),(1,17,16,8522),(2,15,13,8528),(3,21,20,8533)]
    assert [(name,call)for name,call,_ in cases]==[
        ('detection0',6),('detection1',7),('detection2',8),('detection3',9),
        ('core0_confirmation',11),('core0_amount',12),('core2_confirmation',14),('core2_amount',15)]
    source=f'''import ShielddSecurity.{FIELD}
import ShielddSecurity.CanonicalFieldArithmetic
set_option maxHeartbeats 400000
namespace ShielddSecurity.{NAME}
variable {{F : Type}} [Field F] [CharP F Scalar.modulus]
variable (codec : TransferReduction.CanonicalField F)
def hashNat (rho : Nat → F) (call : Nat) : Nat := codec.decode ({FIELD}.hashValue rho call)
def ciphertext (rho : Nat → F) (linear : Linear) : Nat := codec.decode (eval rho linear)
/-- The same modular addition used by the independent Transfer semantics.
This is the actual Fq modulus, not the distinct scalar subgroup order. -/
def addNat (left right : Nat) : Nat := (left + right) % Scalar.modulus
'''
    exports=[]
    for name,call,plaintext in cases:
        assert plaintext in (None,'[]','[(6,1)]','[(108486,1)]','[(4789,1)]',f'{GRAPH}.output 0')
        conclusion=f'hashNat codec rho {call}'
        add=plaintext not in (None,'[]')
        if plaintext==f'{GRAPH}.output 0':
            conclusion=f'addNat (hashNat codec rho 0) ({conclusion})'
        elif add:
            conclusion=f'addNat (codec.decode (eval rho {plaintext})) ({conclusion})'
        source+=f'''theorem {name}_natural (rho : Nat → F) (one : rho 0 = 1)
    (satisfied : Satisfies rho {FIELD}.rawRows) :
    ciphertext codec rho {FIELD}.{name} = {conclusion} := by
  unfold ciphertext
  rw [{FIELD}.{name}_sound rho one satisfied]
'''
        if add:
            source+='  rw [CanonicalFieldArithmetic.decode_add]\n'
        source+='  rfl\n'
        exports.append(f'ShielddSecurity.{NAME}.{name}_natural')
    for tier,_,secret,_ in seeds:
        source+=f'''theorem c2_seed{tier}_natural (rho : Nat → F) (one : rho 0 = 1)
    (satisfied : Satisfies rho {FIELD}.rawRows) :
    ciphertext codec rho {FIELD}.c2_{tier} =
      addNat (codec.decode ({FIELD}.seed{tier} rho)) (hashNat codec rho {secret}) := by
  unfold ciphertext
  rw [{FIELD}.c2_seed{tier}_sound rho one satisfied, CanonicalFieldArithmetic.decode_add]
  rfl
'''
        exports.append(f'ShielddSecurity.{NAME}.c2_seed{tier}_natural')
    source+=f'end ShielddSecurity.{NAME}\n'
    source+=''.join(f'set_option pp.all true in\n#check @{name}\n#print axioms {name}\n'for name in exports)
    assert len(exports)==12
    assert re.findall(r'^#check @([\w.]+)$',source,re.M)==re.findall(r'^#print axioms ([\w.]+)$',source,re.M)==exports
    assert not re.search(r'\b(sorry|admit|axiom|native_decide)\b',source)
    return source,exports
