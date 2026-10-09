"""Replay captured gate definitions with the actual signed zero assertion."""
import ast
import re
from . import transfer_relation as relation
from .generate_hash_round import linear, _signature_audits


def generate(source, index):
    index = relation.natural(index, 131)
    if index not in (0,1,2,*range(67,131)):
        raise relation.RelationError('captured lifecycle gate required')
    namespace = f'RuntimeTransferReceiverLifecycleGate{index:03}'
    if f'namespace ShielddSecurity.{namespace}\n' not in source:
        raise relation.RelationError('exact physical gate namespace required')
    def lc(text):
        values = ast.literal_eval(re.sub(r'\((-?\d+) : Int\)', r'\1', text))
        if text != linear(values):
            raise relation.RelationError('exact captured linear expression required')
        return values
    output = re.search(r'^def output : Linear := (\[[^\n]+\])$', source, re.M)
    raw = re.search(r'^def rawRows : List Row := \[\n(.*?)\]\ndef rows', source, re.M | re.S)
    if output is None or raw is None:
        raise relation.RelationError('closed physical rows and output required')
    pivot = lc(output[1])
    if len(pivot) != 1 or pivot[0][1] != 1:
        raise relation.RelationError('unit zero-assertion output required')
    rows = []
    for line in raw[1].splitlines():
        match = re.fullmatch(r'⟨(\[.*\]),(\[.*\])⟩,?', line)
        if match is None:
            raise relation.RelationError('exact captured row spelling required')
        rows.append((lc(match[1]),lc(match[2])))
    signs = [sign for sign in (1,-1) if ([(pivot[0][0],sign)],[]) in rows]
    if len(signs) != 1 or len(rows) != 4:
        raise relation.RelationError('unique signed physical zero assertion required')
    start = source.index('theorem constantLink :')
    text = source[:start]
    text += '''theorem constantLink : Compiler.checkRow modulus rawRows ⟨[(0,1),(200692,-1)],[]⟩ = true := by decide

theorem actual_gate {F : Type} [Field F] [CharP F modulus]
    (rho : Nat → F) (four : (4 : F) ≠ 0) (satisfied : Satisfies rho rawRows) :
    eval rho left * eval rho right = 0 := by
  have normalized := Compiler.unoutline_rows_sound rho 200692 rawRows satisfied constantLink
  have product := Compiler.checked_product_sound rho rows left right output auxiliary four normalized (by decide) (by decide)
'''
    if signs[0] == 1:
        text += '''  have asserted := Compiler.checked_assertion_sound rho rows output [] normalized (by decide)
  have zero : eval rho output = 0 := by simpa only [eval] using asserted
'''
    else:
        text += '''  have asserted := Compiler.checked_assertion_sound rho rows [] output normalized (by decide)
  have zero : eval rho output = 0 := by simpa only [eval] using asserted.symm
'''
    text += f'''  exact product.symm.trans zero
#print axioms constantLink
#print axioms actual_gate
end ShielddSecurity.{namespace}
'''
    return namespace, _signature_audits(text)
