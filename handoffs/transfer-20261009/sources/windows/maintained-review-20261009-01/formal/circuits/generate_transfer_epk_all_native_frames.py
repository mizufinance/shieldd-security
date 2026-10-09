"""Concrete scalar-input and prior-publication frames for six EPK constructors."""
from . import transfer_relation as relation
from .generate_transfer_epk_write_support import _operands
from .generate_hash_round import _signature_audits


def roles(pairs):
    if not isinstance(pairs,list) or len(pairs)!=5 or [p.get('scope_id') for p in pairs]!=[1,2,3,4,5]:
        raise relation.RelationError('all five genuine original-to-target EPK pairs required')
    columns=[dict(p['restricted_map']) for p in pairs]
    for pair in pairs:_operands(pair)
    return [4930,*[c[4930] for c in columns]],[(4922,4923),*[(c[4922],c[4923]) for c in columns]]


def generate(pairs,writer):
    private,public=roles(pairs)
    if type(writer) is not int or not 0<=writer<=5:
        raise relation.RelationError('exact original or captured target writer required')
    tree=f'RuntimeTransferEpk{writer}ConstructiveWriteTree'
    patch=f'TransferEpkScope{writer}PatchedCompletion'
    name=f'RuntimeTransferEpk{writer}AllNativeFrame'
    kept=[0,200692,*private,*[column for point in public[:writer] for column in point]]
    if len(kept)!=len(set(kept)):
        raise relation.RelationError('captured protected native columns must be distinct')
    text=f'''import ShielddSecurity.{patch}
namespace ShielddSecurity.{name}
set_option maxHeartbeats 200000
set_option maxRecDepth 4096

def kept : List Nat := {kept}

theorem protected_checked : kept.all (fun column =>
    decide (FiniteColumnRenaming.lookup {tree}.tree column = none)) = true := by decide

theorem preserves {{F : Type}} [Field F]
    [CharP F 52435875175126190479447740508185965837690552500527637822603658699938581184513]
    (rho : Nat → F) (n : Nat) (column : Nat) (protectedColumn : column ∈ kept) :
    {patch}.construct rho n column = rho column :=
  {patch}.outside_column rho n column
    (of_decide_eq_true (List.all_eq_true.mp protected_checked column protectedColumn))

#print axioms protected_checked
#print axioms preserves
end ShielddSecurity.{name}
'''
    return name,_signature_audits(text)
