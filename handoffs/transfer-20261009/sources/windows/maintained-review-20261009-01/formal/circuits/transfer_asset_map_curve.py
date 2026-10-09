"""Same-assignment actual image/selected-root row join to curve membership."""
from . import transfer_asset_map_choice as choice, transfer_asset_map_image as image


def generate(data, extracted, accepted_roles):
    from .generate_hash_round import _signature_audits
    # Reaccept the same metadata and original rows independently for both
    # dependencies. A shared hash cannot replace these source/LC/row checks.
    choice_name, _ = choice.generate(data, extracted, accepted_roles)
    image_name, _ = image.generate(data, extracted, accepted_roles)
    name='RuntimeTransferAssetMapImageCurve'
    source=f'''import ShielddSecurity.{choice_name}
import ShielddSecurity.{image_name}
set_option maxHeartbeats 200000
namespace ShielddSecurity.{name}
def rawRows : List Row := {choice_name}.rawRows ++ {image_name}.rawRows

theorem image_on_curve {{F : Type}} [Field F]
    [CharP F {choice_name}.modulus] [DecidableEq F]
    (rho : Nat → F) (one : rho 0 = 1) (four : (4 : F) ≠ 0)
    (satisfied : Satisfies rho rawRows) :
    Group.OnCurve (RuntimeJubjub.d : F) ({image_name}.actualImage rho) := by
  have point := {image_name}.rational_image rho one four
    (fun row member => satisfied row (List.mem_append.mpr (Or.inr member)))
  have curve := {choice_name}.rational_curve rho one four
    (fun row member => satisfied row (List.mem_append.mpr (Or.inl member)))
  rw [point]
  exact curve
#print axioms image_on_curve
end ShielddSecurity.{name}
'''
    return name,_signature_audits(source)
