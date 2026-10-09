"""Same-assignment IVK prefix and actual126 owned-window construction.

Initial row truth is supplied by the same successful SDKProgram scalar's owned
constructor. Actual sparse precompute exclusion and bounded window allocation
certificates preserve it. No prior truth or desired coordinate is a premise.
"""
from . import generate_transfer_ownership_native_constructor as native
from . import generate_transfer_ownership_prefix_frame as frames
from . import generate_transfer_ivk_native_program_rows as program_rows
from . import generate_transfer_ivk_reduction_join as joins


def generate(chunks,selections,ivk_data,ivk_export,reduction_data,reduction_export,
             parameter_root,expected_relation,readonly_lcs=()):
    native.generate(chunks,selections,ivk_data,ivk_export,reduction_data,reduction_export,
                    parameter_root,expected_relation,readonly_lcs)
    list(frames.generate(chunks[0],selections[0],ivk_data,ivk_export,reduction_data,reduction_export,
                         parameter_root,expected_relation,readonly_lcs))
    program_rows.generate(ivk_data,ivk_export,reduction_data,reduction_export,
                          parameter_root,expected_relation,readonly_lcs)
    copy=chunks[0]['metadata']['constant_copy']
    name='RuntimeOwnershipNativePrefix'
    aliases=dict(G='RuntimeOwnershipConstructorTrace',N='RuntimeOwnershipNativeConstructor',
        F='RuntimeOwnershipWindow000PrecomputeFrame',C='RuntimeOwnershipIvkPrefixFrame',
        B='RuntimeTransferIvkNativeProgramRows',P='RuntimeTransferIvkInversePrefixJoin',
        IV='RuntimeTransferIvkNativeInverseOwned',D='RuntimeHashBlock_authorization_ivk_0')
    source=''.join(f'import ShielddSecurity.{aliases[key]}\n' for key in ('N','F','C','B'))
    source+='''import ShielddSecurity.GroupCircuitPrefixTransport
set_option maxHeartbeats 300000
set_option maxRecDepth 4096
'''+f'namespace ShielddSecurity.{name}\n'
    source+=''.join(f'namespace {key} := {target}\n' for key,target in aliases.items())
    source+='''private theorem programs_segments (bits : Nat → Bool) :
    (G.segments bits).map Prod.fst = G.programs bits := by
  simp only [G.segments,G.programs,List.map_append,'''+','.join(
        f'RuntimeOwnershipConstructorChunk{start:03d}.programs' for start in range(0,126,16))+''']
variable {F : Type} [Field F] [CharP F Scalar.modulus]
variable {E S R K Q Signing J Encoded Native : Type} [AddCommGroup J]
variable (fq : GroupNativeSdk.FqBytes Q) (fr : GroupNativeSdk.FrBytes R)
variable (model : Group.StandardCurveModel J (RuntimeOwnershipWindow000Point0Cones.coefficientD : F))
variable (upstream : ShielddNativeSdk.Upstream E S R K Q Signing J fq fr
  (RuntimeOwnershipWindow000Point0Cones.coefficientD : F) model)
variable (backend : ShielddScalarReader.Backend (F := F) Encoded Native)
variable (codec : TransferReduction.CanonicalField F) (nk x y : Q) (sender : S) (scalar : R) (base : Nat → F)
variable (arithmetic : ShielddNativeIvkHash.FqArithmetic (F := F) Q fq)
variable (initial : ShielddNativeIvkSource.SdkInitial fq arithmetic)
variable (square : ShielddNativeIvkSdkProgram.SquarePrimitive (F := F) fq)
variable (primitives : ShielddViewingKeyAdmission.Primitives fq fr)
'''+f'''variable (one : base 0 = 1) (four : (4 : F) ≠ 0) (linked : base {copy} = base 0)
variable (accepted : ShielddViewingKeyAdmission.incomingScalar primitives
  (ShielddNativeIvkSdkProgram.ivk fq arithmetic initial square codec
    (Poseidon.castParameters D.parameters) nk x y) = some scalar)
include arithmetic initial square primitives one four linked accepted in
theorem ivk_original_rows_complete :
    Satisfies (N.completed fq fr model upstream backend codec nk x y sender scalar base) P.originalRows := by
  let ivk := IV.completeAssignment fq backend codec nk x y base
  have original : Satisfies ivk P.originalRows :=
    B.original_rows_complete fq fr arithmetic initial square primitives backend codec nk x y scalar base
      one four linked accepted
  have precomputed : Satisfies (N.precomputed fq fr model upstream backend codec nk x y sender base) P.originalRows :=
    F.rows_preserved fq fr model upstream backend sender ivk P.originalRows original C.outside
  have covered : GroupFixedCircuitBounds.RowsCovered 22738 {copy} G.beforeFrame P.originalRows := C.covered
  have result := GroupCircuitPrefixTransport.certified_preserves 22738 {copy} G.beforeFrame
    (N.precomputed fq fr model upstream backend codec nk x y sender base) P.originalRows
    (G.segments (N.nativeBits fr scalar)) covered (G.certified _) precomputed
  rw [programs_segments] at result
  exact result

include arithmetic initial square primitives one four linked accepted in
theorem prefix_and_windows_complete (imaginary : F)
    (nonSquare : Group.NoUnitSquare (RuntimeOwnershipWindow000Point0Cones.coefficientD : F))
    (imaginarySquare : imaginary*imaginary = -1) :
    Satisfies (N.completed fq fr model upstream backend codec nk x y sender scalar base)
      (P.originalRows ++ G.originalRows) := by
  have earlier := ivk_original_rows_complete fq fr model upstream backend codec nk x y sender scalar base
    arithmetic initial square primitives one four linked accepted
  have windows := (N.native_windows_complete fq fr model upstream backend codec nk x y sender scalar base
    arithmetic initial square primitives one linked accepted imaginary nonSquare imaginarySquare).1
  intro row member
  rcases List.mem_append.mp member with prior | current
  · exact earlier row prior
  · exact windows row current
#print axioms ivk_original_rows_complete
#print axioms prefix_and_windows_complete
'''
    return name,joins._qualify(source+f'end ShielddSecurity.{name}\n',aliases)
