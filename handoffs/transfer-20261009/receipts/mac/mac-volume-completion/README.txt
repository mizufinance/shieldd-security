M4: Exact maintained Transfer volume construction

Result
New module ShielddSecurity.TransferVolumeBranchCompletion proves:
  forall c base (i : LegalVolumeInputs c base),
  TransferSem.VolumeSem c {base with volume := construct c base i}.
The proof imports the byte-exact desktop-maintained TransferSem and TransferCore. It has no premise VolumeSem/TransferSem of the result, no assumed successor/nullifier/commitment/subject/day equations, no proof-verification predicate and no new cryptographic axiom. It computes every owned volume field and proves the exact target, parameterized over every Crypto, base witness and legal input value.

Construction
Inputs carry context, real/start flags, timestamp split, prior amount/blinding/position/path and successor blinding. The constructor computes dayStart (Ordinary86400*day;Fee0), subject hash of sender affine address+asset, predecessor volumeState, real successor prior+outbound (padding0), predecessor commitment, origin or previous-note nullifier, and real or padding successor commitment. Fee nullifier/commitment are0. Padding uses base.auth.nk and base.nonce, matching transfer.rs319 shared padding_seed; it does not use base.paddingSeed. Volume uses auth.nk, while note spending can use effectiveNK. No unrelated witness field changes; restore_full_record covers all fields, beyond the named preservation conjunction.

Legal prerequisites
Timestamp64,dayIndex48,second<=86399,exact timestamp split;context1or2;fee self;tracked real Ordinary+regulated+external;prior/candidate/dailyLimit128;priorPosition48;positive bounded outbound;tracked candidate<=limit;tracked origin prior0;tracked continuation authenticates the computed predecessor through the supplied24-level quaternary State path to base.anchor. These are independent input legality/membership requirements. Padding prior is allowed arbitrary within the unconditional candidate bound; a wallet can normalize it to0. Inactive startsNewDay is arbitrary, so the theorem includes both inactive flags beyond the finite M3 census. Conditional cryptographic membership itself is not reconstructed from raw circuit rows here.

Canonicality and complete frame
canonical_constructed_volume_fields uses the existing named CanonicalCrypto contract plus explicit prior/successor blinding canonical bounds and fieldsCanonical(pathFields priorSiblings). It derives bounds for all13 volume scalar fields and72 path siblings. canonical_witness_preserved also takes CanonicalWitness base and preserves every non-owned canonical field. constructed_canonical_volume_semantics joins these exact semantic and canonical targets. Generic VolumeSem theorem itself requires no hash codomain hypothesis; canonicality makes that additional contract explicit.

Branch and mutation evidence
Fee cannot track and external requires Ordinary are proved from independent legal prerequisites. Exact fee/origin/continuation/padding payload formulas are derived. Seven refusal lemmas reject changed nullifier,commitment,dayStart,invalidcontext,trackedsubject,continuationhead and a continuationpath whose computedroot differs fromanchor. An eighth specialized domain-substitution refusal explicitly requires the unequal computed hash outputs. There is no blanket domain-injectivity/collision-resistance assumption. Full native positive-first circuit controls and36 intersections remain in M3; these M4 refusal lemmas concern maintained semantics, not additional runtime tests.

Checks
21 named new theorem audits: only standard propext and Quot.sound; no Classical.choice, sorryAx or custom axioms. Final Lean4.30.0 compile with-j1,-M1024,400000 heartbeats passed in2.05seconds. Original Core/Sem sources compiled unchanged. Dependencies match recovered desktop manifests exactly (Mathlib v4.30.0 c5ea00351c28e24afc9f0f84379aa41082b1188f). Only122 required cached import modules were fetched;14MiB compressed and~166MiB uncompressed increase. Dependency sources total154MiB; no full Mathlib build/download. leantar used--jobs1. Failed proof attempts retained; partial audits with sorryAx in failed logs are not accepted evidence.

Source correspondence and boundaries
source-map.json identifies exact pinned volume.rs67–181,transfer.rs297–322,range.rs,tree.rs,runtimepari.rs181–227,and payloadselection422–467 with file and line hashes. This is reviewed manual correspondence. Numeric bounds and Boolean gating are algebraic/range obligations; subject/state/nullifier hashes and predecessor-root authentication are explicit computational interpretation/membership inputs. Native output construction agrees at the formula level. Canonical decomposition, Poseidon row/native equivalence, compiler assignment construction/shared columns, constant/public/committed columns and actual Rust decoded-object refinement remain separate obligations. This proves the requested semantic constructive volume component, not full RowsHold completeness or arbitrary-assignment soundness. The full Transfer status remainsOPEN.

Reproduce on prepared Mac project
python3 outputs/mac-volume-completion/recheck.py --project work/mac-volume-completion/project --log work/mac-volume-completion/replayed-audit.txt
Fresh equivalent project (network/installed Lean4.30.0 required;~0.5GiB)
python3 outputs/mac-volume-completion/prepare_project.py --project work/mac-volume-completion/project-new > work/mac-volume-completion/prepare-new.log 2>&1
python3 outputs/mac-volume-completion/recheck.py --project work/mac-volume-completion/project-new --log work/mac-volume-completion/replayed-new-audit.txt
Windows integration: install only new TransferVolumeBranchCompletion.lean under ShielddSecurity in the exact maintained project, then lake env lean-j1-M1024 source; the parent coordinates transport/review. Cached dependencies are standard Mathlib binaries addressed by exact source hashes. The fresh preparer is provided but has not been separately rerun; its steps match the executed dependency/cache/core preparation. Successful recheck tool was executed against the actual prepared project.

Artifacts
TransferVolumeBranchCompletion.lean;lean-audit.txt;results.json;input-identities.json;source-map.json;maintained-inputs byte-exact originals;recheck.py;prepare_project.py;CacheConfig.lean;development-evidence. Awaiting parent/desktop independent review and assembly.
