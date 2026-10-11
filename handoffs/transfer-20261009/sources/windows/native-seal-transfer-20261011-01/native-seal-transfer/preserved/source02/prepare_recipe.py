"""Use reached finalization and supported-native getter contracts only."""
from pathlib import Path
ROOT=Path(__file__).resolve().parent;DIAG=ROOT.parent
old=DIAG/'transfer-native-seal-transfer-20261011-01'
assert not (ROOT/'prepare.py').exists() and not (ROOT/'handwritten').exists()
assert not (old/'events.jsonl').exists()
source=(old/'handwritten/TransferNativeSealTransfer01.lean').read_text()
a='''    (finalization : TransferGlobalCommitJoin01.FinalizationPendingFrame io
      (TransferPendingFiniteCodec01.encode (encodeObject encodeNative)) (TransferPendingFiniteCodec01.decode (decodeObject decodeNative)) io.project)'''
b='''    (finalization : (TransferHostEndBlock01.finalized io host height queued).state.objects (io.project TransferNullifierObjectKeys01.nullifierBytes) =
      (TransferGlobalCommitJoin01.sealedState (TransferPendingFiniteCodec01.encode (encodeObject encodeNative))
        (TransferPendingFiniteCodec01.decode (decodeObject decodeNative)) io.project host.active).objects (io.project TransferNullifierObjectKeys01.nullifierBytes))'''
assert source.count(a)==1
source=source.replace(a,b)
start=source.index('  rw [takeFrames.1]');end=source.index('  exact bounded_source_sct_seal',start)
source=source[:start]+'  rw [takeFrames.1, finalization]\n'+source[end:]
a='''    (typedGetter : io.ending.decodePending = TransferPendingFiniteCodec01.decode (decodeObject decodeNative))
    (finalization : TransferGlobalCommitJoin01.FinalizationPendingFrame io.ending
      (TransferPendingFiniteCodec01.encode (encodeObject encodeNative)) (TransferPendingFiniteCodec01.decode (decodeObject decodeNative)) project)'''
b='''    (typedGetter : ∀ native, nativeSupported native = true → io.ending.decodePending (.inl (encodeNative native)) = restore native)
    (finalization : (TransferHostEndBlock01.finalized io.ending host height final.2).state.objects (io.ending.project TransferNullifierObjectKeys01.nullifierBytes) =
      (TransferGlobalCommitJoin01.sealedState (TransferPendingFiniteCodec01.encode (encodeObject encodeNative))
        (TransferPendingFiniteCodec01.decode (decodeObject decodeNative)) io.ending.project host.active).objects (io.ending.project TransferNullifierObjectKeys01.nullifierBytes))'''
assert source.count(a)==1
source=source.replace(a,b)
start=source.index('  obtain ⟨_, _, _, _, state, _, _, _, taken, _⟩ :=')
end=source.index('\nset_option pp.all true in',start)
body='''  obtain ⟨_, _, _, _, state, frozen, _, _, taken, accepted, _, _, appRoot, _, _, _, _, idle, _, ready, _, _, roots, stored, _⟩ :=
    TransferEndToEnd01.whole_returned_pipeline_derives_exact_inputs_same_boundary_and_actual_physical_recovery io host height final.2 root success
  have initial : Invariant blockCapacity (parentPending (TransferPendingFiniteCodec01.decode (decodeObject decodeNative)) io.ending.project host.active) := by
    rw [projectedKeys, currentState]; exact nativeFinal.1
  have bounded : BoundedPending (parentPending (TransferPendingFiniteCodec01.decode (decodeObject decodeNative)) io.ending.project host.active) := by
    rw [projectedKeys, currentState]; exact nativeFinal.2.1
  have actualObject := actual_finalization_transfer_preserves_supported_native_sealed_pending_object
    encodeNative decodeNative io.ending host height final.2 initial bounded finalization state taken
  rw [projectedKeys, currentState, order.2.1] at actualObject
  have keyBounds := TransferBoundedNativeCodec01.bounded_whole_input_vector_from_native_action_projections requests nativeInputs
  have supported : nativeSupported (.sealed (allInputs requests)) = true := by
    simp only [TransferBoundedNativeCodec01.nativeSupported, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true]
    exact ⟨order.2.2.2.1, keyBounds⟩
  have exactTakenInputs : (parentPending io.ending.decodePending io.ending.project state).ordered = allInputs requests := by
    simp only [parentPending, TransferCurrentPendingReplay01.currentPending, apply_empty, projectedKeys, actualObject,
      typedGetter (.sealed (allInputs requests)) supported, restore]
  have exactAccepted : frozen.insertions.accepted = allInputs requests := accepted.trans exactTakenInputs
  exact ⟨state, taken, actualObject, order.2.2.1, order.2.2.2.1, keyBounds, frozen, exactAccepted, appRoot, ready, idle, roots, stored⟩
'''
source=source[:start]+body+source[end:]
source=source.replace('Every source seal stores the native Sealed enum representation of its current','The modeled source seal stores the native Sealed enum representation of its current')
source=source.replace('The native finalization field correspondence remains explicit and','The native finalization field correspondence at the actual reached state remains explicit and')
source=source.replace('primitive/temporal/crypto/library/ownership/OS contracts','primitive/temporal/crypto/library/ownership/OS contracts')
(ROOT/'handwritten').mkdir()
(ROOT/'handwritten/TransferNativeSealTransfer01.lean').write_text(source)
s=(old/'prepare.py').read_text()
a="POOL = DIAG / 'transfer-native-seal-transfer-owned-floor-20261011-01'";assert s.count(a)==1
s=s.replace(a,"POOL = DIAG / 'transfer-native-seal-transfer-owned-floor-20261011-02'")
start=s.index('\nmapping = ');end=s.index('\ndomain = ',start)
scope='Canonical shared-field bounded Pending modeled SCT seal stores supported native Sealed enum of its actual current ordered input. Pointwise finalization field contract only at actual observed reached height/state/queue, plus derived concrete state-transfer object frame, preserves exact native sealed object in returned state. Getter semantic contract quantifies only supported canonical native enum values, never unsupported ghost objects. Whole bounded default walk through ordinary source pipeline derives actual transferred native Sealed exact global allInputs, Nodup/cap32768/canonical Fq bounds, same source Frozen accepted inputs/application root/Ready/Idle/actual final roots and boundary. Directly reuses source pipeline result, without universal FinalizationPendingFrame or full ExtendedObject getter equality. Three complete proofs. Covers successful modeled step-commit/final pending storage and the direct modeled SCT sealing write/actual successful transfer; no blanket internal native-write trace correspondence. Native field-byte projection/typed enum embedding/Clone/Any/Arc/other-object/finite library, reached component returned field/panic/actual-trace/ownership/locks/snapshot coherence/separate ICS23/physical partition/hash/serde/OS and genuine native replay remain interfaces. Zero native/control/full certification.'
s=s[:start]+"\nmapping = {'runtime_sha': prior_mapping['runtime_sha'], 'runtime_sources': list(runtime_rows.values()),\n    'interfaces': prior_mapping['interfaces'] + ["+repr(scope)+"],\n    'scope': "+repr(scope)+"}"+s[end:]
anchor="plan['pins'] += mapping['runtime_sources']";assert s.count(anchor)==1
extra="unrun_ghost_wide = DIAG/'transfer-native-seal-transfer-20261011-01'\nassert not (unrun_ghost_wide/'events.jsonl').exists()\nplan['pins'] += [pin(unrun_ghost_wide/n) for n in ['prepare_recipe.py','prepare.py','plan.json','review.json','execute_bounded.py','source-mapping.json','handwritten/TransferNativeSealTransfer01.lean','project/ShielddSecurity/TransferNativeSealTransfer01.lean']]\n"
s=s.replace(anchor,extra+anchor)
start=s.index("plan['source_repairs'] = ");end=s.index("\nplan['artifact_policy']",start)
s=s[:start]+"plan['source_repairs'] = 'Prepared source01 UNRUN and withdrawn with zero proof credit; its universal ghost-state finalization/getter contracts replaced by actual reached-state finalization and supported-native getter only. Source02 theorem premises intentionally changed and proof derives inputs directly from exact native transferred object and source pipeline. Original frozen source retained; all physical and per-run guards unchanged, no cumulative project quota introduced.'"+s[end:]
(ROOT/'prepare.py').write_text(s)
print({'fresh_proofs':3,'unrun_original_credit':0,'actual_reached_finalization':True,'getter_only_supported_native_values':True})
