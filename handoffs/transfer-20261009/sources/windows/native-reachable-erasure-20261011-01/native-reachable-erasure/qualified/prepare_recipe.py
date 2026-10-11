"""Factor source walk into a small returned-value Option-bind lemma."""
from pathlib import Path
ROOT=Path(__file__).resolve().parent;DIAG=ROOT.parent
old=DIAG/'transfer-native-reachable-erasure-20261011-02'
assert not (ROOT/'prepare.py').exists() and not (ROOT/'handwritten').exists()
source=(old/'handwritten/TransferNativeReachableErasure01.lean').read_text()
anchor='theorem bounded_actual_request_step_erases_unsupported_encoder_ghosts'
i=source.index(anchor)
helper='''theorem option_bind_equality_from_actual_returned_values {S T : Type}
    (first second : Option S) (left right : S → Option T) (same : first = second)
    (tails : ∀ value, first = some value → left value = right value) :
    first.bind left = second.bind right := by
  cases first with
  | none => simp only [←same, Option.bind_none]
  | some value => simpa only [←same, Option.bind_some] using tails value rfl

'''
source=source[:i]+helper+source[i:]
start=source.index('    simp only [walk, sameStep]');end=source.index('\nset_option pp.all',start)
body='''    change (step (TransferPendingFiniteCodec01.encode (encodeObject encodeNative))
      (TransferPendingFiniteCodec01.decode (decodeObject decodeNative)) project request parent queued).bind
        (fun committed => walk (TransferPendingFiniteCodec01.encode (encodeObject encodeNative))
          (TransferPendingFiniteCodec01.decode (decodeObject decodeNative)) project committed.parent committed.deferred rest) =
      (step (nativeOnlyEncode encodeNative) (TransferPendingFiniteCodec01.decode (decodeObject decodeNative)) project request parent queued).bind
        (fun committed => walk (nativeOnlyEncode encodeNative) (TransferPendingFiniteCodec01.decode (decodeObject decodeNative))
          project committed.parent committed.deferred rest)
    apply option_bind_equality_from_actual_returned_values _ _ _ _ sameStep
    intro committed actualSuccess
    have derived := TransferBoundedNativeCodec01.successful_bounded_whole_step_stores_supported_native_pending
      encodeNative decodeNative supportedRoundtrip project injection request parent queued committed initial bounded actualInputs actualSuccess
    exact ih committed.parent committed.deferred derived.1 derived.2.1
      (fun next inside => nativeInputs next (List.mem_cons_of_mem request inside))

'''
source=source[:start]+body+source[end:]
anchor='set_option pp.all true in\n#check @bounded_actual_request_step_erases_unsupported_encoder_ghosts'
assert source.count(anchor)==1
source=source.replace(anchor,'set_option pp.all true in\n#check @option_bind_equality_from_actual_returned_values\n#print axioms option_bind_equality_from_actual_returned_values\n'+anchor)
(ROOT/'handwritten').mkdir()
(ROOT/'handwritten/TransferNativeReachableErasure01.lean').write_text(source)
s=(old/'prepare.py').read_text()
s=s.replace("POOL = DIAG / 'transfer-native-reachable-erasure-owned-floor-20261011-02'","POOL = DIAG / 'transfer-native-reachable-erasure-owned-floor-20261011-03'")
assert s.count('assert len(names) == 3')==1
s=s.replace('assert len(names) == 3','assert len(names) == 4').replace("'fresh_audits': 3","'fresh_audits': 4")
anchor="plan['pins'] += mapping['runtime_sources']";assert s.count(anchor)==1
extra="rejected_reachable02=DIAG/'transfer-native-reachable-erasure-20261011-02'\nplan['pins'] += [pin(rejected_reachable02/n) for n in ['prepare_recipe.py','prepare.py','plan.json','review.json','execute_bounded.py','source-mapping.json','events.jsonl','handwritten/TransferNativeReachableErasure01.lean','project/ShielddSecurity/TransferNativeReachableErasure01.lean','runs/01-TransferNativeReachableErasure01/stdout.txt']]\n"
s=s.replace(anchor,extra+anchor)
s=s.replace('One definition/two complete proofs.', 'One definition/three complete proofs, including a small polymorphic Option-bind returned-value congruence lemma.')
start=s.index("plan['source_repairs'] = ");end=s.index("\nplan['artifact_policy']",start)
s=s[:start]+"plan['source_repairs'] = 'Sources01/02 failed including fixed kernel heap limit, strict whole0. Source03 adds a small reusable Option-bind congruence lemma and factors the original symbolic walk proof through only actual successful returned step values instead of simplifier/case expansion of full source execution. Existing definitions and step/walk theorem premises/conclusions unchanged; new helper audited separately. Fixed heap, finite heartbeats and all physical/per-run guards unchanged. Both failed originals fully retained, zero compiler/memory control credit.'"+s[end:]
(ROOT/'prepare.py').write_text(s)
print({'fresh_audits':4,'failed_original_credit':0,'repair':'small reusable returned-value bind lemma','heap_guard_unchanged':True})
