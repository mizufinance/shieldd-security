# Published registry source closure

This preparation identifies all 325 exact custom sources imported transitively
by RegistryInputJoin24, in topological order. Every byte identity is present
in the shared repository. Header imports agree with the qualified task's
recorded custom imports. External imports and the pinned package/toolchain
files are explicit in source-closure02.json.

materialize_source_closure.py copies only these exact published source bytes
and three package files into a new directory outside the publication checkout.
It starts no verifier, imports no cache/object files and never edits generated
Lean. One source-only assembly has passed. The copied workspace remains local
and is not committed.

Use --manifest source-closure02.json, --repository the shared checkout, and
--destination a fresh external directory. prepare_source_closure.py regenerates
the manifest from the immutable worker task configuration and inherited closure;
those original provenance inputs remain referenced by their pinned identities.

This closes source availability for this scoped endpoint. Historical generator
closure, official dependency qualification, final scoped kernel replay, whole
Transfer integration and certification remain separate OPEN obligations.
Any later replay belongs to the existing worker lane under its machine guard.


The MerkleInputMeaning28 endpoint now has a separately prepared exact closure:
source-closure03.json contains336 custom sources (11,669,866 bytes) and the
same three pinned package files/five external import roots. Every required
custom source has an exact published Git path. source-materialization02.json
records assembly outside Git without objects/caches/builds. Its original
manifest SHA is22c1166f122535472c4cfdfe179f2efff87b476b56364911c7003562e9d1b60f.
This is source availability and assembly, not a kernel replay, portable closed
generation recipe or full Transfer integration result.
