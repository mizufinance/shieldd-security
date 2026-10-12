# Byte packing and policy prehash proof results

Three reviewed source-model modules establish canonical 31-byte chunk packing,
ordered packing of every finite typed byte list, and length-prefixed policy
prehash field vectors. Packing derives decoder acceptance and exact integer
values. The length prefix makes the returned prehash vector bind the original
bytes injectively. This is an injective encoding result; no hash injectivity or
collision-resistance theorem is claimed.

The runtime target is `844389ee069e1fb2e576708842d0b389b4d9a44a`.
The exact original Windows executions passed 10, 7 and 6 full declaration and
standard-axiom audits. Independent review checked the maintained proof bodies,
all 23 original reports, 215 selected ancestor source identities and the runtime
source copies. The new chunk and walk sources supply the other two ancestors.

[The compact evidence](qualified/evidence.json) records the complete theorem
types, axioms, source and recorded object identities, original successful output
digests, actual commands, time and RSS. Raw compiler logs and detailed failed
attempts remain local. The portable original packets are also retained locally.

Native slice iteration, copying, allocation, indexing, unwrap behavior,
compiler/ABI and production caller refinement remain open. The policy module's
Option model describes checked conversion and returned values. It does not
certify native panic behavior or the final policy hash. Full Transfer and final
combined replay remain open.

`refresh.py` verifies the original successful packets and publishes the source
and compact evidence together into a fresh directory. It does not run Lean or
update the assurance register. No failure bundle, cache or proof object is
included in this publication.
