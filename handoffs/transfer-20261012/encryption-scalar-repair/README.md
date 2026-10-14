# Encryption scalar correspondence repair

The captured circuit allocates ownership scalars before tier ephemeral scalars.
The corrected source maps column 8551 to ownership 0, 10083 to ownership 1,
11611 to tier 0, 13629 to tier 1, 14891 to tier 2, and 16153 to tier 3.
Six direct identity lemmas check this mapping.

The selected replay runner invalidates reused objects when any transitive source
signature changes. The replacement manifest pins both old and corrected sources;
source replacement does not permit reuse of stale dependent proofs. The atomic
refresh independently checks source signatures, receipts, limits, theorem types,
axiom reports, and final file identities before publishing evidence.

This repair applies only to runtime commit
`844389ee069e1fb2e576708842d0b389b4d9a44a`. It adds no assertion coverage and does
not certify the complete Transfer relation. Whole-relation soundness, total
legal-input construction, computed public input binding, and actual native
consequence remain open.
