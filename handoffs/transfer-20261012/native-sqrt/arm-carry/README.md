# Locked ARM64 arithmetic add-carry chains

TransferBlstArmCarryChains01 has six complete type and axiom audits. For arbitrary UInt64 operands and a Boolean incoming carry, one arithmetic step conserves the complete integer and has a single-bit outgoing carry. A symbolic recurrence derives the limb count and full integer/final-flag relation of every addition chain.

These are arithmetic views of the locked ADDS/ADCS chain; ISA execution, register/flag semantics, compiler/ABI/private representations and complete Montgomery normalization remain open. The check took19.08s/1,403,129,856 bytes peak RSS;all251 external dependency identities match retained sources. refresh.py atomically verifies successful source/type/axiom/context and finite resource identities. Raw reports, failed histories and objects stay local. Native/certification credit0.
