# Locked ARM64 arithmetic product decomposition

TransferBlstArmProducts01 has seven complete type and axiom audits. Each arithmetic MUL/UMULH low/high pair conserves the complete UInt64 product, and its low word equals the wrapped multiplication. A symbolic recurrence derives exact packed low/high product vectors for arbitrary operand lists, retaining the limb count.

The check took18.71s/1,410,215,936 bytes peak RSS;all251 external dependency identities match retained sources. ISA execution, register/ABI/compiler/private origins and full Montgomery normalized-value correspondence remain open. These are arithmetic source models, with native/certification credit zero. refresh.py atomically verifies exact successful source/type/axiom/context/resource identities. Raw reports, carriers, failed histories and objects stay local.
