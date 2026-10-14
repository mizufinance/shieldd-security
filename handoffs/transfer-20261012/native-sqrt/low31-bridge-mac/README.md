# Typed low31 observation bridge

The modeled typed BFXIL result has exactly the existing low31 approximation value and retains oddness from the original low word. The bridge comes from desktop draft `12074b745e1aec4dceec4b7487ea715188933945`.

Mac replay passed three modules and thirteen full-type/axiom audits under the unchanged 1536 MiB heap, 4 GiB RSS and 240-second limits. Eleven audits recheck existing Factors and ApproxBits declarations; two are the new bridge theorems. These counts overlap the Windows checkpoint and must not be added as thirteen new results.

The factor module no longer imports the unrelated square-root proof chain. Its algebra proof uses core integer identities and omega; the small integer monoid import preserves the exact original power types. ApproxBits uses qualified core Nat lemmas. All original definition bodies, eleven complete elaborated types and axiom sets match the previously qualified sources. Original sources are retained beside the reviewed variants.

Runtime pin: `844389ee069e1fb2e576708842d0b389b4d9a44a`. Returned-word producer and ordering follow-ups remain unqualified: the Mac window-selector replay hit the existing heap limit. Native ISA execution, full inverse progress and all full Transfer endpoints remain OPEN. Native credit is zero; certification is false; no circuit assertion coverage is added.
