# Typed low31 replacement and conditional gap bounds

Three Mac-replayed modules and eleven complete-type/axiom audits qualify the source-only desktop draft at `f6ac3018e275aab1f4f7cfc314b2893675185818`. Runtime pin: `844389ee069e1fb2e576708842d0b389b4d9a44a`.

Typed high33/low31 extraction and concatenation give the entire unsigned value of the modeled BFXIL replacement, preserve the original low31 bits and fit the 64-bit word. Two arithmetic modules show that opposing actual/approximate orders, together with both bounded prefix errors, imply a conditional closeness bound; the low31 budget specializes it to 2^(shift+32).

The Mac sources append full-type/axiom audits. The BFXIL proof also has two explicit, checked tactic repairs: normalize BitVec.append and qualify the core Nat modulo/zero lemmas. Definition bodies and theorem statements are unchanged; the original draft and failed replay are retained. Original UNRUN comments remain as provenance. All 983 referenced toolchain sources and 13 runtime/locked BLST contexts were independently matched. Replay used the unchanged 1536 MiB heap, 4 GiB RSS and 240-second guard, one process at a time.

First-divergence location, the returned-word producer join, full-input bitlength progress, complete inversion and compiled execution remain OPEN. No circuit assertion coverage or native-consequence credit is added; certification is false. These three Mac modules are recorded separately from the Windows 68-module/497-audit checkpoint to avoid double counting future replays.
