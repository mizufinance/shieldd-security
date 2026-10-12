# Native map controls

Both locked-runtime map tests passed on Mac: SDK and Commonware outputs agree with independently computed Arkworks Elligator outputs across 36 inputs, wrong output assignments and inverted quadratic-choice controls fail, and the recorded domain-separated cases remain distinct.

The cached circuit test build passed in 52.76 seconds at 548 MiB sampled peak group RSS. Libtest completed in 0.06 seconds. That is too short for a reliable execution peak RSS measurement; the initial 32 KiB sample is not claimed as the test's memory peak.

The test source exactly matches runtime `844389ee069e1fb2e576708842d0b389b4d9a44a`. Execution used the retained exact-lock archive plus the recorded diagnostic overlay and source inventory; it does not certify a clean whole-native trace. One worker, finite 4 GiB RSS/7,200-second limits and physical RAM/disk floors were retained. macOS sampling does not provide Linux cgroup/swap enforcement.

`refresh.py --native-root /local/native-workspace --output /fresh/output` checks source, binary, exact two-test result, bounded receipts and identities before atomic compact publication. Logs, objects and workspaces remain local. Native credit is limited to these two finite controls; full Transfer remains **OPEN**.
