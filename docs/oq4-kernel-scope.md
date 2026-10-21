# OQ4 genuine one-step killed kernel

Source: shao@35d4580, `oq4/b01/proof01.md` Section 1 and Section 6 (R1), SHA256 `7c51246eb02a0d694a366ce3ab5a3a9cca03723160c1291bce29dd817f68bc38`.

The module constructs an actual Mathlib measurable kernel from the deterministic starting point and the fixed increment probability law. Each row is exactly the translated increment measure restricted to the closed target interval [-h,h]. Its rows are not normalized. It proves uniform finiteness, total mass at most one in both extended and real forms, and output support in each row's own almost-everywhere sense.

For every bounded Borel real test it proves integrability on both sides and the exact killed-step integral formula. Its cosine specialization agrees with the previously certified Kcos definition. The increment law requires no centering, variance, moments, density or bounded support. Endpoints and atoms, including the zero-width interval atom, are retained. The whole-real-line starting-point extension agrees with the source on its stated starting interval.

Seven public theorems, two definitions, one finite-kernel instance and five generated constants passed author, source-to-statement, independent mathematics and independent final formal checks. The lead checks the target without generating its olean and audits every imported Shao.OQ4 constant transitively. Only propext, Classical.choice and Quot.sound are allowed; actual counts, hashes and commands are in verification/oq4-kernel/receipt.json. Full logs remain on the designated server.

This closes only the one-step kernel object and bounded-test interface. Kernel powers versus finite iid path events, O0, actual R3, R4, Brownian inputs, K/Kv and OQ4 remain OPEN. The next unit supplies the finite kernel iteration and positivity algebra; it will still leave path identification and probability estimates separate.

This branch starts at `9cd1b2baf7691e08d30de8b3dad67ce174cad040` (PR #11, following PR #7, #8 and #9). The latest announced main `7a6ba6438136630ac0ca46b1fbda0d6eaa773827` has not been fetched here after bounded fetch failures. No common root import, shared manifest, audit script, definition or version lock changes. Integration must preserve the coordinator's newer common versions.
