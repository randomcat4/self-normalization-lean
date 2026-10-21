# Server verification, first foundations milestone

PASS. The pinned server toolchain built the integrated library and checked every project theorem, including generated helpers. Independent blind translation and proof review are recorded separately.

Library source contains 83 public theorem declarations. The environment audit checked 119 theorem constants including generated helpers. All transitive axioms are within propext, Classical.choice and Quot.sound; no project placeholder or extra axiom was accepted.

Integration build: 14.397 seconds. Axiom/type audit: 4.021 seconds. Four CPU cores were selected by affinity. Maximum individual child RSS was 2.49 GiB; this is not an aggregate peak measurement.

Non-fatal module-system interoperability warnings remain because the project uses traditional Lean modules while this mathlib snapshot uses the new module system. They do not indicate missing proofs or failed checks. A future syntax migration is separate from this semantic milestone.

See receipt-v1.json for precise commits, source/lock hashes, commands and resource interpretation; declarations.json records actual types and axiom sets. Raw development and build logs remain on the server. The source-bound integration receipt is reused for the audit-script-only fix; library bytes were unchanged. No local Lean verification was performed.
