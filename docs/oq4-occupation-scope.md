# OQ4 finite occupation-layer integral payment

Source: shao@35d4580, `oq4/b01/proof01.md` Section 5 (OC) and Section 6 (R5), SHA256 `7c51246eb02a0d694a366ce3ab5a3a9cca03723160c1291bce29dd817f68bc38`.

This module proves the finite measure-theoretic payment step from explicit layer-mass bounds. A measurable depth lies in [0,L) almost everywhere; an integrable observable has a nonnegative layerwise upper envelope; each layer has mass at most C(j+1). Its integral is therefore at most C times the weighted finite envelope sum. A closed-depth corollary uses floor(h)+1 layers and retains an integer top endpoint.

The observable may be negative or unbounded. The depth conditions remain almost-everywhere conditions. Zero measures, empty layer ranges and atomic measures are covered. The proof selects a valid layer by the natural floor, uses a finite measurable indicator majorant and finite integral linearity; it does not assume a density, atomlessness or any long-time probability result.

The module supplies the deterministic integration bridge used by OC/R5. The layer-mass inequality is an explicit independent input. It does not prove the probability occupation estimate O0, its energy-marked counterpart O2, averaged residual R3, K/Kv or OQ4. The next analytic module must combine this interface with R1/R2 and the already proved R6 payment, while still identifying O0 as the unproved probabilistic input.

The three public theorems and one definition passed designated-server Lean 4.36.0-rc1 checks, isolated source-to-statement review, independent proof/formal review and transitive axiom auditing. Only propext, Classical.choice and Quot.sound are permitted. `verification/oq4-occupation/receipt.json` contains source hashes and exact commands. The source is unmodified across all checks. Root imports and shared manifests remain with the coordinator.

The feature branch is based on e735de390d615a8efbdf8a800faae0dc8027c999 (PR #8, following PR #7). The coordinator's newer main 197b379be3e58691915221a6928aa777d9e3a9e2 was announced during this work. Two bounded fetch attempts failed (HTTP/2 framing and HTTP/1.1 timeout); its merge object was unavailable in this checkout. The base is recorded exactly, and this branch changes no root import, shared manifest, shared audit script or version lock. Integration must preserve the coordinator's newer versions.
