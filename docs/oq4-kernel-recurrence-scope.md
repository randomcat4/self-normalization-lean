# OQ4 conditional killed-kernel recurrence and exact normalization

Source: shao@35d4580, `oq4/b01/proof01.md` Section 8 (D0-D4), SHA256 `7c51246eb02a0d694a366ce3ab5a3a9cca03723160c1291bce29dd817f68bc38`.

The module connects actual finite killed-kernel actions to the source's delayed scalar recurrences. It proves principal-cosine positivity on the closed source interval, F/G bounds, bounded measurable residuals with actual integrability, and the exact one-step defect identity. Explicit R3 and R4 block estimates then imply D0 and D1 by the genuine semigroup and closed-domain order comparison.

For positive free cosine coefficient rho it proves the exact normalized factors: epsilon rho^(-(m+1)) for D2, and A rho^(-m), B rho^(-m) for D3. Under 0<rho<=1 it proves nonnegative normalized sequences and the finite D4 reciprocal-power bound. Zero-step, m=0, k=m and natural subtraction are retained. No global positivity of cosine or increment moment assumption is introduced.

R3/R4 are explicit independent block inputs. The module does not prove their probability estimates, a uniform reciprocal-power bound, the B1 initial approximation or an iid path-law identification. These conditional kernel identities do not close K/Kv or OQ4.

The 18 public theorems, five definitions and fourteen generated constants are checked with the pinned designated-server toolchain. The independent review found one generated helper under the imported killedAction name that the author's original root-based count omitted; all 37 declarations are audited, and the count is corrected without changing mathematical source. Acceptance requires isolated statement review, independent mathematics and final formal review, author/lead target checks and all-constant transitive axiom auditing. Only propext, Classical.choice and Quot.sound are allowed. Exact source/audit hashes and actual counts are in verification/oq4-kernel-recurrence/receipt.json. Full logs stay on the server.

The feature branch starts at `dfe239643bd0b58acec4d83a8b639919761f74d9` (PR #15). A bounded fetch and conflict-free merge brought accepted main `9da55787ce7decdf177b3eaa9ca714503aca544a` into the branch at `7b0648095d6ba3f0b1a89384005af21ce1fee5f0`, the exact base before these new modules are committed. Common files came directly from the accepted main merge; the lane made no manual changes to common definitions, root imports, shared manifests, audit scripts or locks. All frozen OQ4 mathematical source hashes remained unchanged.
