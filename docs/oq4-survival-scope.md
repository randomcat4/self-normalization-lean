# FiniteSurvivalLaplace v1 scope

Current frozen source SHA256: 49241958f2ae692b56db5fe0aa021a5e88b0020ac6487ddb463d05efb69518cb.

This module connects the genuine finite iid product law and the shared maximum-with-zero/closed-upper event to the analytic Laplace chain. It proves integrability, the zero-step value, cross-dimension prefix laws and antitonicity, all series summability, and the normalized generating formula from the original explicit Spitzer input. An explicit ordinary-sum CDF error then gives the actual maximum Laplace bound and the closed upper survival bound with constant sqrt(2) exp(6 + 3 C_BE). Endpoint atoms, d = 0, m = 1 and the zero path remain included.

The module adds 24 public theorems and 30 module-owned constants. The old 63f00181 candidate was withdrawn after detecting a helper name already exported by BoundaryOccupation. Exactly the new helper and its one internal reference were renamed to measurableSet_closedUpper_laplace; no prior API or mathematical hypothesis changed. The author checked the exact new source together with all prior OQ4 modules before uniquely regenerating its olean. Original candidate evidence remains in the server archive and author receipts.

Independent mathematics and final-source acceptance are recorded in separate review tickets. The lead checks unit imports and all 21 OQ4 modules together. Axiom collection includes every constant owned by any imported OQ4 module, even when its declaration is outside the OQ4 namespace.

The frozen prose uses finiteSumLaplacePayment with mathematical argument names k and L; the actual Lean API is nu, k, L. The mathematical ticket records this notation detail without changing the frozen objects.

BE and original Spitzer remain explicit inputs. This is the upper side for nu; reflection and the two-sided S/AC interface are subsequent work. All unconditional S/AC/O0, B1, long-time K/Kv and complete roots remain OPEN.
