# Retained clip1 versus the actual physical statistic

`Shao/OQ6/OriginalRetainedClipComparisonPayment.lean` proves `Shao.OQ6.OriginalRetainedClipComparisonPayment.fixed_original_retained_clip_comparison_payment` under the frozen original-law hypotheses. It compares the retained clipping at `y=1` with the actual total physical statistic, whose zero-studentizer branch is explicitly zero and whose positive branch is `(W+D)/sqrt(centeredSq)`.

The original-law `cg > 0` is selected before `C,a,t0,M,n,r,w,rho`. The theorem keeps genuine canonical/product-envelope assumptions and requires `n ≥ 4`, `rho ≥ 0`, `1+rho ≤ sqrt(n)` and the stated actual remainder-window premise at `y=1`. Its actual comparison-failure event `Eclip` is contained in `G1ᶜ ∪ lowerBad1`, and the genuine original-law payment is

```
P(Eclip) ≤ 3 exp(-q) + exp(-cg*n) + 4 exp(-sqrt(n)/2),
q = boundedPolylogMomentOrder t0 n.
```

The proof uses the literal retained-clipping comparison and the accepted original-good-event bridge. It does not assert a blanket clip1=`d` identity on all `H_z`, add an event-measurability assumption, identify model witnesses, claim a conditional-law-uniform `cg`, or absorb the displayed exponential payment into a Gaussian tail. The deterministic absorption source236 is a subsequent dependency and is excluded from this publication. Continuous-epsilon, external Shao–Zhou/CDF/atom/zero-denominator and original OQ56 root obligations remain open.

Exact source SHA256: `b16dcd02c4a14518bdbbd64b33ce94bcefe7c7770496e8f1a8a7c92872e3fb55` (5430 B, 107 LF). First native001 and the same-first-object audit001 actually exited 0/0. The two actual theorem owners have 258 public TYPE lines plus six generated original sample-law probability-proof TYPE lines, no non-theorem VALUE. Every recursive axiom lies within `propext`, `Classical.choice`, `Quot.sound`. A fresh never-author context completed the full source/proof review and same-source final all-owner machine join; see `docs/OQ6-retained-clip-comparison-payment-qualified.json` and `docs/audits/oq6-retained-clip-comparison-payment/`.

The native source has eighteen warnings. The standing 134 B stderr, strict-wrapper-false fields and wrapper exit1 remain preserved separately from actual Lean exit0. This source did not change after freeze or successful native checking; no old successful proof, producer or axiom audit was replayed.
