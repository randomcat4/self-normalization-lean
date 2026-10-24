# Unit203 / U22DR: finite complex logTaylor quartic correction bound

Freeze BEFORE implementation. Pinned Mathlib-only actual Complex.logTaylor definition, no projectproof dependency. Abstractcomplexdegree2/3/4 coefficient bounds at0<=r<=1 implytruefifthorder bound aftersubtracting quadraticselfcorrection a²/2. All coefficientnormbounds explicitmodularinputs; actualmodelconsumer MUSTderive them from genuine moments. This finite polynomial bound is not a principal-log theorem orroot theorem; use withqualifiedactualmodelDO/DQ later. No source assumption changes; originalhighercumulant/normalizedIID/rootB-D/fullfrequency/inversion/exterior/newrhoLaplaceOPEN.

```lean
theorem complex_log_taylor_quartic_correction_bound
    (a b c : ℂ) (r A B C : ℝ)
    (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (ha : ‖a‖ ≤ A * r ^ 2)
    (hb : ‖b‖ ≤ B * r ^ 3)
    (hc : ‖c‖ ≤ C * r ^ 4) :
    ‖Complex.logTaylor 3 (a + b + c) -
      (a + b + c - a ^ 2 / 2)‖ ≤
        (A * (B + C) + (B + C) ^ 2) * r ^ 5
```
