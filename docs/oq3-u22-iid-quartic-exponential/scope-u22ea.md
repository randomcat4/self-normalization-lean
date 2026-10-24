# EA212 frozen all-real imaginary/real exponential quadratic error

Freeze COMPLETE declaration below before implementation, one theorem, zero statement lets/definitions. ALL real b,c, no smallness/sign/phase/model assumption. Uses qualified DG192 actual global coarse constants (exp(1)+m+1): m3 gives exp1+4, m1 gives exp1+2. Do NOT replace its actual interface with an unproved factorial/sharp constant. Expand exp(i*b+c) by phase remainder + c*(exp(i*b)-1) + exp(i*b)*(exp(c)-1-c); norm(exp(i*b))=1. Real exponential remainder is globally <=c²*exp|c| from pinned finite-complex-exp estimate m2. Actual Edgeworth consumers must later substitute TRUE signed-moment coefficients b/c and DERIVE their bounds/radii; this deterministic bridge has no actual CF/coherence/root assertion. Independent pendingDY review. Source/p54/strictbeta/external attribution and alloriginalB/D/analyticderivative/EdgeworthCFpolynomial/fullfrequency/inversion/exterior/newrhoLaplace boundaries unchanged.

```lean
theorem imaginary_real_exponential_quadratic_error (b c : ℝ) :
    ‖Complex.exp ((b : ℂ) * Complex.I + (c : ℂ)) -
        (1 + (b : ℂ) * Complex.I - (b : ℂ) ^ 2 / 2 + (c : ℂ))‖ ≤
      (Real.exp 1 + 4) * |b| ^ 3 +
        (Real.exp 1 + 2) * |c| * |b| + c ^ 2 * Real.exp |c|
```
