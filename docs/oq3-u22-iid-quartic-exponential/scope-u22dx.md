# DX209 frozen exact complex exponential perturbation

Mathlib-only global perturbation bridge and its real-part-dominated corollary. Freeze both COMPLETE declarations below before implementation, zero statement lets/owned definitions. The first inequality holds for every complex z,e, without a small-error hypothesis. The second keeps explicit modular real-part/error/half-gap premises; actual probability/Edgeworth consumers MUST DERIVE them from their genuine models. The real-part form avoids exponentiating a pure imaginary cubic magnitude. No actual model/root theorem or analytic cumulant derivative is claimed. No dependency on pending DW208. Pinned Exponential norm-exp finite remainder/exp_add/Real.exp_le_exp and Trigonometric norm_exp source/object/API bindings will precede implementation. B/D/EdgeworthCFpolynomial/fullfrequency/inversion/exterior/newrhoLaplace remain OPEN.

```lean
theorem norm_complex_exp_add_error (z e : ℂ) :
    ‖Complex.exp (z + e) - Complex.exp z‖ ≤
      ‖e‖ * Real.exp (z.re + ‖e‖)

theorem norm_complex_exp_add_error_of_re_le (z e : ℂ) (a b : ℝ)
    (hz : z.re ≤ -a) (he : ‖e‖ ≤ b) (hb : b ≤ a / 2) :
    ‖Complex.exp (z + e) - Complex.exp z‖ ≤
      ‖e‖ * Real.exp (-a / 2)
```
