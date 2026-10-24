# Unit 198 / U22DM — complex logarithmic Taylor perturbation

Frozen before implementation. Three complete declarations, zero statement lets. Standard analytic/algebraic enabler for actual characteristic/moment approximation to cumulant expansion. Exact complex powers and exact existing Complex.logTaylor definition, all natural orders including0, explicit norm ball premises for z/w; these premises must be DERIVED by future actual model consumers and are not changes to any source-model assumptions. Power difference bound on unit ball; finite logTaylor stability on unit ball; actual principal-log to perturbed logTaylor error with norm z<=1/2 and norm w<=1. Mathlib-only, independent of pending DK/DL, no target CF/error/cumulant assumed. Primary existing LogBounds source d3711d5d5b528b8d1733d531d5ae78bc77d13a68079a7243af3251abc48380f7 / original read-only object216aff6dbc47d6b7f350f090f48c0d1e983edae8c6c623dc6d0ce123eb16c226; full actual logTaylor definition value and unrestricted-n norm_log_sub_logTaylor_le interface read before freeze. Future canonical consumers must derive smallness/coherence, normalize IID, and control high-order remainder. Original OQ3 B/D/higher Edgeworth/full-frequency inversion/exterior/new-rho Laplace remainOPEN. Source/p54/strictbeta/external attribution unchanged; no novelty or root completion claim.

```lean
theorem complex_power_difference_bound_on_unit_ball
    (z w : ℂ) (hz : ‖z‖ ≤ 1) (hw : ‖w‖ ≤ 1) (j : ℕ) :
    ‖z ^ j - w ^ j‖ ≤ (j : ℝ) * ‖z - w‖

theorem complex_log_taylor_difference_bound_on_unit_ball
    (n : ℕ) (z w : ℂ) (hz : ‖z‖ ≤ 1) (hw : ‖w‖ ≤ 1) :
    ‖Complex.logTaylor n z - Complex.logTaylor n w‖ ≤ (n : ℝ) * ‖z - w‖

theorem complex_log_taylor_perturbation_bound
    (n : ℕ) (z w : ℂ) (hz : ‖z‖ ≤ (1 : ℝ) / 2) (hw : ‖w‖ ≤ 1) :
    ‖Complex.log (1 + z) - Complex.logTaylor (n + 1) w‖ ≤
      2 * ‖z‖ ^ (n + 1) / ((n + 1 : ℕ) : ℝ) +
        ((n + 1 : ℕ) : ℝ) * ‖z - w‖
```

