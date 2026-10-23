# OQ3 unit 118 (U22ak): physical neighborhood and exact local tail event
Frozen before implementation. Workflow math-theorem; no change to original assumptions.
Original source: oq3/proofs/r2/repair01.md section 3 (lines122–134) coordinate map, and report.md lines42–75 physical self-normalized event. Read-only source hashes remain those recorded in AI.
Direct consumer: actual same-chart/cap-selectable AJ plus AE/AG normalized-n integral, on U intersect the physical event.
Eliminated obligation: closed genuine neighborhood of positive a,q; exact local physical event equals the parabolic strip.
This generic lemma takes explicit full-rectangle physical positivity. The actual consumer must obtain it from AI and a new AJ radius below the AI cap, not assume the desired source integral or shrink a previously fixed radius without a new producer.
No definitions, one public theorem. Full exact declaration:
```lean
theorem positive_parabola_window_event_geometry
    (level a0 rho : ℝ) (hlevel : 0 < level) (hrho : 0 < rho)
    (hphysical : ∀ r z : ℝ, |r| ≤ rho → |z| ≤ rho →
      0 < a0 + r ∧ 0 < (a0 + r) ^ 2 / level ^ 2 - z) :
    let U : Set (ℝ × ℝ) := {w | |w.1 - a0| ≤ rho ∧
      |w.1 ^ 2 / level ^ 2 - w.2| ≤ rho}
    let V : Set (ℝ × ℝ) := {w | |w.1 - a0| ≤ rho ∧
      w.1 ^ 2 / level ^ 2 - rho ≤ w.2 ∧ w.2 ≤ w.1 ^ 2 / level ^ 2}
    let D : Set (ℝ × ℝ) := {w | 0 < w.2 ∧ level * Real.sqrt w.2 ≤ w.1}
    IsClosed U ∧ (a0, a0 ^ 2 / level ^ 2) ∈ interior U ∧
      (∀ w ∈ U, 0 < w.1 ∧ 0 < w.2) ∧ V = U ∩ D
```
All local sets are the literal displayed formulas. Preserve a,q positivity, strict physical q>0, inclusive event boundary and full two-sided U; rho>0 provides an actual neighborhood.
No actual probability/density/Edgeworth or exterior estimate, no originalB/D closure. Standard axiom whitelist only. Complete independent final proof/types/values review and server kernel/whole-owner recursive axioms mandatory.

