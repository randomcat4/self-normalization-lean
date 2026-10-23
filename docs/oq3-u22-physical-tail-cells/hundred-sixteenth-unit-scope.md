# OQ3 U22ai — physical tail-event sign and positive source chart neighborhood

DECLARATIONS_FROZEN_BEFORE_IMPLEMENTATION. Original report.md42-75 physical D_x={q>0,a>=x sqrt(q)} and repair01.md122-134 shrink U so a>0, source G(r,z)=(a0+r,(a0+r)²/level²-z). repairSHA2569d2e554838aa15b645aaf74a42468d423fed606aa91c1181d0dddf4e87c57cfd; reportSHA256572e74aa9c12e2771f5543a5709a2807666eeea0a4076e7a3263e5c7bcf87f55.

Module Shao.OQ3.BoundaryLaplacePhysicalDomain; import Mathlib.Analysis.SpecialFunctions.Sqrt. Namespace Shao.OQ3; Topology scoped.

```lean
theorem self_normalized_boundary_event_iff
    (level a q : ℝ) (hlevel : 0 < level) (hq : 0 < q) :
    level * Real.sqrt q ≤ a ↔ 0 < a ∧ q ≤ a ^ 2 / level ^ 2

theorem exists_positive_parabola_window
    (level a0 cap : ℝ) (hlevel : 0 < level) (ha0 : 0 < a0) (hcap : 0 < cap) :
    ∃ rho : ℝ, 0 < rho ∧ rho ≤ cap ∧ ∀ r z : ℝ, |r| ≤ rho → |z| ≤ rho →
      0 < a0 + r ∧ 0 < (a0 + r) ^ 2 / level ^ 2 - z ∧
        (level * Real.sqrt ((a0 + r) ^ 2 / level ^ 2 - z) ≤ a0 + r ↔ 0 ≤ z)
```

Proof plan: positive level and q allow exact squaring/division iff with explicit a>0. Sourcecenter(a0,a0²/level²) has bothpositivecoordinates; continuity yields a common full two-sided closed rectangle under any given positivecap, where q>0 and a>0, and source event is exactly z>=0. No desired probability/integral bound or event equivalence is an assumption. This does not assert current AH's exported rho is automatically this smaller radius; an actual cap-selectable analytic assembly is the next interface to combine. Existing AH proof/source accepted scopes remain exact and B/D OPEN.

Two publicTHM/0defs; complete independent source/proof/allactualtype/localvalue and server kernel/recursiveAX mandatory; CPU14-17,M8192,j4,autoImplicit=false,maxone heavy. No old gates replayed. UTF8LF before gate.
