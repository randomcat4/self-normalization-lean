# OQ3 unit161 CB — actual standardized-cell bounded Borel test
Exact complete declaration and ALL statement let values frozen BEFORE implementation. Module Shao.OQ3.StandardizedCellBoundedBorelTest. Imports ONLY Shao.OQ3.StandardizedCellBounds and Mathlib.MeasureTheory.Integral.Bochner.Set. Namespace Shao.OQ3; open MeasureTheory; scoped Topology; noncomputable section. One public theorem zero definitions.

Actual source need: comparing actual normalized iid laws with Gaussian/Edgeworth requires the EXACT indicator times actual exponential weight as a bounded Borel test. Provide its literal inverse-affine B and exact F-image equality, global Borel measurability, explicit uniform C0>0 independent n/y/rectangle, and actual Bochner Integrable under ANY supplied finite measure. No desired distribution comparison/error premise. A is an arbitrary measurable subset of the ORIGINAL HALFOPEN rectangle; literal physical-window intersections qualify once their known measurability is supplied. y is in ORIGINAL CLOSED rectangle, allowing genuine closure anchor; no interior-minimizer assumption and no boundary atoms dropped.

```lean
theorem standardized_rectangular_cell_uniform_bounded_borel_test
    (n : ℕ) (hn : 1 ≤ n) (theta : ℝ × ℝ)
    (E : (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ)) (y : ℝ × ℝ)
    (aL aR qL qR M R S : ℝ)
    (hM : 0 ≤ M) (hR : 0 ≤ R) (hS : 0 ≤ S)
    (htheta : ‖theta‖ ≤ M)
    (hE : ‖(E : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ))‖ ≤ R)
    (hEinv : ‖(E.symm : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ))‖ ≤ S)
    (hy : y ∈ Set.Icc aL aR ×ˢ Set.Icc qL qR)
    (hawidth : aR - aL ≤ 1 / (n : ℝ))
    (hqwidth : qR - qL ≤ 1 / (n : ℝ))
    (A : Set (ℝ × ℝ)) (hA : MeasurableSet A)
    (hrect : A ⊆ Set.Ioc aL aR ×ˢ Set.Ioc qL qR)
    (nu : Measure (ℝ × ℝ)) [IsFiniteMeasure nu] :
    let F : (ℝ × ℝ) → (ℝ × ℝ) := fun w => Real.sqrt (n : ℝ) • E (w - y)
    let B : Set (ℝ × ℝ) := {v | y + (Real.sqrt (n : ℝ))⁻¹ • E.symm v ∈ A}
    let g : (ℝ × ℝ) → ℝ := fun v => Real.exp (-Real.sqrt (n : ℝ) *
      (theta.1 * (E.symm v).1 + theta.2 * (E.symm v).2))
    let C0 : ℝ := Real.exp ((2 * M) * S * R)
    0 < C0 ∧ MeasurableSet B ∧ B = F '' A ∧
      Measurable (B.indicator g) ∧
      (∀ v : ℝ × ℝ, |B.indicator g v| ≤ C0) ∧
      Integrable (B.indicator g) nu
```

All let values F/B/g/C0 appear above in full and match AO/BW/BX. The genuine bounds M/R/S are explicit: CA's same compactTheta bound and canonical E forward/inverse operator bounds instantiate them with R=2/sqrtlo, S=4hi/sqrtlo. C0=exp(kappa0*R0) for kappa0=(2M)*S, the same natural uniform constant as the Gaussian packet. Do not claim this theorem selects that actual family or supplies its hypotheses; it is the complete source-bound test interface.

Proof plan: n>=1 yields positive s=sqrt n; inverse affine continuity gives measurable B and explicit inverse algebra gives B=F''A. Actual halfopen/closed rectangle bounds imply default MAX pair distance <=1/n; qualified AP support and exponential bounds with Ractual=norm E give indicator bound exp(((abs theta1+abs theta2)*norm Einv)*norm E). abs-coordinate bounds from pair norm<=M plus norm inequalities bound this by C0. Continuous actual g and measurable B yield globally measurable indicator; finite measure integrates constant C0 and Integrable.mono' proves actual indicator integrability. No a.e. replacement in B identity, no compactification of actual law, no integrability totalization.

Qualified old AP source9dca0c3b15c57442b5d36cc96334c64320701e38925753baf47ade096bc3f402 (StandardizedCellBounds) reportu22apaq-proof-review.md SHA4d513e9cd8bd3ae775e697c5d39e8a4d4dc62247fac4aa6aa892ac167e784509 complete221source/12actualincl7generated/allvalues CORRECT138lines. Complete consumed public AP support/exponential declarations and ALL B/g/kappa/R values read, qualification/scope exacthash binding; reuse old proofs/checks, no whole old proof/report reread or gate replay. Exact AP rootv59 source map/library/server binding before first kernel. Primary pinned Integrable.mono' in MeasureTheory/Function/L1Space/Integrable.lean104-107 read: integrable real majorant + AEStronglyMeasurable + AE norm bound -> actual Integrable.

Rootv59 receipt30f1cbf1885bfbd141c23a68844696af992cb4b31eb21afc93b6d912da425ccc checkedcode29c9804c552f0cc494355e6556c112aa3c36c908/tree3105ddcd9ee08c67da77f150f9392e140061a98c, mainb6bdf733 differs; no acceptedhead supplied. PR217fd718003 remains frozenrootintake, active feat/oq3-weighted-grid-reconstruction. BZ freshfullreviewACTIVE solelease1, CA review queued; CB separate laterfreshNONAUTHOR review all actualowned/generated/fulltypes/allvalues mandatory after exact firstPASS. CPU14–17 max1heavy/nativeM8192/j4/autoImplicitfalse ONLYserver Lean/heavy. No localLean/cache/package/sharedwrite/math-ultra/newsidebar/crossmessages/sorry/admit/newaxiom/unsafe/native_decide/implemented_by/weakenedsettings. Preserve all firstPASS bytes/failures/warnings, no cosmetic PASS edit/checkreplay.

This is a generic actual test condition, NOT actual Song Edgeworth proof/distribution comparison or root theorem. Quantitative weighted error/exterior/original B/D OPEN. Corrected fixed-law A/bounded C/p54/strictthreshold/external attribution preserved.
