# OQ3 U22BO / unit148 — frozen actual tilted covariance pair-whitening family

FROZEN before source. math-theorem/no math-ultra. One public theorem/no globaldefinitions; all NEW source/proof/actualownedtypes/allvalues fresh fullreview+recursive actualowner white3AX mandatory. CPU14–17/serveronly/max1/native8192MiB/j4/autoImplicitfalse/pins/read-onlycache unchanged.

Source-bound purpose: BG/BH actualcell Gaussianoscillation must use the true covariance whitening family with explicit uniform maxnorm operatorbounds, not arbitrary E. BN147 supplies a canonical single-matrix pair equivalence; this unit assembles an actual family for the true quadratic exponential tilts and proves exact equality of the centered realpair action with the qualified Fin2 canonical matrix representation. It is deliberately conditional on the explicit universal actual covariance spectral premise used by the existing source family. It does not produce that spectral premise, compact analytic parameter set, or an actual sample probability comparison.

Exact import: Shao.OQ3.QuadraticWhiteningPairEquiv. BN source640a12f87e1cbfcb59a827a10e197763e24fe7be8acae274febf484965eef38a/187lines2actual firstkernel/ownerAXPASS; fresh independent complete review active, must qualify before accepted BO. Only consumed complete canonical declaration with all s/t/A/B values and exact qualified scope will be reused; all newfamilyproof fully reviewed. Actual parabolaCovariance definition from root RegularCovariance source0add3476cc949edc593e15dc195934a6df78a41a55f4a2281f66095733d4c853 matchesv55; symmetry is literalcovariance definition.

Complete exact declaration and ALL local values:
```lean
theorem parabola_covariance_pair_whitening_family
    (mu : Measure ℝ) [IsProbabilityMeasure mu] (Theta : Set (ℝ × ℝ))
    (lo hi : ℝ) (hlo : 0 < lo) (hhi : 0 < hi)
    (hspec : ∀ p ∈ Theta,
      let D : Matrix (Fin 2) (Fin 2) ℝ :=
        parabolaCovariance (mu.tilted (fun x => p.1 * x + p.2 * x ^ 2))
      ∀ xi eta : ℝ,
        lo * (xi ^ 2 + eta ^ 2) ≤
          xi ^ 2 * D 0 0 + 2 * xi * eta * D 0 1 + eta ^ 2 * D 1 1 ∧
        xi ^ 2 * D 0 0 + 2 * xi * eta * D 0 1 + eta ^ 2 * D 1 1 ≤
          hi * (xi ^ 2 + eta ^ 2)) :
    let tilt : (ℝ × ℝ) → Measure ℝ := fun p =>
      mu.tilted (fun x => p.1 * x + p.2 * x ^ 2)
    let D : (ℝ × ℝ) → Matrix (Fin 2) (Fin 2) ℝ := fun p => parabolaCovariance (tilt p)
    let s : (ℝ × ℝ) → ℝ := fun p => Real.sqrt (D p 0 0 * D p 1 1 - (D p 0 1) ^ 2)
    let t : (ℝ × ℝ) → ℝ := fun p => Real.sqrt (D p 0 0 + D p 1 1 + 2 * s p)
    let A : (ℝ × ℝ) → Matrix (Fin 2) (Fin 2) ℝ := fun p =>
      ![![(D p 1 1 + s p) / (s p * t p), -(D p 0 1) / (s p * t p)],
        ![-(D p 0 1) / (s p * t p), (D p 0 0 + s p) / (s p * t p)]]
    let B : (ℝ × ℝ) → Matrix (Fin 2) (Fin 2) ℝ := fun p => D p * A p
    let means : (ℝ × ℝ) → (ℝ × ℝ) := fun p =>
      (∫ x : ℝ, x ∂tilt p, ∫ x : ℝ, x ^ 2 ∂tilt p)
    ∃ E : Theta → ((ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ)), ∀ p : Theta,
      A p * D p * A p = 1 ∧
      (∀ w : ℝ × ℝ, E p w =
        (A p 0 0 * w.1 + A p 0 1 * w.2, A p 1 0 * w.1 + A p 1 1 * w.2)) ∧
      (∀ w : ℝ × ℝ, (E p).symm w =
        (B p 0 0 * w.1 + B p 0 1 * w.2, B p 1 0 * w.1 + B p 1 1 * w.2)) ∧
      ‖(E p : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ))‖ ≤ 2 * (1 / Real.sqrt lo) ∧
      ‖((E p).symm : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ))‖ ≤ 4 * hi * (1 / Real.sqrt lo) ∧
      ∀ x : ℝ, E p ((x, x ^ 2) - means p) =
        ((A p *ᵥ (![x, x ^ 2] - ![(means p).1, (means p).2])) 0,
          (A p *ᵥ (![x, x ^ 2] - ![(means p).1, (means p).2])) 1)
```

mu is an actual probability measure, Theta arbitrary set of actual tilt parameters, lo/hi positive real constants independent of p. hspec is the stated universal quadraticform bound on the actual parabolaCovariance of EACH same quadratic exponential tilt. No desired E/opnorm/whitening/centering equation is assumed. All tilt,D,s,t,A,B,means values repeat the actual canonical definitions; means are actual tilted integrals. E is indexed by the genuine subtype Theta so emptyTheta is allowed. It is an existential choice family of actual continuous linear equivalences, with no assertion that p↦E p is continuous/measurable and no p outsideTheta assertion.

The two uniform operatorbounds are on default MAXNORM ℝ×ℝ and apply to both actual E and inverse, with exact literal forward/inverse row matrices. The final centered identity is an equality of actual values with the Fin2 canonical whitened centered vector, not an assumed centered law, mean-zero/covariance law assertion or a Euclidean-norm replacement. The true tilt spectrum premise remains explicit; general open-MGF/moment/weak-Cramer restrictions belong to the later probability consumers and are not weakened.

Proof route: apply BN to D(p) for every p∈Theta using its actual hspec and literal covariance symmetry. Choose the proved E for each subtype point (classical choice in whitelist) and retain all actual row/norm/whitening facts uniformly. Expand only the two-coordinate centered action and two-term matrix-vector multiplication to prove the final identity exactly. All proof-local copies of tilt/D/s/t/A/B/means and choice values must fullyreview.

OPEN: deriving/choosing actual uniform spectral bounds and compact chart for BL anchors in the original unbounded law scope; uniformGaussian cellcoefficient consumer; actualsampleEdgeworth, exact weighted probabilityreconstruction/cell summation, full exterior and originalB/D. Existing corrected fixed-law A/boundedcompacttiltC, p54/strictWC/externalattribution unchanged. No novel/fullrootclaim.
