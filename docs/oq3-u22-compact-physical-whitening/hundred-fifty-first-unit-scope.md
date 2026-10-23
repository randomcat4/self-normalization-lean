# OQ3 unit151 BR — actual compact-open covariance spectrum
Exact declarations and all statement let-values frozen before implementation. Module Shao.OQ3.CompactOpenDomainCovarianceSpectrum. Imports only Shao.OQ3.OpenDomainCompactMoments and Shao.OQ3.OpenDomainCovarianceAmplitude; namespace Shao.OQ3, open MeasureTheory ProbabilityTheory, scoped Matrix Topology ContDiff, noncomputable section. Two public theorems, zero definitions.

Source-bound dependency: repair01.md actual uniform tilted covariance spectral prerequisites for original compact-window Edgeworth argument. This unit produces them on an arbitrary compact subset of the TRUE open MGF domain under actual pointwise positive covariance determinant. In particular BQ150 gives such a set as the SAME physical mean-chart inverse image of the SAME literal V. No bounded support, arbitrary substitute matrix/family, assumed spectrum, or compactness of unrelated chart.

```lean
theorem quadratic_form_bounds_of_det_trace
    (a b d delta T : ℝ) (ha : 0 ≤ a) (hd : 0 ≤ d)
    (hdelta : 0 < delta) (hdet : delta ≤ a * d - b ^ 2)
    (hT : 0 < T) (htrace : a + d ≤ T) (xi eta : ℝ) :
    delta / T * (xi ^ 2 + eta ^ 2) ≤
        a * xi ^ 2 + 2 * b * xi * eta + d * eta ^ 2 ∧
      a * xi ^ 2 + 2 * b * xi * eta + d * eta ^ 2 ≤
        T * (xi ^ 2 + eta ^ 2)

theorem compact_open_domain_covariance_spectral_bounds
    (mu : Measure ℝ) [IsProbabilityMeasure mu] (Theta : Set (ℝ × ℝ))
    (hcompact : IsCompact Theta)
    (hTheta : Theta ⊆ interior
      (Shao.Probability.bivariateMGFDomain mu (fun x : ℝ => (x, x ^ 2))))
    (hdet : ∀ p ∈ Theta, 0 < (parabolaCovariance
      (mu.tilted (fun x => p.1 * x + p.2 * x ^ 2))).det) :
    let nu : (ℝ × ℝ) → Measure ℝ := fun p =>
      mu.tilted (fun x => p.1 * x + p.2 * x ^ 2)
    let D : (ℝ × ℝ) → Matrix (Fin 2) (Fin 2) ℝ := fun p =>
      parabolaCovariance (nu p)
    ∃ lo hi : ℝ, 0 < lo ∧ 0 < hi ∧ ∀ p ∈ Theta, ∀ xi eta : ℝ,
      lo * (xi ^ 2 + eta ^ 2) ≤
          D p 0 0 * xi ^ 2 + 2 * D p 0 1 * xi * eta + D p 1 1 * eta ^ 2 ∧
        D p 0 0 * xi ^ 2 + 2 * D p 0 1 * xi * eta + D p 1 1 * eta ^ 2 ≤
          hi * (xi ^ 2 + eta ^ 2)
```

Proof plan: generic real symmetric2x2 matrix algebra using determinant and trace, not eigenvalue totalization. With q=ax²+2bxy+dy², z=x²+y², (a+d)q-(ad-b²)z=(ax+by)²+(bx+dy)². Positive determinant/nonnegative diagonal gives positive trace and q>=0. Repeat for adjugate to bound q<=trace*z. Then delta*z<=trace*q<=T*q gives (delta/T)z<=q. Actual producer: det continuous on true Omega from accepted Udet; compact positive continuous function has common delta>0 (empty Theta handled by primary exists_forall_le'). Accepted F gives actual tilt probability and genuinely integrable uniform |X|²/|X|⁴; explicit true L² memberships before variance_eq_sub. Variance diagonal <= actual raw second/fourth moments, hence common trace T=C2+C4+1>0. Actual symmetry is definitionally parabolaCovariance; det_fin_two binds ad-b² to actual determinant. lo=delta/T, hi=T independent of p/direction/cell/n.

Qualified immutable dependencies: OpenDomainCompactMoments source19946ecf589a2012df33b34ad740b4ff30190bd84fe42662bdaa194c5c545093, full consumed compact theorem + all nu values read, report u22f-proof-review.md SHA2d1ff5f523b7c7207d018dd4d5d4419c31d58de2302313e0adfa3cc1845a2eae CORRECT; OpenDomainCovarianceAmplitude sourcec6f20047e1ef46331b19619f05a72dd7e3ecf60bc1ffad7d2d952599ce5f8a1e, complete Udet signature read, qualified u22uv-proof-review.md SHA09fcc0c7b78f3ac2eec58e30142ea588303c2d07d15ec78978f8dae0ca31b2f2 CORRECT. Both sources exact in rootv56 receipt c01ea5fc / checkedcode0187a42c, local readonly and actualserver hashes verified. Reuse old proofs/checks; no reread/replay of old complete proofs. parabolaCovariance exact definition source0add3476 reviewed and unchanged.

Primary pinned Mathlib interface intake read: IsCompact.exists_forall_le' (compact,continuousOn,pointwise strictpositive => strictpositive common lower bound incl empty case), ProbabilityTheory.variance_eq_sub requiring true probability+MemLp2, variance_nonneg, memLp_two_iff_integrable_sq requiring actual AEStronglyMeasurable. All Lean and owner AX ONLY designatedserver CPU14–17 native -M8192 -j4 autoImplicit=false, oneheavy sharedlane. No local Lean/cache, no oldpassed check replay, no shared edits. No sorry/admit/newaxiom/unsafe/native_decide/implemented_by/weakenedsettings. Complete actual source/types/all statement/local values/every actualowned declaration inclgenerated + transitiveAX independentfresh NONAUTHOR review mandatory whitelistpropext/Classical.choice/Quot.sound. Existing BQreview finishes before a freshBRreview (solechildlease1). PR210 frozen0b64fc rootintake, activecontinuation feat/oq3-covariance-cell-family, no merge/rebase. Physical sample Edgeworth/reconstruction/exterior and original B/D OPEN.
