# OQ3 U22BN / unit147 — frozen genuine matrix whitening on the real pair

FROZEN before source. math-theorem/no math-ultra. Two public theorems, zero global definitions. Full fresh independent NEWsource/proofs/actualownedtypes/allvalues+recursiveactualowner standard3AX required. Server-only CPU14–17/max1/native8192MiB/j4/autoImplicitfalse, pins/read-onlycache unchanged.

Source-bound purpose: BG/BH actualGaussian celloscillation and tube statements use a continuous linear equivalence E on the DEFAULT maximum-norm real pair. The qualified true canonical covariance-whitening producer currently supplies a genuine 2×2 matrix on Fin2 functions with uniform spectral data, but an arbitrary E is not automatically that matrix. This unit constructs the actual pair equivalence from mutual matrix inverses and then applies it to the exact canonical whitening matrix from qualified H. It must prove explicit forward/inverse row actions and uniform maxnorm operator bounds, without assuming desired operator bounds or substituting a Euclidean norm.

Exact imports planned: Shao.OQ3.QuadraticWhiteningSpectralData; Mathlib.Topology.Algebra.Module.FiniteDimension; Mathlib.LinearAlgebra.Matrix.NonsingularInverse. Both pinned primary objects observed cached; no hydration/rebuild.
Consumed H source83520a430712a07148396f30f7c07619ef55bda9cc9e464a98eae63e071e874e matches rootv55receipt actualsource map. Its complete public spectral_data declaration including s/t/A and all quantified fields has been read; qualified u22h-proof-review.md binds exactfull245lines/allactualowners, oldproofs/checks reused (not reread). Qualified actual family source622601d0f8650bfc684f4dfde9a615700ad48c4911f5316734193278e115ee8e is motivation, not an assumed/new proof dependency. New theorem still explicitly takes a symmetric D and actual two-sided quadraticform spectral premise; actualfamily substitution is a later consumer.
Primary APIs already read: LinearEquiv.toContinuousLinearEquiv at finiteDimension:368; matrix nonsingularinverse permits two-sided inverse for finite square matrices; Prod.norm_def at Normed/Group/Constructions:237 is maximum of coordinate norms; opNorm_le_bound uses pointwise norm bounds.

Exact complete declarations and ALL statement local values:
```lean
theorem matrix_pair_continuous_linear_equiv_of_inverse
    (A B : Matrix (Fin 2) (Fin 2) ℝ)
    (hAB : A * B = 1) (hBA : B * A = 1) :
    let F : Matrix (Fin 2) (Fin 2) ℝ → (ℝ × ℝ) → (ℝ × ℝ) := fun M w =>
      (M 0 0 * w.1 + M 0 1 * w.2, M 1 0 * w.1 + M 1 1 * w.2)
    ∃ E : (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ),
      (E : (ℝ × ℝ) → (ℝ × ℝ)) = F A ∧
      (E.symm : (ℝ × ℝ) → (ℝ × ℝ)) = F B ∧
      (∀ c : ℝ, 0 ≤ c → (∀ i j : Fin 2, |A i j| ≤ c) →
        ‖(E : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ))‖ ≤ 2 * c) ∧
      (∀ c : ℝ, 0 ≤ c → (∀ i j : Fin 2, |B i j| ≤ c) →
        ‖(E.symm : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ))‖ ≤ 2 * c)

theorem quadratic_whitening_pair_equiv
    (D : Matrix (Fin 2) (Fin 2) ℝ) (hsym : D 1 0 = D 0 1)
    (lo hi : ℝ) (hlo : 0 < lo) (hhi : 0 < hi)
    (hspec : ∀ xi eta : ℝ,
      lo * (xi ^ 2 + eta ^ 2) ≤
        xi ^ 2 * D 0 0 + 2 * xi * eta * D 0 1 + eta ^ 2 * D 1 1 ∧
      xi ^ 2 * D 0 0 + 2 * xi * eta * D 0 1 + eta ^ 2 * D 1 1 ≤
        hi * (xi ^ 2 + eta ^ 2)) :
    let s : ℝ := Real.sqrt (D 0 0 * D 1 1 - (D 0 1) ^ 2)
    let t : ℝ := Real.sqrt (D 0 0 + D 1 1 + 2 * s)
    let A : Matrix (Fin 2) (Fin 2) ℝ :=
      ![![(D 1 1 + s) / (s * t), -(D 0 1) / (s * t)],
        ![-(D 0 1) / (s * t), (D 0 0 + s) / (s * t)]]
    let B : Matrix (Fin 2) (Fin 2) ℝ := D * A
    A * D * A = 1 ∧
      ∃ E : (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ),
        (∀ w : ℝ × ℝ, E w =
          (A 0 0 * w.1 + A 0 1 * w.2, A 1 0 * w.1 + A 1 1 * w.2)) ∧
        (∀ w : ℝ × ℝ, E.symm w =
          (B 0 0 * w.1 + B 0 1 * w.2, B 1 0 * w.1 + B 1 1 * w.2)) ∧
        ‖(E : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ))‖ ≤ 2 * (1 / Real.sqrt lo) ∧
        ‖(E.symm : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ))‖ ≤
          4 * hi * (1 / Real.sqrt lo)
```

The first result is a generic construction from explicit A/B mutual inverse equations. F is the full real-row matrix action, no affine shift/centering/scaling. The second result chooses EXACT canonical s,t,A values from H, and B=D*A as the actual inverse. hspec is the same lower/upper Euclidean quadraticform estimate as H; lo,hi positive. It proves A*D*A=1 and an actual continuous linear equivalence whose row action is exactly that A, inverse exactly B. The E/operatornorms are on ℝ×ℝ's maxnorm, so explicit factors2/4 are retained. No rootprobability theorem or actual family application is assumed/proved here.

Proof route: define full row action F and prove its composition agrees with matrix multiplication and identity. Construct a real linear equivalence with inverse rowaction using hAB/hBA, and use finite-dimensional continuity. For matrix entries bounded by c>=0, each coordinate row absolute value is at most 2c*||w|| in maximum norm, yielding actual operatorbound on both forward and inverse maps.
For canonical A consume H's actual s/t positivity, A*D*A=1 and ALLentry |Aij|<=U=1/sqrt(lo). Derive A*(D*A)=1 and the reverse squarematrix inverse identity. From hspec at coordinate and (1,±1) probes derive all actual |Dij|<=hi using hsym; then |(D*A)ij|<=2hiU by the literal two-term matrix product and triangle inequality. The generic result yields ||E||<=2U and ||E^-1||<=4hiU. All matrix coefficients/functions/local values must be fully reviewed; no finite probes substitute for the universal hspec or whitening proof.

OPEN: putting this actual E family on the selected compact tilt/anchor chart, proving all needed parameter-uniform cell/Edgeworth constants, actualsampleEdgeworth/probability reconstruction/cell summation/exterior and original B/D. Generic spectral whitening/pair equivalence alone does not close these. No novelty claim; fixed-law A/bounded compact-tilt C/p54/strictWC/externalattribution unchanged.
