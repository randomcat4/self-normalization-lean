# OQ3-U19b: literal source geometric curvature and corrected scale

Frozen v1 DECLARATION_REVIEW_PENDING; no implementation. Proposed Shao/OQ3/SourceGeometricScale.lean; exact single import Shao.OQ3.CorrectedScaleContinuity. Namespace Shao.OQ3, open MeasureTheory, open scoped Matrix Topology BigOperators, noncomputable section. Zero public definitions, one complete public theorem. U19a entire226line CORRECT fullproof70f98f21119dea78526f6f0e4d242cc8c4caa17222fd47fd71b7a58ab57a1c05 has been lead-read before acceptance/exactPR146 publication and this next scope. PR146 head5d14dbdb619fd7d2eb97ec31e049053de53be871 and C144f698 are frozen/preserved.

Original target -> R1 section3, actual saddle geometry/positive corrected constant at lines239-257 and its use in the final fixed-law remainder. Original report SHA3473d34ff20bd0d334b9ef3ea3c3ee167fba4d5cc3a742849820ce54d639e662; root-contract defines x0=sqrt(q)/4,a0=q/4,t0=-sourceEll, Lambda1=2*t0/x0^2+(1,2*a0/x0^2)Delta^-1(1,2*a0/x0^2)^T, vCorr=(-t0)*sqrt(detDelta)*sqrt(Lambda1). Remaining obligation -> C's actual correctedInverseScale uses (ell*sqrt(S-(32ell/q)detDelta))^-1, while the literal source geometric formula has not yet been identified with it. The theorem below proves that exact identity for the same actual atomic law/covariance, with true positive determinant, curvature and scale; the let bindings are explicit expressions, not extra caller-supplied objects or assumptions. Direct consumer -> root's canonical source saddle constant bridge and sameC-law rootA assembly after the separate true Hessian/covariance identification. Root owns shared K/domain/rate/saddle definitions; this module adds none. GeneralKL9/10, the canonical extended supremum bridge, K derivatives/Hessian identity and all root assemblies remain OPEN.

```lean
theorem source_corrected_scale_geometric_identity
    (q : ℝ) (hq0 : 1 < q) (hq1 : q < 103 / 100)
    (w : AtomicIndex → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hbase : ∀ i : Fin 4, 0 < w (Sum.inl i))
    (hm : ∀ k : Fin 4,
      HasSum (fun i => w i * constraintFeature sourceEll (fixedAtom i) k)
        (constraintTarget q k)) :
    let D : Matrix (Fin 2) (Fin 2) ℝ := parabolaCovariance (atomicMeasure w)
    let x0 : ℝ := Real.sqrt q / 4
    let a0 : ℝ := q / 4
    let v : Fin 2 → ℝ := ![1, 2 * a0 / x0 ^ 2]
    let curvature : ℝ := 2 * (-sourceEll) / x0 ^ 2 + dotProduct v (D⁻¹ *ᵥ v)
    0 < D.det ∧ 0 < curvature ∧
      0 < sourceEll * Real.sqrt D.det * Real.sqrt curvature ∧
      correctedInverseScale sourceEll q (atomicMeasure w) =
        (sourceEll * Real.sqrt D.det * Real.sqrt curvature)⁻¹
```

The actual q/w/sourceEll law is fixed before the let expressions. q is in the original strict source window; w may have infinitely many positive/zero added entries, while the four base entries must be truly positive. Full4HasSum are literal source feature/target rows. No supplied determinant, curvature, inverse identity, radicand positivity, manually defined scale or differentiability hypothesis is accepted. D is the genuine same atomicMeasure covariance matrix, with the existing actual variance/covariance definitions; matrix inverse means the pinned Mathlib nonsingular inverse and must not get its force from totalized singular behavior. Curvature retains the literal x0/a0 expression until proved equal to S/detD-32ell/q. The third conjunct states the actual geometric scale is strictly positive, not just its inverse is a defined real number. The last is an equality to the existing correctedInverseScale used by C, not a new definition or renamed proxy constant.

Implementation route to be independently checked, not a proof premise: hm0 produces genuine HasSum w1 and probability. AE support gives bounded moments. Positive base weights produce positive actual base atom masses, then the public parabolaCovariance_det_pos gives true detD>0. Real.sqrt q is strictly positive, so x0>0 and x0^2=q/16. Show 2*a0/x0^2=8 and 2*(-ell)/x0^2=-32ell/q with positive nonzero denominators before cancellation. Actual Matrix.inv_def, Matrix.adjugate_fin_two and Ring.inverse_eq_inv expand the genuine 2x2 inverse. D10=D01 from the actual covariance definition, and normalVariance_eq_covariance gives S=64D00-16D01+D11. Hence dotProduct ![1,8](D^-1 *v ![1,8])=S/detD. Public atomic_curvature_pos gives the true strict curvature. Multiplying by detD proves detD*curvature=S-(32ell/q)detD; positive determinants and Real.sqrt_mul identify both square-root formulas. sourceEll_pos and strict sqrt positivity give actual geometric-scale positivity, and inverses of equal real quantities give the final exact same-law scale identity.

Private pure algebra helpers are allowed only if fully audited with all actual types, generated items and transitive axioms; no cross-module private access, new project axiom, proof weakening, extra public definition, or changed mathematical assumption. No source/probe/Audit/newbranch until the entire independent declaration final is read and CORRECT. All Lean runs on the designated server CPU14-17, at most one heavy lane process, native-M8192/j4/autoImplicitfalse; externalCPU0-9/80GiB untouched. Root alone owns integration/merge/rebase/retarget/pins/cache.

Prospective exact single-import readiness completed2026-10-22T18:17:26.674886Z:17Shao2747Mathlib physical, public2457internal+189externalstops=2646, no source/olean gaps; source-relative canonical17mapa1f4b5aa595cc437fb511345cdcd4b9d3471b3f88bcc50fbc7ea90247e421766. Candidate JSON SHA91abb5a4d85d218e40b372631e76faee3e3e911e1d786c520aad1dabbcf29467. All17 source metadata match the rootv36 receipt7d76700e85b2b495b7d1f0ba771f7029682c999eab062fbebb31a9acc3fe6b35. All are accepted imports; neither C144 nor U19a146 is an import dependency. This is source/cache existence metadata for this new prospective target, not a successful Lean test or acceptance. Reviewer should independently inspect the exact declaration/source/API gates before relying on metadata; prior successful U19a/rootKL checks must not be repeated.

All root groups A/B/C/D remain OPEN. This identity does not by itself assert that the actual D is the Hessian of root's canonical K, that the source parameters form a global saddle, or that root's vCorr has already been connected. Those actual source/canonical consumers remain separate explicit obligations.
