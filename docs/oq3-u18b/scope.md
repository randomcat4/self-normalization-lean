# OQ3-U18b: actual finite-stage source coefficient limit, R1(19)

Frozen v1 DECLARATION_REVIEW; not approved/implemented. Proposed Shao/OQ3/StageSourceAsymptotic.lean; imports Shao.OQ3.NormalLayerWeakConvergence and Shao.OQ3.StageLayerSeriesLimit; namespace Shao.OQ3, open MeasureTheory Filter, open scoped Topology BigOperators, noncomputable section. Zero public definitions, one complete public target. U18a entire162line26441B CORRECT fullproof final c9c87bfbf424a2ee5f94cbe7a474d317844903cb331772e75bd27e8ee8192cea was read before its acceptance/PR139 exact publication and this successor scope.

Original target -> R1 report sections5/6, especially(15)/(17)/(19), actual fixed finite-law positive-tail coefficient along every phase->0 subsequence. Original report SHA3473d34ff20bd0d334b9ef3ea3c3ee167fba4d5cc3a742849820ce54d639e662. Remaining obligation -> accepted StageLayerSeriesLimit gives the genuine full integer Gaussian-layer sum and actual normalizedTailCoefficient limit after an explicit complete actual hcont family. This module eliminates that analytic premise by producing it for the same actual finite-stage law from accepted U18a. Direct consumers -> actual source26 arbitrarilylate phase witnesses and source31 fixed-law prefix-first construction. Remaining -> final law diagonal/unbounded remainder, general KL/global extended-Legendre minimizer, exact original root assemblies and all OQ3 A/B/C/D OPEN; no claim about a uniform triangular-array rate, hW, literalPhi or exact source24 zeta expansion.

```lean
theorem normalizedTailCoefficient_stage_subsequence_tendsto_of_stage
    (w : AtomicIndex → ℝ) (hw : ∀ i, 0 ≤ w i) (hs : HasSum w 1)
    (J : ℕ) (q : ℝ) (hq0 : 1 < q) (hq1 : q < 103 / 100)
    (hmeanY : (∫ x : ℝ, normalValue x ∂atomicMeasure w) = q)
    (hmeanX : (∫ x : ℝ, x ∂atomicMeasure w) = q / 4)
    (hrange : ∀ᵐ x ∂atomicMeasure w, x ∈ Set.range (fun i : Fin 4 ⊕ Fin J =>
      stageAtom (fun j : Fin J => addedAtom j.val) i))
    (hpos : ∀ i : Fin 4 ⊕ Fin J, 0 < (atomicMeasure w).real
      {stageAtom (fun j : Fin J => addedAtom j.val) i})
    (m : ℕ → ℕ) (hm : Tendsto m atTop atTop)
    (hphase : Tendsto (fun j : ℕ => Int.fract ((m j : ℝ) * q / dyadicMesh J))
      atTop (nhds 0)) :
    Summable (fun k : ℤ => sourceGaussianLayerWeight (atomicMeasure w) q sourceEll
        (dyadicMesh J * (k : ℝ))) ∧
      Tendsto (fun j : ℕ => normalizedTailCoefficient sourceEll q w (m j))
        atTop (nhds ((dyadicMesh J / Real.sqrt (normalVariance (atomicMeasure w))) *
          ∑' k : ℤ, sourceGaussianLayerWeight (atomicMeasure w) q sourceEll
            (dyadicMesh J * (k : ℝ))))
```

The full target preserves the accepted conditional series theorem's w/hw/HasSum1/J/qwindow/true EY and EX=q/4/actual AE finite support/all active atoms positive/m->atTop/phase->0 and its entire Summable-and-Tendsto conclusion. Only its old public hcont binder is removed. No law or q is chosen again along n, m, d, frequency, or a target set. Finite inactive weights may be zero; strict positivity is only for Fin4+FinJ active actual singleton masses. J0 and the existing all-n normalized coefficient remain valid. No stronger measurability or pointwise n-positive/normal-layer-positive premise is introduced.

Inside the proof the actual atomicMeasure w is a probability from hw and HasSum w 1. Derive hb from actual AE stage range and fixedAtom_bounds; obtain base singleton positivity from the active inl points, then public normalVariance_pos and parabolaCovariance_det_pos for that same actual measure. For arbitrary whole d with its stated all-n bound and eventual lattice compatibility, and arbitrary A with actual Gaussian frontier null, U18a stage_normalLayerConditionalLaw_real_tendsto supplies precisely the removed hcont with a=q/4 and all existing true means/support gates. Consume the accepted complete series theorem at those same objects. These are implementation obligations, not extra public assumptions; a manually assumed hcont, changed Gaussian or new probability proxy is disallowed.

U18a source88lines4406B SHA9ffb7595e90afe46ab4e207241b26bbee281e01e1f08d91dafce3aed73bc76d5 is independently accepted and frozen PR139 head468fcefcf6205827a9551cba39b4c5afaf959150, authorreceipt7cbfefaccc6a00113853ec339c76a23d2d9de92ea30c1b74d2bfbb19d2756484. StageLayerSeriesLimit remains accepted source SHA4c797f9f5f9b47c0f62764c0b62396b9679172782d144fca29a091b83a52e02d. Root latest v34 main60c8bb8169de0576fa38b2d83e6ba93953677650/receipt9937f78ea9e9137faebffad65191a9b49b7d2a1852ffe131b2c5da8b3df3c1b6 preserves old dependencies; source checkout remains frozen U18a until a suitable integrated checkpoint, no lane merge/rebase/reset or shared/cache edits.

Read-only candidate closure for exactly these two actual imports completed16:10UTC: physical53 Shao/2973 Mathlib, public2696 internal+189 external stops=2885, source/olean missing0, canonical53project-map SHA64b2df2d535f500ead30cf7d5d3bfd8b66016f9fd15c154e2f8254b138a031fb. U18a was still provisional when that metadata was captured and has since been independently accepted with unchanged source hash; the other52 entries match v34 receipt metadata. This readiness is not this target's proof. Do not repeat root successful import smoke or download raw complete logs; root owns caches and pins. Reviewer independently checks actual APIs/necessary graph last without reading author candidate/scanner or future notes.

Independent declaration review first extracts this one complete type and persists blind translation, then scope/R1/actual accepted U18a and series/model APIs, mechanical last. No successor source/Audit/probe/new branch is written before complete CORRECT declaration final is read in full. Reviewer owns only its report, no source/cache/Lean/probe/rebuild/spawn. All Lean work on designated server CPU14-17/native-M8192-j4/-DautoImplicit=false, one lane heavy total. No sorry/admit/new axiom/unsafe/native_decide/implemented_by or settings weakening; whitelist propext/Classical.choice/Quot.sound. ExternalCPU0-9/80GiB untouched. All original roots remain OPEN.
