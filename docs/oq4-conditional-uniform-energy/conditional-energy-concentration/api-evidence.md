# Direct API evidence — author163 E4 proposal

This records direct API reading and existing qualification, not a new review of old producers. Only the owned proposal directory was written. No server/Lean/build/cache/Git operation occurred. No local Lean/toolchain probe was attempted: SERVER.md fixes Lean4.36.0-rc1/mathlib807d3836 and expressly forbids local checks; the parent authorized mathematical proposals only. Original source, actual public heads and transparent values below received complete reading in this author context. Old complete proof packets are not being re-certified.

## Source, pins and ownership

- Original `C:/game/shao/current/oq4/energy01.md`: complete125lines,5244bytes, SHA256 `2e0387f0a35ca677853e45fff271cc2fb0e87db9ee9c6b2f00d3bcf56b51d9e6`; E4(11)–(12), lines99–120 only. Original C:/game/shao is read-only.
- Current REGISTRY explicitly lists active OQ4 lead `01a1669c-2422-7fa2-9f3c-16bb5bd2dfc4`, old writer released, replacement activated. The present author owns only `drafts/oq4/conditional-energy-concentration-author-v1/`; no children or threads were created.
- Read AGENTS.md, SERVER.md, current TEAM ownership/constraints, current REGISTRY OQ4 fields, takeover/restart instructions and streamlined acceptance. Use math-theorem, not math-ultra. Parent is the exclusive lane lead, not the root coordinator.
- Curated library SNAPSHOT v59 is `MERGED_AND_EXACT_TREE_VERIFIED`, main `b6bdf7333a514f9f908c838ddd0161b5617e422e`, receipt-v59 SHA256 `30f1cbf1885bfbd141c23a68844696af992cb4b31eb21afc93b6d912da425ccc`. Direct old source hashes below are present unchanged in its frozen-source map. This snapshot is read-only, not a build checkout.

## Qualified direct dependencies and exact source/object chain

| Direct module | Source SHA256 actually checked locally | Existing original producer object / qualification |
|---|---|---|
| EnergyJointTransport | `fe6fe757c7fe997cc36727477b4d22f17c2373b7e90657d68f7b5d7ef8d2a39e` | Unique original object `2979d67eb763a4a8e69f38dd736db5cee49e6169d93bc74f82c7bfce023d807a`; qualified full independent review SHA `c800930e19960f001423af6039d4b9f44b10f29678a62c6aaef5bacb5403e164`; source/object identity and actual all-owned kernel/axioms are bound in that report and existing author receipt. |
| EnergyE2Bounds | `41b7343861549f55ae86cddb514a5ed55612448b1ab0efc1e3bb580182746ca8` | Unique original author object `df937ab8fafcaacc7bbd37e3413356f15fddff0ed282807692269934614dd7c9`; qualified full independent review SHA `e658429f2932761cfa3535bb49a6f050730f75d5b9635075e6e35064f6ca1d0b`; existing checks are successful exact-source target/complete-source and full imported-owner axiom audits. |
| EnergyPathLaw | `3336b977fbe88ae4c27ff7531ffeec6e14c71508587ac2abae99bf475757a177` | Qualified old dependency within the E2/JointTransport source-object chain; no new producer check or separate new object is requested. |
| EnergyRelativePathBounds | `7f9242f4116924f26c9c7b75313e4e37b49c13f7da4f4052e7a7585984a2b654` | Qualified old dependency; complete transparent conclusion value was read, not assumed from its name. Its integrability conjunct agrees with the direct EnergyPathLaw public integrability head. |

Evidence locations: `library/docs/oq4-energy-joint-transport-{author-receipt.json,formal-review-v1.md}`, `library/verification/oq4-energy-joint-transport{,-all}/receipt.json`, `library/docs/oq4-energy-e2-{author-receipt.md,formal-review-v1.md}`, `library/verification/oq4-energy-e2/receipt.json`, and `library/verification/receipt-v59.json`. The joint all-import receipt is SHA `d13be4ec2849965d948b0a0b062cca5a980934659ce9b95d844b20116c586ccb`. Both old reviews accept their exact finite/scalar scope and leave E4/K/Kv and general OQ4 OPEN. Old historical PENDING_ROOT/publication fields are not treated as current acceptance status; the current curated snapshot and lead's qualification instruction determine reuse. No old evidence is rewritten.

## Future dependency and qualification boundary

Future `drafts/oq4/unconditional-kernel-inputs-author-v1/UnconditionalKernelAsymptotic.lean`, actual source SHA256 `adb54266b148a86a116a198a8d31f3a206f487457430e5dd9e787daca0eac10b`,233LF; frozen heads file SHA256 `559fe9d75db2c25c79daa0f9cd7b81cb275f3a2bc7dc2daddd19222570d45811`. The future161 public Kv head is read as the direct planned composition interface; its proof is not reviewed or copied here. K for ν is obtained as the v=1 case, rather than introducing a desiredK premise. The theorem's all-index law/height conditions are discharged by the explicitly proved finite-prefix adapter in proof.md.

Parent update during this turn: rootBE is QUALIFIED, source `8bf02df1210d69a2934746987d0022a85166d17c9850fa4fd27656eb88bb2af9`, commit `ba7ef8674924248e6eb6fb78d8c59aaf848a6627`, original object `d67df1b97eddcde16ee7d9fedc6e6e7e4af11e22e04732a69dbd0b5883b76b57`, fresh complete review SHA `01ab66c3d10f4ed72d28ddffa1b56c5de177d32a260e0efc9c7c42e81883ecec`. This is parent-reported status, not a second author audit. Future161 and149→150→154→156 qualifications are still pending. No K/Kv/E4/root closure is claimed.

## Exact direct heads and transparent values read

The following selected excerpts are copied from the pinned local sources, with proof bodies omitted. They are API-reading evidence, not new declarations or proof proposals. Every additional value used in the new proof is proof-local and explicitly specified in proof.md. The new module proposal has no new definitions or instances.

### library/Shao/Basic/FinitePath.lean:18-31
```lean
abbrev Path (n : ℕ) := Fin n → ℝ

variable {n : ℕ}

/-- Sum of the first k coordinates, saturated at the path length. -/
def prefixSum (a : Path n) (k : ℕ) : ℝ :=
  ∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val < k), a i

/-- Actual squared coordinates in the first k positions. -/
def prefixSquares (a : Path n) (k : ℕ) : ℝ :=
  ∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val < k), (a i) ^ 2

/-- Genuine final energy, without centering or replacement by variance. -/
def energy (a : Path n) : ℝ := ∑ i, (a i) ^ 2
```

### library/Shao/Basic/ClosedSurvival.lean:26-27
```lean
def closedStrip (h : ℝ) : Set (Path n) :=
  {a | ∀ k : ℕ, k ≤ n → |prefixSum a k| ≤ h}
```

### library/Shao/OQ4/RademacherScalarBounds.lean:17-17
```lean
def lambda : ℝ := Real.pi ^ 2 / 8
```

### library/Shao/OQ4/TruncatedEnergy.lean:17-21
```lean
noncomputable def energyWeight (h s x : ℝ) : ℝ :=
  if |x| ≤ 2 * h then Real.exp (s * x ^ 2 / h ^ 2) else 0

noncomputable def energyNormalizer (ν : Measure ℝ) (h s : ℝ) : ℝ :=
  ∫ x : ℝ, energyWeight h s x ∂ν
```

### library/Shao/OQ4/EnergyTiltedLaw.lean:11-12
```lean
noncomputable def energyTiltedLaw (ν : Measure ℝ) (h s : ℝ) : Measure ℝ :=
  ν.withDensity (fun x => ENNReal.ofReal (energyWeight h s x / energyNormalizer ν h s))
```

### library/Shao/OQ4/EnergyLinearTiltLaw.lean:9-10
```lean
noncomputable def energyLinearNormalizer (ν : Measure ℝ) (h s t : ℝ) : ℝ :=
  ∫ x : ℝ, Real.exp (t * x) ∂energyTiltedLaw ν h s
```

### library/Shao/OQ4/EnergyLinearTiltLaw.lean:21-23
```lean
noncomputable def energyLinearTiltLaw (ν : Measure ℝ) (h s t : ℝ) : Measure ℝ :=
  (energyTiltedLaw ν h s).withDensity
    (fun x => ENNReal.ofReal (Real.exp (t * x) / energyLinearNormalizer ν h s t))
```

### library/Shao/OQ4/EnergyE2Bounds.lean:9-15
```lean
noncomputable def energyE2Threshold (M T : ℝ) : ℝ := energyLinearCenteringThreshold M T

noncomputable def energyE2Constant (M T : ℝ) : ℝ :=
  1 + energyLinearCenteringK M T +
    energyLinearCenteringK M T * (energyLinearVarianceA M T + 2 * energyLinearCenteringK M T) +
    (energyLinearVarianceA M T + energyLinearVarianceB M T (energyLinearCenteringK M T)) +
    Real.exp 2 * energyLinearVarianceA M T
```

### library/Shao/OQ4/EnergyE2Bounds.lean:17 (complete head)
```lean
theorem energyE2Constant_dominates (M T : ℝ) (hM : 0 ≤ M) (hT : 0 ≤ T) :
    1 ≤ energyE2Constant M T ∧ energyLinearCenteringK M T ≤ energyE2Constant M T ∧
    energyLinearCenteringK M T * (energyLinearVarianceA M T + 2 * energyLinearCenteringK M T) ≤ energyE2Constant M T ∧
    energyLinearVarianceA M T + energyLinearVarianceB M T (energyLinearCenteringK M T) ≤ energyE2Constant M T ∧
    Real.exp 2 * energyLinearVarianceA M T ≤ energyE2Constant M T
```

### library/Shao/OQ4/EnergyE2Bounds.lean:118-129
```lean
def energyE2Conclusion (ν : Measure ℝ) (M T h s θ : ℝ) : Prop :=
  energyLinearMean ν h s θ = 0 ∧
  IsProbabilityMeasure (energyLinearTiltLaw ν h s θ) ∧
  (∀ᵐ x ∂energyLinearTiltLaw ν h s θ, |x| ≤ 2 * h) ∧
  Integrable (fun x : ℝ => x) (energyLinearTiltLaw ν h s θ) ∧
  Integrable (fun x : ℝ => x ^ 2) (energyLinearTiltLaw ν h s θ) ∧
  Integrable (fun x : ℝ => |x| ^ 3) (energyLinearTiltLaw ν h s θ) ∧
  (∫ x : ℝ, x ∂energyLinearTiltLaw ν h s θ) = 0 ∧
  |θ| ≤ energyE2Constant M T / h ^ 2 ∧
  |Real.log (energyLinearNormalizer ν h s θ)| ≤ energyE2Constant M T / h ^ 4 ∧
  |(∫ x : ℝ, x ^ 2 ∂energyLinearTiltLaw ν h s θ) - 1| ≤ energyE2Constant M T / h ∧
  (∫ x : ℝ, |x| ^ 3 ∂energyLinearTiltLaw ν h s θ) ≤ energyE2Constant M T
```

### library/Shao/OQ4/EnergyPathLaw.lean:85-89
```lean
noncomputable def energyPathIntegrand {n : ℕ} (h s : ℝ) (a : Shao.Path n) : ℝ :=
  by
    classical
    exact if a ∈ Shao.closedStrip h then
      Real.exp (s * (Shao.energy a - (n : ℝ)) / h ^ 2) else 0
```

### library/Shao/OQ4/EnergyPathLaw.lean:149 (complete head)
```lean
theorem energyPathIntegrand_integrable (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (n : ℕ) (T h s : ℝ) (hT : 0 ≤ T) (hh : 1 ≤ h) (hs : |s| ≤ T) :
    Integrable (energyPathIntegrand (n := n) h s) (Measure.pi (fun _ : Fin n => ν))
```

### library/Shao/OQ4/EnergyJointTransport.lean:15-29
```lean
noncomputable def energyJointCenteredProbability (ν : Measure ℝ) (n : ℕ) (h s θ : ℝ) : ℝ :=
  (Measure.pi (fun _ : Fin n => energyLinearTiltLaw ν h s θ)).real (Shao.closedStrip h)

noncomputable def energyJointIntegral (ν : Measure ℝ) (n : ℕ) (h s : ℝ) : ℝ :=
  ∫ a, energyPathIntegrand h s a ∂Measure.pi (fun _ : Fin n => ν)

def energyJointErrorLimits (M T : ℝ) (h : ℕ → ℝ) (n : ℕ → ℕ) : Prop :=
  Tendsto (fun j => energyRelativePathError2 M T (n j) (h j)) atTop (𝓝 0) ∧
  Tendsto (fun j => energyRelativePathError M T (n j) (h j)) atTop (𝓝 0) ∧
  Tendsto (fun j => Real.exp (energyRelativePathError2 M T (n j) (h j)) - 1) atTop (𝓝 0) ∧
  Tendsto (fun j => Real.exp (energyRelativePathError M T (n j) (h j)) - 1) atTop (𝓝 0) ∧
  Tendsto (fun j => Real.exp (-energyRelativePathError2 M T (n j) (h j))) atTop (𝓝 1) ∧
  Tendsto (fun j => Real.exp (energyRelativePathError2 M T (n j) (h j))) atTop (𝓝 1) ∧
  Tendsto (fun j => Real.exp (-energyRelativePathError M T (n j) (h j))) atTop (𝓝 1) ∧
  Tendsto (fun j => Real.exp (energyRelativePathError M T (n j) (h j))) atTop (𝓝 1)
```

### library/Shao/OQ4/EnergyJointTransport.lean:41-64
```lean
def energyJointFiniteConclusion (ν : Measure ℝ) (M T h s θ : ℝ) (n : ℕ) : Prop :=
  energyE1Conclusion ν T h s ∧ energyE2Conclusion ν M T h s θ ∧
  0 < energyLinearNormalizer ν h s θ ∧ 0 < energyNormalizer ν h s ∧
  energyRelativePathConclusion ν M T h s θ n ∧
  0 ≤ Real.exp (energyRelativePathError2 M T n h) - 1 ∧
  0 ≤ Real.exp (energyRelativePathError M T n h) - 1 ∧
  |energyJointBaseProbability ν n h s - energyJointCenteredProbability ν n h s θ| ≤
    (Real.exp (energyRelativePathError2 M T n h) - 1) *
      energyJointCenteredProbability ν n h s θ ∧
  |energyJointIntegral ν n h s - energyJointCenteredProbability ν n h s θ| ≤
    (Real.exp (energyRelativePathError M T n h) - 1) *
      energyJointCenteredProbability ν n h s θ

def energyJointSequenceConclusion (ν : Measure ℝ) (M T : ℝ)
    (h s θ : ℕ → ℝ) (n : ℕ → ℕ) : Prop :=
  energyJointErrorLimits M T h n ∧ energyJointNormalizationLimits ν h s θ n ∧
  (∀ᶠ j in atTop, energyJointFiniteConclusion ν M T (h j) (s j) (θ j) (n j)) ∧
  ∀ η : ℝ, 0 < η → ∀ᶠ j in atTop,
    |energyJointBaseProbability ν (n j) (h j) (s j) -
        energyJointCenteredProbability ν (n j) (h j) (s j) (θ j)| ≤
      η * energyJointCenteredProbability ν (n j) (h j) (s j) (θ j) ∧
    |energyJointIntegral ν (n j) (h j) (s j) -
        energyJointCenteredProbability ν (n j) (h j) (s j) (θ j)| ≤
      η * energyJointCenteredProbability ν (n j) (h j) (s j) (θ j)
```

### library/Shao/OQ4/EnergyJointTransport.lean:339 (complete head)
```lean
theorem energyJointTransport_common_bounds (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (M T : ℝ) (h s : ℕ → ℝ) (hM : 0 ≤ M) (hT : 0 ≤ T)
    (hh : Tendsto h atTop atTop) (hs : ∀ j, |s j| ≤ T)
    (hSq : Integrable (fun x : ℝ => x ^ 2) ν) (hCube : Integrable (fun x : ℝ => |x| ^ 3) ν)
    (hsecond : (∫ x : ℝ, x ^ 2 ∂ν) = 1) (hmean : (∫ x : ℝ, x ∂ν) = 0)
    (hβM : (∫ x : ℝ, |x| ^ 3 ∂ν) ≤ M) :
    ∃ θ : ℕ → ℝ,
      (∀ j, h j < energyE2Threshold M T → θ j = 0) ∧
      (∀ᶠ j in atTop, energyE2Conclusion ν M T (h j) (s j) (θ j) ∧
        ∀ m : ℕ, energyRelativePathConclusion ν M T (h j) (s j) (θ j) m) ∧
      energyJointIIDTail.{u,v,w} ν M T h s θ ∧
      ∀ n : ℕ → ℕ, Tendsto (fun j => (n j : ℝ) / h j ^ 3) atTop (𝓝 0) →
        energyJointSequenceConclusion ν M T h s θ n
```

### drafts/oq4/unconditional-kernel-inputs-author-v1/UnconditionalKernelAsymptotic.lean:190 (complete head)
```lean
theorem varying_row_variance_closedStrip_relative_asymptotic
    (νSeq : ℕ → Measure ℝ) (hprob : ∀ j, IsProbabilityMeasure (νSeq j))
    (vSeq : ℕ → ℝ)
    (h3 : ∀ j, Integrable (fun x : ℝ => |x| ^ 3) (νSeq j))
    (hmean : ∀ j, (∫ x : ℝ, x ∂(νSeq j)) = 0)
    (hsecond : ∀ j, (∫ x : ℝ, x ^ 2 ∂(νSeq j)) = vSeq j)
    (hvlower : ∀ j, (1 / 2 : ℝ) ≤ vSeq j)
    (hvupper : ∀ j, vSeq j ≤ 2)
    (M : ℝ) (hM : ∀ j, (∫ x : ℝ, |x| ^ 3 ∂(νSeq j)) ≤ M)
    (hSeq : ℕ → ℝ) (NSeq : ℕ → ℕ) (hpos : ∀ j, 0 < hSeq j)
    (hinfty : Tendsto hSeq atTop atTop)
    (hlong : Tendsto (fun j => (NSeq j : ℝ) / hSeq j ^ 2) atTop atTop)
    (hshort : Tendsto (fun j => (NSeq j : ℝ) / hSeq j ^ 3)
      atTop (𝓝 (0 : ℝ))) :
    Tendsto (fun j =>
      (Measure.pi (fun _ : Fin (NSeq j) => νSeq j)).real
        (@Shao.closedStrip (NSeq j) (hSeq j)) /
          ((4 / Real.pi) *
            Real.exp (-lambda * vSeq j * (NSeq j : ℝ) / hSeq j ^ 2)))
      atTop (𝓝 (1 : ℝ))
```

