# Exact consumed API and qualification — author165 v1

This records read-only public-interface inspection, not new verification. No old proof was rechecked and no old successful gate was rerun. The parent supplied the curated modules as qualified sources. Local `library/SNAPSHOT.json` at inspection says v59, MERGED_AND_EXACT_TREE_VERIFIED, PR218, main `b6bdf7333a514f9f908c838ddd0161b5617e422e`, accepted head `d9956f24a088a74d7265c6266db1746685be9d35`, tree `daf0d75114c28a26de01399fbaafade1ebae97a1`, receipt SHA256 `30f1cbf1885bfbd141c23a68844696af992cb4b31eb21afc93b6d912da425ccc`.

Pinned environment read from SERVER.md: Lean `leanprover/lean4:v4.36.0-rc1`; mathlib `807d3836b165983210ee2ecf3cd28f239436949c`. No server was contacted and no local toolchain probe/Lean command was run under this proposal-only assignment. Kernel status of the NEW proposal: NOT_IMPLEMENTED_NOT_CHECKED. Final independent review: NOT_YET_COMMISSIONED. Existing qualification is reused only for the exact public values/types listed below; it does not establish any new theorem.

## Exact files read

| Curated/source file | SHA256 |
|---|---|
| original `C:/game/shao/current/oq4/denom01.md`, full131lines/5518bytes | `71b4f28df03edfe3cc8a4ff5f95beb7d80b716d4b7c64fed01a2dc6989448d3f` |
| original `C:/game/shao/current/oq4/energy01.md`, full125lines | `2e0387f0a35ca677853e45fff271cc2fb0e87db9ee9c6b2f00d3bcf56b51d9e6` |
| `library/Shao/OQ4/TruncatedEnergy.lean` | `bd8015535312de5812ccca340e5bb6e7dd2d1c55a8da1e627f6aa228500495c0` |
| `library/Shao/OQ4/EnergyTiltedLaw.lean` | `ea13bcf07671ee77a90910807f09f6c1c1deb95e1834f0715bcc042ab5ecbddd` |
| `library/Shao/OQ4/EnergyLogNormalizer.lean` | `6bbf4093ed296e5fa40cc680f77670c5a3889d95a3679a1cfaf011a84efa6906` |
| `library/Shao/OQ4/EnergyE1Bounds.lean` | `448db6e250307358455e7c8da660ffdb094ddb5a42f0e7e81e9c08c02aa4d39d` |
| `library/Shao/OQ4/EnergyPathLaw.lean` | `3336b977fbe88ae4c27ff7531ffeec6e14c71508587ac2abae99bf475757a177` |
| `library/Shao/Basic/FinitePath.lean` | `898262898f9c088e2d10e6238e411b4397387b21b1b71a2b545c5edef936e1bb` |
| `library/Shao/Basic/ClosedSurvival.lean` | `bb6f334d2a7956ebf2d727d2feabd0765c30af33da4e8b4197f1fd658921811f` |
| `library/Shao/Probability/MeasurablePath.lean` | `827dc47b74dae67101a4d874f412e4cb55bafe1e67b9ba767c6896c0b7e58b41` |
| `library/Shao/Probability/FiniteIID.lean` | `d1b565489199d55af70a27c31a0f803a2b7433e78c9197a361b3c10c0598845b` |

Only public heads and transparent values required for consumption were selected; bodies of unrelated old lemmas are not part of the new review obligation. Source candidates are not labeled already formally proved or novel. All original files are untouched.

## Actually consumed transparent old values

Namespace `Shao.OQ4`, TruncatedEnergy lines17–24:

```lean
noncomputable def energyWeight (h s x : ℝ) : ℝ :=
  if |x| ≤ 2 * h then Real.exp (s * x ^ 2 / h ^ 2) else 0
noncomputable def energyNormalizer (ν : Measure ℝ) (h s : ℝ) : ℝ :=
  ∫ x : ℝ, energyWeight h s x ∂ν
noncomputable def energyNormalizerErrorConstant (T : ℝ) : ℝ :=
  1 / 8 + T / 2 + Real.exp (4 * T) * T ^ 2
```

Namespace `Shao`, FinitePath lines18–32,97–108, and ClosedSurvival26:

```lean
abbrev Path (n : ℕ) := Fin n → ℝ
def prefixSum (a : Path n) (k : ℕ) : ℝ :=
  ∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val < k), a i
def energy (a : Path n) : ℝ := ∑ i, (a i) ^ 2
noncomputable def upperMax (a : Path n) (hn : 0 < n) : ℝ :=
  (Finset.Icc 1 n).sup' (positivePrefixes_nonempty hn) (prefixSum a)
noncomputable def lowerMax (a : Path n) (hn : 0 < n) : ℝ := upperMax (-a) hn
noncomputable def absMax (a : Path n) (hn : 0 < n) : ℝ :=
  max (upperMax a hn) (lowerMax a hn)
def closedStrip (h : ℝ) : Set (Path n) :=
  {a | ∀ k : ℕ, k ≤ n → |prefixSum a k| ≤ h}
```

`positivePrefixes_nonempty` in the displayed old transparent upperMax value is an old proof-valued argument only; no access/copy to this private theorem is proposed. All new mathematical uses call public heads below. The Path measurable space and product probability instances are existing Pi/function instances, not new values to be installed by this unit.

## Actual direct public heads: E1 primitives

```lean
-- Shao.OQ4.TruncatedEnergy
theorem energyWeight_nonneg (h s x : ℝ) : 0 ≤ energyWeight h s x
theorem energyWeight_integrable (ν : Measure ℝ) [IsFiniteMeasure ν]
    (T h s : ℝ) (hT : 0 ≤ T) (hh : 0 < h) (hs : |s| ≤ T) :
    Integrable (energyWeight h s) ν
theorem energyNormalizer_at_zero (ν : Measure ℝ) [IsFiniteMeasure ν] (h : ℝ) :
    energyNormalizer ν h 0 = ν.real {x : ℝ | |x| ≤ 2 * h}
theorem energyNormalizerErrorConstant_nonneg (T : ℝ) (hT : 0 ≤ T) :
    0 ≤ energyNormalizerErrorConstant T
theorem energyNormalizer_expansion (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (T h s : ℝ) (hT : 0 ≤ T) (hh : 1 ≤ h) (hs : |s| ≤ T)
    (hSq : Integrable (fun x : ℝ => x ^ 2) ν)
    (hCube : Integrable (fun x : ℝ => |x| ^ 3) ν)
    (hsecond : (∫ x : ℝ, x ^ 2 ∂ν) = 1) :
    |energyNormalizer ν h s - 1 - s / h ^ 2| ≤
      energyNormalizerErrorConstant T * (∫ x : ℝ, |x| ^ 3 ∂ν) / h ^ 3

-- Shao.OQ4.EnergyTiltedLaw line157
theorem energyTilt_weight_difference_inside (T h s x : ℝ)
    (hT : 0 ≤ T) (hh : 0 < h) (hs : |s| ≤ T) (hx : |x| ≤ 2 * h) :
    |energyWeight h s x - 1| ≤ (Real.exp (4 * T) * T / h ^ 2) * x ^ 2
```

Use map: new H05 uses actual weight integrability and finite product Fubini. New H06 calls the last head with T=s and |s|=s, then integrates the global cutoff weight difference; the integral of x² is1. New H07 calls the raw expansion with T=s. E1 combined mean/variance conclusions are not inputs. No global exponential moment is needed. For sign/nonnegative constants use `energyWeight_nonneg` and `energyNormalizerErrorConstant_nonneg` plus nonnegative integrals.

## Actual direct public heads: paths, closed walls and measurability

All path heads below have ambient `{n : ℕ}` as in their files.

```lean
-- Shao.Basic.FinitePath
theorem energy_nonneg (a : Path n) : 0 ≤ energy a
theorem prefixSum_eq_zero_of_energy_eq_zero (a : Path n)
    (h : energy a = 0) (k : ℕ) : prefixSum a k = 0

-- Shao.Basic.ClosedSurvival lines44,111
theorem mem_closedStrip_iff_absMax_le (a : Path n) (hn : 0 < n) (h : ℝ)
    (hh : 0 ≤ h) : a ∈ closedStrip h ↔ absMax a hn ≤ h
theorem abs_coordinate_le_two_mul_of_mem_closedStrip (a : Path n) (h : ℝ)
    (ha : a ∈ closedStrip h) (i : Fin n) : |a i| ≤ 2 * h

-- Shao.Probability.MeasurablePath lines17,25,61
theorem continuous_prefixSum (k : ℕ) :
    Continuous (fun a : Path n => prefixSum a k)
theorem continuous_energy : Continuous (energy : Path n → ℝ)
theorem measurable_energy : Measurable (energy : Path n → ℝ)
```

New H10 uses finitely many continuous prefix sublevel conditions with the actual continuous variable wall. H11 uses the old exact closedStrip/absMax equivalence at a nonnegative random radius. H12 uses the genuine zero-energy prefix theorem. H15 uses the old public coordinate theorem after deriving membership in the larger fixed closed strip. There is no new boundary convention.

## Finite product/density choice and unconsumed heads checked

`EnergyPathLaw` public `finitePi_withDensity` (line70), `energyPathLaw_withDensity` (line160), `energyPathLaw_real_apply` (line188) and `energyPathLaw_integral` (line230) were inspected. The normalized density interface requires1≤H and genuine unit-second-moment inputs in the energy specialization. The general public product-density head additionally requires that the density measure is a probability. None of these gives the cutoff exponential DIFFERENCE directly. Accordingly this proposal chooses the direct finite cutoff-product identity H04–H05, which was explicitly authorized by the assignment. It does not access/copy `finitePi_withDensity_lintegral`, `energyPath_density_integrable` or `energyPath_closed_density`, all private.

Relevant exact unconsumed public general density head, for scope comparison only:

```lean
theorem finitePi_withDensity (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (d : ℝ → ENNReal) (hd : Measurable d)
    [IsProbabilityMeasure (ν.withDensity d)] (n : ℕ) :
    Measure.pi (fun _ : Fin n => ν.withDensity d) =
      (Measure.pi (fun _ : Fin n => ν)).withDensity (fun a => ∏ i, d (a i))
```

No EnergyPathLaw import is proposed. `energyTiltedLaw` itself is `ν.withDensity(fun x => ofReal(energyWeight h s x/energyNormalizer ν h s))`, but this value is not consumed by any new assertion. EnergyLogNormalizer/EnergyE1Bounds were inspected to confirm that the raw expansion supplies the needed weaker interface without centering. Their thresholds/combined conclusions are not new premises.

`Shao.Probability.iid_samplePath_map_eq_pi` was also checked (FiniteIID32) and remains available to a consumer transferring these π_n bounds to an external iid sample. No redundant iid transport declaration is introduced here. The unit itself already uses the actual iid product measure.

## Mathlib-only proof tools and import freeze

The standard finite product identity is `MeasureTheory.integral_fintype_prod_eq_pow` (actual local curated use in `QuadraticFullNoise.lean`106), with `Integrable.fintype_prod` (actual curated use in `EnergyPathLaw.lean`184). Nonnegative integrable comparisons use ordinary Bochner integral monotonicity/indicator identities. Countable probability subadditivity plus real summable majorants can be formalized either in ENNReal then converted using finiteness or by finite partial unions and continuity from below; no mathematical premise is deferred to this API choice.

The proposal import list is exactly eight imports, reproduced in `declarations.lean.txt`: EnergyTiltedLaw, MeasurablePath, ClosedSurvival, Mathlib Integral.Pi, InfiniteSum.Real, SpecificLimits.Basic, Log.Basic and Trigonometric.Basic. Standard real sqrt/exp/power/finite-set and geometric-series tools are available through these and their pinned dependencies. Resolving exact Mathlib proof-combinator names is an implementation task after freeze, not an extra mathematical assumption. No new top-level helper beyond the26 frozen-proposal heads is authorized by this document.

The theorem statement/proof scope is the finite and asymptotic FAR region only. The unqualified new K/Kv chain149→150→154→156→161, conditional concentration E4, center/middle layers and full OQ4 root are neither consumed nor declared closed.
