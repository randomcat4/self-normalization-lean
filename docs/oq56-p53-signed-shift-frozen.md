# Unit104: fixed signed shift (frozen v1)

Source: p53§3 G=A+eta*d_B. This unit realizes only the tagged shiftcomponent, to supply honestL1/zero-mean/allpositivepolynomialmoments before constructingGwithuniformnoise. The literal underlying d_j is accepted sparseLevelShift (zeroat0, otherwise t_j²/((N_j:ℝ)-2)); retainreal subtraction andallacceptedCoreconditions.

One publicdefinitionbody and8 complete theoremtypes are frozen below. Measurability/symmetry usearbitraryα/x/N; all6analytictypes explicitlykeepα>0 andthe sameSparseSelectionCore fromaccepted101shiftmomentinterfaces. The sameα/fullgivenpossiblynonmonotonex/N precede everyq. Symmetryisactualpushforwardmeasureequalityevenwhenamplitudescollide. PayL1beforemean/integrals.

Mainleaddesignedthissource-boundinterface, usingthe103consumerpattern;103theoremsarenotformal dependencies. Onlyaccepted101+102areimported. Source-reviewerandlaterfinalreviewermustbeindependentneverauthor. Noimplementation/LeanbeforeSOURCEacceptance. No exponentialmoment/strictshiftvariance claim; fullA/G/Zjointlaw,iid/encoding/kernel/operator/trueR/events/tailsstayOPEN. P53/OQ6/RS2OPEN.

Module Shao.OQ5.P53.SparseSignedShift; namespace Shao.OQ5.P53.

## sparseSignedShift

```lean
def sparseSignedShift (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) (z : ℕ × Bool) : ℝ :=
  if z.2 = true then sparseLevelShift α x N z.1
  else -sparseLevelShift α x N z.1
```

## measurable_sparseSignedShift

```lean
theorem measurable_sparseSignedShift :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ), Measurable (sparseSignedShift α x N)
```

## sparseSignedShift_symmetric

```lean
theorem sparseSignedShift_symmetric :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ),
  (sparseSignedLabelMeasure α x N).map (fun z => -sparseSignedShift α x N z) =
    (sparseSignedLabelMeasure α x N).map (sparseSignedShift α x N)
```

## integrable_sparseSignedShift

```lean
theorem integrable_sparseSignedShift :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ),
  0 < α → SparseSelectionCore α x N → Integrable (sparseSignedShift α x N) (sparseSignedLabelMeasure α x N)
```

## integral_sparseSignedShift_zero

```lean
theorem integral_sparseSignedShift_zero :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ), 0 < α → SparseSelectionCore α x N →
  (∫ z, sparseSignedShift α x N z ∂(sparseSignedLabelMeasure α x N)) = 0
```

## integrable_sparseSignedShift_rpow

```lean
theorem integrable_sparseSignedShift_rpow :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ), 0 < α → SparseSelectionCore α x N → ∀ q : ℝ, 0 < q →
  Integrable (fun z => |sparseSignedShift α x N z| ^ q) (sparseSignedLabelMeasure α x N)
```

## integral_sparseSignedShift_rpow

```lean
theorem integral_sparseSignedShift_rpow :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ), 0 < α → SparseSelectionCore α x N → ∀ q : ℝ, 0 < q →
  (∫ z, |sparseSignedShift α x N z| ^ q ∂(sparseSignedLabelMeasure α x N)) =
    ∫ j, |sparseLevelShift α x N j| ^ q ∂(sparseLabelMeasure α x N)
```

## integrable_sparseSignedShift_sq

```lean
theorem integrable_sparseSignedShift_sq :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ), 0 < α → SparseSelectionCore α x N →
  Integrable (fun z => (sparseSignedShift α x N z) ^ 2) (sparseSignedLabelMeasure α x N)
```

## integral_sparseSignedShift_sq

```lean
theorem integral_sparseSignedShift_sq :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ), 0 < α → SparseSelectionCore α x N →
  (∫ z, (sparseSignedShift α x N z) ^ 2 ∂(sparseSignedLabelMeasure α x N)) =
    ∫ j, (sparseLevelShift α x N j) ^ 2 ∂(sparseLabelMeasure α x N)
```


Frozen source interface identities: MD SHA256 `47d0f040afd13cb3e72b2b7c4ba0adb24848908d40deabb214bb26dd7a86cf6c`; contracts JSON SHA256 `e73c213da81a480b8065eaeb9859bf10321eab178c9b8df73eeeb1fd02c3daff`. Canonical implementation: `962c69c03535613659530ffd6f9890e987e1742572167531dd119a19c5dbf187`, 7387 bytes.
