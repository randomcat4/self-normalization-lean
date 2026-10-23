# p53 actual marginal symmetry and faithful real population coding

These substantive literal definitions and complete theorem types were frozen before implementation. Original p53 section3, SHA2560bfadbb2021248859f8b15df2ff184c73c879a7203991c27fdc4f5dd6c04f561. Unit109 freezeefaea42bfb1168813061fcb4e7dfc4dcc41fc8f294034156b7d5a0fc9a058d1c; unit110 freeze278787646a7c375c7d3af96eee1aa240bef4c0b2dd0a0efaccb42a5a2e399500.

## Actual population reflection symmetry

```lean
theorem sparsePopulationG_symmetric :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ),
  (sparsePopulationMeasure α x N).map (fun z => -sparsePopulationG α x N z) =
    (sparsePopulationMeasure α x N).map (sparsePopulationG α x N)

theorem sparsePopulationZ_symmetric :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ),
  (sparsePopulationMeasure α x N).map (fun z => -sparsePopulationZ α x N z) =
    (sparsePopulationMeasure α x N).map (sparsePopulationZ α x N)
```

## Actual real observation coding and complete law recovery

```lean
def sparsePopulationEncode (z : (ℝ × (ℕ × Bool)) × (ℕ × Bool)) : ℝ :=
  Shao.OQ5.P35.encodeObservation (Encodable.encode (z.1.2, z.2)) z.1.1

def sparsePopulationDecode (y : ℝ) : (ℝ × (ℕ × Bool)) × (ℕ × Bool) :=
  let labels := (Encodable.decode (Shao.OQ5.P35.decodeCategory y) :
    Option ((ℕ × Bool) × (ℕ × Bool))).getD ((0, false), (0, false))
  ((Shao.OQ5.P35.decodeNoise y, labels.1), labels.2)

def sparseRealMeasure (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) : Measure ℝ :=
  (sparsePopulationMeasure α x N).map sparsePopulationEncode

theorem measurable_sparsePopulationEncode : Measurable sparsePopulationEncode

theorem measurable_sparsePopulationDecode : Measurable sparsePopulationDecode

theorem sparsePopulationDecode_encode :
  ∀ (z : (ℝ × (ℕ × Bool)) × (ℕ × Bool)),
  z.1.1 ∈ Set.Icc (-1 : ℝ) 1 →
  sparsePopulationDecode (sparsePopulationEncode z) = z

theorem sparsePopulationEncode_injectiveOn :
  Set.InjOn sparsePopulationEncode
    {z : (ℝ × (ℕ × Bool)) × (ℕ × Bool) | z.1.1 ∈ Set.Icc (-1 : ℝ) 1}

theorem sparsePopulation_noise_mem_Icc_ae :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ),
  ∀ᵐ z ∂sparsePopulationMeasure α x N, z.1.1 ∈ Set.Icc (-1 : ℝ) 1

theorem sparseRealMeasure_probability :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ),
  IsProbabilityMeasure (sparseRealMeasure α x N)

theorem sparsePopulationDecode_realMeasure_law :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ),
  (sparseRealMeasure α x N).map sparsePopulationDecode =
    sparsePopulationMeasure α x N

theorem sparsePopulationEncode_decode_ae :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ),
  ∀ᵐ y ∂sparseRealMeasure α x N,
    sparsePopulationEncode (sparsePopulationDecode y) = y

theorem measurePreserving_sparsePopulationEncode :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ),
  MeasurePreserving sparsePopulationEncode
    (sparsePopulationMeasure α x N) (sparseRealMeasure α x N)

theorem measurePreserving_sparsePopulationDecode :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ),
  MeasurePreserving sparsePopulationDecode
    (sparseRealMeasure α x N) (sparsePopulationMeasure α x N)

theorem sparsePopulationDecode_realMeasure_prod_law :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ),
  ((sparseRealMeasure α x N).prod (sparseRealMeasure α x N)).map
    (Prod.map sparsePopulationDecode sparsePopulationDecode) =
    (sparsePopulationMeasure α x N).prod (sparsePopulationMeasure α x N)
```

The sourceG symmetry uses genuine independent symmetric noise and signedshift; meanzero is insufficient. Allalpha/x/N statements are structural under the same actual fixedpopulation. Naturalpairedtagcodes need not be surjective. Decode/encode recovery and injectivity require A in closed[-1,1]; encode/decode reconstruction is onlyAE undertheactualreallaw. The totaldecoder uses fixedzerotags offcodeimage.
