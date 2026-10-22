# Actual full source noise: exact declaration proposal

STATUS: PROPOSED_FOR_INDEPENDENT_DECLARATION_REVIEW.

Four dependency nodes are proposed below. They are the minimum useful split:
actual single-chord moments; an actually inhabited fixed scalar density; actual
finite-product full noise; its original conditional-law budget specialization.
No implementation, Lean invocation, object or mechanical acceptance is claimed.

## Source binding and bearing

Fixed source bytes, independently rehashed this turn:

```text
main.tex       beb00f718487e36de433175c97f1d500cb48e7a92ce5bd5ad5d62bb132122d06
supplement.tex b99f2ac4d2f39dd39772d98a5702b7a923c2f10f8730a08fc1b4cd6bba4742bd
```

Main650–670 fixes the biased-pair chord, the two independent families J=8,
the fixed even smooth scalar density and the reflection argument. Main673–690
defines actual characteristic integrals and gives the Xi product formula.
Supplement486–518 states all support/moment and smoothing-size constants;
supplement1988–2042 proves them. The exact constants must be 34,64,67/3,128/3,
70/3, with the source coefficient100 subsequently obtained. Later Xi derivative,
gap optimization and inversion claims remain separate open dependencies.

Accepted actual inputs, unchanged:

```text
QuadraticChordNoise.lean 75069c06d5794a5e530e99260e6e3308656623ea39944ac70f1d958ffd40d275
SourceFourierScale.lean  5f31eb92eff8ded33b91f55a59a16de4e58cdd7a9e0514d082a2c4932f5feff0
```

All Probability nodes use namespace Shao.Probability, open MeasureTheory
ProbabilityTheory, open scoped BigOperators, and autoImplicit false.
The final source node uses namespace Shao to match SourceFourierScale.

## Node A: QuadraticChordMoments.lean, two public theorems

Import the accepted QuadraticChordNoise. The displayed definitions of V,m3,gamma
are lets, not additional free inputs. The actual probability and support facts
are reused from the accepted law_data theorem.

```lean
theorem quadraticTriangle_moments :
    Integrable (fun t : ℝ => t) quadraticTriangleLaw ∧
    Integrable (fun t : ℝ => |t|) quadraticTriangleLaw ∧
    Integrable (fun t : ℝ => t ^ 2) quadraticTriangleLaw ∧
    (∫ t : ℝ, t ∂quadraticTriangleLaw) = 0 ∧
    (∫ t : ℝ, |t| ∂quadraticTriangleLaw) = (1 / 3 : ℝ) ∧
    (∫ t : ℝ, t ^ 2 ∂quadraticTriangleLaw) = (1 / 6 : ℝ)

theorem quadraticChord_moments (nu : Measure ℝ) [IsProbabilityMeasure nu]
    (h3 : Integrable (fun a : ℝ => |a| ^ 3) nu)
    (hV : 0 < variance (id : ℝ → ℝ) nu)
    (h : ℝ) (hh : 0 < h) (hs : ∀ᵐ a : ℝ ∂nu, |a| ≤ h) :
    let V := variance (id : ℝ → ℝ) nu
    let gamma := (∫ a : ℝ, |a| ^ 3 ∂nu) / V
    Integrable (fun z : ℝ × ℝ => z.1) (quadraticChordLaw nu) ∧
    Integrable (fun z : ℝ × ℝ => |z.1|) (quadraticChordLaw nu) ∧
    Integrable (fun z : ℝ × ℝ => z.1 ^ 2) (quadraticChordLaw nu) ∧
    Integrable (fun z : ℝ × ℝ => |z.2|) (quadraticChordLaw nu) ∧
    (∫ z : ℝ × ℝ, z.1 ∂quadraticChordLaw nu) = 0 ∧
    (∫ z : ℝ × ℝ, |z.1| ∂quadraticChordLaw nu) =
      (∫ p : ℝ × ℝ, |p.1 - p.2| ^ 3 ∂nu.prod nu) / (6 * V) ∧
    (∫ z : ℝ × ℝ, z.1 ^ 2 ∂quadraticChordLaw nu) =
      (∫ p : ℝ × ℝ, (p.1 - p.2) ^ 4 ∂nu.prod nu) / (12 * V) ∧
    (∫ z : ℝ × ℝ, |z.1| ∂quadraticChordLaw nu) ≤ (4 / 3 : ℝ) * gamma ∧
    (∫ z : ℝ × ℝ, |z.2| ∂quadraticChordLaw nu) ≤ (8 / 3 : ℝ) * h * gamma ∧
    (∫ z : ℝ × ℝ, z.1 ^ 2 ∂quadraticChordLaw nu) ≤ (4 / 3 : ℝ) * h * gamma
```

The exact triangle integrals must come from the actual accepted density.
The chord identities must use its actual biased product/map law. The bound
integral |D|^3<=8m3 and integral D^4<=16hm3 are proved, not assumed.

## Node B: SourceScalarNoise.lean, three definitions, three public theorems

Use Mathlib.Analysis.Calculus.BumpFunction.Normed plus the real bump instance
from InnerProduct (read-only API confirmed, compilation not yet checked).
The following private bump is fixed actual data, with no chosen-law premise:

```lean
private def sourceScalarBump : ContDiffBump (0 : ℝ) :=
  ⟨1 / 2, 1, by norm_num, by norm_num⟩

noncomputable def sourceScalarDensity : ℝ → ℝ := sourceScalarBump.normed volume

noncomputable def sourceScalarLaw : Measure ℝ :=
  volume.withDensity (fun t => ENNReal.ofReal (sourceScalarDensity t))

noncomputable def sourceScalarChar (t : ℝ) : ℂ :=
  ∫ r : ℝ, Complex.exp (((t * r : ℝ) : ℂ) * Complex.I) ∂sourceScalarLaw

theorem sourceScalarDensity_data :
    ContDiff ℝ ∞ sourceScalarDensity ∧ HasCompactSupport sourceScalarDensity ∧
    (∀ t : ℝ, 0 ≤ sourceScalarDensity t) ∧
    (∀ t : ℝ, sourceScalarDensity (-t) = sourceScalarDensity t) ∧
    (∀ t : ℝ, 1 ≤ |t| → sourceScalarDensity t = 0) ∧
    (∫ t : ℝ, sourceScalarDensity t) = 1

theorem sourceScalarLaw_data :
    IsProbabilityMeasure sourceScalarLaw ∧
    Measure.map (fun t : ℝ => -t) sourceScalarLaw = sourceScalarLaw ∧
    (∀ᵐ t : ℝ ∂sourceScalarLaw, |t| ≤ 1) ∧
    Integrable (fun t : ℝ => t) sourceScalarLaw ∧
    Integrable (fun t : ℝ => |t|) sourceScalarLaw ∧
    Integrable (fun t : ℝ => t ^ 2) sourceScalarLaw ∧
    (∫ t : ℝ, t ∂sourceScalarLaw) = 0 ∧
    (∫ t : ℝ, |t| ∂sourceScalarLaw) ≤ 1 ∧
    (∫ t : ℝ, t ^ 2 ∂sourceScalarLaw) ≤ 1

theorem sourceScalarChar_even_bound (t : ℝ) :
    sourceScalarChar (-t) = sourceScalarChar t ∧
    (sourceScalarChar t).im = 0 ∧ ‖sourceScalarChar t‖ ≤ 1
```

Mathlib's normalized-bump integral theorem supplies real mass1, and the bump
at zero supplies evenness. The withDensity law is genuinely a probability.
No scalar characteristic formula, sign, decay or derivative bound is assumed.

## Node C: QuadraticFullNoise.lean, five definitions, four public theorems

Import Nodes A/B and integral Pi, independence/integration/variance APIs.

```lean
noncomputable def quadraticChordFamilyLaw (nu : Measure ℝ) :
    Measure (Fin 8 → ℝ × ℝ) := Measure.pi (fun _ => quadraticChordLaw nu)

noncomputable def quadraticNoiseInputLaw (nu : Measure ℝ) :
    Measure (((Fin 8 → ℝ × ℝ) × (Fin 8 → ℝ × ℝ)) × ℝ) :=
  ((quadraticChordFamilyLaw nu).prod (quadraticChordFamilyLaw nu)).prod sourceScalarLaw

noncomputable def quadraticFullNoiseMap (nu : Measure ℝ)
    (p : ((Fin 8 → ℝ × ℝ) × (Fin 8 → ℝ × ℝ)) × ℝ) : ℝ × ℝ :=
  let gamma := (∫ a : ℝ, |a| ^ 3 ∂nu) / variance (id : ℝ → ℝ) nu
  ((∑ j : Fin 8, (p.1.1 j).1) - (∑ j : Fin 8, (p.1.2 j).1) + gamma * p.2,
   (∑ j : Fin 8, (p.1.1 j).2) + (∑ j : Fin 8, (p.1.2 j).2))

noncomputable def quadraticFullNoiseLaw (nu : Measure ℝ) : Measure (ℝ × ℝ) :=
  Measure.map (quadraticFullNoiseMap nu) (quadraticNoiseInputLaw nu)

noncomputable def quadraticFullNoiseChar (nu : Measure ℝ) (u v : ℝ) : ℂ :=
  ∫ z : ℝ × ℝ, Complex.exp
    (((u * z.1 + v * z.2 : ℝ) : ℂ) * Complex.I) ∂quadraticFullNoiseLaw nu
```

The next three statements share EXACT premises `(nu : Measure ℝ)
[IsProbabilityMeasure nu] (h3 : Integrable (fun a : ℝ => |a|^3) nu)
(hV : 0 < variance id nu) (h : ℝ) (hh : 0<h)
(hs : ∀ᵐ a ∂nu, |a|≤h)`. Spelling this common telescope once is only a display
abbreviation; implementation must retain it on each public theorem.

```lean
theorem quadraticFullNoise_law_data <common telescope> :
    IsProbabilityMeasure (quadraticChordFamilyLaw nu) ∧
    IsProbabilityMeasure (quadraticNoiseInputLaw nu) ∧
    IsProbabilityMeasure (quadraticFullNoiseLaw nu) ∧
    Measure.map (fun z : ℝ × ℝ => (-z.1, z.2)) (quadraticFullNoiseLaw nu) =
      quadraticFullNoiseLaw nu

theorem quadraticFullNoise_support_moments <common telescope>
    (hgamma : (∫ a : ℝ, |a| ^ 3 ∂nu) / variance (id : ℝ → ℝ) nu ≤ 2 * h) :
    let gamma := (∫ a : ℝ, |a| ^ 3 ∂nu) / variance (id : ℝ → ℝ) nu
    let law := quadraticFullNoiseLaw nu
    (∀ᵐ z : ℝ × ℝ ∂law, |z.1| ≤ 34 * h ∧ |z.2| ≤ 64 * h ^ 2) ∧
    Integrable (fun z : ℝ × ℝ => |z.1|) law ∧
    Integrable (fun z : ℝ × ℝ => |z.2|) law ∧
    Integrable (fun z : ℝ × ℝ => z.1 ^ 2) law ∧
    (∫ z : ℝ × ℝ, |z.1| ∂law) ≤ (67 / 3 : ℝ) * gamma ∧
    (∫ z : ℝ × ℝ, |z.2| ∂law) ≤ (128 / 3 : ℝ) * h * gamma ∧
    (∫ z : ℝ × ℝ, z.1 ^ 2 ∂law) =
      16 * (∫ z : ℝ × ℝ, z.1 ^ 2 ∂quadraticChordLaw nu) +
        gamma ^ 2 * (∫ t : ℝ, t ^ 2 ∂sourceScalarLaw) ∧
    (∫ z : ℝ × ℝ, z.1 ^ 2 ∂law) ≤ (70 / 3 : ℝ) * h * gamma

theorem quadraticFullNoiseChar_product <common telescope> (u v : ℝ) :
    let gamma := (∫ a : ℝ, |a| ^ 3 ∂nu) / variance (id : ℝ → ℝ) nu
    quadraticFullNoiseChar nu u v =
      quadraticChordChar nu u v ^ 8 * quadraticChordChar nu (-u) v ^ 8 *
        sourceScalarChar (gamma * u) ∧
    quadraticFullNoiseChar nu (-u) v = quadraticFullNoiseChar nu u v ∧
    (quadraticFullNoiseChar nu u v).im = 0 ∧
    ‖quadraticFullNoiseChar nu u v‖ ≤ 1
```

The fourth theorem also has the common telescope, followed by the arbitrary
sample arguments; it proves actual independent realization and both marginals:

```lean
theorem quadraticFullNoise_independent_sample <common telescope>
    {Omega : Type*} [MeasurableSpace Omega] (mu : Measure Omega)
    [IsProbabilityMeasure mu] :
    IndepFun (fun p : Omega × (ℝ × ℝ) => p.1) (fun p => p.2)
      (mu.prod (quadraticFullNoiseLaw nu)) ∧
    Measure.map (fun p : Omega × (ℝ × ℝ) => p.1)
      (mu.prod (quadraticFullNoiseLaw nu)) = mu ∧
    Measure.map (fun p : Omega × (ℝ × ℝ) => p.2)
      (mu.prod (quadraticFullNoiseLaw nu)) = quadraticFullNoiseLaw nu
```

The actual finite Pi products give independence; phases factor pointwise before
Fubini. Reflection uses `(families,t)↦(swapped families,-t)`, not an untrue
single-chord u-even premise. The second-moment identity must prove the zero
cross terms using the actual independent mean-zero variables.

## Node D: SourceFullNoiseBridge.lean, one public theorem, no definitions

Import Node C and accepted SourceFourierScale. This is the direct source
payment, with the whole telescope copied from sourceTruncation_gamma_bounds.

```lean
theorem sourceTruncation_fullNoise
    (nu : Measure ℝ) [IsProbabilityMeasure nu] (n : ℕ)
    (h2 : Integrable (fun z : ℝ => z ^ 2) nu)
    (hnorm : (n : ℝ) * (∫ z : ℝ, z ^ 2 ∂nu) = 1)
    (hmean : (∫ z : ℝ, z ∂nu) = 0)
    (x epsilon : ℝ) (hx : 0 ≤ x)
    (hepsilon : 0 < epsilon) (hepsilonHalf : epsilon ≤ 1 / 2)
    (hR : truncationBudget nu n x ≤ epsilon ^ 3 / 8) :
    let h := epsilon / (1 + x)
    let rho := ProbabilityTheory.cond nu {z | |z| ≤ h}
    let gamma := (∫ z : ℝ, |z| ^ 3 ∂rho) / variance (id : ℝ → ℝ) rho
    let law := Probability.quadraticFullNoiseLaw rho
    IsProbabilityMeasure law ∧
    IndepFun (fun p : (Fin n → ℝ) × (ℝ × ℝ) => p.1) (fun p => p.2)
      ((Measure.pi (fun _ : Fin n => rho)).prod law) ∧
    (∀ᵐ z : ℝ × ℝ ∂law, |z.1| + (1 + x) * |z.2| ≤ 100 * h) ∧
    (∫ z : ℝ × ℝ, |z.1| ∂law) +
      (1 + x) * (∫ z : ℝ × ℝ, |z.2| ∂law) ≤ 100 * gamma ∧
    gamma ≤ 4 * truncationBudget nu n 0
```

## Edges, implementation route and acceptance

Edges: acceptedChord→A; Mathlib normalized real bump→B; A+B+finite product
measure APIs→C; C+accepted source truncation/scale→D. There are no desired
law/symmetry/moment/characteristic inputs and no circular reference to Xi.
This is a source formalization, not a research-new theorem claim.

Read-only pinned API check found `ContDiffBump.normed`, `nonneg_normed`,
`contDiff_normed`, `normed_neg`, `integral_normed`, `tsupport_normed_eq`;
`integral_fintype_prod_eq_pow`, product swap preservation, and product
`indepFun_prod`. Remote rg is absent; grep/read was used. No Lean probe occurred.

Required boundary attacks: noncentered two-point nu (single K is not u-even);
diagonal pair D=0 with positive product mass; u=v=0; scalar support endpoints;
gamma exactly2h; repeated chord values; and positive-probability atomic nu.
V=0 is excluded explicitly. No division by characteristic/gap is permitted.

Freeze and a fresh independent statement review are required before proof work.
Then each node is a checkpoint and targeted server Lean gate under root's
scheduler. Final acceptance needs exact source hashes, all owned/private/
generated transitive axioms under the standard three-axiom whitelist, forbidden
feature scan and an independent source-to-statement plus full-proof review.
