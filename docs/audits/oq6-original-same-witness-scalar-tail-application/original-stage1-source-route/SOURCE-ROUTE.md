# Prospective243 source/interface design

STATUS: STAGE1_DECLARATION_DESIGN_COMPLETE; NOT_FROZEN; NOT_IMPLEMENTED; NOT_QUALIFIED.

The proposed theorem keeps every original242 parameter, all138 public ordinary occurrences, all old242 output clauses, and the same sole cg/m₀/μ₀ selection. Its only public mathematical addition is a conditional, fixed-k scalar finite-cost tail pair, inside the retained universal n/C0/z branch. The external constants and hSZ occur after that model selection. This does not prove the external input, construct another model, use239's separate witness, or claim a physical/CDF/limit/root result.240/242 are prospective frozen interfaces only;241 is independently qualified exact a3f6a76b636d66b1049289293c12884bcc8474379b059f835507f3f49f73e5f8/19004B, publishedPR488.

## Exact new conclusion

```lean
        (∀ (cSZ C1 C2 C3 C4 : ℝ)
            (hSZ : Shao.OQ6.NormalizedIntegrableTailAssembly.ScalarShaoZhouFiniteCostTailInput.{u}
              cSZ C1 C2 C3 C4)
            (k : ℕ) (hz1 : 1 ≤ z)
            (hδη : ∀ i : Fin n, δη k i ≤ 1)
            (hLη : Lη k ≤ cSZ * z ^ 2),
          Shao.standardNormalTail z * Real.exp (-C1 * Lη k) *
              (1 - C2 * unperturbedSourceCostη k) ≤
            ν.real {x : Fin n → Ω × ℝ | z ≤ Tη k x} ∧
          ν.real {x : Fin n → Ω × ℝ | z ≤ Tη k x} ≤
            Shao.standardNormalTail z * Real.exp (C3 * Lη k) *
                (1 + C4 * unperturbedSourceCostη k) +
              ν.real {x : Fin n → Ω × ℝ | z * |Dη k x| > Vη k x / 4} +
              ν.real {x : Fin n → Ω × ℝ |
                z ^ 2 * |D2 (q x)| > (1 / 4 : ℝ)}) ∧
```

The surrounding conjunction and all old242 clauses are in PROPOSED-HEAD.txt. Removing this one addition and restoring the theorem name recovers FROZEN-HEAD.txt byte-for-byte. No original assumption is moved, weakened or added. The constants cSZ,C1,C2,C3,C4 are arbitrary under the complete external Prop, whose positivity conjuncts remain part of that explicit input. cBudget stays arbitrary positive. This candidate does not require cBudget=cSZ or cBudget<=cSZ. It claims no eventual-k budget or new source window: hδη/hLη are explicit per-k conditions.

## Selection and factor data

The intended future implementation first obtains the entire qualified242 result once, then selects its sole cg and m₀. It never calls240 or239 independently to obtain another witness. The existing140 optional ordinary mirrors/selections retain their types/RHS and scope order; their actual243 hCg/hModel contexts are the strengthened242 suffixes, embedded in the inventory. Original242 weaker proof contexts are preserved separately for exact provenance.

At fixed n/C0/z/k, hNumeratorFactors, hFullTriple and hDeletedPairs are propositions extracted from that very packet. The inventory embeds their full types, the complete enclosing original parameter/model/let context, all seven proposed ordinary factor type/RHS/scope rows, and the measurable/factor-equation types. F1 and F2 choose the two numerator factors. Ffull chooses the retained full triple; FA and FB are its second and third scalar projections. The dependent families FAdelete and FBdelete choose the TWO unperturbed deleted factors for every i. The full propositions and nested choose RHS are explicit; there is no hidden callback or arbitrary measurable-factor premise. These choices can be made before the external constants/input. No new public existential is introduced.

## External-input premise availability at exact actual types

Below X abbreviates the displayed type Fin n → Ω × ℝ in prose only. The actual declarations, inventory types and RHS never use this abbreviation.

1. Domain, space and probability. Use the SAME original242 augmented product with ν : @Measure (Fin n → Ω × ℝ) mAug. Install the already listed augmentedProductSpace (RHS mAug) and the newly proposed augmentedProbability : @IsProbabilityMeasure (Fin n → Ω × ℝ) mAug ν (RHS hνProbability). The full hνProbability proposition is an exported242 conclusion. This is a local instance from the same law, not a new measure or assumption. The external universe u can contain Fin n → Ω × ℝ. The external hn : 1 ≤ n follows from original hn : 4 ≤ n.

2. Actual scalar observations. ζ is η k, with complete η RHS actualNormalizedFamily ν (Y k); all Y/a/s/η and local-coordinate lets are retained exactly.242 exports, for each k, iIndepFun (η k) ν, every measurable and MemLp 2 coordinate, mean0, and total second moment1. Thus the exact types are:

```lean
∀ i : Fin n, Measurable[mAug, borel ℝ] (η k i)
iIndepFun (η k) ν
∀ i : Fin n, MemLp (η k i) 2 ν
∀ i : Fin n, (∫ x, η k i x ∂ν) = 0
(∑ i : Fin n, ∫ x, (η k i x) ^ 2 ∂ν) = 1
```

3. Full and deleted factors. The complete choice inputs, type/RHS and exact context are in INTERFACE-INVENTORY.json and the complete primary242 head is in API-CONTEXT.md. The facts required by the external input and the equations used for rewriting are exactly:

```lean
Measurable[borel (Fin n → ℝ), borel ℝ] F1
Measurable[borel (Fin n → ℝ), borel ℝ] F2
Measurable[borel (Fin n → ℝ), borel ℝ] FA
Measurable[borel (Fin n → ℝ), borel ℝ] FB
∀ i : Fin n, Measurable[borel ({j : Fin n // j ≠ i} → ℝ), borel ℝ] (FAdelete i)
∀ i : Fin n, Measurable[borel ({j : Fin n // j ≠ i} → ℝ), borel ℝ] (FBdelete i)
∀ x : Fin n → Ω × ℝ, Dη k x = F1 (C k x)
∀ x : Fin n → Ω × ℝ, D2 (q x) = F2 (C k x)
∀ x : Fin n → Ω × ℝ, Anew k x = FA (C k x)
∀ x : Fin n → Ω × ℝ, B x = FB (C k x)
∀ (i : Fin n) (x : Fin n → Ω × ℝ), Adelete i x = FAdelete i (fun j : {j : Fin n // j ≠ i} => η k j.val x)
∀ (i : Fin n) (x : Fin n → Ω × ℝ), Bdelete i x = FBdelete i (fun j : {j : Fin n // j ≠ i} => η k j.val x)
```

F1 represents Dη k; F2 represents fun x => D2 (q x); FA represents Anew k; FB represents B. Adelete/Bdelete are UNPERTURBED. Scalar projections of the Borel Ffull are Borel and satisfy FA/FB equations by product equality. The two dependent deleted families inherit Borel measurability and their literal equations from hDeletedPairs, specialized separately at each i. No claim that an arbitrary factor is definitionally equal to the original function is made: all later identities use these equations.

4. Nonnegative envelopes. The exact needed types are:

```lean
∀ x : Fin n → Ω × ℝ, 0 ≤ Anew k x ∧ 0 ≤ B x
∀ (i : Fin n) (x : Fin n → Ω × ℝ), 0 ≤ Adelete i x ∧ 0 ≤ Bdelete i x
```

The Anew clause is exported242. For B,242 exports |D2 ζ|≤B0 ζ pointwise, so abs_nonneg and transitivity give B0≥0, then compose with q. Adelete is the absolute value residualStatisticDDeleted n r (q x) i. Bdelete is literally studentizerClipBudgetDeleted n r C0 rho 1 (q x) i. The complete primary clippedDeletion_envelopes_nonneg head gives the last two nonnegative facts using hC0 and rho=Real.sqrt v>=0 and 1>=0. Alternatively its displayed definitions make this direct: residualEnergyJDeleted is a finite sum of squares divided by ((n:ℝ)-2)^2, hence nonnegative; the two terms of the budget have nonnegative numerator/denominator. Real division by zero is total and still preserves this nonnegativity; original hn>=4 is retained. No integrability of Bdelete is needed.

5. Domination and positive denominators. Required exact types:

```lean
∀ᵐ x ∂ν, |Dη k x| ≤ Anew k x ∧ |D2 (q x)| ≤ B x
∀ᵐ x ∂ν, 0 < 1 + D2 (q x)
∀ᵐ x ∂ν, 0 < Vη k x
```

First domination is pointwise exported242; second is original clipped bound transported by q.242 exports (1/2:ℝ)≤1+D2 ζ pointwise, so the second premise is pointwise positive.242 exports a.e.0<Vη k x (in its normalized positivity conjunction). The source input needs Vη positivity, not original V positivity. Original projection-zero mass is neither assumed small nor silently removed.

6. Tilt weight integrability. Required exact type:

```lean
Integrable[mAug] (fun x : Fin n → Ω × ℝ => Real.exp (Sη k x)) ν
```

This is not an explicit242 output and must not be mistaken for one. It is available without extra assumptions: η coordinate measurability implies measurability of ℓη, the finite sum Sη, and exp(Sη). For every real t, t-t²/2=1/2-(t-1)²/2≤1/2. Therefore Sη k x≤(n:ℝ)/2 pointwise; 0<exp(Sη k x)≤exp((n:ℝ)/2). Under the exported probability ν, this is measurable and dominated in norm by an integrable constant, hence integrable. This is a source-level elementary derivation for later implementation, not a Lean proof or accepted new lemma. It introduces no ordinary helper or integrability premise. The general assembly's unweighted assumptions are not used for this step.

7. Positive tilt and full/deleted weighted integrability. Required exact types:

```lean
0 < Iη k
Integrable[mAug] (fun x : Fin n → Ω × ℝ =>
  fullTestη k x * Real.exp (Sη k x)) ν
∀ i : Fin n, Integrable[mAug] (fun x : Fin n → Ω × ℝ =>
  deletedTestUnperturbedη k i x * Real.exp (Sηminus k i x)) ν
```

The first two are explicit inherited242 outputs at every k. The third is the explicit new242 unperturbed bridge output at every k,i, using exact qualified241. No later large-k positivity is fabricated, and no additional unweighted B/Bdelete integral is requested. The bridge is required because using old perturbed deletedTestη would produce the wrong R.

8. Actual threshold and finite budgets. External x is original z. The exact conditions hz1 : 1≤z, hδη : ∀i,δη k i≤1, hLη : Lη k≤cSZ*z² occur inside the new conclusion, at each k. Fz(t)=(z*t)²*min|z*t|1 makes the scalar δ and total L identical to retained δη k and Lη k.242's separate strict-budget/window outputs are retained and could support a future eventual-k consumer, but no such consumer is claimed in243.

9. Exact statistic, costs and exceptional events. After rewriting the six factor equations, the external W,V,S,Sminus,I,δ,L,full,deleted,T,R match Wη k,Vη k,Sη k,Sηminus k,Iη k,δη k,Lη k, fullTestη k*exp(Sη k), deletedTestUnperturbedη k i*exp(Sηminus k i), Tη k,unperturbedSourceCostη k respectively. The full list of18 generic external lets and actual specialized type/RHS is included in the inventory; these scoped lets add no proof aliases. In particular:

```lean
unperturbedSourceCostη k =
  ((∫ x, fullTestη k x * Real.exp (Sη k x) ∂ν) +
    ∑ i : Fin n, ∫ x,
      deletedTestUnperturbedη k i x * Real.exp (Sηminus k i x) ∂ν) / Iη k
```

The numerator event is literally {x | z*|Dη k x|>Vη k x/4}; the denominator event is {x | z²*|D2(q x)|>1/4}. The external product Vη*sqrt(1+D2(q x)) is exactly the retained b definition in Tη. There is no atomlessness, zero-denominator extension, threshold transport, passage to a limit, or replacement by the original physical statistic in this per-k result.

## Excluded generic assembly route and genuine remaining prerequisites

The accepted actual_normalized_integrable_tail_assembly additionally takes unweighted A/B/Adelete/Bdelete measurability/integrability arguments. In particular the current original single-witness frontier has not exposed all of that theorem's B/Bdelete unweighted integrability premises. This design neither calls it nor assumes those premises. The direct ScalarShaoZhouFiniteCostTailInput interface needs only the facts enumerated above.

No missing mathematical premise was found for this smallest CONDITIONAL per-k declaration at source level. This is not a proof certificate. Implementation remains gated by qualified exact240 AND242 (including qualified exact241 reuse), lead intake and exact declaration/data freeze, then explicit implementation activation. Independent complete proof review plus actual server kernel/all-owner recursive-axiom evidence remain required after implementation. No local/server Lean, network, uploads, Git/API publication, old-check replay or child dispatch occurred in this Stage1 work.
