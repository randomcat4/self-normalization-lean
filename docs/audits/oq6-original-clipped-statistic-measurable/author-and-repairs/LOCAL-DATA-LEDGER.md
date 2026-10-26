# Unit220 implementation data and capture ledger

The exact source is OriginalClippedStatisticMeasurable.lean. SOURCE-MAP.json is the authoritative machine-readable inventory, with complete source ranges and every proof lambda occurrence. This is a source inventory, not an elaborated TYPE/VALUE or kernel certificate.

## Frozen data reused without substitution

The caller data are Ω:Type u, mΩ:MeasurableSpace Ω, μ:@Measure Ω mΩ, h:Ω→Ω→ℝ, n:ℕ, z:ℝ and C0:ℝ, exactly as frozen. Other caller binders are Props. The23header values are introduced directly by intro, retaining their original definitions and types:

| Name | Type | Value | Direct captures |
| --- | --- | --- | --- |
| g | `Ω → ℝ` | `fun o => ∫ y, h o y ∂μ` | Ω, mΩ, μ, h |
| r | `Ω → Ω → ℝ` | `fun o y => h o y - g o - g y` | Ω, h, g |
| v | `ℝ` | `∫ t : Ω × Ω, r t.1 t.2 ^ 2 ∂(μ.prod μ)` | Ω, mΩ, μ, r |
| rho | `ℝ` | `Real.sqrt v` | v |
| N | `ℝ` | `Real.sqrt (n : ℝ)` | n |
| W | `(Fin n → Ω) → ℝ` | `projectionW n g` | n, Ω, g |
| V | `(Fin n → Ω) → ℝ` | `projectionV n g` | n, Ω, g |
| D | `(Fin n → Ω) → ℝ` | `residualStatisticD n r` | n, Ω, r |
| J | `(Fin n → Ω) → ℝ` | `residualEnergyJ n r` | n, Ω, r |
| Ddel | `(Fin n → Ω) → Fin n → ℝ` | `residualStatisticDDeleted n r` | n, Ω, r |
| Jdel | `(Fin n → Ω) → Fin n → ℝ` | `residualEnergyJDeleted n r` | n, Ω, r |
| A | `(Fin n → Ω) → ℝ` | `fun ξ => \|D ξ\|` | n, Ω, D |
| Adel | `(Fin n → Ω) → Fin n → ℝ` | `fun ξ i => \|Ddel ξ i\|` | n, Ω, Ddel |
| B1 | `(Fin n → Ω) → ℝ` | `studentizerClipBudget n r C0 rho 1` | n, Ω, r, C0, rho |
| B1del | `(Fin n → Ω) → Fin n → ℝ` | `studentizerClipBudgetDeleted n r C0 rho 1` | n, Ω, r, C0, rho |
| s2 | `(Fin n → Ω) → ℝ` | `centeredSq n g r` | n, Ω, g, r |
| s | `(Fin n → Ω) → ℝ` | `fun ξ => Real.sqrt (s2 ξ)` | n, Ω, s2 |
| d | `(Fin n → Ω) → ℝ` | `centeredDelta n g r` | n, Ω, g, r |
| e | `(Fin n → Ω) → ℝ` | `clippedCenteredDelta n g r C0 rho 1` | n, Ω, g, r, C0, rho |
| Tclip | `(Fin n → Ω) → ℝ` | `clippedCenteredStatistic n g r C0 rho 1` | n, Ω, g, r, C0, rho |
| Tactual | `(Fin n → Ω) → ℝ` | `fun ξ => if s ξ = 0 then 0 else (W ξ + D ξ) / s ξ` | n, Ω, s, W, D |
| cap | `(Fin n → Ω) → Fin n → ℝ` | `fun ξ i => min (\|g (ξ i)\| / N) (1 / (1 + z))` | n, Ω, g, N, z |
| deletedTest | `(Fin n → Ω) → Fin n → ℝ` | `fun ξ i => cap ξ i * (\|A ξ - Adel ξ i\| + z * \|B1 ξ - B1del ξ i\|)` | n, Ω, cap, A, Adel, z, B1, B1del |

## Added proof data

### F

- Type: `({j : Fin n // j ≠ i} → Ω) → ℝ`
- Value/source: `existential elimination of Shao.OQ6.ResidualDeletion.erasedSamplePairSum_measurable_factorization r hr i`
- Binding: typed obtain witness; source line 225.
- Direct data/context captures: Ω, mΩ, n, r, hr, i.

### Lrow

- Type: `({j : Fin n // j ≠ i} → Ω) → ℝ`
- Value/source: `existential elimination of Shao.OQ6.ResidualDeletion.erasedSampleRowSqSum_measurable_factorization r hr i`
- Binding: typed obtain witness; source line 233.
- Direct data/context captures: Ω, mΩ, n, r, hr, i.

### pdel

- Type: `(Fin n → Ω) → ({j : Fin n // j ≠ i} → Ω)`
- Value/source: `fun (ξ : Fin n → Ω) (j : {j : Fin n // j ≠ i}) => ξ j.val`
- Binding: typed proof-local let; source line 242.
- Direct data/context captures: Ω, n, i.

### Dret

- Type: `({j : Fin n // j ≠ i} → Ω) → ℝ`
- Value/source: `fun q : {j : Fin n // j ≠ i} → Ω => F q / (Real.sqrt (n : ℝ) * ((n : ℝ) - 1))`
- Binding: typed proof-local let; source line 244.
- Direct data/context captures: Ω, n, i, F.

### Jret

- Type: `({j : Fin n // j ≠ i} → Ω) → ℝ`
- Value/source: `fun q : {j : Fin n // j ≠ i} → Ω => Lrow q / ((n : ℝ) - 2) ^ 2`
- Binding: typed proof-local let; source line 247.
- Direct data/context captures: Ω, n, i, Lrow.

### Bret

- Type: `({j : Fin n // j ≠ i} → Ω) → ℝ`
- Value/source: `fun q : {j : Fin n // j ≠ i} → Ω => C0 * (((1 + rho) * 1) / Real.sqrt (n : ℝ) + Jret q / ((1 + rho) * 1 * Real.sqrt (n : ℝ)))`
- Binding: typed proof-local let; source line 249.
- Direct data/context captures: Ω, n, i, C0, rho, Jret.

### E

- Type: `({j : Fin n // j ≠ i} → Ω) → ℝ × ℝ × ℝ`
- Value/source: `fun q : {j : Fin n // j ≠ i} → Ω => (Dret q, Jret q, Bret q)`
- Binding: typed proof-local let and final existential witness; source line 253.
- Direct data/context captures: Ω, n, i, Dret, Jret, Bret.

F and Lrow are existential outputs of previously qualified theorems. Their source obtains give complete types and pointwise constraints. They are not additional hypotheses. The final E is the explicitly typed tuple of Dret,Jret,Bret. Its transitive data captures are the same Ω,mΩ,n,r,C0,rho,i and their original μ,h,g definitions; it captures no full sample ξ, deleted observation ξ_i, filler observation or replacement law. pdel is only the full-to-retained restriction map used in the proof of the identities.

## Data parameters and implicit constructions

The local derived habs proof quantifies over f:(Fin n→Ω)→ℝ and hf:Measurable f. All helper indices i,j,k,l have type Fin n. Retained subtype indices have type {j:Fin n//j≠i}; their domains are explicit in the source. Every q parameter has type (retained indices)→Ω. Pair variables have type Ω×Ω. Full sample variables have type Fin n→Ω. Finite-sum membership proofs, order branches and equalities are Props. The48local have declarations are all derived Prop proofs (possibly universally quantified); their type headers, source values/ranges and special existing-provider type reference are inventoried separately in SOURCE-MAP.json.

The two guard predicates are fun ξ:Fin n→Ω=>V ξ=0 and fun ξ:Fin n→Ω=>s ξ=0; their associated sets have type Set(Fin n→Ω). Pi measurable spaces, real Borel/product structures, finite-index instances and the classical decision mechanism are existing inferred structures, listed in SOURCE-MAP.json. The classical tactic enables existing Classical.propDecidable; it supplies no Ω-value and makes no mathematical assumption. There is no new letI, instance declaration or global non-theorem value. Actual generated values after elaboration remain subject to the mandatory all-owner TYPE/VALUE audit.

The continuous cap and deletedTest are full-sample data families with their original dependence on i. Their measurability does not assert deleted-coordinate independence. All n,n-1,n-2 coefficients occur literally in Dret/Jret/Bret; the retained index subtype is never treated as a replacement sample size.
