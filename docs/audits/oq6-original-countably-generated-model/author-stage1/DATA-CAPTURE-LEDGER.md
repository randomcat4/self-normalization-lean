# Data and capture ledger

Status: proposed exact data boundary, parent freeze required. The complete authoritative types and values are retained in candidate-declarations-data.json and CANDIDATE-HEAD.txt. No Lean source or proof body exists.

The head has 45 typed ordinary lets, one reduced measurable-space letI, one public theorem, zero public/private helper declarations and zero new global definitions. The45 count is derived from the exact head, not copied from220. The23-value220 schema moves g/r/v/rho to model scope;19 statistic values remain sample-local.

| ID | Type | Direct captures |
|---|---|---|
| original.f | `ℕ → Ω → ℝ` | Ω |
| original.g | `Ω → ℝ` | Ω, mΩ, μ, h |
| original.r | `Ω → Ω → ℝ` | Ω, h, g |
| original.v | `ℝ` | Ω, mΩ, μ, r |
| original.rho | `ℝ` | v |
| original.rowIntegrable | `Ω → Prop` | Ω, mΩ, μ, h |
| original.gLp | `ℝ≥0∞ → Prop` | Ω, mΩ, μ, g |
| original.projectionLaw | `Measure ℝ` | Ω, mΩ, μ, g |
| original.pairLaw | `@Measure (Ω × Ω) (mΩ.prod mΩ)` | Ω, mΩ, μ |
| reduced.μ₀ | `@Measure Ω m₀` | Ω, mΩ, m₀, μ, hm₀ |
| reduced.g₀ | `Ω → ℝ` | Ω, m₀, μ₀, h |
| reduced.r₀ | `Ω → Ω → ℝ` | Ω, h, g₀ |
| reduced.v₀ | `ℝ` | Ω, m₀, μ₀, r₀ |
| reduced.rho₀ | `ℝ` | v₀ |
| finite.mJ | `MeasurableSpace (J → Ω)` | J, Ω, mΩ |
| finite.mJ₀ | `MeasurableSpace (J → Ω)` | J, Ω, m₀ |
| finite.P | `@Measure (J → Ω) mJ` | J, instJ, Ω, mΩ, μ, mJ |
| finite.P₀ | `@Measure (J → Ω) mJ₀` | J, instJ, Ω, m₀, μ₀, mJ₀ |
| sample.mN | `MeasurableSpace (Fin n → Ω)` | n, Ω, mΩ |
| sample.mN₀ | `MeasurableSpace (Fin n → Ω)` | n, Ω, m₀ |
| sample.P | `@Measure (Fin n → Ω) mN` | n, Ω, mΩ, μ, mN, Fintype (Fin n) |
| sample.P₀ | `@Measure (Fin n → Ω) mN₀` | n, Ω, m₀, μ₀, mN₀, Fintype (Fin n) |
| sample.N | `ℝ` | n |
| sample.W | `(Fin n → Ω) → ℝ` | n, Ω, g |
| sample.V | `(Fin n → Ω) → ℝ` | n, Ω, g |
| sample.D | `(Fin n → Ω) → ℝ` | n, Ω, r |
| sample.J | `(Fin n → Ω) → ℝ` | n, Ω, r |
| sample.Ddel | `(Fin n → Ω) → Fin n → ℝ` | n, Ω, r |
| sample.Jdel | `(Fin n → Ω) → Fin n → ℝ` | n, Ω, r |
| sample.A | `(Fin n → Ω) → ℝ` | n, Ω, D |
| sample.Adel | `(Fin n → Ω) → Fin n → ℝ` | n, Ω, Ddel |
| sample.B1 | `(Fin n → Ω) → ℝ` | n, Ω, r, C0, rho |
| sample.B1del | `(Fin n → Ω) → Fin n → ℝ` | n, Ω, r, C0, rho |
| sample.s2 | `(Fin n → Ω) → ℝ` | n, Ω, g, r |
| sample.s | `(Fin n → Ω) → ℝ` | n, Ω, s2 |
| sample.d | `(Fin n → Ω) → ℝ` | n, Ω, g, r |
| sample.e | `(Fin n → Ω) → ℝ` | n, Ω, g, r, C0, rho |
| sample.Tclip | `(Fin n → Ω) → ℝ` | n, Ω, g, r, C0, rho |
| sample.Tactual | `(Fin n → Ω) → ℝ` | n, Ω, s, W, D, Classical.propDecidable (s ξ = 0) |
| sample.cap | `(Fin n → Ω) → Fin n → ℝ` | n, Ω, g, N, z |
| sample.deletedTest | `(Fin n → Ω) → Fin n → ℝ` | n, Ω, cap, A, Adel, z, B1, B1del |
| retained.mRet | `MeasurableSpace ({j : Fin n // j ≠ i} → Ω)` | n, i, Ω, mΩ |
| retained.mRet₀ | `MeasurableSpace ({j : Fin n // j ≠ i} → Ω)` | n, i, Ω, m₀ |
| retained.PRet | `@Measure ({j : Fin n // j ≠ i} → Ω) mRet` | n, i, Ω, mΩ, μ, mRet, Fintype {j : Fin n // j ≠ i} |
| retained.PRet₀ | `@Measure ({j : Fin n // j ≠ i} → Ω) mRet₀` | n, i, Ω, m₀, μ₀, mRet₀, Fintype {j : Fin n // j ≠ i} |

The original rowIntegrable and gLp are Prop-valued DATA families. Both are frozen before letI, so their Integrable/MemLp meanings use original mOmega/mu. They cannot be regenerated under the reduced instance. Their exact lambda bodies are retained, including every exponent p.

The family f is exactly Nat→Omega→Real, value fun (_k:Nat) (_o:Omega) =>0, with no observation selection. The same h is already an explicit data input. All implicit integral lambdas in g/g0/v/v0 and normalization/AE predicates are bound by the exact head; original and reduced measures are explicit where both structures coexist.

m0 is the existential218 witness at that f; hm0 is its exact order-proof binder. mu0 is literally mu.trim hm0. E is the existential signed triple from the future qualified220 specialization, with captures Omega,m0,n,r,C0,rho,i; its r/rho closures retain original h/mu. It cannot capture ξ i, a filler/default observation, an independent kernel/law, or a newly inserted z-dependent formula. All E values are constrained by the exact pointwise triple equation. No new global selected family E_i is proposed.

The retained subtype predicate is exactly fun j:Fin n => j≠i. Its pi structure is explicitly defined twice, once using mOmega and once m0. The existing Fin n and finite-subtype Fintype instances are typed in the head and ledger. The physical conditional uses an explicit Classical.propDecidable (s ξ=0); no unresolved guard decider is left as implementation freedom. Scalar/triple Borel structures and their right-association are fixed.

The inline conclusion data comprise the two exact zero sets; six typed coordinate slices cap/Ddel/Jdel/Adel/B1del/deletedTest; literal restriction fun j=>ξ j.val; the signed triple and its two identical map lambdas; the identity observation/pair/sample maps; the h/r0 pair lambdas; the AE canonicality predicate. Each is fully typed with direct captures in candidate-declarations-data.json. Universal B,mB,T,J,instJ are explicit data, with v/w universes fixed in the preamble.

Planned internal data are limited to Fin0 and its canonical Fintype for the base219 specialization, the displayed map-composition lambda, and the exact reduced probability/countable-generation proof instances coming from qualified producers. All remaining proof-local DATA must be reuse/renaming of already frozen header values or existing producer witnesses; any new selector/helper/value/instance/lambda requires parent capture approval before use. This is a boundary for later implementation, not a proof body.

Original coefficient and guard checks: D/Ddel keep sqrt(n)*(n-1); J/Jdel keep (n-2)^2; all y arguments are1; continuous cap is min(|g(ξ i)|/sqrt(n),1/(1+z)); Tactual tests s=0 while imported Tclip tests V=0. Only Ddel/Jdel/B1del factor through retained samples. cap and deletedTest remain full-sample.
