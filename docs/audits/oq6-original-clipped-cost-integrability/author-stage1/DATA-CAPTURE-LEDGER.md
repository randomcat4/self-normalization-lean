# Complete candidate data/capture ledger

Status: proposed, not parent-frozen or elaborated. All domains and measurable structures are the original ones. JSON preserves exact multiline types/RHS; this ledger adds the capture explanation. No proof body is present.

There are 17 ordinary head lets, 8 planned ordinary proof-local values, zero Prop-valued ordinary data lets, zero non-Prop existential witnesses/selectors, and zero new local measurable-space switches. Proposition hypotheses and result predicates are separately inventoried. One public theorem and no global definitions/helpers are proposed.

| Head value | Complete type | Captures |
|---|---|---|
| g | `Ω → ℝ` | Ω, mΩ, μ, h |
| r | `Ω → Ω → ℝ` | Ω, h, g |
| v | `ℝ` | Ω, mΩ, μ, r |
| rho | `ℝ` | v |
| N | `ℝ` | n |
| P | `Measure (Fin n → Ω)` | Ω, mΩ, n, μ |
| D | `(Fin n → Ω) → ℝ` | Ω, n, r |
| J | `(Fin n → Ω) → ℝ` | Ω, n, r |
| Ddel | `(Fin n → Ω) → Fin n → ℝ` | Ω, n, r |
| Jdel | `(Fin n → Ω) → Fin n → ℝ` | Ω, n, r |
| A | `(Fin n → Ω) → ℝ` | Ω, n, D |
| Adel | `(Fin n → Ω) → Fin n → ℝ` | Ω, n, Ddel |
| B1 | `(Fin n → Ω) → ℝ` | Ω, n, r, C0, rho |
| B1del | `(Fin n → Ω) → Fin n → ℝ` | Ω, n, r, C0, rho |
| e | `(Fin n → Ω) → ℝ` | Ω, n, g, r, C0, rho |
| deletionMass | `(Fin n → Ω) → Fin n → ℝ` | Ω, n, A, Adel, B1, B1del |
| deletionTotal | `(Fin n → Ω) → ℝ` | Ω, n, deletionMass |

All right sides are literal in CANDIDATE-HEAD.txt and copied losslessly into candidate-declarations-data.json. P uses the literal finite product of mu, with original mOmega; no reduced law or CG structure is introduced.

| Planned proof-local value | Complete type | Captures |
|---|---|---|
| F | `(Fin n → Ω) → ℝ` | Ω, n, r |
| psi | `(Fin n → Ω) → Fin n → ℝ` | Ω, n, r |
| LambdaSq | `(Fin n → Ω) → ℝ` | Ω, n, psi |
| LambdaDelSq | `(Fin n → Ω) → Fin n → ℝ` | Ω, n, r |
| sigma | `ℝ` | rho |
| base | `ℝ` | sigma, N |
| K | `ℝ` | sigma, n, N |
| BcoarseDel | `(Fin n → Ω) → Fin n → ℝ` | Ω, n, base, LambdaDelSq, K |

The proof-local values above are only planned expressions. Their exact right sides, all head lambdas by line, integral lambdas, predicate families, induced instances, and consumer adapter lambdas are in JSON. Every lambda local is typed: o/y are Omega, t is Omega product Omega, xi is Fin n -> Omega, i/j/k/l are Fin n. The summand implicit in deletionTotal is explicitly expanded. Integral notation expands to the typed lambda recorded at each occurrence; the outer projection integrand captures the original mu and h, and its inner integrand also captures its outer o.

Typeclass data: ambient mOmega; real Borel; mOmega product mOmega; literal pi measurable structure; Fintype and DecidableEq Fin n. These are existing or induced instances, not new premises. IsProbabilityMeasure mu is the given Prop instance, and IsProbabilityMeasure P is the derived product Prop instance. Exact tactic elaboration is not claimed. No instance with a reduced measurable space is introduced.

The head has proposition hypotheses hh/hh2/hhsymm/hcenter/hprojectionsecond/hn/hC0. These are proof binders rather than ordinary hidden data. JSON also spells out all proposition-family functions used by Measurable/MemLp/Integrable and the deletion quantifiers. There is no hidden rowIntegrable/gLp predicate DATA let or selected function witness.

All imported theorem-local lets and their ordinary lambda/integral context are retained losslessly in BEARING-PUBLIC-HEADS.json with full source hashes. Their exact proposed argument substitutions are recorded there. They are imported producer data, not author-created helper values. No private producer helper is called.

Prospective proof tuples and scalar inequalities are proposition proofs. A later implementation may need Lean elaboration repairs; any additional data-valued local, helper, selector, witness, instance, or premise must be reported and frozen before it is introduced.
