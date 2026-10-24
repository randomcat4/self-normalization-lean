# Independent complete final review: C12 units 167–168

STATUS: CORRECT

The three exact frozen declarations and their complete production proofs are correct within the stated auxiliary scope. I found no critical gap in source fidelity, mathematical proof, actual elaborated types, newly consumed-interface interactions, or all-owner recursive axiom evidence. Parent qualification remains pending; the reviewer does not accept an original C2/C12 root.

The reviewer is a fresh independent context configured as gpt-6.1-sol/xhigh, with no authorship, source edits, proof advice to the author, child agent, or Lean/audit execution. Actual backend model/effort telemetry and separate input, cached-input, output and reasoning-subset counts are unavailable and null. Only this review folder was written. Source, shared, cache, old review, server and publication bytes were not written. The initial runtime ACK and checkpoint precede mathematical review.

## Source correspondence and scope

The read-only main.tex hash is `beb00f718487e36de433175c97f1d500cb48e7a92ce5bd5ad5d62bb132122d06`; supplement.tex is `b99f2ac4d2f39dd39772d98a5702b7a923c2f10f8730a08fc1b4cd6bba4742bd`. I read main.tex 147–175, 1191–1222 and 1328–1362, supplement.tex 4971–4999, 5040–5078, 5085–5167. These fix actual sums/energies, the original finite-second-moment law, auxiliary finite-third-moment status, v_x=sqrt(9x²/4−1), H=K beta²(1+x)^6 and its ceiling, the native tilt, remaining ranks and the rare factor phi(s)^n P_s(rare).

Unit167 proves the literal change of measure used in supplement5094–5139 and 5148–5160. Unit168 pays the actual remaining-block rare Laplace factor at the original source cutoff. The paper's use of a bounded auxiliary law is covered by these declarations for general auxiliary laws with finite third moment. No bound is asserted for an original law without the auxiliary finite-third preprocessing. No full marked/unmarked moment, inverse moment, weighted record, circular witness or C2 root closure follows from these leaves.

## Exact evidence and declarations

### Unit 167: Shao.C2.AuxiliaryProductTiltLaw

sourceSHA256: `893229475c5fcc2f4f0f9d5601229c237b30e5b2b1aca16e4a0ecd2409c357ff`.

objectSHA256: `9e20e8af3151edefce2323b399d66611977d800f638cf1848e10e679734f2b25`.

receiptSHA256: `2166fd1f48d67ab4d4bfc18c444ea1527377306c6f32a32bc1319fe8f98cd383`.

frozenSHA256: `98a0be7ab3757fd556d306c857cad4f7a2f6d27c303d582ec3e427beeb79b46a`.

Complete frozen imports, context and public heads (proof bodies removed only for this display):

```lean
import Shao.C2.AuxiliaryEnergyTilt
import Shao.OQ4.EnergyPathLaw
import Mathlib.MeasureTheory.Integral.Pi

set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section
namespace Shao.C2.AuxiliaryProductTiltLaw
open MeasureTheory ProbabilityTheory
open scoped BigOperators

theorem auxiliary_actual_product_tilt_law
    (nu : Measure ℝ) [IsProbabilityMeasure nu]
    (h2 : Integrable (fun z : ℝ => z ^ 2) nu)
    (h3 : Integrable (fun z : ℝ => |z| ^ 3) nu)
    (hmean : (∫ z : ℝ, z ∂nu) = 0)
    (hnorm : (∫ z : ℝ, z ^ 2 ∂nu) = 1)
    (s : ℝ) (hs : 0 ≤ s) (n : ℕ) :
    let Z : ℝ := ∫ z : ℝ, Real.exp (-s * z ^ 2) ∂nu
    let rho : Measure ℝ := nu.tilted (fun z => -s * z ^ 2)
    let Praw : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => nu)
    let Ptilt : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => rho)
    let W : Shao.Path n → ℝ := fun v => Real.exp (-s * Shao.energy v)
    0 < Z ∧ IsProbabilityMeasure Ptilt ∧ Integrable W Praw ∧
      (∫ v : Shao.Path n, W v ∂Praw) = Z ^ n ∧
      Ptilt = Praw.tilted (fun v => -s * Shao.energy v) := by

theorem auxiliary_actual_event_laplace_identity
    (nu : Measure ℝ) [IsProbabilityMeasure nu]
    (h2 : Integrable (fun z : ℝ => z ^ 2) nu)
    (h3 : Integrable (fun z : ℝ => |z| ^ 3) nu)
    (hmean : (∫ z : ℝ, z ∂nu) = 0)
    (hnorm : (∫ z : ℝ, z ^ 2 ∂nu) = 1)
    (s : ℝ) (hs : 0 ≤ s) (n : ℕ)
    (A : Set (Shao.Path n)) (hA : MeasurableSet A) :
    let Z : ℝ := ∫ z : ℝ, Real.exp (-s * z ^ 2) ∂nu
    let rho : Measure ℝ := nu.tilted (fun z => -s * z ^ 2)
    let Praw : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => nu)
    let Ptilt : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => rho)
    let W : Shao.Path n → ℝ := fun v => Real.exp (-s * Shao.energy v)
    Integrable (A.indicator W) Praw ∧
      (∫ v : Shao.Path n, A.indicator W v ∂Praw) = Z ^ n * Ptilt.real A := by

end Shao.C2.AuxiliaryProductTiltLaw
```

### Unit 168: Shao.C2.AuxiliaryRareLaplace

sourceSHA256: `06b4ca90fe289342c88c7b4bd218ca6b28fac676a7fe0c2f2bc46da19630d9e1`.

objectSHA256: `7dccd0f0cb2f2b025b18147930d8631730a39c0196691818f86c571b31dc0621`.

receiptSHA256: `0a20ed74b06f9531598c5113dcc244f04e82a68c2d24bde1a5b3ea5671d96b40`.

frozenSHA256: `f1c60a4fe1dd48e188640493ab3e3adc83fcb1ce5dd7b29d5c630fc07a9cbb17`.

Complete frozen imports, context and public heads (proof bodies removed only for this display):

```lean
import Shao.C2.AuxiliaryOriginalCutoffRare
import Shao.C2.AuxiliaryProductTiltLaw
import Shao.C2.AuxiliaryEnergyLaplace

set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section
namespace Shao.C2.AuxiliaryRareLaplace
open MeasureTheory ProbabilityTheory

theorem auxiliary_original_cutoff_rare_laplace :
    ∃ C : ℝ, 0 < C ∧
      ∀ rhoStar : ℝ, 0 < rhoStar → rhoStar ≤ 1 / 16 →
        ∀ L : ℝ, 0 ≤ L →
          ∀ K : ℝ, 8000000 * (1 + L) ^ 2 ≤ K →
            2 * (768 / rhoStar) ^ 2 ≤ K →
            ∀ (nu : Measure ℝ) [IsProbabilityMeasure nu],
              Integrable (fun z : ℝ => z ^ 2) nu →
              Integrable (fun z : ℝ => |z| ^ 3) nu →
              (∫ z : ℝ, z ∂nu) = 0 →
              (∫ z : ℝ, z ^ 2 ∂nu) = 1 →
              ∀ s : ℝ, 0 ≤ s →
                ∀ x : ℝ, 1 ≤ x →
                  ∀ t n : ℕ,
                    Nat.ceil (K * (∫ z : ℝ, |z| ^ 3 ∂nu) ^ 2 * (1 + x) ^ 6) ≤ t →
                    (n = t ∨ n = t - 1) →
                    s * (t : ℝ) ≤ L * x ^ 2 →
                    let Praw : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => nu)
                    let a : ℝ := Real.sqrt ((9 / 4) * x ^ 2 - 1)
                    let A : Set (Shao.Path n) := {v | 0 < Shao.energy v ∧
                      a * Real.sqrt (Shao.energy v) ≤ |Shao.prefixSum v n|}
                    let W : Shao.Path n → ℝ := fun v => Real.exp (-s * Shao.energy v)
                    Integrable (A.indicator W) Praw ∧
                      (∫ v : Shao.Path n, A.indicator W v ∂Praw) ≤
                        C * Real.exp (-(7 / 8) * s * (n : ℝ)) *
                          Shao.standardNormalTail ((3 / 2) * x) := by

end Shao.C2.AuxiliaryRareLaplace
```

## Complete proof and actual-type review

### Shao.C2.AuxiliaryProductTiltLaw.auxiliary_actual_product_tilt_law

Literal scalar native tilt and literal finite product of that tilt equal the native actual-energy tilt of the actual raw product, with genuine positive scalar Z, actual W integrability and exact product normalizer Z^n. All n including zero and every nonnegative s; no normalization/density/HasLaw oracle.

1. Qualified150 supplies Integrable(exp(-s*z²)), positive actual Z and probability of the literal scalar tilt; the let-bound rho and density probability instance reduce to that exact measure.
2. Actual energy=sum of squares, so exp(-s*energy)=product of coordinate exponentials. Native Integrable.fintype_prod applies to Fin n and probability-derived sigma-finite coordinate measures. The scalar coordinate integrals multiply to Z^n.
3. The measurable density d=ofReal(exp(-s*z²)/Z) is exactly the native scalar tilted density. Accepted public finitePi_withDensity applies to this actual d and its actual probability measure.
4. ofReal finite-product conversion is justified by exp positivity and Z>0. Product division gives W/Z^n, including the empty product. Rewriting Measure.tilted using the independently established actual product integral yields equality of actual measures.

Boundary and premise checks: n=0: all finite products and Z^0 are 1; the singleton empty-path probability and W=1 are retained. s=0: exp weights and normalizers are 1; no division by s. Unbounded auxiliary laws and atoms allowed; finite third is an explicit auxiliary-law hypothesis, not an original-law condition.

### Shao.C2.AuxiliaryProductTiltLaw.auxiliary_actual_event_laplace_identity

For every measurable actual path event A, raw-product integral of its indicator times actual exp(-s*energy) is integrable and equals Z^n times actual tilted product real probability.

1. The previous actual product law supplies hW, Z>0, exact product normalizer, probability of Ptilt and equality to the native whole-path tilt.
2. Integrable.indicator uses the explicit MeasurableSet A. Ptilt is a probability measure, so its actual real probability is exactly the integral of indicator 1.
3. Native integral_tilted rewrites this indicator integral using actual density W/Z^n. A pointwise A/not-A split identifies the integrand with A.indicator W divided by Z^n.
4. integral_div pulls out the constant. Positive Z gives Z^n≠0 for all n; eq_div_iff and real commutativity yield the desired equality. No cancellation at a possibly zero normalizer occurs.

Boundary and premise checks: Every measurable A, including empty/universal events and events with atoms on the boundary. n=0 and s=0 remain covered by the actual previous identity; no positive-rank or small-s premise is inserted. No sample-energy division, no event-conditioned probability, no fabricated path law.

### Shao.C2.AuxiliaryRareLaplace.auxiliary_original_cutoff_rare_laplace

One universal positive C precedes rhoStar,L,K and the auxiliary law, s,x,t,n. Under the original ceil cutoff and either remaining rank, actual raw-product rare-event indicator Laplace integral is integrable and bounded by C exp(-7sn/8) times actual standard-normal tail at 3x/2.

1. Obtain C once from qualified166 before introducing any later parameters. The exact rhoStar/L/K/law/s/x/t/n quantifier order is maintained.
2. Qualified152 derives beta=actual integral |z|³≥1. Qualified165 consumes the true source ceiling, n=t or t−1, st≤Lx² and both K bounds to supply the actual remaining-rank/time hypotheses.
3. Qualified158 numerical payment supplies s*beta²≤1/128. This implies the exact ≤1/64 premise of qualified153, which gives the actual scalar Z≤exp(-7s/8). Integral of the everywhere-positive exponential is nonnegative.
4. pow_le_pow_left₀ preserves order for nonnegative Z. Native exp_nat_mul and ring yield Z^n≤exp(-(7/8)*s*n), for all n.
5. A is the intersection of 0<actual energy and a*sqrt(actual energy)≤abs(actual full prefix sum). Both factors are measurable from accepted continuous/measurable actual statistics. No atomlessness or strict-endpoint approximation is used.
6. New167 applied to that exact A gives the integrability and integral=Z^n*Ptilt.real A. Qualified166 gives the probability bound for the same literal native product, same raw energy and weak endpoint event.
7. Z^n≥0 permits substitution of the probability upper bound. C>0 and actual Gaussian-tail nonnegativity permit substitution of the exponential power upper bound. A ring reassociation gives the frozen RHS.

Boundary and premise checks: Both n=t and n=t−1 are paid by the exact source-rank interface; Nat subtraction is not silently replaced by real subtraction. x=1, s=0, L=0, weak endpoint equality and arbitrary atoms are included. The event keeps actual raw energy>0. The all-zero path is outside this source rare suffix event; no normalization by energy appears. The finite3 premise applies only to nu at the auxiliary stage. Original finite-positive-second-moment scope is unchanged.

I read the complete production Lean source of both modules, their complete freeze records and freeze comparisons, both source-and-proof notes, releases, receipts, owner maps and audit programs, actual-type exports, empty value exports, finish-receipt programs and the documented dependency delta. The full actual owned types were read without ellipsis: 16,514 bytes for unit167 and 26,784 for unit168, totaling 43,298 bytes. The first file was read in full; the second was read in contiguous line intervals 1–156 and 157–EOF. Both 0-byte global definition-value exports were inspected and bound. Their exact hashes and line counts are in full-review.json. The exports match the corresponding complete TARGET_DECL/ACTUAL_TYPE blocks of the bound remote audit logs, rather than a pretty-printed approximation supplied independently of the checked object.

The actual event identity type has exactly the explicit probability law, h2/h3, zero mean, unit second, s≥0, arbitrary n, measurable A and literal Z/rho/Praw/Ptilt/W lets shown above. Its result is actual indicator integrability and equality with Measure.real A. The actual product type additionally contains actual positive Z, probability of actual Ptilt, integrability of actual W, its exact integral and the equality of actual measures. The actual168 type starts with Exists C before all subsequent parameters, uses real constants 8000000, 768, 1/16, 7/8 and 3/2, the natural ceiling and natural t−1 branch, and retains exactly the actual positive-energy/weak-endpoint indicator and raw-product measure. There are no hidden typeclass assumptions about support, density, atomlessness, boundedness or extra probability oracles.

## Imported interfaces and separation of old/new review

Qualified unit150 supplies actual positive normalization and probability of the native scalar tilt; qualified152 supplies beta≥1; qualified153 supplies true scalar Laplace decay under s beta²≤1/64; qualified158 supplies the actual ≤1/128 smallness from rank/time; qualified165 supplies the original cutoff's remaining rank/time payment; qualified166 supplies the actual tilted-product rare probability. I read each consumed complete frozen public interface/context and checked each new application and definitional identification in units167/168. Their exact source/object pairs occur in their already qualified complete-review records, with parent-acceptance and report seals verified. Qualified161/163/166 evidence is reused from parent `54c7e1bd4fc94ae29e4d3944f8fc545f8dc5e8eaf482735052e0508d1b857232`, report JSON `4a499afbc7593525d14026f2fb1c32dcf971b1a657bd1bc8390bfc240c44633a`. Qualified165 uses parent `4d8a0c300e837be64a9f2972735156defefae79939d41e3add8aae8ec599dc92` and JSON `6ab5661af3fd2d0eb383a6a2eece26aba31a2f88730c61e0ec8e86384084ac8b`. No unchanged old proof received another complete review and no old successful gate was replayed.

The new density use consumes the accepted PUBLIC Shao.OQ4.finitePi_withDensity, not an old private proof reimplementation. The complete extracted public import/context/head is hash195e65e4f0b9983a1fc5b068ab3a06e6b09a1a3b5fec417913df6f8db1c5d805 and its theorem head is byte-identical to the accepted actual source. It requires a probability measure nu, measurable d, probability of the actual nu.withDensity d, and arbitrary n, and concludes equality of actual pi-withDensity measures. Source3336b977fbe88ae4c27ff7531ffeec6e14c71508587ac2abae99bf475757a177/object6331d6941ff5d6c857191d5a4693035dfeb7ba811f2ba26dcf732c951a367669 are bound to root accepted-v85 receipt bee6010790734dfc41f2819b76948946a7dec1ac6bd08a5139c8accf1e493fdd and old OQ4 publication receipt e04d25cf8e05beabef60a1c6d1d7301fc4409b7df76018adf9821ba3422c225d. Old mathematical/formal review and source-format evidence fingerprints were verified, including that the published source is the frozen original plus exactly one final LF. No mathematical or format change is introduced here. The author observation records all24 accepted Shao source/object closure entries present before the first Lean attempt, at 2026-10-24T22:31:53.444192+00:00; those24 source/object pairs were freshly observed exact again.

Native definitions and contracts were read from the pinned server sources and bound in native-interfaces.json. Measure.tilted is literally withDensity(ofReal(exp(f)/integral(exp(f)))); integral_tilted is the corresponding native Bochner integral formula. Integrable.fintype_prod and integral_fintype_prod_eq_prod operate on actual finite product measures with sigma-finite coordinates; probability provides these instances. Thus no imported interface changes the law or replaces the genuine normalizer. The accepted finite-path definitions are Path n=Fin n→Real, energy=sum of squared coordinates, and prefixSum at n is the full coordinate sum. Accepted continuous/measurable actual energy, sqrt-energy and prefix-sum interfaces make168's event measurable. standardNormalTail is the real Gaussian measure of Ioi, with its accepted strict positivity/nonnegativity; the final monotone multiplications use only nonnegativity.

## Kernel, owner and recursive-axiom evidence

Both original attempt002 target checks ended KERNEL_EXIT=0; both original all-owner audit checks ended AUDIT_EXIT=0. I read both attempted commands and complete attempt001/002 kernel logs via bounded read-only server observations. The checked objects, output snapshots, current worktree sources and corresponding build-library objects all match the exact hashes above. No reviewer target build or audit was run.

The audit imports the checked target, traverses every env.constants entry, obtains each actual imported owner via env.getModuleIdxFor? and env.header.moduleNames, and selects exact module ownership rather than a namespace prefix or public list. For every selected constant Lean.collectAxioms is called, and every returned axiom is checked against propext, Classical.choice, Quot.sound. Public lists are additional completeness checks, not the owner selector. The collector source was read in full: it recursively visits constant types and values, uses checked kernel constants, and uses export-time precomputed transitive axiom entries for imports, preserving private-body dependence. Its fresh hash b39bd22253a76816ee6d24284e69674d0b491be343fd71f9ee9376833d1485f6 matches the qualified prior evidence; the environment owner lookup source was also read and bound. Axioms are not merely direct names appearing in the theorem statement.

Deriving from actual owner maps and new source declaration heads gives two modules, three actual owners, three actual/public theorem constants, zero private theorem heads, zero generated theorem constants and zero global non-theorem values. Unit167 owns exactly its two public declarations;168 owns exactly its one declaration. Each actual owner has precisely propext, Classical.choice and Quot.sound as its transitive axiom list. Complete sources contain no sorry, admit, new axiom, unsafe or native_decide. Empty value exports agree with the absence of non-theorem owners; local proof lets do not create global declarations.

The historical resources and pins are Lean4.36.0-rc1, mathlib807d3836b165983210ee2ecf3cd28f239436949c, accepted shared-v34 read-only package view, CPU14–17, c12-heavy.lock, -M8192 -j4. Read-only server observation confirms the branch author/c12-own-c1-budget-v71 and frozen base HEAD123547c9275f119c38975c95cd2dbc61d8bdf551. The recurring package-local-change warning is retained in original logs; the pin and consumed native source fingerprints are checked explicitly and no package is written or rebuilt by this review.

## Failure provenance and exact-byte continuity

Unit167 attempt001 had only local-let/function unfolding and product-integral rewrite elaboration failures. Its preserved source00a34b16034b698e418a5f8b8c7203791111d51e9769e5a1c35cc0c14fed47a3 became the exact successful source893229475c5fcc2f4f0f9d5601229c237b30e5b2b1aca16e4a0ecd2409c357ff through proof-only changes. Complete imports, context and both frozen heads were compared against the final source and are unchanged. Unit168 freeze references the then-draft167 bytes; dependency-source-delta.json explicitly binds the unchanged167 interface to its final kernel/axiom-checked source/object/receipt. The168 successful receipt uses final167 bytes. Historical freeze records are not rewritten.

Unit168's local dependency-map KeyError preceded upload/Lean and resulted only from interpreting Windows-relative paths; normalized backslash→slash keys agree without collisions. Its actual attempt001 is preserved, failing only on the unavailable measurable.abs field projection. Attempt002 uses the accepted continuous absolute full sum and passes. Its complete frozen imports/context/head are unchanged. Both production files are UTF-8 without BOM and have zero CR bytes. Original failures and source snapshots remain remote and immutable; this review stores hashes and compact observations rather than copying raw logs, binaries or caches.

One review location probe initially assumed the accepted root-owned SourceOriginalFullRelative source was in the C12 tree. It is intentionally in the root accepted producer/integration worktrees; the corresponding accepted object is exported into C12. Fresh observations verify both canonical source hashes and the C12 object hash120612e9a6ce6ba95ce5b36d809ba3c1d5e676312c2460840a04e9f395b18b52. This is an evidence-path correction, not a mathematical/source change. Additional harmless query failures and their recovery are recorded in query-mistakes.json; they did not invoke Lean or write remote/shared evidence.

## Verdict and handoff

All three new proof/statement/type/interface judgments are CORRECT. The exact scope is the native finite-product tilt/event Laplace identity and original-cutoff actual auxiliary rare-event Laplace factor. There is no independent novelty claim; these are source-bound auxiliary components. Full marked and unmarked damped moments, inverse moments, weighted record/circular witness and the original C2/C12 root remain OPEN. Parent must read this complete report, validate its exact sealed bindings and coverage, and decide qualification/publication separately. Validation and writer release record no heavy command, no pending remote command and no in-flight write.
