STATUS: CORRECT

# U22DU / unit206 complete independent proof review

Reviewer role: fresh non-author complete final reviewer; prescribed gpt-6.1-sol / xhigh context. This reviewer authored no DU proof and made no source, Git, cache, or shared coordination mutation. The only owned write is this report. No subagent or sidebar chat was created.

## Exact reviewed version and evidence

- Frozen scope: `two-hundred-sixth-unit-scope.md`, all 20 lines / 1477 bytes, SHA256 `6656117546b41844a13ef0013b2f468a28aafa463fce3c5ad12dedf9f206f4b2`.
- Complete new source: `u22du-source.lean`, all 51 lines / 2056 bytes, SHA256 `5b3386db0cc96b3078690f34a621ec715ee211528dc2484ba4be9afa7718842f`.
- Complete actual owned types: `u22du-actual-types.txt`, all 14 lines / 775 bytes, SHA256 `e2719efcabe868a6009e03cfa653455aab038ea3ecb0ead06fe8fc9dfcc01b53`.
- Complete owner-audit source: `u22du-Audit.lean`, all 47 lines / 2043 bytes, SHA256 `cd6f54d99a021ebab73748789b5890004f1399b49a354a995f6dae570227673b`.
- Complete author receipt: `u22du-receipt.json`, all 137 lines / 8834 bytes, SHA256 `933c4d909dc23a1a12bfa68e19d76e5af45499a4a1b60fdf1da66431271641be`.
- Also fully read build-history, audit-record, audit-environment, and dependency-source-binding JSON; hashes respectively `a33e09c99b7596fa49e04e5b001f095a3d9724dd5d58d8d042a356cef4d016d2`, `dfe6210f3a92b3b63f6ae950980218cb414db472f7de4a27f8c9cc3eaf6c6c3b`, `7f9f79d0b127ceb71c0f255451ba7cf9fc4d96862625fb89233c7ac4c2b58ab9`, and `f09e91f2cddb8c49b20a69cc27d34e3e726912f8bd0eca0b49144c28d42dfc0a`.
- Read-only server observation verified the same frozen run source, scope, Audit, actual types, records and receipt, plus unchanged current production source and original object. Server run: `/root/rivermind-data/shao-lean-20261021/runs/oq3/u22du-20261023`; worktree: `/root/rivermind-data/shao-lean-20261021/workspaces/lead-oq3`.
- Original production object: 112272 bytes, SHA256 `2aae684e7c0f28ca325baf8e89a6987a011d08ffa566c1b5f552a729aad0bd4b`. Frozen server source and scope are valid UTF-8, without BOM or CR bytes. No frozen bytes were rewritten.

## Statement fidelity and complete actual owner coverage

The two declarations are exactly those frozen in scope lines 6–19. The full elaborated owner output, including the only statement-local let value, is:

```text
DECL Shao.OQ3.euclidean_frequency_radius_scalar_mul
TYPE ∀ (s u v : ℝ), √((s * u) ^ 2 + (s * v) ^ 2) = |s| * √(u ^ 2 + v ^ 2)
AXIOMS [propext, Classical.choice, Quot.sound]
KIND theorem
DECL Shao.OQ3.pair_projection_moment_homogeneity
TYPE ∀ (law : MeasureTheory.Measure (Fin 2 → ℝ)) (m : ℕ),
  MeasureTheory.Integrable (fun y => √(y 0 ^ 2 + y 1 ^ 2) ^ m) law →
    ∀ (u v s : ℝ),
      have L := fun y => u * y 0 + v * y 1;
      MeasureTheory.Integrable (fun y => L y ^ m) law ∧
        MeasureTheory.Integrable (fun y => (s * u * y 0 + s * v * y 1) ^ m) law ∧
          ∫ (y : Fin 2 → ℝ), (s * u * y 0 + s * v * y 1) ^ m ∂law = s ^ m * ∫ (y : Fin 2 → ℝ), L y ^ m ∂law
AXIOMS [propext, Classical.choice, Quot.sound]
KIND theorem
```

This is an arbitrary actual measure on `Fin 2 → ℝ`, with precisely the stated Euclidean radial natural moment integrability hypothesis. There is no probability, finite-measure, nonzero-scale, positive-scale, nonzero-direction, centering, independence, or target-integrability premise hidden in the actual type. Both signed directional integrability conclusions are proved. The integrals use the very same `law`; there is no measure replacement, pushforward, or dummy moment variable. The local `L` is fully specified and is the original unscaled linear projection.

The module has exactly 2 actual owned declarations, both public theorems: 0 private theorems, 0 generated theorems, and 0 owned definitions/definition values. The statement-local `L` is not an extra global declaration and its value has been completely reviewed. All owner types and the entire new proof source have been reviewed; this is not only an exported-head review.

## Qualified dependency and primary API binding

The only consumed project result is qualified DJ195 `Shao.OQ3.pair_projection_absolute_moment_bound`. I read its complete 10-line actual interface, including `f := fun y => |u * y 0 + v * y 1| ^ m`, the same radial hypothesis and measure, and all three conjunction components. DU uses only its first component, namely the integrability of that actual absolute projection power.

The DJ source hash is `19cc0b3b4d191ad64745541503822fbb85bfaebf094229995b5d914e009713f9`; I verified its unchanged production source and 61680-byte object `488fc0f7d3f5f9a5bc488d2ec3942b5e726182dedfabb83d5b64fc6e2238dc1d` on the server. The complete actual-interface hash is `a710ed7aeec4232fc3e0502dd3e4f545d408a888d0bb340a1042cce3c500da9d`; receipt hash is `220ec0bac89061d4160c65ca462cb01a575a55f812f158ac53befeae706edd9f`. Its already qualified 93-line complete CORRECT review has hash `3dc8928583aa782d48378d2e0334364025bad27dac1b1bf2c1820a512e6779aa`, verified unchanged with CORRECT status. The parent had fully read that report and stopped its reviewer before DU implementation. That prior complete qualification is reused; I did not rereview DJ's old complete proof/report or replay its gates.

I also inspected the exact needed primary library source excerpts and verified their source/original-object hashes against the pre-implementation binding:

- `Mathlib/Analysis/Real/Sqrt.lean`: source `1f19e1d6722b2f51c2cd676d0b28ede856c7915ac815b597cef4b3919040c204`, object `9a09ac674e3d6008c67e5082620f5ffe3e96dbe72472fdd1c43d5d0670f0df34` (263048 bytes). Actual `Real.sqrt_mul` requires nonnegativity of its first factor, and `Real.sqrt_sq_eq_abs` is valid for every real argument.
- `Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`: source `66837a733a5514a0fd824591ac10d43063c5a5cd94c9bdbbf80025686c16c670`, object `f5094fe4e519cc8ffde3283787cbd42f5f686cd9121e35776578902dadae75a7` (688952 bytes). Actual `integral_const_mul` and `integral_congr_ae` have the needed same-measure orientation and real scalar specialization.
- `Mathlib/MeasureTheory/Function/L1Space/Integrable.lean`: source `d80e3495465030c1accca450935e4bfafcfe31d9b695e17f23ee9cfcea537759`, object `6fe2b53c5cd131f560eeff2765fbdbbf956a12b8676cb5ec9b2bae9c74239aa0` (621928 bytes). I checked `integrable_norm_iff` at lines 604–606, the exact `Integrable.congr` at lines 126–127, and `Integrable.const_mul` at lines 1028–1030. The final binding names `Integrable.congr`, not the nearby `congr_enorm`. The handoff's earlier display-extraction correction was before implementation, not a kernel failure or proof repair.

## Complete proof review

Source lines 20–23 introduce precisely the statement-local `L` and prove its continuity from the two coordinate projections, scalar products and sum. Therefore `L^m` is continuous and hence AE strongly measurable for the same arbitrary `law`. No measurability of an unrelated function or extra measure class is assumed.

Lines 24–28 use `integrable_norm_iff` in the correct `.mp` direction: integrability of the norm of the measurable signed power implies integrability of the signed power itself. Since this norm is the norm of a real number, `Real.norm_eq_abs` and `abs_pow` identify it exactly with `|u*y 0 + v*y 1|^m`, whose integrability is DJ's first component. This does not substitute the Pi-space supremum norm for the literal Euclidean radial moment. The sole radial-to-projection estimate is the already qualified, exactly bound DJ interface.

Lines 29–33 prove pointwise, for each actual `y`, the identity `((s*u)*y 0 + (s*v)*y 1)^m = s^m * L y^m`. Distributivity is checked by `ring`; `mul_pow` applies to every natural exponent over the reals. There is no division, cancellation requiring a nonzero factor, absolute-value substitution, or asymptotic argument.

Lines 34–36 start from the proved signed base integrability and apply `const_mul (s^m)`. Its integrand is `s^m * L y^m`; thus `(hscale y).symm` is exactly the AE equality required by `Integrable.congr` to obtain the scaled signed projection integrability. `Eventually.of_forall` supplies this equality for every `y` under the same `law`, without an unstated exceptional set.

Lines 37–42 assemble the two actual integrability conclusions and the actual signed moment identity. In `integral_congr_ae`, `hscale` is now used in the forward direction, from the scaled projection to `s^m * L^m`. `integral_const_mul` then moves exactly the real constant `s^m` outside the same integral. Both relevant integrands have already been proved integrable, so the result is a genuine moment identity, not an equality exploiting the nonintegrable-integral convention.

Lines 44–48 prove the exact Euclidean frequency identity. `ring` factors the squared radius as `s^2*(u^2+v^2)`; `sq_nonneg s` is precisely the premise of `Real.sqrt_mul`; `Real.sqrt_sq_eq_abs` supplies `|s|`. Neither positivity nor a nonzero radius is required. The conclusion retains the literal square-root Euclidean radius and the correct absolute scale.

## Boundary and assumption checks

All real `u,v,s`, including negative `s`, are retained. Odd signed moments carry the sign of `s^m`; even moments follow from the same unrestricted identity. No replacement by `|s|^m` occurs in the signed integral formula. In contrast, the radius correctly uses `|s|`.

Every natural `m`, including 0, is retained. For `m=0`, natural-power semantics give `x^0=1` also when `x=0`, and `s^0=1` including `0^0=1`. The given radial integrability is then integrability of the constant 1; any finiteness needed for this case is contained in that written premise, not silently added as a typeclass. For `s=0,m>0`, the scaled integrand and right scalar factor are both zero. Zero directions, the origin, zero measures, and degenerate supports require no separate excluded case. No cast or change from natural powers to real powers appears.

## Original successful server evidence and transitive axioms

I read both original logs in full through the read-only server transport, not by downloading raw logs. First and only kernel attempt: exit 0, 4.6799448896199465 seconds; `build-01.log` is 133 bytes with SHA256 `fe9a6b741bba0630c9977614157f0259907b0b7ebce576a9400b542ee4518626`. It contains only the known Lake package-overlay warning. There are no failed kernel attempts or source repairs in this run.

Original sole owner/transitive-axiom gate: exit 0, 5.662740081548691 seconds; `audit.log` is 1027 bytes with SHA256 `a093ab0de9d7bd9f257f23b6a06c82b79ccf5e6b5ffd2dffb18f8cb8e7ca0caf`. It prints both complete types above and reports frozen definitions 0, frozen theorems 2, all theorems 2, all declarations 2, AXIOM_GATE PASS. The audit source checks actual module ownership across all environment constants, rejects a new owned axiom, and calls recursive `Lean.collectAxioms` for every actual owner. Both actual owners have exactly `[propext, Classical.choice, Quot.sound]`; there is no unexamined private/generated owner or definition value.

The whole new source contains no `sorry`, `admit`, new axiom, `unsafe`, or `native_decide`. Noncomputability is ordinary and does not bypass the kernel. The pinned server `lean-toolchain` is `leanprover/lean4:v4.36.0-rc1`, and `lake-manifest.json` pins mathlib `807d3836b165983210ee2ecf3cd28f239436949c`. Original gates record CPU14–17, native memory 8192 MiB, jobs 4, `autoImplicit=false`, and the existing shared-v34 read-only package view. This reviewer ran no Lean, build, audit, smoke, installation, hydration, or successful-gate replay; only original evidence and hashes were read.

## Scope verdict and stop

CORRECT for the entire exact DU206 source, both frozen statements, all actual owners/types/local values, proof details, semantic fidelity, qualified dependencies, and exact-source server kernel/transitive-axiom evidence. No critical mathematical or evidence gap remains within this helper's stated scope.

This is a necessary directional-moment/frequency normalization helper. It does not establish analytic higher cumulant identities, normalized IID Edgeworth bounds, full-frequency control, inversion, exterior bounds, a new rho-Laplace result, or original OQ3 B/D closure. Original source scope, p54 repairs, strict root beta and external-result attribution are preserved; no mathematical assumption or historical novelty claim is changed. DU does not consume unfinished DS/DQ/DR proofs. This report does not merge or accept a PR or change a root integration receipt.

Review complete. Sole report written; all reviewer tool use and writes stop after recording its hash and line count.
