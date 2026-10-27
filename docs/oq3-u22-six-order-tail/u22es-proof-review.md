# ES230 independent complete final review

STATUS: CORRECT

Unit: ES230, `Shao.OQ3.ComplexTwoScalePolynomialTail`.
Reviewer: `/root/oq3_es230_final_review`, fresh independent final-review context, prescribed `gpt-6.1-sol` / `xhigh`.
Author/reviewer separation: the parent authored the proof; this reviewer neither authored nor edited any proof, statement, dependency, audit, receipt or publication file. My sole writable artifact is this report.
Final state: `COMPLETED_STOPPED`; report-writing authority and this review context are released upon delivery. No further writer, execution or delegated authority is retained.

## Exact coverage and byte identity

I read all 70 LF of the production source, all 13 LF of the frozen declaration, all 24 LF of the scope, all 20 LF of the actual-type output, all 47 LF of the audit source, and the complete receipt, build history, audit record and two dependency-binding JSON files. Full source proof and both actual-owned types were reviewed directly, without a duplicate-expression dictionary or type/proof summary standing in for unread text. All following hashes were independently recomputed from local bytes. These files are UTF-8 with LF and zero CR; the production source is 2942 bytes.

| Artifact under `drafts/oq3/` | SHA-256 | Bytes / LF |
| --- | --- | --- |
| `u22es-source.lean` | `af4b6c9addf8590da6c2d643b9e47af012d64d8412c454e62b939ee07baedf27` | 2942 / 70 |
| `u22es-frozen-declaration.lean.txt` | `53fe54c47e3969069e1b5d5ee315aea23bd8163d2ece37177651a011d0c0fdd9` | 618 / 13 |
| `two-hundred-thirtieth-unit-scope.md` | `e59e57272401a9a7b5e9565ace1972f56258a81990886ebe738d933d487a78c2` | 1565 / 24 |
| `u22es-actual-types.txt` | `fd20912332c54171f1194a7bac070d0170497bb2acbea9eb1cbdbc17ec2f593f` | 974 / 20 |
| `u22es-Audit.lean` | `e555c4e7d11f3a02ad9db792a98f1648a4a40477914ec3cf0d918e6b340621d5` | 2010 / 47 |
| `u22es-receipt.json` | `b319fbf2801e37ee056d0bad883c99386a48b4647809d69ba867e7ee4dbac569` | 5444 / 186 |
| `u22es-build-history.json` | `f4b642ec0f01ae7c90ae46bebcb70c9507c76fed2b41299175b634152a459c69` | 2158 / 82 |
| `u22es-audit-record.json` | `616f3c313e6da9369dbc087c51b4a57d62dc2f15ad4e086f8d930d9266096436` | 3104 / 104 |
| `u22es-qualified-dependency-binding.json` | `162833bbe70df28aea861d58820d03c604d691184225d5574bb99029f277220d` | 1314 / 27 |
| `u22es-server-dependency-binding.json` | `4796fb9fd355c932e70b0e7a63bc7c4ae76d3ce290f8fa5a983c0ecf3c2b7415` | 376 / 9 |

The declaration extracted from source lines 7-19, before `:= by`, equals the frozen declaration text after trimming only the surrounding whitespace. There is one source theorem and zero statement lets. The source contains none of `sorry`, `admit`, new `axiom`, `unsafe` or `native_decide`.

## Statement fidelity and uniformity

For arbitrary finite index types `ι` and `κ`, arbitrary complex coefficients `c`, natural exponent table `p` and weights `w`, and nonnegative real bounds `A`, the explicit premises require, for each monomial `i`, temporal degree `T_i = sum_j w_j p_ij >= 7` and physical degree `D_i = sum_j (w_j+2) p_ij` in `[9,48]`. The conclusion gives one strictly positive real `K` before every real `t,r` and every complex input family `a`, and bounds the norm of the whole finite polynomial by `K t^7 (r^9+r^48)` whenever `0 <= t <= 1`, `r >= 0`, and the displayed componentwise norm bounds hold.

This is exactly the frozen generic helper. No restriction to nonzero `t`, bounded `r`, real/nonnegative complex inputs, nonempty index types, positive weights or positive coefficients appears. `K` depends only on the fixed coefficient/exponent/bound data, not on `t`, `r` or `a`; the construction is stronger in that it does not use `w` or a choice of degree witnesses. The `hdeg` inequalities remain premises rather than being asserted for an actual omitted Taylor polynomial.

## Complete proof review

1. Source lines 20-26 set `P_i = product_j A_j^(p_ij)` and `B = sum_i norm(c_i) P_i`. Every `P_i` is nonnegative because `A_j >= 0`, and every summand of `B` is nonnegative. Thus `B >= 0`, and the chosen `K = B+1` is strictly positive. The existential witness is introduced before all `t,r,a` binders. This is a finite explicit sum, with no compactness argument or dependence on a later input.
2. Lines 27-36 fix arbitrary admissible `t,r,a` and set `A'_j = A_j r^(w_j+2)`. These bounds are nonnegative by `A_j >= 0` and `r >= 0`. The given norm inequality is exactly `norm(a_j) <= A'_j t^(w_j)` after associating/commuting real factors. The qualified EK222 polynomial estimate is instantiated with its variable-index type equal to ES230's `κ`, its monomial-index type equal to ES230's `ι`, bound family `A'`, radius `t`, and requested degree `7`. Its hypotheses `0 <= t`, `t <= 1`, nonnegative bounds, componentwise bounds and `7 <= T_i` are supplied verbatim. Its conclusion is the norm of this whole polynomial bounded by `C_r t^7`, where `C_r = sum_i norm(c_i) product_j (A_j r^(w_j+2))^(p_ij)`. The reused API is quantitatively strong enough and no converse or strengthened variant is assumed.
3. Lines 37-42 prove the required estimate on every radial monomial. If `0 <= r <= 1`, exponent antitonicity and `9 <= D_i` give `r^D_i <= r^9`; adding the nonnegative `r^48` gives the stated bound. In the other branch `not (r <= 1)` gives `1 < r`, hence `1 <= r`; `D_i <= 48` and exponent monotonicity give `r^D_i <= r^48`, then nonnegative `r^9` is added. `pow_le_pow_right₀` is used in its base-at-least-one/exponent-monotone direction. The split covers `r=1` in its first branch.
4. Lines 43-47 use `(A_j r^(w_j+2))^(p_ij) = A_j^(p_ij) r^((w_j+2)p_ij)`, distribute the finite product, and combine powers of the common base `r`. The stated `Finset.prod_pow_eq_pow_sum (s) (f) (a)` interface is precisely `product_{i in s} a^(f i) = a^(sum_{i in s} f i)`. Together with `mul_pow`, `pow_mul` and `Finset.prod_mul_distrib`, it gives `product_j (A_j r^(w_j+2))^(p_ij) = P_i r^D_i`. These are identities for natural powers and finite products and do not require a positive or invertible base.
5. Lines 48-58 multiply the radial estimate by the nonnegative `norm(c_i) P_i` and sum over every monomial. `Finset.sum_mul` expresses `B (r^9+r^48)` as that sum, giving `C_r <= B (r^9+r^48)`. Complex signs or phases cannot affect this step: EK222 has already taken the polynomial norm and the real coefficients here are norms times nonnegative products.
6. Lines 59-67 multiply the coefficient inequality by nonnegative `t^7`, enlarge `B` to `B+1` using nonnegative `r^9+r^48`, and commute real factors to obtain exactly `(B+1) t^7 (r^9+r^48)`. Both order multiplications have their nonnegativity premises present. The source ends with this goal, not a renamed intermediate inequality.

This checks every proof segment. No mathematical gap, altered premise, circular dependency or unjustified external analytic estimate was found.

## Boundary and adversarial checks

- If `ι` is empty, the polynomial and `B` are zero, the degree premise is vacuous, and `K=1` works because the right side is nonnegative.
- If `κ` is empty and `ι` has an inhabitant, each temporal degree is zero, contradicting `7 <= T_i`; such data cannot satisfy the premise. If both are empty, the preceding empty-sum case applies. Empty products still have their standard value one, throughout the algebra.
- At `t=0`, temporal degree at least seven ensures the vanishing required by EK222. Natural zero powers use their standard value one; no division or cancellation by `t` occurs. At `r=0`, each variable's factor `r^(w_j+2)` vanishes, and physical degree at least nine supplies the vanishing monomial bound; again no division is used.
- At `t=1` and `r=1`, the weak endpoint inequalities remain valid. Arbitrarily large `r` uses the upper degree bound 48. Arbitrarily small nonnegative `r` uses the lower bound 9. Reversing either of those exponent inequalities would fail; the source uses both correctly.
- Zero `A_j`, zero coefficients, zero exponents, and weights `w_j=0` are allowed. A zero weight contributes zero to temporal degree and two per unit exponent to physical degree; the source makes no unwritten inference that a single variable must have positive weight. The explicit monomial degree premises do the necessary work.
- Coefficients and inputs are arbitrary complex values, including negative real or nonreal values and cancellation among monomials. Norm bounds, not an ordering on complex numbers, are used. There is no probabilistic independence, law, moment, measurability or tail-event assumption hidden in this finite algebraic theorem.

## All actual-owned declarations and transitive axioms

The complete actual-type artifact is 20 LF. Its two declarations, with every binder and target, are as follows:

```text
DECL Shao.OQ3.complex_two_scale_weighted_polynomial_tail_bound._simp_1_1
TYPE ∀ {M : Type u_2} [inst : Monoid M] (a : M) (m n : ℕ), (a ^ m) ^ n = a ^ (m * n)
AXIOMS []
KIND theorem
DECL Shao.OQ3.complex_two_scale_weighted_polynomial_tail_bound
TYPE ∀ {ι : Type u_1} {κ : Type u_2} [inst : Fintype ι] [inst_1 : Fintype κ] (c : ι → ℂ) (p : ι → κ → ℕ) (w : κ → ℕ)
  (A : κ → ℝ),
  (∀ (j : κ), 0 ≤ A j) →
    (∀ (i : ι), 7 ≤ ∑ j, w j * p i j ∧ 9 ≤ ∑ j, (w j + 2) * p i j ∧ ∑ j, (w j + 2) * p i j ≤ 48) →
      ∃ K,
        0 < K ∧
          ∀ (t r : ℝ),
            0 ≤ t →
              t ≤ 1 →
                0 ≤ r →
                  ∀ (a : κ → ℂ),
                    (∀ (j : κ), ‖a j‖ ≤ A j * t ^ w j * r ^ (w j + 2)) →
                      ‖∑ i, c i * ∏ j, a j ^ p i j‖ ≤ K * t ^ 7 * (r ^ 9 + r ^ 48)
AXIOMS [propext, Classical.choice, Quot.sound]
KIND theorem
```

The generated `_simp_1_1` theorem is the general monoid natural-power composition identity, consistent with the `simp_rw` power rewrite at line 46, and has no axioms. The public theorem's full actual type agrees with the freeze in all finite-type instances, domains, degree conjunctions, input bounds, existential placement and universal quantifiers. There are two actual owners, both theorems, zero non-theorem values and zero statement lets. Local proof `let B` and `have` bindings are not additional environment-owned definitions or statement lets; their mathematical values and uses were reviewed in the full source above. No required non-theorem value is omitted.

I reviewed the complete audit implementation. It enumerates every environment constant, identifies the actual owner using `env.getModuleIdxFor?`, and selects the module `Shao.OQ3.ComplexTwoScalePolynomialTail`; it does not filter by a declaration namespace or just the public target. For each actual owner it rejects new axioms, recursively runs `Lean.collectAxioms`, enforces only `propext`, `Classical.choice`, `Quot.sound`, prints the type and any definition value, and checks the one public frozen theorem is present. The exact result is 2 TYPE / 0 VALUE; the generated theorem has empty axioms, and the main theorem has exactly the standard three. Theorems' tactic-generated certificate terms are bound through the accepted kernel object, without claiming to have printed or reread those proof terms.

## Exact existing server evidence and dependency reuse

The existing native history has one entry: attempt 001, exact ES230 source above, natural RC0, 4.789291530847549 seconds, recorded at `2026-10-27T16:27:47.690135+00:00`. Native log hash is `fe9a6b741bba0630c9977614157f0259907b0b7ebce576a9400b542ee4518626` / 133 bytes. First original object is `60e99f8bbc33e18b6eb8ef9adbc7a05f8a6f4e86942eeee149790eadd17e7cff` / 175704 bytes.

The same-first-object all-actual-owner audit then ended naturally RC0, 5.589496789500117 seconds, at `2026-10-27T16:28:13.198511+00:00`. Its log hash is `59427576764e46b77868bc59bae3ddc19a9d4751b1e980f348576554d1a4972d` / 1226 bytes; its source and actual-type hashes are in the table above. Receipt and audit record agree on the source, freeze, scope, first object, 2 actual owner names, 2 theorem types, 0 values and allowed axioms. There are no failed attempts in this unit's saved history. The parent reports only the known package-overlay notice, no new warning or failure. I did not directly read the raw server logs, independently query the server/object store or rerun Lean/AX; these are reused exact compact server receipts, not a new execution claim. There is no concrete receipt gap requiring raw-log access or a replay.

The recorded effective resource phase is `ROOT_OQ56_OQ3_40`, CPU 36-39/44-47, native `-M8192 -j4`. The shared memory helper's embedded phase39 label is historical and is distinguished from that effective execution phase. The pinned local project files and `SERVER.md` agree on Lean `leanprover/lean4:v4.36.0-rc1` and mathlib `807d3836b165983210ee2ecf3cd28f239436949c`; no local compiler or server command was run by this review. Acceptance status for this complete frozen helper can use `LEAN_FULLY_CHECKED` from its existing native and same-object all-owner receipts together with this semantic review, without extending that status to the original root.

I read EK222's entire 20-LF actual-type file (both public interfaces and its generated power-identity theorem), its qualification and the two ES bindings, and recomputed these existing dependency hashes:

- Source `u22ek-source.lean`: `0b3e9eac03a3ad7124ff0b4cf87a4a74deaeead2dfeb630c5e57106d570317c1` / 2270 bytes / 54 LF.
- Actual types: `841cdb7ceb19fc18419926c4d2fa7cf3db6c839c2460cd5ea8e732d40ffc3ff2` / 1126 bytes / 20 LF, 3 TYPE / 0 VALUE.
- Receipt: `ca42980ece616ce7c7ad3cafdf9297775275890e52b79aa86828e904611a4c20` / 7781 bytes / 267 LF.
- Qualified independent complete review: `d21e469b28e1141e8fc76cb6b645c55c7aac50767cfbe90b725b634d47ca25a2` / 21029 bytes / 119 LF; existing reviewer `/root/oq3_ek222_final_review` is recorded completed/stopped. Its old complete proof/report was not reread or recommissioned here.
- Qualification: `dfe4698c5b30d7bb6f80d95af9a94142a75e190254310c2283298b0d4b56c00a` / 1102 bytes / 24 LF, state `COMPLETE_QUALIFIED`, prescribed model/effort `gpt-6.1-sol` / `xhigh`.
- First original imported object, as bound in qualification and the worktree observation: `3c6dd3a6d5560d8d44469d391f1d5ba8701f75b802eed958a62d89be86b39fd8`.

The server dependency binding was recorded `AFTER_FIRST_NATIVE_BEFORE_SAME_OBJECT_AUDIT`, not before the native check. It records the exact EK source/object pair imported by this worktree, zero old-source/object changes, zero cache writes and zero new view links. ES230's exclusive source bytes remain unchanged. I rely on this exact observation and qualification, not a fresh dependency build or a repeated old proof/AX gate. The API instantiation and its interaction with the new radial algebra were independently checked above.

## Original-source scope and exclusions

I read the original `C:/game/shao/current/oq3/proofs/r2/report.md` lines 1-158 (sections 1-2) and terminal scope/accounting text, with whole-file hash independently verified as `572e74aa9c12e2771f5543a5709a2807666eeea0a4076e7a3263e5c7bcf87f55` / 20102 bytes / 523 LF. I also read the complete 58-LF `C:/game/shao/current/oq3/verdict.md`, hash `fd0a5732845aa96ab1725e6d1e52676502092e49d2c00225ce1fde26ac06f3b5` / 3041 bytes. This is source-scope intake for the new helper, not a repeated complete review of an old accepted proof.

The source requires an actual same-law weak-Cramer/tilted Edgeworth application with strict `0 < beta < 2/5`, fixed-tail geometry and appropriate localization. Its verdict preserves the accepted original counterexample and calls the positive repair one sufficient repair, not a characterization or optimal threshold. The final verdict attributes the uniform-in-law Edgeworth step to Song; ES230 imports no external analytic theorem and must not be used to turn the earlier report's Angst-Poly wording into a new attribution claim. Historical priority remains uncertified. The actual original law, E/rho quantities, strict beta range, p54 repairs, counterexample and external-result attribution are unchanged by this theorem.

ES230 proves only a finite quantitative polynomial dependency. It assumes its component norm bounds and all monomial degree inequalities. A future full order-six Taylor/exponential consumer must construct its actual omitted finite polynomial, identify these coefficients/exponents, prove temporal degree at least 7, physical degree between 9 and 48, and derive the actual same-law norm controls. It must also independently supply the actual cumulant coherence, CF/error, Gaussian/local-frequency control, full-frequency/Fourier/inversion and exterior arguments that are absent here. This review establishes none of actual full order six, the characteristic-function approximation, original error estimate, exterior or B-D/root completion. It does not replace E/rho or desired-error conclusions by helper premises. Original root status stays OPEN at the scope of this packet.

## Verdict and usage record

`CORRECT`: the exact frozen ES230 statement is true, its entire Lean source proof is mathematically complete, the full types of all actual-owned declarations faithfully match it, and the exact existing native/same-first-object transitive-axiom receipts cover it with the standard three-axiom whitelist. No correction is requested and no mathematical or evidence issue remains within this helper's declared scope. This is an elementary finite-algebraic quantitative helper for later analytic assembly; no mathematical novelty or original-root completion is certified.

Usage: model `gpt-6.1-sol`; effort `xhigh`; input_tokens `null`; cached_input_tokens `null`; output_tokens `null`; reasoning_subset_tokens `null` (runtime counters not exposed in this review context). No subscription percentage or purchased-credit allocation is inferred from token counts.

`COMPLETED_STOPPED`: only this review report was created. No source edits, server execution, Lean/AX replay, Git/API publication, external-chat message or additional agent was performed. The final delivery records this report's SHA-256, bytes and LF count; that self-hash is intentionally not embedded in its own bytes.
