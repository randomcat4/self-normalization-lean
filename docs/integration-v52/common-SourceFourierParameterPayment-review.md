# Actual threshold/Fourier parameter payment — independent final review

STATUS: **CORRECT**

LEAN_STATUS: **LEAN_FULLY_CHECKED for this exact module**, by verified reuse of the original server kernel and all-owned transitive-axiom receipts. This review launched no Lean command. The mathematical conclusion is parameter payment only; probability, five-region assembly, C1/C2, and novelty are not certified.

Reviewer: `/root/common_parameter_review`, fresh `gpt-6.1-sol` / `xhigh`, independent of author `/root/common_parameter_author`. The reviewer never authored or changed this unit. Only this report and its companion JSON are written. Author release was supplied before assignment; the server worktree remains at the frozen commit with no tracked changes. The two previously documented untracked modules were untouched. No successor is started by the reviewer.

## Exact version and declaration

Module: `Shao.Probability.SourceFourierParameterPayment`.

Commit `52b6e4727f84f23810f019a2c20c068974be3acc`, parent `bf3a6fd2cf2a8f1ddab3e1dabc289e44effcc9d5`. The actual Git delta adds only `Shao/Probability/SourceFourierParameterPayment.lean`. The committed blob, live server source, and local source all have SHA256 `e6b366379bb3997678076327835bbce2f2da3661594552f83cb6be2695f70d30` (5,283 bytes, 109 LF lines, zero CR). The source scan has no `sorry`, `admit`, `axiom`, `unsafe`, or `native_decide` token.

| Frozen artifact | Verified SHA256 |
|---|---|
| Root declaration freeze | `18b2822d336cbe162622251cdf8300c12359405826efc20ca4baea71cd28597c` |
| Complete literal candidate | `8da1c0ef097f0a69409634ebc2d4ffbb96c106ff4875b1b8d9f24d7e7e48322f` |
| Complete source contract | `8c5ccfbe26e40c07abceb85a9b293971e0f60d6a6ab70a05d45e107a5ced953e` |
| Author receipt | `b2e1589ac32b85fa51cb592f14840b7d2c943b0d3201a7afae4e547b335c6940` |

The complete implemented public declaration equals both the root-frozen declaration and the literal candidate after whitespace normalization. The root's approval controls the preserved candidate's historical proposed-status text. The full elaborated actual owned type was independently read from server log lines 6–272, not inferred from the source header. It has exactly the frozen real/natural types, quantifier order, premises, conditional law, raw absolute third moment, actual variance, and all ten output clauses. `autoImplicit false` is preserved; there are no hidden extra hypotheses.

Positive `kappa, delta` precede the existential `epsilon0`. That witness precedes every source law, `n`, `x`, `epsilon`, and `y`. Inputs remain: original probability law; original square integrability; `(n:ℝ) * ∫z² dν0 = 1`; original raw mean zero; `x≥0`; `epsilon>0`; `epsilon≤epsilon0/2`; actual `truncationBudget ν0 n x≤epsilon³/8`; `y>0`; and the exact window `|y-x|≤1/[2(1+x)]`. Support, gamma bounds, smallness, and cone inclusion are outputs. In particular the conditional law is never assumed centered.

## Complete source-to-statement review

The original source bytes were verified: `main.tex` SHA256 `beb00f718487e36de433175c97f1d500cb48e7a92ce5bd5ad5d62bb132122d06`; `supplement.tex` SHA256 `b99f2ac4d2f39dd39772d98a5702b7a923c2f10f8730a08fc1b4cd6bba4742bd`.

Read main LF373–379, 425–430, 622–625, 638–642 and supplement LF2045–2070, 2105–2118, 2370–2384, 2471–2476, 2501–2505, 2517–2520. These retain the original normalized observation, raw `n*m2` normalization, zero mean of the original law, true cutoff `h_x=epsilon/(1+x)`, and fixed conditional law. The source `gamma=m3/tau²` uses raw absolute third moment and true conditional variance; it is not a centered third moment or a ratio with raw second moment. The accepted `truncationBudget` is exactly `n∫F((1+x)z)dν0`, with the source budget, not a replacement envelope.

Main's chosen epsilon supplies `epsilon≤epsilon0/2`, and the comparison window is unchanged. Supplement's claims `h_x≤h`, actual support, `gamma≤2h`, `hy≤epsilon0`, and `C⊆C_x` are precisely the numerical obligations proved here. The two scales used outside are the actual `gamma/kappa` and `4h`. Consumer-specific low-frequency restrictions and `gamma≤y≤2` are not needed for this more general parameter lemma; they remain duties of their consumers. The theorem's positive `y` includes the source comparison domain `y≥gamma>0`. It does not claim the outside integrals, any probability identity, or the original root theorem.

## Complete proof review, lines 35–107

**Witness, lines 35–44.** `epsilon0=min(1/4,min(kappa*delta/2,delta/4))` is strictly positive from the two fixed positive inputs, and gives all three upper bounds. Its construction uses no later quantified data, so the required uniform order is real.

**Threshold and support, lines 45–78.** `1+x>0` and `1+y>0` are proved before division. The upper half of the genuine absolute-value window gives `y−x≤1/[2(1+x)]≤1`. With `x≥0` this yields `1+y≤2(1+x)`. Multiplying `epsilon≤epsilon0/2` by positive `1+y` and then using the denominator comparison gives `epsilon(1+y)≤epsilon0(1+x)`, hence `h_x≤h`. Both denominators are positive. `h>0` and `h≤epsilon0≤1/4` follow from `y>0`. The original epsilon gate also gives `epsilon≤1/2` (indeed ≤1/8); it is paid rather than assumed anew. The exact accepted `sourceTruncation_law_data` is called with the original law, `n`, square integrability, normalization, `x`, epsilon, and budget. Its fourth conjunct is the actual same-law AE cutoff support, which transfers by `h_x≤h`. No zero-mass conditional measure is used as a spurious probability law.

**Gamma, lines 79–85.** The accepted `sourceTruncation_gamma_bounds` receives exactly the same source inputs plus the original-law mean-zero premise. Its second and fifth conjuncts are respectively actual `gamma>0` and `gamma≤2h_x`, with actual `variance id ρ` as denominator. The definitional changes at lines 82–83 identify precisely the local `ρ` and `gamma`. Thus `gamma≤2h` follows by the established scale inequality. The theorem never assumes `∫z dρ=0`, nor substitutes the raw second moment for variance. Positivity and integrability needed to justify this ratio belong to the exact previously accepted interface, whose proof is reused unchanged.

**Smallness, lines 86–96.** The denominator identity gives `h(1+y)=epsilon0`; since `h≥0`, `hy≤epsilon0`. The bound `epsilon0≤delta/4` supplies `hy≤delta` and `(4h)y≤delta`, with the frozen parenthesization. Multiplying `gamma≤2h` by nonnegative `y` gives `gamma*y≤2hy≤2epsilon0≤kappa*delta`. Only after using `kappa>0` does division give `(gamma/kappa)y≤delta`. All three smallness conditions are produced, without importing any desired conclusion as a guard.

**Assembly and cone, lines 97–107.** All nine scalar/support outputs and the final cone implication are assembled without changing their order or definitions. `h_x>0` follows from positive epsilon and `1+x`. Positive denominators and `h_x≤h` imply `|u|/(4h)≤|u|/(4h_x)` by multiplying `4h_x≤4h` by `|u|≥0`. Transitivity with the input cone condition gives the source direction `C⊆C_x`. The frozen `u≠0` premise is retained even though this scalar implication also holds at zero.

The proof covers `x=0`, epsilon and budget equality, the closed window boundary, any admissible positive `y`, cutoff atoms, and nonzero conditional drift. It performs no unjustified cancellation at zero. `n=0` is incompatible with original normalization; no new sample-size or nondegeneracy premise was silently added. There is no gap, missing case, or changed mathematical assumption.

## Exact accepted interface reuse

| Dependency | Source SHA256 | Object SHA256 |
|---|---|---|
| SourceFourierScale | `5f31eb92eff8ded33b91f55a59a16de4e58cdd7a9e0514d082a2c4932f5feff0` | `181f3e96c2cde028a900a0d7c167ca7e521e1a19b28ac97427b9530e6433ab8b` |
| SourceTruncationBridge | `05321c22d1b2ea178fbc116178af345f4186bfce51011c8242b4ccfd2e0dd7d1` | `3a23c563b69b9316b50d14f3b008ad26575d4c547602f4abd13e9c1718295c7a` |

These are actual current server hashes and match the accepted local snapshot and author binding. The complete called interface types were read. Existing complete CORRECT reviews are reused: `drafts/c12/SourceFourierScale-proof-review.md` SHA256 `e265f21823ba9b0e01344f94115b1dbeed107fb7086fce258cb910e5d48a35ed` and `drafts/c12/SourceTruncationBridge-proof-review.md` SHA256 `1f86c5ce2b808ff9ce16a79daab53bc9c98933e32bd3e9f42a9c0d0b68cafef8`. No old proof or successful old check was repeated.

## Server execution and complete actual-owned coverage

Worktree `/root/rivermind-data/shao-lean-20261021/workspaces/common-cone-derivatives-v44`, branch `feat/common-chord-cone-derivatives`, at the exact commit above. Actual `lean-toolchain` is `leanprover/lean4:v4.36.0-rc1`; actual mathlib HEAD is `807d3836b165983210ee2ecf3cd28f239436949c`. All original checks use root's shared `root-heavy.lock`, CPU10–13, `-M8192 -j4 -DautoImplicit=false`. No local Lean, new compilation, cache mutation, or source mutation occurred during review.

Original kernel command, direct Lean exit **0**:

```text
flock /root/rivermind-data/shao-lean-20261021/locks/root-heavy.lock taskset -c 10-13 lake env lean -M8192 -j4 -DautoImplicit=false -o .lake/build/lib/lean/Shao/Probability/SourceFourierParameterPayment.olean Shao/Probability/SourceFourierParameterPayment.lean
```

The actual output object is 428,440 bytes, SHA256 `767cabeac679f2337f99b6936ea5f4c8063c6057a5eb16a222fbe371fe48b95e`. The original 524-byte `outputs/common-parameter-payment/check01.log` was read completely; SHA256 `cb270ef6aa20eaccff94c75b3a76b0ee35509c45cfd71972562cf17c71a9abbe`. It contains only the already documented mathlib local-change warning and the harmless `letI` style diagnostic. Original `check01-receipt.json` SHA256 `d87ce520d5160aecd6c5dcba894c5752a570085eda8ce220ec4cf071241b844e` was read on the server and matches the local receipt and original tool return's direct exit zero.

Original all-owned audit command, direct Lean exit **0**:

```text
flock /root/rivermind-data/shao-lean-20261021/locks/root-heavy.lock taskset -c 10-13 lake env lean -M8192 -j4 -DautoImplicit=false /root/rivermind-data/shao-lean-20261021/outputs/common-parameter-payment/OwnedAudit.lean
```

The actual audit source was read completely and hashes to `7e207973e1946ae2a55cd0cce75cbaa76a763109c3d5283bad2e57b7ce1494dc`. It enumerates every environment constant with defining owner module equal to this exact module, including private/generated constants, and runs recursive `Lean.collectAxioms` on each selected constant. It does not infer ownership from public names or source word counts. It rejects every axiom outside the standard whitelist and separately checks public theorem kind and presence.

The actual 46,124-byte `outputs/common-parameter-payment/actual-owned-types-values-and-axioms.log` has SHA256 `bae9e108a8a046d55b91073d703c911d88c44baa0f21a6ec1bc613f072d2535a`. Its complete sole `ACTUAL_TYPE` block (lines 6–272), owner/axiom record (3–5), actual summary (273), and final `#print axioms` record (541–543) were read without truncation. The second `#check` type is redundant and is not counted as another owner. Actual `owned-audit.json` SHA256 `7e7c15fb76e5605a301c4e5779828286ef5a69548702de6a423049f53c1bb0e8` was read on server. Original `audit-receipt.json` SHA256 `0820f3e07cec1d394da45cac85a514a59773893124ac4db05404e9f4043456ec` matches both the local receipt and the original audit tool return's direct exit zero.

| Actual owner | Kind | Full type | Full definition value | Recursive axioms |
|---|---|---|---|---|
| `Shao.Probability.sourceTruncation_threshold_fourier_parameter_payment` | theorem | Complete, reviewed | Not a definition | `propext`, `Classical.choice`, `Quot.sound` only |

Verified owner-map counts: **1 actual constant, 1 theorem, 1 public theorem, 0 definitions including private/generated**. Thus actual-type coverage is **1/1**, theorem source-proof coverage is **1/1**, definition-value coverage is complete at **0/0**, and recursive-axiom coverage is **1/1**. These counts come from actual module ownership, not textual declaration counts. No unreviewed owned helper or generated definition exists in this object.

One read-only log extraction attempt failed because it expected an absent display prefix; it wrote nothing and invoked no Lean. It was corrected by exact line extraction, yielding the complete actual block above. There was no proof, source, check, or receipt change.

## Final scope and release

No critical gap was found. The exact frozen theorem, its entire proof, actual type, zero-definition-value scope, and all actual-owned recursive axioms are accepted **CORRECT**. Root may reuse this review plus the exact original kernel/object/audit evidence at integration, checking unchanged hashes, interfaces and interactions. This review does not merge or publish anything and does not close C1/C2, a probability root, or any other original root.

Reviewer runtime: all read-only tool calls returned; only the two assigned report files were written; no Lean/source writer or successor is in flight. Reviewer slot is released on return. Exact token telemetry was not exposed: input, cached input, output and reasoning-subset counts remain unknown, with no subscription-percentage allocation inferred.
