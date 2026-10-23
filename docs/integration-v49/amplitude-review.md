# Independent amplitude-family review — CORRECT

Fresh independent final reviewer `/root/common_amplitude_review`, gpt-6.1-sol / xhigh; no authorship, source edits, delegated reviewers or Lean/check replay. Review completed 2026-10-23T09:04:30.958727+00:00.

The complete first frozen theorem is correct: one **M > 0** bounds every actual r derivative of orders **0 through 32**, for **k=0 or 2**, every **|theta| <= 1/16** including endpoints, and every real r. The amplitude is exactly `sourceKernelCutoff r / (Real.sqrt r + theta)^k`; global C-infinity smoothness and tsupport inclusion in `[1/16,4]` are proved. There is no supplied amplitude budget. The public signature matches the first original frozen declaration after whitespace normalization; only the approved owning-module split changed.

## Exact scope and identity

- Author commit: `f607d3399121d6058d09e96eca8bf299f6e12076`; module `Shao.Probability.SourceKernelAmplitudeFamily`, 192 source lines / 8808 bytes.
- Source SHA256: `1a5c4ca17ab1cfbad4565412827f3546de519512a577a7e4041347f9c48e9970`. Local draft, current server target and frozen commit blob all match; target-path Git status is clean. Later author work elsewhere does not invalidate this version.
- Object SHA256: `15cc5fde79f240f26782f0daabf9c49c1a06f60968068cebf2a684818db94ff7` (443864 bytes).
- Frozen candidate: `ad064d55bd60ef9770c5c67ce1a16600a0afdbcd67d695b0849f9f880b484806`; source contract: `9af7cff8c8088425844e7c6d09880bed3c82ff9e5b08313910a2269b8231a115`. Root approvals are `public-marked-outside-declaration-freeze.md` and `public-marked-amplitude-module-split.md`.
- Complete original supplement ranges read: LF2402–2424, 2571–2582, 3239–3266; source SHA256 `b99f2ac4d2f39dd39772d98a5702b7a923c2f10f8730a08fc1b4cd6bba4742bd`.

## Mathematical review

LF2571–2582 produces exactly chi and chi/(sqrt(r)+/-w/y)^2. For y>0, |w|<=y/16 gives the full closed signed parameter interval. The accepted cutoff has actual support `[3/32,97/32]`, and its consumed theorem gives strict inclusion in `(1/16,4)`. Hence sqrt(r)>1/4 there; the public denominator is >3/16. On-support sqrt is smooth at nonzero r. Outside tsupport, chi is locally zero, and so is the totalized quotient, including at sqrt(0), negative r and every other possible denominator zero. The proof covers support boundary points in its on-support branch.

For uniformity, the proof multiplies by a smooth parameter bump equal to one on the **closed** interval [-1/16,1/16] and supported in [-1/8,1/8]. On the joint support the denominator remains >1/8. Outside either factor's support the joint quotient is locally zero. Its support is contained in a fixed closed compact rectangle, so the actual globally smooth joint function has one bound for all Frechet derivatives through order 32. The linear slice r -> (0,r), translated by (theta,0), identifies actual r derivatives with the joint derivative evaluated on j copies of (0,1). Each direction has norm one; the empty product at j=0 is also one. The consumed mathlib derivative/translation/finite-bound interface statements were checked.

Separate nonnegative C0 and C2 are combined as `max C0 C2 + 1`. This pays the exact outer existential M with no dependence on k, theta, j or r. No oscillatory tail or frequency-dependent derivative budget occurs. This is the ordinary additive-parameter family, not source(b)'s distinct localized smooth-step Theta.

## Complete actual declaration coverage

The entire 614-line actual export was read, including every fully expanded type, all three definition values, every private/generated relation and the repeated full public type. It contains 23 actual-type blocks and 3 definition-value blocks, the final counters and public end marker; there are no ellipses or truncation markers. Selection uses exact module ownership, not namespace/name prefixes. Full owner names, export line ranges and individual findings are in the JSON report.

| Actual declaration (private names shortened here only) | Source lines | Export lines | Finding |
|---|---:|---:|---|
| `markedParameterBump._proof_3` | 66-67 | 3-17 | CORRECT: Generated obligation 0 < (1/16 : Real); correct rational positivity. |
| `markedParameterBump` | 66-67 | 18-35 | CORRECT: Actual value is ContDiffBump at 0 with inner radius 1/16 and outer radius 1/8 and the checked positivity/order proofs. |
| `markedJointAmplitude.eq_1` | 69-71 | 36-56 | CORRECT: Generated defining equation is exactly bump(theta)*sourceKernelCutoff(r)/(sqrt(r)+theta)^k. |
| `markedJointAmplitude_contDiff` | 79-113 | 57-79 | CORRECT: Joint smoothness for each k: quotient on the support product has sqrt(r)>1/4 and denominator>1/8; off either support the numerator is locally zero. |
| `markedParameterBump._proof_1` | 66-67 | 80-84 | CORRECT: Generated Nat.AtLeastTwo (15+1) instance; no additional hypothesis. |
| `markedJointAmplitude_slice` | 131-138 | 85-101 | CORRECT: Closed inner ball gives bump(theta)=1 for every abs(theta)<=1/16, including both endpoints; exact function equality with markedAmplitude. |
| `markedAmplitude_tsupport` | 19-26 | 102-112 | CORRECT: Pointwise zero of the numerator forces totalized quotient zero for all k/theta; closure monotonicity gives tsupport inclusion. |
| `markedAmplitude_denominator_pos` | 28-38 | 113-132 | CORRECT: Accepted strict support r>1/16 implies sqrt(r)>1/4, and theta>=-1/16 gives positive denominator (>3/16). |
| `markedAmplitude_deriv_eq` | 140-155 | 133-268 | CORRECT: Translation and linear slice L(r)=(0,r) identify the actual r derivative with joint Frechet derivative applied j times to (0,1), including j=0. |
| `markedParameterBump._proof_4` | 66-67 | 269-287 | CORRECT: Generated rational order obligation (1/16 : Real)<1/8. |
| `Shao.Probability.sourceKernel_marked_amplitude_family` | 171-190 | 288-353 | CORRECT: Exact frozen complete public statement. M=max(C0,C2)+1 is positive and precedes k,theta,j,r; k=0/2 and all j<=32 use this one M. |
| `markedAmplitude_uniform_bound` | 157-169 | 354-383 | CORRECT: Compact globally smooth joint function supplies one finite-order Frechet bound; unit slice directions transfer it to every theta in the closed parameter interval and every real r. |
| `markedAmplitude` | 16-17 | 384-394 | CORRECT: Actual value is precisely sourceKernelCutoff(r)/(sqrt(r)+theta)^k, with totalized real division and natural power. |
| `markedParameterBump_abs` | 73-77 | 395-418 | CORRECT: Exact tsupport closed-ball formula yields abs(theta)<=1/8. |
| `markedJointAmplitude_compact` | 115-129 | 419-427 | CORRECT: Nonzero quotient implies both numerator factors nonzero; their support product lies in the fixed closed compact rectangle [-1/8,1/8] x [1/16,4]. |
| `markedAmplitude_support_interval` | 60-64 | 428-446 | CORRECT: Accepted source cutoff tsupport is inside (1/16,4); quotient support inclusion yields the requested closed [1/16,4]. |
| `markedJointAmplitude` | 69-71 | 447-468 | CORRECT: Actual value is the parameter bump times the exact source cutoff, divided by the stated natural power; no substituted amplitude or derivative budget. |
| `markedParameterBump.eq_1` | 66-67 | 469-486 | CORRECT: Generated equation has exactly center 0, radii 1/16 and 1/8, and the corresponding generated proof fields. |
| `markedAmplitude_contDiff` | 40-58 | 487-509 | CORRECT: On tsupport use smooth sqrt at r!=0 and positive denominator; outside tsupport use an eventually zero cutoff and hence eventually zero quotient. Covers r=0 and every other denominator zero. |
| `ContDiffBump.mk.congr_simp` | 66-77 | 510-525 | CORRECT: Fully read generalized constructor congruence: equality of radii transports the positivity/order proof fields, yielding equality of bump records; only explicit equality hypotheses. |
| `markedParameterBump._proof_2` | 66-67 | 526-530 | CORRECT: Generated Nat.AtLeastTwo (7+1) instance; no additional hypothesis. |
| `markedJointAmplitude._proof_1` | 69-71 | 531-537 | CORRECT: Generated HasContDiffBump Real instance from the real inner-product structure; no new mathematical premise. |
| `markedAmplitude.eq_1` | 16-17 | 538-547 | CORRECT: Generated defining equation is exactly the actual quotient for all natural k and real theta/r. |

## Reused server evidence

Pinned Lean `leanprover/lean4:v4.36.0-rc1` and mathlib `807d3836b165983210ee2ecf3cd28f239436949c` match the worktree's pinned files. The author receipt records successful kernel and all-owned transitive-axiom exits under the shared root lock / CPU10–13 / -M8192 -j4. Current source/object/artifact hashes were independently checked through the existing broker:

- Kernel log SHA256 `e737184c2f87adf2667327bab4abebab172f4f20d49ec8e12bd6dc6246ad139b`; only the existing mathlib-local-changes warning is present.
- Actual type/value/axiom log SHA256 `f6ffa8ca68f7f62465f06278d768ecf0190612c4d91177e67970eab6eeca443a`.
- Owned audit JSON SHA256 `6c32c57832e06464ac3e5953915924df3ae116b05b4ea61d8335c9ed71192ff7`; exporter source SHA256 `fcc851c9b6b7e4e5f490a64e53dc678a50cf5e0f5ae46b112d150e6d4d70ec31`.
- Exact owner-map/log names agree: **23 constants = 20 theorems including generated + 3 definitions; 1 public theorem**. Every transitive axiom set lies within `{propext, Classical.choice, Quot.sound}`. The generated global `ContDiffBump.mk.congr_simp` is included. No forbidden proof placeholders, new axiom, unsafe or native_decide occurs; frozen source is UTF-8 LF with zero CR.

The accepted `SourceFourierTestKernel` source/object hashes are unchanged: `151fe42cda5414873ea9c9ea3359d256e971132073ea9d1c714ea0105af234d3` / `f3d751f7a84fa991841a6a005e009b1d6ee28cb2347f55a0280417637adaaeba`. Its actual cutoff and data interface were read; its existing qualified internal proof review and v46 root acceptance were reused.

**No required fixes or critical gaps.** This accepts the complete first amplitude-family theorem only. N0=32 outside-v IBP/tails and sine minimum factor, actual Fourier inversion, Region3/5 composition and whole-u boundary terms, localized/growing-y work, probability bounds, de-smoothing and C1/C2 remain OPEN. Root integration still checks interactions under its normal gate; this report does not certify an unbuilt aggregate or claim novelty.

Runtime: review complete and reviewer released; no source ownership, Lean/audit process or child remains. No successor task was assigned. Actual token counters are unavailable and are not inferred from subscription percentages.
