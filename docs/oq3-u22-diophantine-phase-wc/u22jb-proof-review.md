STATUS: CORRECT

JB343 independent complete final review, 2026-10-28.
Reviewer: fresh non-author context /root/oq3_jb343_final_review. Sole write scope is this report.
Requested model/effort: gpt-6.1-sol / xhigh. Runtime-confirmed actual model/effort are not exposed: null / null.

The entire frozen finite-algebra theorem and proof are correct. The actual exported theorem faithfully preserves the frozen statement. Exact successful server kernel and all-owned transitive-axiom evidence is reusable for this exact source; no new check was run by this reviewer. This verdict does not close original D, WC, a probability-law construction, or any other research root.

Reviewed exact inputs

- Entire source: u22jb-source.lean, 2468 bytes, 60 LF, SHA256 6677e408b9210e586797a4827833328b284f5bda0e7dd6d692e60af3e3b0db9e.
- Entire declaration freeze: u22jb-frozen-declaration.lean.txt, 301 bytes, 7 LF, SHA256 8d9c2b9425917790b7d9bb334b2d99894825bc0763c6eeeee35e3f66f61c8120.
- Entire scope: three-hundred-forty-third-unit-scope.md, 1385 bytes, SHA256 da9b681d9843c5de981f2d05eb27a397e2731ae437ccfb4c59e9305dbbc0112a.
- Entire review map: u22jb-review-input-map.json, SHA256 68fcb5d13e780e94b68f9f1b3be782dfd56390b5ae79b226cab1a54ec4e22864. All 32 bound inputs were read completely, including historical request files as inert data, all three failed sources, repair notes, full history, audit program and receipts. Final deterministic rehash: 32/32 expected hashes and byte sizes match; map and scope hashes remain exact.
- Entire actual-owned types: u22jb-actual-types.txt, 627 bytes, 13 LF, SHA256 b112381941c86b1cd434b357a5990c6e3d29886ef2ac97623686a4db7d975534. Both actual theorem types below were read, including the generated finite-sum theorem.
- Current REGISTRY.currentAuthoritativeState identifies Root coordinator 01a17d3c-6dfd-7cc0-94ed-35d758a423a5 and resumed OQ3 owner 01a16c48-80ee-7520-a9d9-faeeb6d05c78 under ROOT_OQ56_OQ3_40. Its phase document SHA256 is 2b69e1eb2251724f2236bd8176623e7445a794dbb12a4f17a346885469fba480. The selected current authority and streamlined acceptance policy were read; historical pause/resource descriptions are not treated as current authority.

Statement and quantifier fidelity

For every natural n, real weights w on Fin n with w k >= 0 and sum w = 1, and complex phases z with EACH norm equal to one, the conclusion holds for every ordered pair i,j:

    (w i * w j / 4) * norm(z i - z j)^2 <= 1 - norm(sum k, w k smul z k).

The scalar action is the real scalar action on the complex vector space viewed as a real inner-product space. There is no distinctness, strictly positive weight, positive n, phase representation, probability-law, independence, Diophantine, or desired-WC premise. The final source header matches the entire frozen declaration after whitespace normalization; freeze-binding time precedes first implementation. There are zero statement lets. The proof-local let S is only an abbreviation for the actual weighted sum and introduces no premise or independent owned value.

All boundary cases are preserved. For n=0, sum w = 1 is inconsistent and there are no indices i,j. For n=1 the only pair has zero chord and the normalized sum has norm one. For i=j or either selected weight zero, the selected term vanishes; the same proof still establishes the nonnegative norm defect. Repeated phases are allowed. No selected weight is divided by, and no denominator depending on a phase or norm is introduced.

Complete proof review, source lines 14-57

1. Lines 15-28 set S equal to the finite weighted sum and prove the exact cross identity

       sum k, sum l, w k * w l * inner_R(z k,z l) = norm(S)^2.

   Finite-sum linearity and the two real-scalar inner-product laws expand inner_R(S,S). Expanding in the library's order can expose inner_R(z l,z k). Line 26 explicitly invokes real_inner_comm (z l) (z k); it is a symmetry law for the REAL inner product, so no illicit complex Hermitian symmetry or missing conjugation is used. Ring normalization then handles scalar order/association. The final self-inner-product identity is exactly norm squared.

2. Lines 29-34 use sum w = 1 to obtain sum k,l w k*w l = 1, and expand each squared chord using norm_sub_sq_real and BOTH unit-norm hypotheses. Thus each term equals 2*w k*w l - 2*w k*w l*inner_R(z k,z l). These are identities, with no positivity or nondegeneracy assumption hidden in their use.

3. Lines 35-43 distribute both finite sums and combine those exact identities. The result is

       V := sum k,l, w k*w l*norm(z k-z l)^2 = 2*(1-norm(S)^2).

   The sum is over ordered pairs, including the diagonal. The factor two is correct. No probability integral or unproved variance interface is substituted for the finite sums.

4. Lines 44-55 prove every summand nonnegative from hw k, hw l and square nonnegativity. The first Finset.single_le_sum places the selected (i,j) term below row i; the second places that entire nonnegative row below V. Both membership obligations are membership in Finset.univ. This requires neither i != j nor a separate symmetric pair. Therefore, writing A = w i*w j*norm(z i-z j)^2 and r = norm(S), the proof has A <= 2*(1-r^2).

5. Lines 56-57 rewrite only the abbreviation S and use (r-1)^2 >= 0. The exact final algebra is

       4*(1-r)-A >= 4*(1-r)-2*(1-r^2) = 2*(r-1)^2 >= 0.

   Dividing by the positive constant four gives the frozen conclusion. This explains the nlinarith certificate and the coefficient 1/4. It needs no extra premise r < 1, no division by 1+r, and no independent norm-sum estimate. The factor is a valid conservative consequence of retaining one ordered-pair term.

Primary contracts

Read directly from the pinned server package, not inferred from theorem names: Mathlib/Analysis/InnerProductSpace/Basic.lean SHA256 82474b89f5565ab39507c3a9ac48044d6f266407c36dbc2d20be1e5a12ccf89d, including its real-inner-product section assumptions (lines 42-49), real_inner_comm (61), real_inner_smul_left/right (110/120), sum_inner/inner_sum (159/164), real_inner_self_eq_norm_sq (398), and norm_sub_sq_real (437). The ambient real-inner-product contract applies to complex vectors with their standard real inner product. Defs.lean was also hash-read, SHA256 1cd82a3742b60afb50e16c42d6a9b14bb96a047e9c1f852e9509bce40236201d. Finset.single_le_sum is the additive generated form of single_le_prod in Mathlib/Algebra/Order/BigOperators/Group/Finset.lean lines 272-278, SHA256 6e3729de582d0087db6e0323c32b3b1d5a645aa04eb1c2245b6ce75b449eff1c: nonnegative summands and membership are exactly the conditions supplied here.

Complete actual-owned declaration review

The module owns exactly two declarations, both theorems, and zero non-theorem VALUE declarations. The complete main TYPE is:

```lean
∀ (n : ℕ) (w : Fin n → ℝ),
  (∀ (k : Fin n), 0 ≤ w k) →
    ∑ k, w k = 1 →
      ∀ (z : Fin n → ℂ),
        (∀ (k : Fin n), ‖z k‖ = 1) → ∀ (i j : Fin n), w i * w j / 4 * ‖z i - z j‖ ^ 2 ≤ 1 - ‖∑ k, w k • z k‖
```

The other owned declaration is Shao.OQ3.finite_weighted_unit_phase_gap._simp_1_1. Its entire actual TYPE is:

```lean
∀ {ι : Type u_1} {R : Type u_4} [inst : NonUnitalNonAssocSemiring R] (s : Finset ι) (f : ι → R) (a : R),
  ∑ i ∈ s, a * f i = a * ∑ i ∈ s, f i
```

It is finite distributivity of left multiplication over a sum, valid even for this stated nonunital/nonassociative semiring class. It contains no phase/probability premise, hidden result assumption, or new standalone definition. No owned private/generated declaration is left outside the review or the audit.

Exact server evidence reused

The reviewer independently read and hashed current server source, preserved source-04, freeze, scope, audit program, actual types, full history, audit record and combined receipt. All matched the bound local inputs. The first original object at workspaces/lead-oq3/.lake/build/lib/lean/Shao/OQ3/FiniteWeightedUnitPhaseGap.olean is 226296 bytes with SHA256 52e86bd850c0b80a4d84ba23361c755963be441a6a9a191d8d3914ec6ffb4c9a. The accepted-source-view entry is a symlink resolving to that same original object, with that same hash. Current source and preserved source-04 have the reviewed 6677e408... hash.

Native attempt004 naturally returned RC0 in 4.607754394412041 seconds for the complete exact source, with native -M8192 -j4 and autoImplicit=false. Its entire 133-byte log was read, SHA256 fe9a6b741bba0630c9977614157f0259907b0b7ebce576a9400b542ee4518626; it contains only the known mathlib local-changes warning. The same-original-object audit naturally returned RC0 in 5.239706177264452 seconds. Its entire 879-byte log was read, SHA256 0a9e878f8566614ea18f2d04168d30f905606c097b3535aa3011d96ae7b249c6, and ends with U22JB_AXIOM_GATE PASS, all declarations2, all theorems2, frozen public theorem1, frozen definitions0.

The complete audit program selects declarations by actual module ownership and traverses every owned declaration's transitive axioms, rejecting new owned axioms and anything outside [propext, Classical.choice, Quot.sound]. The generated theorem uses [propext, Quot.sound]; the public theorem uses all three standard axioms. There are no VALUE/safety entries because there are no owned definitions. Source scan found no sorry, admit, new axiom, unsafe, or native_decide. Pinned server files confirm leanprover/lean4:v4.36.0-rc1 and mathlib807d3836b165983210ee2ecf3cd28f239436949c; the accepted package path remains shared-v34. This is complete exact-source kernel/owned-axiom coverage reused with independent semantic review, not a reviewer recompilation or publication/root-acceptance claim.

The entire saved logs for attempts001-003 were also read. Attempt001 failed on the unneeded Complex.Exponential object; removing only that import neither changed the statement nor requested cache repair. Attempt002 exposed the real-inner index orientation; explicit symmetry repaired it. Attempt003 exposed residual scalar association; ring repaired it. Their exact source hashes d03d9649..., 448f10a4..., 676cfef4... and full failed logs/repair records remain preserved. All attempts retain the same frozen declaration; only attempt004 is claimed successful. No failed or uncertain attempt is treated as a pass, and no old accepted producer/leaf audit was replayed.

Original-source purpose and remaining scope

Read the original read-only r2 report, SHA256 572e74aa9c12e2771f5543a5709a2807666eeea0a4076e7a3263e5c7bcf87f55, lines 326-491, including identity(21) at 352-367 and the complete requested 375-491 section. Lines 435-458 need a positive-pair characteristic-function gap for sixteen atoms at +/- eight amplitudes. JB343 supplies precisely a finite phase-sum/pair-chord inequality that can later be specialized to such positive pairs. It is a classical weighted-variance consequence and has no research-novelty claim. The same-actual-law characteristic-function identity, chord-to-lattice-distance comparison, TWO simultaneous real-parameter Diophantine properties and amplitude existence, joint nonlattice/near-resonance properties, small positive regular saddle, and full source-D assembly remain OPEN. No arbitrary two-dimensional vector replacement or desired WC assumption is introduced; this finite identity proves none of those existence or root claims.

Independence, final integrity and release

This reviewer did not author or modify the source, statement, freeze, scope, input map, audit program, qualification/status records or shared implementation. All 32 bound input hashes/sizes and the scope/map hashes were checked again after saving this report; the entire saved report was read back. Only this report was written. No Lean/AX/heavy command, lock acquisition, upload, Git/API publication, cache action, accepted-proof replay, child context or next unit was initiated. Read-only server inspection has completed; no reviewer request is left pending or uncertain.

Usage: actual_model=null, actual_effort=null; input_tokens=null, cached_input_tokens=null, output_tokens=null, reasoning_subset_tokens=null (not exposed). No subscription-percentage allocation is inferred.

FINAL_RUNTIME: COMPLETED_STOPPED. SOLE_REPORT_WRITER: RELEASED. heavy=0; inflight=0; pending=0; uncertain=0; children=0. No next unit.
