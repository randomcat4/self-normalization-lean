# Unit 222 complete independent source review

STATUS: CORRECT

This verdict concerns the frozen source and its mathematical/static interface review only. formalQualified=false. No Lean kernel, TYPE/VALUE ownership, generated-declaration, or transitive axiom receipt exists in this review. No compiler, server, network, upload, Git or API action was run.

## Identity, independence and bytes

Reviewer role: /root/centered_double_sandwich_formal_review001. Author: parent C12 owner 01a174b9-5b2e-7611-ba13-02580d678eb3. The reviewer did not write or repair the candidate and did not change any input. Configured model/effort: gpt-6.1-sol/xhigh; actual model/effort and input/cached-input/output/reasoning-subset usage are unobservable here and recorded as null, not inferred from configuration.

The exact parent activation is a8a4eeffd5c814380ff7cca0b517b9cd9d8da6ff6c596a2b50cedb6430fcbf0f (5213 bytes). All 15 listed inputs matched both SHA256 and byte length before ACTUAL-ACK.json was written. The candidate is:

- source001/AuxiliaryCenteredDoubleSandwich.lean
- SHA256 a2d1096fdda6e4dd64c77c78bad2d718c89040e107eff0950498b1f618ada552
- 9327 bytes, 191 LF, zero CR, no BOM
- exactly five source theorems: two private helpers and three public results; zero new source definitions or instances.

I read every line of the 191-line source and all five complete proofs; the declaration-only file, all five frozen heads, frozen preamble, freeze and checkpoint; the full supplied original excerpt (g:main lines 1429–1540); and the four bound library interface/definition files. Old producer proof certification is reused rather than newly commissioned. The parent freeze predates the complete-source checkpoint in the bound records. Each candidate head and the preamble match their frozen files byte for byte, and reconstruction of DECLARATIONS-ONLY.lean.txt from those pieces is exact. Each of the checkpoint's five proof-body hashes was independently reproduced using the source block beginning with “by” and ending with one LF after trimming trailing LF blank lines.

## Source-to-statement scope

Let A=v, C_i=v_i-mu, Q_A=Σv_i², Q_C=Σ(v_i-mu)², d=n|mu|, and e=√n|mu|. FinitePath defines prefixSum by the actual first min(k,n) coordinates, energy by the actual sum of squares, upperMax over times 1,…,n, and lowerMax as upperMax of the negated path. Events defines the signed weak crossings using the same path's own final energy. TwoSided defines doubleCrossing as the intersection of the upper and lower crossings.

Thus doubleCrossing has two independent existential hitting times, one for each wall. It does not require a common time, does not replace the intersection by an absolute or one-sided event, and includes equality. The proof's use of separate maxima respects these semantics. Neither maximum silently inserts the empty prefix.

The generic public result assumes x≥0 and the exact sufficient inequality d+x e≤h√Q_C. It returns both implications D_C(x+h)→D_A(x) and D_A(x)→D_C(x-h), retaining Q_A and Q_C separately. The specialized result supplies this inequality from x/√n≤1/2, Q_C≥1/4, and h=3d. It does not assert these prerequisites from a distributional law.

In the supplied original source, E={Q_C≥v0/2} and v0≥1/2, so E implies Q_C≥1/4. Consequently the specialized theorem applies on original E and gives both inclusions in lines 1503–1504 after retaining E on the two sides. Its probability theorem uses the explicit bill B={Q_C<1/4}. This is a slightly stronger extracted bound: B⊆Eᶜ when v0≥1/2, so monotonicity can enlarge its bill to the original P(Eᶜ). The theorem does not itself introduce v0, prove v0≥1/2, or prove the source's exponential payment for Eᶜ.

The sqrt error e equals d/√n for n>0, since (√n)²=n. No energy quotient or division by Q_A/Q_C occurs. The original source's x-h≥1/2, x+h≤a and smallness conditions are needed by later comparison/payment steps, not by this extracted transport lemma. Their absence from the helper is legitimate: its reverse implication remains valid even for x-h<0.

The probability statement uses one arbitrary finite parent measure P on Path n. All centered events are pullback subsets of that same original path space, evaluated under that same P. No iid, centering, symmetry, density, atom-free law, probability normalization, conditional-law identity, or zero-energy exclusion is inserted. With [IsFiniteMeasure P], P.real is finite real outer-measure evaluation on every set; monotonicity and union subadditivity are sufficient and no disjointness or extra measurability premise is required.

## Complete proof review: private centered_prefix_abs_le (12–29)

The finite set I contains exactly the coordinates with i.val<k. For any natural k, including k=0 and k>n, I⊆univ gives card(I)≤n. The cast to reals preserves this inequality. The sum identity is S_C(k)=S_A(k)-card(I) mu, obtained by distributing subtraction and summing the constant; the use of card(I), rather than blindly k, handles saturation correctly. Therefore |S_C(k)-S_A(k)|=card(I)|mu|≤n|mu|.

Static Lean checks: Path n is definitionally Fin n→ℝ; the local I unfolds to the exact prefixSum filter at “change”. card_univ/Fintype.card_fin close the finite-cardinality upper bound. sum_sub_distrib, sum_const and nsmul_eq_mul match a real constant sum. Nat.cast_nonneg supplies the sign for abs_of_nonneg and abs mu is nonnegative for the final multiplication. All binders, including arbitrary k and potentially n=0, are present. No missing branch or mathematical gap was found.

## Complete proof review: private upper_max_difference_le (31–47)

For each monitored k, the upper side of |S_v(k)-S_w(k)|≤d and S_w(k)≤M_w imply S_v(k)≤M_w+d; upperMax_le_iff then gives M_v≤M_w+d. The lower side gives the reverse M_w≤M_v+d. Combining the two yields |M_v-M_w|≤d. No assumption d≥0 is needed separately, since it is already forced by the uniform absolute bound.

Static Lean checks: upperMax_le_iff has exactly the ∀k,1≤k→k≤n interface used by the proof, and le_upperMax takes the same hn,k,hk,hkn arguments. abs_le.mp produces the signs used at 38 and 44, and the final pair is in the correct order for abs_le.mpr. The positive-length binder supplies nonemptiness of the monitored set. Both directions are proved in full.

## Complete proof review: generic transport (49–109)

Lines 58–64 instantiate the prefix estimate and upper maximum estimate with C and A. Lines 65–72 apply prefixSum_neg to derive |S_(-C)-S_(-A)|≤d and obtain the independent lower maximum estimate. lowerMax is definitionally upperMax(-path), so the second application matches exactly and does not change the path or event.

Lines 73–85 obtain both true norm inequalities. The accepted producer gives √Q_C≤√Q_A+e. Applying that same producer to C and -mu, and proving C-(-mu)=A pointwise by ring, gives √Q_A≤√Q_C+e. The absolute value |-mu| is rewritten to |mu|. These are two genuine energies, rather than a variance or substitute denominator. Multiplication by x preserves both inequalities because hx is explicitly x≥0.

Write U_C,U_A for the upper maxima and L_C,L_A for the lower maxima. The four final nlinarith calls correspond to the following four verified inequality chains:

- From D_C(x+h), U_A≥U_C-d≥(x+h)√Q_C-d≥x(√Q_C+e)≥x√Q_A.
- The identical calculation with L_C,L_A gives the lower wall.
- From D_A(x), U_C≥U_A-d≥x√Q_A-d≥x√Q_C-xe-d≥(x-h)√Q_C.
- The identical calculation with L_C,L_A gives the lower wall.

The third comparison in each direction is precisely h√Q_C≥d+xe; the last energy comparison in the first direction uses the original-energy bound, while the reverse direction uses the centered-energy bound. The signs selected from abs_le at 89–92 are correct: forward uses U_C-U_A≤d and L_C-L_A≤d; reverse uses -d≤U_C-U_A and -d≤L_C-L_A. No multiplication by x-h or h with an unproved sign is used.

Static Lean checks: the let-bound C,d,e are reducible at the producer applications and hShift' assignment; hBack is a function equality with Fin n binder; rewriting hBack and abs_neg gives the required producer output. The changes at 95–106 unfold membership, doubleCrossing, the crossing definitions and the local C to exactly the conjunctions printed. Each nlinarith call is an algebraic combination of the listed polynomial inequalities; there is no omitted branch or external theorem call hidden in the arithmetic. All of lines 57–109 were checked, not only the four terminal tactic lines.

## Complete proof review: specialized sandwich (111–143)

Positive n gives √n>0, so div_le_iff₀ converts x/√n≤1/2 to x≤√n/2. From Q_C≥1/4, r=√Q_C≥0 and r²=Q_C, one obtains r≥1/2. Since √n|mu|≥0, multiplying the x bound gives xe≤n|mu|/2=d/2, with (√n)²=n used explicitly. Also 3d≥0 and r≥1/2 give 3dr≥3d/2. Adding d to the former inequality proves d+xe≤3dr, exactly the transport premise with h=3d.

Static Lean checks: hnReal is the exact cast of hn; sqrt_pos.mpr and div_le_iff₀ use the established strict positivity, not a division-by-zero convention. sq_sqrt receives the actual energy_nonneg proof or Nat.cast_nonneg as appropriate. The root lower bound uses both nonnegativity and the square identity. mul_le_mul_of_nonneg_right uses the nonnegative √n|mu| factor. The identity at 137 is a ring equality, and 138 uses the correct sq_sqrt. hRootWeighted is multiplication by the nonnegative 3d. The final nlinarith follows simply by combining xe≤d/2 and 3d/2≤3d√Q_C; no unused side condition is needed for this addition. The public theorem is exactly a specialization of the frozen generic theorem.

## Complete proof review: probability sandwich (145–189)

The proof defines bad=B, plus=D_C(x+3d) as a pullback, and minus=D_C(x-3d) as a pullback. For each v, it splits the exact dichotomy Q_C≥1/4 versus Q_C<1/4. In the first branch the specialized theorem supplies the correct direction; in the other branch lt_of_not_ge yields membership in bad. It thereby proves plus⊆D_A(x)∪bad and D_A(x)⊆minus∪bad.

Finite real outer-measure monotonicity followed by the ordinary union bound gives P.real plus≤P.real D_A+P.real bad and P.real D_A≤P.real minus+P.real bad. Subtracting the finite real bad bill yields the lower sandwich. This is subtraction in ℝ, not truncated ENNReal subtraction and not subtraction of two infinite quantities.

Static Lean checks: P is explicitly the same measure in every expression; [IsFiniteMeasure P] supplies the finiteness obligations used by measureReal_mono and measureReal_union_le. The target expected types infer P at the two measureReal_union_le applications. The local Set definitions reduce at membership and at the final change. The complements use ≥ versus strict < in the correct order, so the energy threshold equality 1/4 remains in the good branch. Similar existing curated-source calls use these exact API forms; those calls were only interface crosschecks, not a replacement for this proof review or a new proof certification. The final linarith is hp rearranged, while hm supplies the second conjunct verbatim.

## Boundary and adversarial checks

- Arbitrary prefix lengths: k=0 and k>n are covered by the card(I) argument; monitored maxima remain exactly 1,…,n.
- mu=0: C=A, d=e=0 and the specialized shifts vanish; no sign or division defect occurs.
- x=0 and x/√n=1/2: all inequalities are weak and the multiplication/division directions remain valid, including equality cases.
- Q_C=1/4: belongs to the good set and yields √Q_C=1/2 without loss.
- Q_C=0: belongs to the explicit bad event in the specialized/probability result. The generic result still correctly quantifies it; with n>0 its shift premise forces mu=0 if Q_C=0, and then both paths have zero energy.
- Q_A=0: original weak doubleCrossing membership is retained. No general false claim that Q_A=0 implies bad is made. If Q_C≥1/4, the signed inequality proof still works, potentially at a negative x-h. The original paper additionally pays Q_A=0 using its separate smallness premises at 1529–1530; those premises and that payment are not claimed by this helper.
- n=1: the two signed maxima and their independent witnesses still have their actual definitions; no nonexistent second time is required.
- Negative lower threshold: permitted by the frozen statement, and no proof step assumes x-h≥0.
- Degenerate finite measure, atoms and threshold mass: monotonicity/union subadditivity and the closed event definitions apply directly.
- Independence of upper and lower hitting times, true Q_A/Q_C, absence of iid/symmetry assumptions, and all low-energy mass are preserved.

## Prohibitions, qualification and next gate

The complete new source contains no sorry, admit, axiom, unsafe or native_decide token, and no new source definition or instance. This is a static source observation; it is not a transitive axiom audit. Whitelisted axioms remain propext, Classical.choice and Quot.sound, subject to the future exact-source server audit.

No critical mathematical or static Lean interface gap was found in any of the five complete proofs. I approve this exact source for a first source-bound native gate when C12 receives a heavy slot. This approval is sourceOnly=true and formalQualified=false. The actual compiled owner set, all full TYPEs, every non-theorem VALUE including generated/private declarations, and all-owned transitive axioms remain unknown. A later successful original-object native check, exact all-actual-owned TYPE/VALUE/AX receipt and independent final machine supplement are required before formal qualification. This review must be reused only while its exact source/inputs remain bound; affected source changes require affected review.

This finite recentering/probability helper is not a proof of the original retained conditional law, moment/budget bounds, Brownian threshold payment, exponential low-energy payment, original threshold discard or mixture identity. It does not close original C2, C12 or fullRootOD; these remain OPEN. Original immutable C1 completion and OQ3 PAUSED_BY_USER are unchanged. No novelty or full research theorem completion is claimed.

The reviewer held heavy=0 throughout, spawned no child, launched no remote operation and has no pending external action. The final RELEASE.json records relinquishment of this review writer after the sealed deliverables.

