# Unit201 static late omitted Gaussian bill

Status: COMPLETE_STATIC_CANDIDATE_PENDING_INDEPENDENT_REVIEW_AND_SERVER_GATES.

The owned snippet is `static-late-omitted-gaussian-proof.lean.txt`, SHA256
`8e2efa1b9964f51a3f9d4bfd14324f1e6ddf67ef689aa92c0709f9f2756df004`,
23627 bytes, 443 LF-terminated lines, UTF-8 without BOM. It contains exactly
one global declaration, the complete frozen private theorem
`arr_iid_late_omitted_gaussian_bill`. Its signature agrees exactly with the
frozen head after removal of the final newline before ` := by`.

This is a complete static Lean proof candidate, not a compiler result or an
independent acceptance. Native Lean, axiom audit, server operations, uploads,
Git/API publication, subdelegation and schedules: NOT_RUN / zero. C2/C12
remains OPEN. There is no new mathematical premise, oracle or global helper.

## Bound inputs and read coverage

* Exact frozen private head: `c5f46e277a6ca1fe622d9ec4b66a3dc67fae48d9066b0e96047040316fb8bc40`.
  Its before-body freeze receipt is
  `5f13cf9f28eca169337887bcd054cf829b2f5228d8ad2eeefb5248981a04d2d8`.
* Exact imports, namespace, three definitions and local instance context:
  `frozen-public.lean.txt`,
  `9aa1ce015f0a6128b404b428dce988d84f6f9e261fb002d85f9e907ba9c0f81c`.
  The complete frozen context and heads were read.
* Common same-module source:
  `static-common-proof.lean.txt`,
  `19860c4f0abdb59641e597f86e6a0365a019e3eb11571d266494fcd19ebcc97f`.
  Complete needed `arr_late_fixed_suffix_gaussian_bound` and
  `arr_omitted_mask_iff` heads and values were read. These are same-module
  private references, not accesses to foreign private names. Their current
  common source is native NOT_RUN and will be part of the combined gate.
* Accepted unit196 complete mathematical candidate, all 320 lines:
  `d51c4a8281888a287d1f9fbc98672d437b0ad80bdcb4da9270873e61235db4ec`.
  Its complete independent report was read:
  `8c6a6e936e90f90117f7b4362f3b645c4911452fc2a9a13be920650623e90035`.
  Parent acceptance `9b88e69e8cd0d77c49d53a4cd010204f43cfdaeec8397d46c6d341b1ae161e05`
  is inherited accepted provenance, not a new review by this author.
* Qualified numerical producer:
  `library/Shao/Probability/SourceLateOmittedSuffixBudget.lean`,
  `23178ba87c6edb340724b81559a398912f5d6791f93b1b02a2067e1343f0992d`.
  The complete public `iid_actual_late_omitted_suffix_budget` head, including
  the literal W and lateOmitted values and every let, lines 443-475, was read.
  Its existing proof and qualification are reused; no re-review or new
  check of that old proof is claimed. Its concrete split/reorder/state
  proof patterns were also inspected for local construction.
* `SourceIIDGaussianProfileBudget`: complete firstValue, fixed/rank Gaussian
  values, complete state-identification head/value, complete measurable
  bound head and complete `iid_rank_gaussian_weight_fubini` head/value were
  read. The source state supplies tail energy, sum and the actual first
  label. The generic Fubini template imposes no upper bound on x.
* `SourceMarkedSuffixAveraging`: complete suffixD and cubicMass values and
  complete `suffix_normalized_geometry` head/value were read. Its geometry
  supplies the cubic/energy and drift bounds used for genuine L1. The
  public energy-integrability interface was inspected; the candidate
  instead proves energy integrability directly by a finite sum of iid
  second moments.
* Unit200 template
  `static-bad-retained-allranks-proof.lean.txt`,
  `c8a2ae2374eda92b0e6fb968f356f5ee4229a08b80eca7b61d8a0b388827f630`:
  its split/Fubini, iid reorder and coefficient proof patterns were read
  and copied locally where applicable. No unit200 file was edited.

## Complete mathematical route of this assembly

1. Choose the universal constants CL from the frozen common fixed-suffix
   Gaussian bound and CW from the old qualified actual late omitted suffix
   producer before rho, n, x and the sign. The final constant is exactly
   C = 2 CL CW > 0.
2. Bounded rho supplies the genuine second and third absolute integrability
   premises. The existing absolute-third-moment inequality gives beta >= 1,
   hence h0 = 4 beta^2 > 0. The fixed K and x >= 16 imply H >= h0 > 0.
3. For each complete suffix u of length t define one weight W_t by the
   exact union mask h0 <= energy(u) and (energy(u) < H or t <= m). Its raw
   value is |firstValue u|^3 / sqrt(energy u) times
   (1 + |sum u|/sqrt(energy u))^5. This includes the crossing label before
   conditioning. The union is one mask and its overlap is counted once.
4. W_t is measurable. On its selected branch the energy T is strictly
   positive. The qualified deterministic geometry gives firstCube <=
   T sqrt(T) and suffixD <= 1 + sqrt(t). Thus
   0 <= W_t <= (1 + sqrt(t))^5 T. Energy is integrable under rho^t by
   summing the integrable coordinate squares. This proves genuine L1 of
   the selected future carrier independently of either numerical bound.
5. Split a full iid path by the canonical finite-coordinate equivalence
   into prefix length r and COMPLETE suffix length n-r. The split is
   measure preserving into the product of the two iid laws. Its suffix
   projection is also measure preserving. The masked Gaussian function
   on this product is measurable, nonnegative and bounded by
   (1 + sqrt(n-r))^3; genuine L1 is obtained before Fubini.
6. At every strict late rank floor(n/2) < r < n, r > 0 and n <= 2r.
   After fixing the complete suffix, the omission mask is constant under
   the prefix integral. In the selected branch apply
   arr_late_fixed_suffix_gaussian_bound with threshold h0, unchanged x,
   the same complete suffix, and the chosen singleton sign. Its value
   agrees exactly with W_t because h0 <= T forces T > 0. This yields
   E_prefix maskedGaussian <= (CL/r) W_t <= (2CL/n) W_t.
   Unselected suffixes and non-late ranks give zero. Ordinary product
   Fubini, with L1 already established, yields the corresponding full-path
   rank bound. Summing preserves precisely the strict late rank set.
7. The iid whole-path random-reorder law maps revealLaw(P) to P. Its full
   path is used jointly for every mask and every Gaussian term. Tail
   energy, tail sum and firstValue are identified with the original
   remainingEnergy, remainingSum and actual a(sigma r), respectively.
   arr_omitted_mask_iff identifies the original tau <= r < nu exactly with
   h0 <= T and (T < H or n-r <= m). There is no randomly stopped iid
   suffix, stopping premise or loss of the first label.
8. This gives an exact equality between the frozen Gaussian bill and the
   summed full-path Gaussian carrier after random reorder, supplying its
   measurability, genuine L1 and pointwise nonnegativity. Separately the
   old producer's literal lateW equals (1/n) times the sum of W_t at the
   same complete tails after that SAME random reorder. The identification
   uses the exact actual mask and actual label, and is an equality of
   entire selected carriers.
9. Transport both entire carriers by the iid reorder law. Finite summation
   of the rank bounds gives E bill <= 2CL E lateW. Consume both old
   producer bounds for that one literal lateW. Multiplication by the
   nonnegative 2CL and ring normalization gives exactly C beta sqrt(H)/n
   and C delta standardNormalTail(x), with the same C.

## Boundary and semantic checks

The threshold h0 is weak (T >= h0), the energy omission comparison is
strict (T < H), the time condition is weak (t <= m), and late rank is
strict. No m <= n hypothesis is added; natural subtraction in the exact
selection lemma permits every m. Zero-energy suffixes are inactive because
h0 > 0. All n > 0 are covered; the strict late sets for n = 1 and n = 2
are empty. Both parity cases use n <= 2r without introducing the middle
rank. Repeated values, zero first label, atoms and non-symmetric rho are
covered by the whole labeled iid transport and the common two-sign
theorem. No Brownian law Q occurs in this private Gaussian bill.

Static checks found: exact frozen head = true; global declarations = 1;
imports/options/new global instances = 0; forbidden proof constructs = 0;
CR bytes = 0; trailing LF = true. These are deterministic text/byte checks,
not native Lean checks or an axiom receipt. There is no known remaining
mathematical interface gap in this static assembly. Compilation has not
been attempted and must not be inferred from this statement.

## Runtime metadata and final handoff

The requested configuration remains fresh gpt-6.1-sol/xhigh. Actual backend,
model, effort and input/cached-input/output/reasoning-subset counts are not
independently observable here and are null in the corrected ACK. The early
ACK initially copied the prescribed configuration into its actual fields;
parent requested a metadata-only correction. Its original byte SHA256 is
`a86edeab35d81f497726e7309eb76347f16240aa3bf0cf31899ae244d1fc0636`.
The corrected ACK SHA256 is
`f14160eb70cf83fcbdeb4f15455e7b5eb02f9ada8a22739948ecef9e81db2731`.
The original requested fields and timestamp remain, and the corrected ACK
records the original hash and the correction reason. This changes no
mathematical head or proof claim.

Ownership was confined to the five authorized late-omitted author files.
No other owner or shared source was edited. The final release relinquishes
sourceWriter, executionWriter and inflight, all exactly zero. Parent owns
integration of the snippet after the common private helpers and before
the public omitted-retained consumer, the fresh complete independent formal
review, and later authorized exact-source kernel/transitive-axiom gates.
