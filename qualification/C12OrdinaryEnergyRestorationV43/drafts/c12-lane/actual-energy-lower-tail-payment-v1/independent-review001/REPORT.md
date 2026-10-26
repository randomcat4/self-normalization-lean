# Unit 226 — independent complete source/proof review 001

STATUS: CORRECT

QUALIFICATION: SOURCE_ONLY; formalQualified=false. This is a complete independent reading of the two new theorem statements and their entire source proofs. It is not a Lean elaboration, kernel, compiled-owner, full-TYPE, full-VALUE, object, or transitive-axiom certificate.

## Identity, authority and exact input

The assigned reviewer role is `/root/energy_lower_tail_payment_formal_review001`, separate from the C12 author/parent owner `01a174b9-5b2e-7611-ba13-02580d678eb3`. The configured model/effort in the parent activation is `gpt-6.1-sol`/`xhigh`; the actual runtime model, effort and all token categories are not observable here and are recorded as null. This reviewer wrote only inside `independent-review001`. No proof-source write, Lean invocation, axiom command, server access, network request, upload, Git/API publication or child delegation occurred.

The parent activation is exactly 4050 bytes, SHA256 `aba5952428bce369d563428992bcbcf85a6e67ec86fe91bac60c3a653a170730`. All eleven listed input payloads matched both their byte lengths and SHA256 values before the actual ACK was written. The new source is exactly 5053 UTF-8 bytes, SHA256 `9b7842c343fb5bb9a7c471c2ff4a53088e93e1d01bb80e8fb3282c7f4e724bca`, with 104 LF and zero CR bytes. The complete source, including lines 1–104, was read. It has two public theorems and no new private declarations, definitions or instances. A lexical forbidden-token scan found no `sorry`, `admit`, `axiom`, `unsafe` or `native_decide`; this scan does not replace the required eventual recursive axiom audit.

The preamble at lines 1–11 and the full public heads at lines 12–16 and 76–87 exactly match the separately frozen payloads after attaching the implementation delimiter ` := by`. The freeze records stage `EXACT_TWO_PUBLIC_HEADS_PREAMBLE_FREEZE_BEFORE_IMPLEMENTATION`, timestamp 2026-10-26T01:48:14.061690+00:00; the completed-source checkpoint is later, at 01:49:46.878582+00:00. This verifies the provided freeze/checkpoint record and exact payload relationship; it does not claim an independent historical filesystem observation before implementation.

The full proof-body hashes also reproduce the author checkpoint. The convention is the literal `by` followed by LF, the complete proof body, and one final LF, excluding the blank separator before the next declaration/end. Public1 has 2972 bytes and SHA256 `022ac4b33abe4c9ef091e325e60b63c61510ef2d7f76fcabedae4e23145a84c5`; public2 has 841 bytes and SHA256 `8c6c26a8c2a0787990a87aeef03c6f1e3ff89188ca5f8f9e24bf533e1ebd3864`.

## Public1: own cubic budget pays the exponential

Lines 12–16 quantify real delta and x, with delta>0, x≥0, and the law's own cubic budget delta(1+x)^3≤1/16. The conclusion is the exact exponential exp(-1/(64 delta^2))≤32 delta(1+x)^3 Psi(x). There is no probability premise, substituted budget, hidden bound on a different law, or unmentioned mean/density/symmetry condition.

Lines 17–22 set A=1/(128 delta^2)>0. For x≥0, expansion gives (1+x)^3−1=x^3+3x^2+3x≥0 and (1+x)^3−(1+x)=x^3+3x^2+2x≥0. The explicit hypotheses given to both `nlinarith only` calls contain x≥0, x^2≥0 and x^3≥0, so they justify the exact two polynomial inequalities used. No monotonicity premise is omitted.

Lines 23–29 multiply those inequalities by the nonnegative delta. Thus delta≤delta(1+x)^3≤1/16 and delta(1+x)≤1/16. Also delta(1+x)≥0, because delta>0 and 1+x≥1. Squaring the latter upper bound therefore preserves order and yields [delta(1+x)]^2≤1/256. The base-positivity argument to `pow_le_pow_left₀` is supplied at the use point. This covers equality in the small-budget premise.

Lines 30–40 use x+x^2/2≤(1+x)^2: the difference is 1+x+x^2/2≥0. Multiplication by 128 delta^2 preserves order. The preceding square bound then yields

`128 delta^2 (x+x^2/2) ≤ 128 delta^2 (1+x)^2 ≤ 1/2 ≤ 1`.

The actual source requests the weaker last bound ≤1, which follows by the same polynomial calculation. The denominator 128 delta^2 is strictly positive. Accordingly `le_div_iff₀ ... .mpr hProduct` has the correct direction and proves x+x^2/2≤1/(128 delta^2)=A. No division by zero or reversal of an inequality is hidden here.

Lines 41–43 call precisely the reused public API `auxiliary_exponential_le_gaussian_tail x A hx hTailExponent`, whose full head requires x≥0 and x+x^2/2≤A and concludes exp(-A)≤(8/3)Psi(x). Both actual arguments and their order match. This is the unconditional analytic API at AuxiliaryLowEnergyGaussian lines 10–12, rather than that module's later theorem with centering/tilting/rank hypotheses. The old producer proof is reused and was not re-reviewed or re-executed.

Lines 44–54 establish a second independent payment for the same half-exponential. The known inequality 1+A≤exp(A) implies A≤exp(A). Since A>0, taking reciprocals reverses the order: 1/exp(A)≤1/A. `Real.exp_neg` gives exp(-A)=1/exp(A), and the inverse-of-inverse identity gives 1/A=128 delta^2; delta≠0 is supplied to the rational normalization. Finally delta≤1/16, multiplied by delta≥0, gives delta^2≤delta/16 and hence 128 delta^2≤8 delta. The direction and all signs in `one_div_le_one_div_of_le hApos hExpLower` are correct.

Lines 55–60 prove the exact split. With A=1/(128 delta^2), -A+(-A)=-1/(64 delta^2). `Real.exp_add` is used in the orientation converting the product into the exponential of the sum, and the remaining equality follows by rational algebra with delta≠0. There is no 64/128 mismatch.

Lines 61–74 obtain Psi(x)≥0 from the correctly projected existing theorem `standardNormalTail_basic.2.2.1 x`. They multiply the two bounds on exp(-A). In the `mul_le_mul` application the nonnegative third argument is exp(-A)≥0 and the fourth is 8 delta≥0, exactly the factors required by the ordered-ring rule. The product upper bound is (8 delta)((8/3)Psi(x))=(64/3)delta Psi(x). Since 64/3≤32 and delta Psi(x)≥0, this is at most 32 delta Psi(x). Since (1+x)^3≥1, another multiplication by the nonnegative 32 and Psi(x) yields the frozen target. The final associativity simplification matches every factor; it does not drop a term.

At x=0 all premises and steps still apply. Delta=0 is excluded explicitly in this theorem, rather than being assigned a value through totalized division. Negative x is outside the frozen domain and is never used. The proof provides the exact stated uniform constants 32 and 1/16.

## Public2: payment for actual iid energy

Lines 76–87 quantify a probability measure nu on the reals, n>0, integrability of z^2 and |z|^3, and the raw second-moment normalization n integral(z^2)=1. They define delta locally as n integral(|z|^3) and assume only delta(1+x)^3≤1/16 with x≥0. The target includes positivity of this very delta and the probability of the real product-measure event `{v : Shao.Path n | Shao.energy v ≤ 1/2}`. It does not replace energy by an expectation, variance, centered sum or auxiliary tilted energy.

The necessary old interface was fully read at QuadraticEnergyLowerTail lines 164–175. It takes exactly nu, n, hn, h2, h3, hnorm, kappa, 0<kappa and kappa≤1, and returns positive beta=n integral(|z|^3) together with the actual product probability bound at threshold 1−kappa and exponent -kappa^3/(8 beta^2). Its entire old proof and accepted checks are reused. The supplemental definitions were read directly at FinitePath lines 18 and 30–31: `Path n = Fin n → ℝ` and `energy v = sum_i (v i)^2`. The Gaussian tail definition and the complete `standardNormalTail_basic` head were also read. Supplemental definition bytes are sealed separately, without changing the eleven mandatory activation inputs.

Lines 88–94 introduce the frozen let-bound delta and the implication premise, instantiate the Root producer at kappa=1/2, and preserve the exact original law nu and the actual iid product. The supplied numerical proofs establish both kappa side conditions. The producer's let-bound beta is definitionally the local delta, and its let-bound product measure is definitionally the one in the target; the `change` commands only expose those identities. They add no mathematical condition. Strict delta positivity is obtained from the qualified producer under the same normalization, not assumed as a new premise.

Lines 95–100 calculate (1/2)^3/(8 delta^2)=(1/8)/(8 delta^2)=1/(64 delta^2), using the newly available delta≠0. Also 1−1/2=1/2. Thus the source's `simpa only` rewrite preserves both the real probability and the weak event at the correct threshold. Lines 101–102 chain this exact lower-tail upper bound with public1, using this delta, this x, hdelta, hx and the same hsmall. The conjunction returns positivity and the desired Gaussian-weighted cost.

No mean-zero, symmetry, density, atomlessness, extra independent-copy, or abstract unpaid-probability premise occurs in either frozen head or proof. Independence and identical distribution are encoded by the actual product `Measure.pi (fun _ : Fin n => nu)`. Equality atoms at energy=1/2 and zero-energy samples are included in the weak event and are paid for by the reused weak-event theorem. Normalization n integral(z^2)=1 excludes a law with identically zero raw energy; it is not a variance normalization and does not assert centering. The n=0 case is excluded explicitly. In cases where the smallness premise is impossible, the implication retains its ordinary exact quantifiers.

## Original-source fidelity and remaining scope

The complete supplied original excerpt, main.tex lines 1487–1496, was read against its recorded original SHA256 `beb00f718487e36de433175c97f1d500cb48e7a92ce5bd5ad5d62bb132122d06`. It describes the actual B with n E B^2=1 and delta=n E|B|^3, kappa=1/2, and the bound exp(-1/(64 delta^2))≤C delta a^3 Psi(x). Public1 supplies this analytic payment with explicit C=32 and smallness delta(1+x)^3≤1/16. Public2 supplies the corresponding actual-B iid energy subestimate. The first theorem is scalar analytic and the second binds its actual probability premise internally through the existing Root producer.

The excerpt also refers to the centered event E={Q_C≥v0/2}, its complement, a=1+x in the surrounding construction, the actual B/C law/scale identification, and the final conversion u′≤C0 Lambda to C Lambda Psi(x). Those distributional transports and the Lambda comparison are not statements of this module and are not certified here. This unit faithfully supplies the identified payment substep; it does not by itself prove the full displayed E-complement estimate or any original C2/root theorem. Original C1 immutablev85 remains outside this review; C2/C12/fullRootOD remain OPEN and OQ3 remains PAUSED_BY_USER.

## Verdict and next evidence gate

No critical mathematical or source-level proof gap was found in either entire new proof. Every new public binder, premise, target, local sign condition, exponent/denominator, constant, imported public API call and final argument was reviewed. The verdict is CORRECT for this exact source-only scope, with formalQualified=false.

Actual compiled ownership, full TYPE/VALUE output, original object identity, kernel status and recursive all-owned transitive axioms remain unknown/null. No claim of Lean acceptance is made from source inspection. Any later machine check must use the authorized server phase and exact source bytes; a source change invalidates only the affected review. This reviewer now releases its review-directory write authority and all execution/child authority with zero in-flight or queued work. The parent can continue the separate centered-product/probability-scale transport dependency.
