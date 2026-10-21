# Lindley finite Duhamel identity: source and API proposal

Status: ALL SIGNATURES FROZEN / AUTHOR SERVER CHECK COMPLETE / FINAL BLIND
REVIEW PENDING. The coordinator first approved the three definitions and
the first two pure finite theorem signatures from proposal SHA256
`f2ae55fa3668716b8fc6457791ba0425acc16714a3e3a187ada79bcbe92f11e0`.
After the independent pre-implementation semantic review returned
`CORRECT` (`LindleyTelescoping-statement-review.md`), the coordinator froze
and authorized the remaining nine unchanged signatures. This is a finite
identity unit, not the Fourier comparison or the C1 root theorem.
New implementation file:
`Shao/Probability/LindleyTelescoping.lean`. Existing `Lindley`, `LindleyLaw`,
`FiniteIID`, path statistics and event definitions stay unchanged.

## Exact source and what is already available

The source is the current read-only `C:/game/shao/current/c12` snapshot.

```text
main.tex SHA256
beb00f718487e36de433175c97f1d500cb48e7a92ce5bd5ad5d62bb132122d06
supplement.tex SHA256
b99f2ac4d2f39dd39772d98a5702b7a923c2f10f8730a08fc1b4cd6bba4742bd
```

| Source location | Actual assertion used |
|---|---|
| `main.tex:552–565`, labels `h:eq:boundedstatistics`, `h:eq:lindley` | `S_0=Q_0=W_0=0`, `Q_i=sum A_j^2`, `W_i=max(W_(i-1)+A_i,0)`, `U_i=max(-W_(i-1)-A_i,0)`. |
| `main.tex:574–585`, label `h:eq:futurekernel` | For an independent iid copy, `f_l^psi(w,q)=E' psi(w+S'_l,q+Q'_l)` and `Delta_i=f_(n-i)(0,Q_i)-f_(n-i)(-U_i,Q_i)`. The test is measurable and takes values in `[0,1]`. |
| `main.tex:587–591`, label `h:eq:duhamel` | `E psi(W_n,Q_n)-E psi(S_n,Q_n)=sum_(i=1)^n E Delta_i`. |
| `supplement.tex:405–413` | The genuine future-kernel recursion plus independence gives the conditional expectation of the pre-reflection term. |
| `supplement.tex:414–441` | Pointwise reflection defect, with the **same** square coordinate `Q_i` before and after reflection. |
| `supplement.tex:442–455`, label `h:eq:reflection-step` | Take expectations, sum, and use `f_0=psi`, `W_0=Q_0=0` and the independent-copy law to obtain the displayed Duhamel identity. |
| `main.tex:595–608` | For `t>0`, the literal test is `1_{q>0, abs(w)<t sqrt(q)}`. It gives the strict CDF difference. The zero-energy restriction and strict threshold are both explicit. |

The genuine recursion and reversal have already been proved:

* `Shao.lindleyState`, `lindleyState_zero`, `lindleyState_succ`,
  `lindleyState_eq_maxWithZero_reverse_prefix`, `lindleyState_length`;
* `Shao.Probability.iid_lindley_energy_identDistrib_maxWithZero`, which is a
  joint-law statement of `(W_n,Q_n)`, not a pointwise equality with the
  original path's prefix maximum;
* `iid_samplePath_map_eq_pi` and `iid_samplePath_identDistrib`, which identify
  the genuine iid path law with its finite product law;
* measurable prefix sums, genuine energies and `maxWithZero` in
  `Shao.Probability.MeasurablePath`'s imported `Shao` namespace.

Read-only server hashes checked for the actual dependencies:

```text
Shao/Basic/Lindley.lean
81c0b9cea36513e456c4867dd0478a370eb4ef881c8aff9f0bab69009136eef7
Shao/Probability/LindleyLaw.lean
e661e493559b19537800ba432538aa053bd6ce742ddf2d0571bd152a4bcbea25
Shao/Probability/FiniteIID.lean
d1b565489199d55af70a27c31a0f803a2b7433e78c9197a361b3c10c0598845b
```

## First independently closable unit

The finite Duhamel identity itself has **no Gaussian or Fourier input**.
Neither positive variance nor a first, second or third moment is needed.
It is valid for every probability increment law, including an atom at zero,
a deterministic law, a noncentered law, and the empty sample.

The frozen complete unit is the three definitions and eleven theorem
signatures below. It closes the actual finite expectation identity and its
literal strict-CDF specialization, not just the scalar `max` identity.
The independent-copy future is realized by a finite product integral; it is
not introduced by assuming the semigroup law or the desired telescope.

Namespace: `Shao.Probability`; `open MeasureTheory ProbabilityTheory` and
`open scoped BigOperators`; `set_option autoImplicit false`.
In the signatures, `Shao.Path n = Fin n -> R`, and its existing prefix and
energy functions are used verbatim. The zero-based `i : Fin n` represents
the source's step `i.val+1`.

### Three definitions

```lean
noncomputable def lindleyFutureKernel (ν : Measure ℝ) (l : ℕ)
    (ψ : ℝ × ℝ → ℝ) (s : ℝ × ℝ) : ℝ :=
  ∫ b : Shao.Path l,
    ψ (s.1 + Shao.prefixSum b l, s.2 + Shao.energy b)
    ∂Measure.pi (fun _ : Fin l => ν)

def lindleyRegulator {n : ℕ} (a : Shao.Path n) (i : Fin n) : ℝ :=
  max (-(Shao.lindleyState a i.val (Nat.le_of_lt i.is_lt) + a i)) 0

noncomputable def lindleyDelta {n : ℕ} (ν : Measure ℝ)
    (ψ : ℝ × ℝ → ℝ) (a : Shao.Path n) (i : Fin n) : ℝ :=
  lindleyFutureKernel ν (n - (i.val + 1)) ψ
      (0, Shao.prefixSquares a (i.val + 1)) -
    lindleyFutureKernel ν (n - (i.val + 1)) ψ
      (-lindleyRegulator a i, Shao.prefixSquares a (i.val + 1))
```

The product integral is the source's independent-copy expectation for
**every** real starting pair `(w,q)`. We do not restrict it to `q>=0`:
later smoothed tests also need a kernel defined on all of `R^2`.

### Theorems 1–2: real finite reflection and a pathwise telescope

```lean
theorem lindley_reflection_defect (g : ℝ × ℝ → ℝ) (r q : ℝ) :
    g (max 0 r, q) - g (r, q) =
      g (0, q) - g (-(max (-r) 0), q)

theorem lindley_pathwise_telescoping {n : ℕ} (a : Shao.Path n)
    (ψ : ℝ × ℝ → ℝ) :
    ψ (Shao.lindleyState a n le_rfl, Shao.energy a) -
        ψ (Shao.prefixSum a n, Shao.energy a) =
      ∑ i : Fin n,
        (ψ (Shao.prefixSum a n - Shao.prefixSum a (i.val + 1),
            Shao.energy a) -
          ψ (Shao.prefixSum a n - Shao.prefixSum a (i.val + 1) -
              lindleyRegulator a i, Shao.energy a))
```

The second statement is a substantive finite bridge, not a recursive
definition of a defect. To prove it, telescope the genuine mixed positions

```text
T_k = W_k + S_n - S_k,  0 <= k <= n.
```

Then `T_0=S_n`, `T_n=W_n`. The successive difference is the reflection
defect at step `k+1` after the same actual suffix sum is added. Every term
keeps the actual full square sum `Q_n`. This uses the genuine recursion,
the prefix-sum successor identity and finite sum cancellation. No
measurability, moment, independence or symmetry hypothesis is needed here.

### Theorems 3–6: actual future expectation and its semigroup

```lean
theorem lindleyFutureKernel_zero (ν : Measure ℝ) (ψ : ℝ × ℝ → ℝ)
    (s : ℝ × ℝ) :
    lindleyFutureKernel ν 0 ψ s = ψ s

theorem measurable_lindleyFutureKernel (ν : Measure ℝ)
    [IsProbabilityMeasure ν] (l : ℕ) (ψ : ℝ × ℝ → ℝ)
    (hψ : Measurable ψ) :
    Measurable (lindleyFutureKernel ν l ψ)

theorem lindleyFutureKernel_bounds (ν : Measure ℝ)
    [IsProbabilityMeasure ν] (l : ℕ) (ψ : ℝ × ℝ → ℝ)
    (hψ : Measurable ψ) (hψ01 : ∀ s, 0 ≤ ψ s ∧ ψ s ≤ 1)
    (s : ℝ × ℝ) :
    0 ≤ lindleyFutureKernel ν l ψ s ∧
      lindleyFutureKernel ν l ψ s ≤ 1

theorem lindleyFutureKernel_succ (ν : Measure ℝ)
    [IsProbabilityMeasure ν] (l : ℕ) (ψ : ℝ × ℝ → ℝ)
    (hψ : Measurable ψ) (hψ01 : ∀ s, 0 ≤ ψ s ∧ ψ s ≤ 1)
    (s : ℝ × ℝ) :
    lindleyFutureKernel ν (l + 1) ψ s =
      ∫ z : ℝ, lindleyFutureKernel ν l ψ
        (s.1 + z, s.2 + z ^ 2) ∂ν
```

`lindleyFutureKernel_zero` needs no probability assumption: the empty
product has mass one even if the unused measure `ν` is arbitrary.
For the other kernel assertions the source's genuine probability law is
used. In particular all relevant integrands are integrable because their
absolute values are bounded by one under probability measures. The
implementation must establish this before applying Fubini; total Bochner
integral conventions cannot be used to cancel nonintegrable terms.

The successor equality is a theorem about the explicit finite-product
definition, not its defining equation. The finite product is split by a
measure-preserving coordinate equivalence and genuine square/sum
identities; Fubini then proves the equality.

### Theorems 7–11: transfer to the actual iid sample

Shared objects for the following declarations:

```lean
variable {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
variable {μ : Measure Ω} {ν : Measure ℝ}
variable [hμ : IsProbabilityMeasure μ] [hν : IsProbabilityMeasure ν]
variable {X : Fin n → Ω → ℝ}
include hμ hν
```

All independence and identical-law hypotheses below are precisely the
existing `FiniteIID` hypotheses. No explicit independent copy is an extra
input: the product law realizes its joint distribution.

```lean
theorem iid_lindley_initial_futureKernel
    (hX : ∀ i, Measurable (X i)) (hIndep : iIndepFun X μ)
    (hLaw : ∀ i, IdentDistrib (X i) (id : ℝ → ℝ) μ ν)
    (ψ : ℝ × ℝ → ℝ) (hψ : Measurable ψ)
    (hψ01 : ∀ s, 0 ≤ ψ s ∧ ψ s ≤ 1) :
    lindleyFutureKernel ν n ψ (0, 0) =
      ∫ ω, ψ (Shao.prefixSum (samplePath X ω) n,
        Shao.energy (samplePath X ω)) ∂μ

theorem integrable_lindley_test_and_delta
    (hX : ∀ i, Measurable (X i))
    (ψ : ℝ × ℝ → ℝ) (hψ : Measurable ψ)
    (hψ01 : ∀ s, 0 ≤ ψ s ∧ ψ s ≤ 1) :
    Integrable (fun ω => ψ
        (Shao.lindleyState (samplePath X ω) n le_rfl,
          Shao.energy (samplePath X ω))) μ ∧
      Integrable (fun ω => ψ
        (Shao.prefixSum (samplePath X ω) n,
          Shao.energy (samplePath X ω))) μ ∧
      ∀ i : Fin n,
        Integrable (fun ω => lindleyDelta ν ψ (samplePath X ω) i) μ

theorem iid_lindley_future_step
    (hX : ∀ i, Measurable (X i)) (hIndep : iIndepFun X μ)
    (hLaw : ∀ i, IdentDistrib (X i) (id : ℝ → ℝ) μ ν)
    (ψ : ℝ × ℝ → ℝ) (hψ : Measurable ψ)
    (hψ01 : ∀ s, 0 ≤ ψ s ∧ ψ s ≤ 1) (i : Fin n) :
    (∫ ω, lindleyFutureKernel ν (n - (i.val + 1)) ψ
        (Shao.lindleyState (samplePath X ω) i.val
            (Nat.le_of_lt i.is_lt) + X i ω,
          Shao.prefixSquares (samplePath X ω) (i.val + 1)) ∂μ) =
      ∫ ω, lindleyFutureKernel ν (n - i.val) ψ
        (Shao.lindleyState (samplePath X ω) i.val
            (Nat.le_of_lt i.is_lt),
          Shao.prefixSquares (samplePath X ω) i.val) ∂μ

theorem iid_lindley_telescoping
    (hX : ∀ i, Measurable (X i)) (hIndep : iIndepFun X μ)
    (hLaw : ∀ i, IdentDistrib (X i) (id : ℝ → ℝ) μ ν)
    (ψ : ℝ × ℝ → ℝ) (hψ : Measurable ψ)
    (hψ01 : ∀ s, 0 ≤ ψ s ∧ ψ s ≤ 1) :
    (∫ ω, ψ (Shao.lindleyState (samplePath X ω) n le_rfl,
        Shao.energy (samplePath X ω)) ∂μ) -
        (∫ ω, ψ (Shao.prefixSum (samplePath X ω) n,
          Shao.energy (samplePath X ω)) ∂μ) =
      ∑ i : Fin n, ∫ ω, lindleyDelta ν ψ (samplePath X ω) i ∂μ

theorem iid_maxWithZero_strictCDF_difference
    (hX : ∀ i, Measurable (X i)) (hIndep : iIndepFun X μ)
    (hLaw : ∀ i, IdentDistrib (X i) (id : ℝ → ℝ) μ ν)
    (t : ℝ) (ht : 0 < t) :
    let ψt : ℝ × ℝ → ℝ := fun s =>
      if 0 < s.2 ∧ |s.1| < t * Real.sqrt s.2 then 1 else 0
    (μ {ω | 0 < Shao.energy (samplePath X ω) ∧
        Shao.maxWithZero (samplePath X ω) <
          t * Real.sqrt (Shao.energy (samplePath X ω))}).toReal -
      (μ {ω | 0 < Shao.energy (samplePath X ω) ∧
        |Shao.prefixSum (samplePath X ω) n| <
          t * Real.sqrt (Shao.energy (samplePath X ω))}).toReal =
        ∑ i : Fin n, ∫ ω, lindleyDelta ν ψt (samplePath X ω) i ∂μ
```

The integrability theorem deliberately needs neither independence nor
identical distribution; measurability of the sample and boundedness of
the test suffice. It uses `[IsProbabilityMeasure ν]` to bound its future
kernel and `[IsProbabilityMeasure μ]` to integrate the resulting bounded
random variables. `lindleyDelta` lies in `[-1,1]`.

The one-step theorem is the **unconditional** expectation equality obtained
from the displayed conditional equality at `supplement.tex:409–413`.
This proposal does not claim to have encoded a filtration or conditional
expectation theorem. That extra interface is unnecessary for the finite
Duhamel equality. A direct finite-product/Fubini proof retains exactly the
source's increment law and all its hypotheses.

For the final telescope one can either sum the proved one-step equalities,
or integrate the pathwise theorem and split the actual iid product into
its first `i.val+1` coordinates and its remaining `n-(i.val+1)`
coordinates. The latter split must prove that the suffix sum and square
sum, jointly, have exactly the product-law future used in
`lindleyFutureKernel`. The regulator is a measurable function only of the
first block. The identity `Q_n=Q_(i.val+1)+Q_suffix` is part of this proof;
replacing `Q_n` by a variance or treating the square coordinate as
independent of the sum coordinate is not allowed. Both routes derive the
future-law averaging rather than postulate it.

The final CDF theorem uses the existing joint reversal law and the
nonnegativity of the true reflected state, then applies the generic
telescope to the **literal** source indicator. It includes all atoms at
`Q_n=0` and at `abs(S_n)=t sqrt(Q_n)` correctly by excluding them from the
strict event. There is no replacement by a closed-survival event, by a
complement of weak crossing, or by a normalized statistic's special
zero-energy branch. No assumption `Q_n>0` almost surely is introduced.

## Dependencies, feasibility, and the precise remaining boundary

The needed finite measure infrastructure is already present on the server:

* `Mathlib.MeasureTheory.Constructions.Pi` provides
  `measurePreserving_piFinSuccAbove` and the finite product splitting
  equivalences;
* `Mathlib.MeasureTheory.Integral.Prod` provides genuine Fubini
  (`integral_prod`, `integral_prod_symm`) and parameter-integral
  measurability (`StronglyMeasurable.integral_prod_right'`);
* `Mathlib.MeasureTheory.Integral.Pi` is also cached. Its product-of-functions
  theorem is **not** a substitute for the general bounded test/Fubini
  argument needed here;
* the existing iid path-map equality transfers canonical product identities
  to arbitrary measurable probability spaces.

Read-only reconnaissance confirmed the `Integral/Prod.olean` and
`Integral/Pi.olean` artifacts exist. The initial scope reconnaissance was
not a compiler receipt. The later first finite batch receipt is below;
it covers no kernel theorem or iid expectation assertion.

Private helpers may establish continuity/measurability of bounded-time
`lindleyState`, prefix successor/splitting identities, finite-product
coordinate changes and the bounded integrability facts. They must prove
those facts from the frozen definitions, not take the desired expectation
identity as an assumption. No existing source/import/cache/lock is edited.

The next genuinely analytic assertion is **outside** this unit:
`main.tex:629–647`, `h:prop:smoothed`, needs construction of the actual
law-adapted independent noise and a quantitative bound on the sum of
reflection defects for that test. The construction starts at
`main.tex:650–689`; the cone-restricted spectral/Fourier bounds begin at
`main.tex:691–721`. Nothing in the finite telescope proves these bounds,
supplies Gaussian comparison, or assumes the target estimate as a kernel
hypothesis. Those later analytic inputs remain OPEN. The present finite
identity itself is not blocked on them.

## One minimum next action at the proposal stage

Coordinator review/freeze of the three definitions and eleven signatures
above. After that freeze, create only the new module and first prove the
actual pathwise finite telescope and product-integral successor identity;
these are the two checkable bridges on which the final iid telescope
depends. All compilation, axiom audit and recomputation must run on the
designated server. A fresh independent reviewer must still check the
source-to-statement mapping and the final proof before acceptance.

## Authorized first finite batch receipt

Implemented only the three unchanged definitions and the first two public
theorems in `drafts/c12/LindleyTelescoping.lean`, with the matching remote
file `workspaces/lead-c12/Shao/Probability/LindleyTelescoping.lean`.
Private helpers prove the actual prefix successor identity and finite sum
cancellation. The pathwise theorem evaluates the genuine recursion only
at times in `Fin (n+1)`, hence never extends it beyond the sample.

Server command, after activation and selecting `workspaces/lead-c12`:

```text
taskset -c 0-3 lake env lean \
  -o .lake/build/lib/lean/Shao/Probability/LindleyTelescoping.olean \
  Shao/Probability/LindleyTelescoping.lean
```

Final result: exit code 0, empty stdout and stderr. A subsequent server
`lake env lean --stdin` audit imported the resulting module and printed
the axioms of all five public declarations, plus the actual pathwise
theorem type. All five had exactly the standard whitelist
`[propext, Classical.choice, Quot.sound]`; the private proof helpers are
covered transitively. The source scan found no prohibited proof escape.

Local/remote matching Lean source SHA256:

```text
6df61c8a867c65d4bfe41656821a8f8f1659f68e5023a6d1d0091b129083c222
```

At the time of that first receipt the other nine signatures had not been
implemented. The future kernel remained the literal product-law integral,
not a recursive definition. The complete-unit receipt below supersedes
that implementation status.

## Complete frozen unit: author implementation receipt

All three definitions and all eleven public theorem signatures above have
now been implemented in the same new file, without changing any frozen
signature or old definition. The pure first-batch proofs are preserved.
The final module also proves the actual kernel semigroup, actual iid
single-step expectation equality, finite Duhamel identity and the literal
strict-CDF specialization.

Proof obligations worth exposing to the final independent reviewer:

* `measurable_lindleyFutureKernel` uses the general strongly measurable
  parameter Bochner-integral API. Its only test hypothesis is
  `Measurable ψ`; neither its type nor its proof assumes a unit bound.
* The semigroup splits the real finite-product future with
  `measurePreserving_piFinSuccAbove` at coordinate zero. Fubini is applied
  only after the corresponding product integrand is proved integrable by
  the actual unit bound.
* The iid step transfers the genuine sample law to its canonical product,
  splits at the current coordinate, and proves that the true previous
  Lindley state and partial square sum are unchanged as that coordinate
  varies. Integrating the current coordinate then uses the already proved
  product-law semigroup. No conditional expectation or semigroup equality
  is an input hypothesis.
* The expectation telescope separately proves both integrands integrable
  before using `integral_sub`, then telescopes on `Fin (n+1)`. Its initial
  term is identified with the actual endpoint expectation by iid path-law
  transfer.
* The CDF corollary applies the literal indicator
  `1_{q>0, abs(w)<t sqrt(q)}`. The maximum is reached through the existing
  **joint** reversal law, and its nonnegativity removes the absolute value.
  No moment, centering, positive variance or positive-energy-a.s. premise
  has been added.

Final targeted server command is the same command displayed in the first
receipt. Result: exit code 0, empty stderr. The only stdout diagnostics are
two unused-variable warnings for the retained frozen hypotheses:
`hψ01` in the initial law-transfer identity and `ht` in the strict-CDF
corollary. Those two statements happen to hold under weaker hypotheses,
but their frozen signatures are deliberately unchanged. No linter is
disabled.

The subsequent server import/audit had exit code 0 and empty stderr. It
printed transitive axioms for **all fourteen public declarations**
(three definitions, eleven theorems): every declaration had exactly
`[propext, Classical.choice, Quot.sound]`. It also printed the actual final
types of kernel measurability, iid step, Duhamel and strict-CDF theorems,
confirming the frozen inputs and boundaries. Private helpers are covered
transitively. The prohibited-escape scan had no matches.

Final local and remote Lean source SHA256, frozen for final blind review:

```text
518b7029d435ddd3b32a414f8893d6c49e26910cff18117d8da0cc6eb67bc93c
```

All compilation and recomputation occurred on the server. Only the new
owned Lean file and this corresponding draft were edited; no old source,
root import or shared cache/lock was changed. This author reports the
check receipt, not an independent acceptance verdict. Quantitative
smoothed/Fourier comparison remains outside this finite unit and OPEN.
