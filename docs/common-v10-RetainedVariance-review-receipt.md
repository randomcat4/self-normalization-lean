# RetainedVariance frozen server receipt

Status: the three frozen public statements and their proofs pass the designated
server check and transitive axiom audit. Fresh independent source-to-statement
and proof review is still required from the coordinator's separate reviewer.

Frozen source: `drafts/c12/RetainedVariance.lean`, 271 lines.
Remote source:
`/root/rivermind-data/shao-lean-20261021/workspaces/lead-c12/Shao/Probability/RetainedVariance.lean`.
Local and remote SHA256:

```text
5361ad40f82d6c273135729df66c056d01a9cf090d1e9f80cffce44f61296fa6
```

The source has not changed since the final successful target check and audit.
The root froze all three public signatures at scope proposal SHA256
`d8ab157b03ccbc398997044edecc6510abde8f3659a8d5834309cc405fadae9b`.
A textual comparison of the three complete statement bodies against those
scope declarations, ignoring whitespace only, reports three matches. No extra
public theorem or new definition was added.

## Server evidence

Pinned Lean: 4.36.0-rc1,
`c9afcddf514a6772bd4d649f7cfc04eff0b9f15e`.
Pinned Mathlib: `807d3836b165983210ee2ecf3cd28f239436949c`.

Final targeted compilation:

```sh
source /root/rivermind-data/shao-lean-20261021/activate.sh
cd /root/rivermind-data/shao-lean-20261021/workspaces/lead-c12
taskset -c 0-3 lake env lean -o .lake/build/lib/lean/Shao/Probability/RetainedVariance.olean Shao/Probability/RetainedVariance.lean
```

Exit code 0, with no compiler stdout/stderr diagnostics. This produces the
module's own `.olean`. Old dependencies were not rebuilt.

A following separate `taskset -c 0-3 lake env lean --stdin` imported the
final module and Lean, printed transitive axioms for all three public results,
and scanned the imported environment for the three public-name prefixes and
`_private.Shao.Probability.RetainedVariance.`. For every matched declaration it
called `Lean.collectAxioms` and rejected any axiom outside the standard whitelist.

Final audit exit code 0, `AUDITED_DECLARATIONS 12`: three public theorems,
one private helper, and generated proof/simp declarations. Public theorems
and the private helper use `[propext, Classical.choice, Quot.sound]`; generated
declarations use subsets of that whitelist. No other axiom occurs. The audit
was supplied through standard input and did not modify a shared audit file.

Separate `#check @...` output confirms that the generic centered theorem takes
only a real probability law, `x>0`, actual positive conditioning mass, and
original square integrability. The last two statements take exactly the old
source hypotheses and expose the actual integrals under the existing
`retainedCutoffLaw`. The source token scan for `sorry`, `admit`, new `axiom`,
`unsafe`, and `native_decide` is clear.

## Proof review entry points

- Lines 18-42 prove `|integral z|^3 <= integral |z|^3` under a genuine
  probability law from actual first- and third-moment integrability. The
  proof integrates the polynomial inequality
  `(u-b)^2(u+2b)>=0`, with `u=|z|`, `b=|integral z|`, and combines it with
  the norm-of-integral inequality. Jensen is a derived fact, not an input.
  No division by the mean is used, so a zero mean is included.
- Lines 44-107 establish all three centered integrability assertions, the
  centered mean identity, the actual variance expansion, and the absolute
  cube comparison. Conditional-law probability and raw moments come from
  the existing genuine conditioning interfaces. The centered square is an
  actual integrable polynomial expansion. The centered cube is dominated by
  the integrable function `4(|z|^3+|mu|^3)`; only after proving this
  integrability does `integral_mono` compare the integrals. The derived
  Jensen step gives the final constant eight. This generic theorem does
  not assert that variance is positive.
- Lines 109-202 derive the source row's centered support, positive variance,
  interval `1/2<=M V<=2`, and `M centered_cube<=16/y^3`. Existing size and
  mass theorems give `n>=64`, `m>=1`, and actual positive cutoff mass.
  The stronger old raw-square estimate is retained, giving
  `M raw_second>=(31/32)(3/4)=93/128`; the proof does not subtract the
  mean-square loss from the relaxed lower bound `1/2`.
- In that same proof, `x>=2` implies `N|mu|<=2/x<=1`. With `N>=64`, this
  gives `|mu|<=1/64` and
  `N mu^2=(N|mu|)|mu|<=1/64`, hence also `M mu^2<=1/64`.
  This is a shorter route to the same planned numerical loss than passing
  through `4/(N x^2)`. The variance identity therefore gives the genuine
  separation `M V>=91/128>1/2`; its positivity is derived, not assumed.
  The upper bound subtracts a nonnegative mean square from the true raw
  second moment. The support conclusion uses the original cutoff `1/x`
  and the derived `|mu|<=1/x`.
- Lines 204-269 bound the exact actual parameter
  `centered_cube/(sqrt(M)*sqrt(V)^3)`. The proof derives `M>0`, `V>0`, and
  `y>0`, including strict positivity of every displayed denominator.
  With `s=sqrt(M V)`, it proves the exact denominator identity
  `s^3=M*(sqrt(M)*sqrt(V)^3)`. From `M V>=1/2`, it obtains `s^3>=1/4`.
  The actual retained centered-third bound then yields `64/y^3`.
  No external Berry--Esseen bound, variance assumption, or Lyapunov
  assumption enters this argument.

## Scope and unchanged dependencies

The source statement is tied to `supplement.tex` SHA256
`b99f2ac4d2f39dd39772d98a5702b7a923c2f10f8730a08fc1b4cd6bba4742bd`:
raw retained moments at lines 170-210, actual centered inputs in the generic
bounded-endpoint proof at lines 1240-1309, and the actual third-moment ratio
in the Berry--Esseen/completion passages. The constants `1/2`, `16`, and
`64` are proved retained-law helper constants; they are not claimed to be
literal source quotations or a proof of the bounded-endpoint tail theorem.

The original common premise is still the literal
`n * integral F(xz) <= 1`, with `x^6<=n`; it was not replaced by a narrower
truncation-budget branch. The conditional law and cutoff remain exactly the
previous definitions. No global third moment under the original law is
assumed. The proof reuses the original square and actual conditional cube
integrability, not Bochner's default value at a nonintegrable function.

Boundary cases include `j=0`, the allowed equality `j=x^2/2`, zero retained
mean, and atoms on the retained cutoff boundary. The first theorem allows
degenerate conditional laws. Only the full source size and moment premises
force positive variance. The source size premises themselves derive `n>=64`
and `m>=1`; no extra exclusion of `n=0` or hidden signed length is added.
Existing natural-subtraction handling is reused without a premature cast.

Accepted unchanged dependencies:

```text
RetainedMoments 512cf7a51125f18f94f42b4ef855e21290a28f7a3185865a3d375bde8100d6cb
RetainedSample  a507e549e2973dd04ce25f22e2c6973e0e6c491433a1d7fd2d88fbb082e86ca4
```

No previous source, retained-law definition, root import, version pin,
common audit script, cache, or other author's file was edited. All Lean
execution was on the designated server through the existing authenticated
broker; no uncertain-operation response occurred, and no Lean ran locally.
