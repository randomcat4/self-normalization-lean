# ClockControl author execution receipt

Status: IMPLEMENTED, TARGET CHECKED, COMPLETE MODULE/DEPENDENCY AXIOM GATE
PASSED; PENDING FRESH INDEPENDENT PROOF REVIEW. This is execution evidence,
not an independent verdict by the author.

## Frozen scope and actual source

- Frozen proposal: `drafts/c12/ClockControl-next-scope.md`, SHA256
  `0f39fda02d4b854b4969601b62bf8a5cd8a75a3c17d18fcc8bf4ba6813146afb`.
  Its original bytes are unchanged. Independent statement review:
  `ClockControl-declaration-review.md`, CORRECT.
- Local new source: `drafts/c12/ClockControl.lean`.
- Server new source:
  `/root/rivermind-data/shao-lean-20261021/workspaces/lead-c12/Shao/Probability/ClockControl.lean`.
- Frozen source SHA256, actually equal locally and on the server:
  `c7782d17c1b6dec827cde84d1d44f9b6cb7a7d8dd166bee2183cac4d2dd5cdba`.
- 468 lines, UTF-8 without BOM, LF, zero new definitions, exactly the three
  frozen public theorem names in namespace `Shao.Probability`:

```text
iid_bounded_clock_exp_integral
iid_bounded_clock_deviation_le
iid_bounded_clock_bad_probability_le
```

The author changed only this new source and receipt. No frozen source,
scope, old definitions, root import, audit tool, pin or cache was edited.

## Actual proof coverage

The eight private proof lemmas establish:

1. Genuine finite moments from a.e. bounded support under a probability law.
2. Actual raw second moment between zero and h².
3. Actual centered square `B=a²-m2` bounded by h² a.e.
4. Genuine B² integrability, EB=0 and EB²<=m4 using integrable polynomial
   expansion and the probability-one integral of constants.
5. Genuine one-coordinate exponential integrability and its Taylor/MGF
   bound for signed theta in the frozen unit range.
6. Exact reindexing of the existing filtered raw prefixSquares by Fin k
   using an explicit finite bijection when k<=n, including k=0.
7. Actual m4<=h m3, with cube and fourth moments truly integrable under
   this bounded law.
8. The scalar actual Gaussian comparison
   exp(-(1+y)²)<=sqrt(2*pi) standardNormalTail(y), using the accepted true
   density definition and Mills lower bound.

The first public proof transports a.e. support with real `IdentDistrib`,
uses the fixed-prefix independent subfamily and the actual independent
product-integral identity, and separately proves the entire exponential
truly integrable by finite a.e. domination. It works for signed/zero
theta, k=0 and n=0. It does not treat an unproved exponential moment or
finite-sum expectation as input.

The second proof uses both actual integrable exponential branches to
derive integrability of cosh minus one and its exact excess bound. The
genuine positive cosh-excess denominator follows from theta*delta>0;
real Markov applies only to the resulting nonnegative integrable variable.
The weak absolute-deviation event is kept exactly. No union-bound factor
two replaces the actual cosh argument, and the numerator minus one is
retained.

The final proof derives n>=7 from raw normalization and the actual support
scale, and uses natural-number division for n/2. The inequality
`n<=3*(n/2)` is established in Nat before the real cast. The raw half-clock
strict event and final closed-interval complement are included in their
weak deviations without any atomlessness hypothesis. Its small-excess
bound retains actual n*m4; the derived m4<=h*m3 and support scale then
pay the frozen raw cube budget. The scalar Gaussian bridge gives precisely
the coefficient 2048 sqrt(2*pi).

No original global absolute cube/fourth moment, mean-zero condition,
positive increment variance, Berry--Esseen estimate, MGF/concentration
conclusion or clock probability goal was added as an assumption. The law
in these theorems is the actual displayed bounded marginal law; no original
or later tilted law is substituted for it.

## Actual server target result

All Lean execution was on the designated server, with the existing fixed
Lean 4.36.0-rc1 / Mathlib 807d3836b165983210ee2ecf3cd28f239436949c setup.
No local Lean or cache command was used.

The final exact source command was

```sh
source /root/rivermind-data/shao-lean-20261021/activate.sh &&
cd /root/rivermind-data/shao-lean-20261021/workspaces/lead-c12 &&
taskset -c 0-3 lake env lean \
  -o .lake/build/lib/lean/Shao/Probability/ClockControl.olean \
  Shao/Probability/ClockControl.lean
```

Actual remote result: `exit_code=0`, empty stdout and stderr, no warnings.
The produced `.olean` was used by a separate fresh import audit.

The coordinator centrally prepared DerivHyp and its reported three-file
cache closure after correcting the cache invocation; the author did not
download, rebuild or write that cache. Early pre-start broker failures were
handled using the explicitly authorized `server_direct.py` fallback.
No command reported as already started was blindly replayed. The final
upload, target check, fresh audit and closure/hash scan succeeded through
the configured shared `server.py` broker.

## Full new-declaration and real-dependency axiom audit

A separate `lake env lean --stdin` imported `Shao.Probability.ClockControl`
and `Lean`. It enumerated constant ownership using
`env.getModuleIdxFor? name` and `env.header.moduleNames[idx.toNat]!`, not
merely a declaration-name prefix. For every owned declaration it ran
`Lean.collectAxioms` and rejected anything outside
`propext`, `Classical.choice`, `Quot.sound`.

It audited every declaration of the new module and of its entire actual
project import closure, then rejected any unexpected Shao module in the
imported environment. Actual remote result: `exit_code=0`, empty stderr:

```text
MODULE Shao.Probability.ClockControl AUDITED 26
MODULE Shao.Probability.GaussianTail AUDITED 29
MODULE Shao.Probability.FiniteIID AUDITED 8
MODULE Shao.Basic.FinitePath AUDITED 67
ALL_PROJECT_DECLARATIONS_AUDITED 130
```

The new 26 comprise 3 public theorems, 8 private theorems and 15 generated
declarations. The ownership audit explicitly included the new
`Shao.Probability.samplePath.eq_1`, which is generated in this module but
would not be found by a ClockControl-name prefix. All generated proof,
equation and simplification declarations passed, as did all 104 actual
project dependency declarations. `collectAxioms` recursively covers their
used Mathlib proof dependencies as well.

The same successful fresh import printed `#check @...` for all three
public theorems and `#print axioms` for each. The signatures match the
frozen scope, including all real/Nat parameters, raw moments, n/2, strict
lower event, closed final interval and exact normal-tail coefficient.
Each public theorem's transitive axiom list is precisely the standard
three above.

## Final source closure and forbidden-token scan

A separate actual server command recursively read all project imports,
scanned every source for forbidden tokens, and rechecked the hashes:

| Actual module | SHA256 |
|---|---|
| `Shao.Basic.FinitePath` | `898262898f9c088e2d10e6238e411b4397387b21b1b71a2b545c5edef936e1bb` |
| `Shao.Probability.FiniteIID` | `d1b565489199d55af70a27c31a0f803a2b7433e78c9197a361b3c10c0598845b` |
| `Shao.Probability.GaussianTail` | `f166fab0061199e25d0391bbde5c977905e368513a6e0e18b492877c65160922` |
| `Shao.Probability.ClockControl` | `c7782d17c1b6dec827cde84d1d44f9b6cb7a7d8dd166bee2183cac4d2dd5cdba` |

Actual result: `exit_code=0`, empty stderr,
`CLEAN_ALL_FOUR_PROJECT_SOURCES`. The literal whole-source token scan
found zero occurrences of sorry/admit/axiom/unsafe/native_decide in all
four sources, so there was no need to exempt comments or strings. The
same gate confirmed exactly the three intended public theorem names and
eight private theorems. Final local hash checks matched the server source
and the unchanged frozen scope.

## Independent review and nonclosure

Both source paths and the exact frozen hash were handed to the coordinator
for a new independent final proof/source-to-statement review. The author
keeps this source frozen pending that review.

This module closes the three frozen generic bounded-law probability
statements. It does not derive all their numerical hypotheses from the
source's h_x cutoff/D3 definitions, transport a later tilted clock's
moments, prove the small-x desmoothing Chebyshev specialization, or close
the full clock/Fourier/C1/C2 or OQ4 energy-denominator arguments. Those
source-specialization and root boundaries remain OPEN exactly as frozen.
