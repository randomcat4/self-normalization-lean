# RetainedComparison frozen author receipt

Status: two frozen definitions and three public theorems pass the designated
server target check and full new-declaration transitive axiom audit. Fresh
independent proof/source review remains required. The earlier independent
statement review is `RetainedComparison-statement-review.md`; it accepted
the unchanged proposal SHA256
`fe2969bf94db460176175726853dc71cd4bdb055279623dcff58c38d89eaa23f`
before implementation.

Frozen local source: `drafts/c12/RetainedComparison.lean`, 270 lines.
Remote source:
`/root/rivermind-data/shao-lean-20261021/workspaces/lead-c12/Shao/Probability/RetainedComparison.lean`.
Local and remote SHA256:

```text
fc5b9316c9571465dabc324d57d901da328f9c38c1d9f02a4ac26b8f55687604
```

No source change followed the successful target check and audit. The two
definition bodies and all three complete public statement bodies were
compared against the frozen proposal, ignoring whitespace only: all five
match. The later open Gaussian theorem printed as an explicitly excluded
goal in the scope was not implemented, assumed, or added as an axiom.

## Server check and audit

Pinned Lean: 4.36.0-rc1,
`c9afcddf514a6772bd4d649f7cfc04eff0b9f15e`.
Pinned Mathlib: `807d3836b165983210ee2ecf3cd28f239436949c`.
Existing dependency artifacts in `lead-c12` were reused; no old dependency
or entire library build was performed.

Successful target command:

```sh
source /root/rivermind-data/shao-lean-20261021/activate.sh
cd /root/rivermind-data/shao-lean-20261021/workspaces/lead-c12
taskset -c 0-3 lake env lean -o .lake/build/lib/lean/Shao/Probability/RetainedComparison.olean Shao/Probability/RetainedComparison.lean
```

Remote exit code 0. No stdout/stderr compiler diagnostics. The new target's
`.olean` is present at the displayed output path.

A separate `taskset -c 0-3 lake env lean --stdin` imported the frozen module
and Lean, printed axioms for its two public definitions and three public
theorems, and printed all three complete `#check @...` signatures. It then
traversed actual environment constants under their name prefixes plus
`_private.Shao.Probability.RetainedComparison.`. Every matched declaration
was passed to `Lean.collectAxioms`, with rejection of any nonstandard axiom.

Audit remote exit code 0; `AUDITED_DECLARATIONS 9`: two definitions, three
public theorems, one private measurability helper, and three generated proof
declarations. The five public declarations and private helper use exactly
`[propext, Classical.choice, Quot.sound]`; the generated declarations use
`[propext, Quot.sound]`. There are no other axioms. The audit was supplied
through standard input, not written into a shared audit source.

The frozen source scan for `sorry`, `admit`, new `axiom`, `unsafe`, and
`native_decide` has no hits. No local Lean command was run.

## Proof review map

- Lines 21-27 define the exact original-cutoff affine observable
  `(z-mu_x)/sqrt(V_x)` and its actual measure pushforward. They do not
  redefine the original retained conditional law or postulate a new measure
  with desirable moments. The sole private helper at lines 29-31 proves
  measurability of the actual observable, including its total zero-variance
  definition. No unit-variance conclusion is claimed at that boundary.
- Lines 37-66 prove the complete transformed conditional path law. The
  existing fixed-fiber theorem supplies actual positive good-set mass,
  conditional independence, and common genuine conditional law. Both
  conditional probability instances are installed from those nonzero
  masses. The old full finite iid map-to-product theorem gives the raw
  ascending path law; measurable coordinate composition and
  `Measure.pi_map_pi` then give the claimed fixed-transform product law.
  There is no assumption that the conditional sample is iid apart from
  the established original iid hypotheses and the checked fixed-fiber
  conditioning theorem.
- Lines 70-153 prove actual moments under `retainedStandardLaw`. Source
  size and cutoff-mass bounds first give `n>=64`, `q_x>0`, and a true
  retained probability law. Existing centered moment integrability and
  variance bounds give actual centered id/square/cube integrability and
  `V_x>0`, hence `tau_x>0`, `tau_x^2=V_x`. Constant division then proves
  actual integrability of the three normalized observables under the raw
  conditional law. `integrable_map_measure` transfers all three to the
  actual standardized law. Only after this does integral pushforward and
  scaling compute mean zero, second moment one, and the real third moment
  `C_c/tau_x^3`. The final ratio is exactly the accepted
  `C_c/(sqrt(n-j)*tau_x^3)<=64/y^3`.
- Lines 159-266 prove the actual event-level probability comparison. The
  proof derives `s.card<=n` and the natural identity
  `n-(n-s.card)=s.card` before deriving positive original/retained lengths.
  Source inputs then give `j<n`, `x>0`, and strict `j<x^2`. The deleted
  complement `s^c` has actual cardinality `j`, and its retained complement
  is exactly `s`. Existing chronological deletion therefore supplies an
  all-path inclusion into the raw retained weak crossing. The proof
  transports the length-dependent nonempty-prefix event over this set
  identity without replacing its index order or energy.
- In the same final theorem, `g=id` in the first public theorem identifies
  the actual conditional raw-path crossing probability with the canonical
  raw product event. Measure monotonicity gives the first claimed inequality.
  Next `g=retainedStandardize nu x` gives the actual standardized path law.
  Derived `tau_x>0` proves everywhere the inverse identity
  `mu_x+tau_x*((z-mu_x)/tau_x)=z`. Thus restoring the raw coordinates of
  the standardized retained path gives exactly the raw retained path,
  before any probability is taken. The second claimed equality follows
  from this identity and measurable event pushforward, not from a tail
  estimate or only marginal identical distributions.

The rightmost event in the final statement is exactly
`upperCrossing hs y` evaluated on `a_i -> mu_x+tau_x*a_i`. Its final energy
is the actual sum of those raw squared coordinates. Expanding that energy
would give

```text
tau_x^2 * energy a
  + 2*mu_x*tau_x * prefixSum a s.card
  + (s.card:R) * mu_x^2.
```

The proof does not drop the cross term, identify realized energy with a
variance sum, or turn the restored event into a self-normalized crossing
of the centered path itself. Keeping the event on the exact restored path
makes this faithful without requiring an extra public expansion lemma.

## Scope, boundaries, and unchanged material

Read-only source anchors are recorded in the frozen scope: supplement
126-140 for weak chronological deletion, 144-209 for fixed deleted-set
conditioning and the actual retained law/raw moments, and 1075-1084 for
the actual Lyapunov parameter required by later BE. Main 421-430 uses the
different fine cutoff `epsilon/(1+x)`; only the first generic measurable-set
path-law theorem specializes there without fresh cutoff-specific moment
work. Source hashes remain

```text
main.tex       beb00f718487e36de433175c97f1d500cb48e7a92ce5bd5ad5d62bb132122d06
supplement.tex b99f2ac4d2f39dd39772d98a5702b7a923c2f10f8730a08fc1b4cd6bba4742bd
```

All current statements preserve literal `H_x=n integral F(xz)<=1`, not a
narrower budget branch, and preserve actual square normalization and the
existing conditional law. No original global third moment, conditional
positive-variance premise, Jensen premise, Gaussian comparison premise,
or BE conclusion is added.

The good cutoff remains closed and the deleted cutoff strict. Weak crossings
at genuine nonempty prefixes include actual zero raw square sum. Restoring
the standardized path also restores that zero-energy case, even if its
standardized coordinates are not zero. No atomlessness is used. `j=0`,
`s=univ`, and equality in the allowed deletion-size bound remain valid.
The generic first theorem takes nonempty `s` to derive a legitimate common
conditional law. The two source-conditioned theorems derive all nonempty
and positivity facts; their size premises already rule out `n=0`/empty
retained sample. They make no unconditional iid claim at random length.

The Gaussian bounded-random theorem, completion, Petrov BE, exponential and
square tilts, denominator-layer estimates, Mills comparison, and averaging
over random deleted sets remain outside this implementation. No complete
conditional Gaussian bound, C1/C2 root, or standalone external analysis
theorem is claimed closed by this unit.

Only this new source and this author receipt were written. No old proof,
retained definition, root entry point, version pin, shared audit file, cache,
or another collaborator's source was modified. All Lean execution used the
designated server through its existing broker, with no uncertain-operation
response or local compilation.
