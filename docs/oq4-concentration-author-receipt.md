# IntervalConcentration author implementation receipt

Date: 2026-10-21. This records implementation and actual checks, not an
independent mathematical or formal review certificate.

Frozen interface: `drafts/oq4/frozen-interval-concentration-v1.md`.
Remote source: `Shao/OQ4/IntervalConcentration.lean` under
`/root/rivermind-data/shao-lean-20261021/workspaces/lead-oq4`.
Local identical source: `drafts/oq4/concentration/IntervalConcentration.lean`.

Final source SHA256:
`491e088fccc4457f18701ab7440da8cc9811183d462e3f3b7f22b096ccbf0875`.

Unique author-generated olean SHA256:
`7def082f20b5f1758889f0b97c9eb65c595027b8bf55f57695333cdb5e78b388`.

## Actual execution

All Lean ran only on the designated server, one process at a time with
CPU affinity 0–3, using Lean v4.36.0-rc1 and mathlib
807d3836b165983210ee2ecf3cd28f239436949c. No local Lean, Git commands,
shared-cache writes, public/root changes, dependency-lock changes, or edits
to previously reviewed sources or oleans were performed.

The module imports only common MeasurablePath and the standard Mathlib
Gaussian, CDF, basic trigonometric, set-integral and tactic modules. It
does not import killed-kernel block or recurrence algebra. The standard
density bound uses `Real.two_le_pi`, already available in the cached
basic trigonometric module; no extra Pi.Bounds cache is needed.

Complete original logs remain only on the server in
`repro_outputs/oq4-concentration/`:

1. `check-03.log` and `.exit`: full module target, exit 0, zero-byte log.
2. `olean.log` and `.exit`: unique same-source olean emission, exit 0,
   zero-byte log.
3. `audit.log` and `.exit`: actual import and dynamic transitive axiom
   audit of all declarations owned by this module, exit 0.

The audit uses `env.getModuleIdxFor?` and `env.header.moduleNames`, with
no namespace or root-name filter. There are 9 explicit declarations
(1 definition, 8 theorems) and 4 generated constants, 13 total. The server
parser verified 13 declaration names and 13 axiom records, with zero
unexpected axioms: 9 standard three-axiom sets, 3 `{propext}` sets, and
1 `{propext, Quot.sound}` set. Source scan found no sorry, admit, added
axiom, unsafe or native_decide.

Earlier complete logs preserve corrections to the explicit nonpositive
exponent proof, pointwise function-addition rewriting under integrals,
the map CDF expression, and instance/simplification style warnings. These
were fixed before final source freeze. No source change followed the
successful zero-diagnostic check.

The common MeasurablePath source was checked read-only at SHA256
`827dc47b74dae67101a4d874f412e4cb55bafe1e67b9ba767c6896c0b7e58b41`.

## Four frozen results

The arbitrary-measure closed interval result bounds [a,b] by (a-delta,b]
for every strictly positive delta, using the exact Iic difference only at
the smaller cutoff. It then removes the extra L delta by an arbitrary
positive slack argument. It never replaces the closed mass by F(b)-F(a).
The case a=b therefore retains the full atom and gives mass<=2 epsilon.

`standardNormalCDF` is exactly `ProbabilityTheory.cdf (gaussianReal 0 1)`.
Its equality to the actual Iic real mass is proved. The actual standard
Gaussian density is proved <=1 from the library formula; its genuine
integrability and the actual Gaussian set-measure integral formula give
the interval mass bound. The actual CDF is consequently globally
1-Lipschitz, not assumed Lipschitz.

The beta>=1 theorem assumes only genuine square and absolute-cube
integrability, probability total mass, and second moment one. It
integrates the pointwise polynomial inequality derived from
(|y|-1)^2(2|y|+1)>=0. It adds no mean or fourth-moment requirement.

The final concentration theorem constructs the actual pushforward of
the finite product law by the measurable standardized prefix sum. Its
probability instance and the exact Iic and closed-Icc preimage identities
are proved. Positive sqrt(t) is supplied by t>=1. The displayed BE-type
error is retained as a hypothesis on the actual product probabilities,
and the actual Gaussian comparison plus beta>=1 yields exactly
(1+2 C_BE) beta/sqrt(t). No time-zero division, density, atomlessness,
or conditional independence premise is added.

## Reproduction

Run sequentially on the designated server:

```sh
source /root/rivermind-data/shao-lean-20261021/activate.sh
cd /root/rivermind-data/shao-lean-20261021/workspaces/lead-oq4
taskset -c 0-3 lake env lean Shao/OQ4/IntervalConcentration.lean
taskset -c 0-3 lake env lean -o .lake/build/lib/lean/Shao/OQ4/IntervalConcentration.olean Shao/OQ4/IntervalConcentration.lean
taskset -c 0-3 lake env lean repro_outputs/oq4-concentration/Audit.lean
sha256sum Shao/OQ4/IntervalConcentration.lean .lake/build/lib/lean/Shao/OQ4/IntervalConcentration.olean
```

The exact helper is preserved locally as `Audit.lean`. `summary.json` is
a curated hashes/counts/names summary, not a raw log. `declarations.md`
lists all explicit and generated names. The anonymous complete derivation
was written first in `proof.md`.

BE itself, unconditional AC, SP, one-sided S, O0/R3/R4, B1/Brownian
inputs, long-time K/Kv, 4/pi and OQ4 remain OPEN. Independent review is
separate and is not self-signed here.
