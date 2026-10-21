# CosinePowers author implementation receipt

Date: 2026-10-21. This records implementation and actual checks, not an
independent mathematical or formal review certificate.

Frozen interface: `drafts/oq4/frozen-cosine-powers-v1.md`.
Final remote source: `Shao/OQ4/CosinePowers.lean` under
`/root/rivermind-data/shao-lean-20261021/workspaces/lead-oq4`.
The local identical final source is `drafts/oq4/powers/CosinePowers.lean`.

Source SHA256:
`2f54864af99038bfb3e751d59df9d0f09969ae4aa29cd456c1e0fd8fe6758704`.

Unique author-generated olean SHA256:
`798e2ef84fc22ff24b2be455c555ef797c8327ba299e14c6edff5b3a6afaa96e`.

## Imports and unchanged dependencies

The mathematics uses the certified CosineCoefficients R0 bound and standard
real logarithm, exponential, order, and natural floor interfaces. The
existing definition `cosineCoefficient` lives in KilledCosine rather than
CosineCoefficients, so KilledCosine is minimally imported to name that
exact actual coefficient. No kernel iteration or recurrence module is
imported, and no reviewed source is modified.

Read-only source hash checks confirmed:

- CosineCoefficients:
  `8fa6f094c330a8006c5664f8912cafd035524cc461df95e81446d2384a46c104`.
- KilledCosine:
  `054816685c54b0001d10063cabf445755e54bd33017289be6a0356a31a5b3de8`.
- KilledIteration:
  `03b97e5708ffa552cfa4eccec5cf3c042da9805f9ab69561f4cb3e2701a690b5`.
- KernelRecurrence:
  `a4a5fc67cf47c8e188cbe2e2360afa4fa1bfe0a7082bb9f30fbacd6a5ad5c940`.

The last two are unchanged-source checks only, not mathematical imports.

## Actual execution

All Lean ran on the designated server, one process at a time, with CPU
affinity 0–3. Lean v4.36.0-rc1, mathlib
807d3836b165983210ee2ecf3cd28f239436949c. No local Lean, Git actions,
shared-cache writes, version-lock changes, root imports, or other-source
changes were made.

Complete original logs remain only on the server in
`repro_outputs/oq4-powers/`:

1. `check-03.log` and `.exit`: full target, exit 0, zero-byte log.
2. `olean.log` and `.exit`: unique same-source olean generation, exit 0,
   zero-byte log.
3. `audit.log` and `.exit`: actual import of that olean, dynamic enumeration,
   and transitive axiom output for every new root/descendant, exit 0.

There are 11 explicit theorems and 14 generated constants, 25 total.
The server parser checked 25 declaration names and 25 transitive axiom
records, with zero unexpected axioms. Thirteen sets are
`{propext, Classical.choice, Quot.sound}`; twelve are `{propext}`. Source
token scan found no sorry, admit, added axiom, unsafe, or native_decide.

Preserved earlier logs document two redundant post-field_simp tactics,
one ambiguous absolute-value rewrite, and unused-variable warnings. These
were repaired before source freeze. No final source change followed the
successful zero-diagnostic check.

## Exact mathematical choices

The logarithmic estimate is derived from
`Real.one_sub_inv_le_log_of_pos` and `Real.log_le_sub_one_of_pos`:
the error is at most (1-rho)^2/rho, hence at most 2(1-rho)^2.
The Log.Deriv series-remainder interface was read but is unnecessary and
is not imported. The explicit constant remains exactly
`(pi^3*M/48 + pi^4/8)/h^3`.

All final frozen-goal statements retain the full three integrability
premises, mean zero, second moment one, M>=0, beta<=M, h>=1 and
pi(1+M)<=h. The standalone R0 remainder auxiliary is stronger and needs
only h>=1 and beta<=M in addition to the moments; it does not assert any
power, positivity, or logarithmic conclusion without the frozen threshold.

## Reproduction

Run sequentially on the designated server:

```sh
source /root/rivermind-data/shao-lean-20261021/activate.sh
cd /root/rivermind-data/shao-lean-20261021/workspaces/lead-oq4
taskset -c 0-3 lake env lean Shao/OQ4/CosinePowers.lean
taskset -c 0-3 lake env lean -o .lake/build/lib/lean/Shao/OQ4/CosinePowers.olean Shao/OQ4/CosinePowers.lean
taskset -c 0-3 lake env lean repro_outputs/oq4-powers/Audit.lean
sha256sum Shao/OQ4/CosinePowers.lean .lake/build/lib/lean/Shao/OQ4/CosinePowers.olean
```

The exact audit helper is locally preserved as `Audit.lean`.
`summary.json` is a curated hashes/counts/names summary, not a raw log.
`declarations.md` lists every explicit/generated constant.
`proof.md` is the complete anonymous derivation written before implementation.

Only the stated actual free-coefficient positivity, finite inverse-power
control, and logarithmic error are established. Rho is not identified as
a killed spectral eigenvalue. B1/O0/R3/R4/K, long-time limits, 4/pi, and
the root K/Kv/OQ4 claims remain OPEN. Independent certification is left to
the separate reviewers.
