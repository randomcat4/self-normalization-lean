# KernelAbsorption author implementation receipt

Date: 2026-10-21. This records implementation and execution only; it is not
an independent mathematical or formal review certificate.

Frozen interface: `drafts/oq4/frozen-kernel-absorption-v1.md`.
Final remote source: `Shao/OQ4/KernelAbsorption.lean` in
`/root/rivermind-data/shao-lean-20261021/workspaces/lead-oq4`.
The local identical source is `drafts/oq4/absorption/KernelAbsorption.lean`.

Source SHA256:
`b11d2f68db3581ed61abab670e72234b950df669b379e98f65172f3097f5d168`.

Unique author-generated olean SHA256:
`9b61d35c7c877c44c0aa68d82c4fa2b3f3fd018a4f6ca0bf522fe10ca1f23a8f`.

## Actual checks

All Lean commands ran on the designated server, sequentially with CPU
affinity 0–3, using Lean v4.36.0-rc1 and mathlib
807d3836b165983210ee2ecf3cd28f239436949c. No local Lean, Git commands,
shared-cache writes, public/root changes, version-lock changes, or edits
to previously reviewed sources or their oleans were performed.

Complete original logs stay only on the server in
`repro_outputs/oq4-absorption/`:

1. `check-01.log` and `.exit`: full source target passed on the first run,
   exit 0, zero-byte log.
2. `olean.log` and `.exit`: actual unique same-source olean emission,
   exit 0, zero-byte log.
3. `audit.log` and `.exit`: actual import of that olean and dynamic audit
   of every declaration owned by this module, exit 0.

The ownership filter uses `env.getModuleIdxFor?` and
`env.header.moduleNames`, with no namespace or declaration-root filter.
There are four new constants: one explicit theorem, two generated
arithmetic proofs, and `Shao.OQ4.principalRate.eq_1`, a generated constant
under an imported name. All four transitive axiom sets are exactly
`{propext, Classical.choice, Quot.sound}`. The server parser verified four
names and four axiom records, with no unexpected axioms. Source token
scan found no sorry, admit, added axiom, unsafe, or native_decide.

The source was frozen immediately after the successful first target run
and was not subsequently modified. Read-only hash checks confirmed all
three direct dependencies remain unchanged:

- KernelRecurrence:
  `a4a5fc67cf47c8e188cbe2e2360afa4fa1bfe0a7082bb9f30fbacd6a5ad5c940`.
- CosinePowers:
  `2f54864af99038bfb3e751d59df9d0f09969ae4aa29cd456c1e0fd8fe6758704`.
- DelayedRecurrence:
  `2b8655db071125a3ee51f1a28cdc06a60b56d9e79ccb930c59f32abb5f73e50b`.

## Actual recurrence connection

The proof derives rho positivity from all the stated moments and h
thresholds; m>=1 from h>=1 and the natural floor; and the three inverse
power bounds from CosinePowers. Actual-kernel nonnegativity is recorded
as `hf0` and `hg0`. The short initial mass bound `hinit` and principal
initial bound `hfm` come from actual kernel mass and inverse powers.

The two independent block inputs enter `hincrement` and `hdelay`, which
are exactly the hypotheses of DelayedRecurrence with
`(A',B',D,C)=(AR,BR/h,ER/h^3,R)`. Enlargement of the D3 coefficients
explicitly multiplies their bounds by `hf0` and `hg0`. The exact smallness
premise is then passed to the certified noncircular finite theorem.
The desired global Ghat bound is never supplied as an assumption.

The final result is H=2(1+AR)R with both 0<=Ghat_k<=H for k<=N and the
stated fluctuation bound for m<=k<=N. N=m and A/B/E=0 are retained.
There is no division by any of A, B, or E.

## Reproduction

Run sequentially on the designated server:

```sh
source /root/rivermind-data/shao-lean-20261021/activate.sh
cd /root/rivermind-data/shao-lean-20261021/workspaces/lead-oq4
taskset -c 0-3 lake env lean Shao/OQ4/KernelAbsorption.lean
taskset -c 0-3 lake env lean -o .lake/build/lib/lean/Shao/OQ4/KernelAbsorption.olean Shao/OQ4/KernelAbsorption.lean
taskset -c 0-3 lake env lean repro_outputs/oq4-absorption/Audit.lean
sha256sum Shao/OQ4/KernelAbsorption.lean .lake/build/lib/lean/Shao/OQ4/KernelAbsorption.olean
```

The exact helper is locally preserved as `Audit.lean`; `summary.json` is
a curated hash/count/name summary. All declaration names are in
`declarations.md`. The complete anonymous proof was written first in
`proof.md`.

This is a conditional finite actual-kernel D8 bridge. It does not prove
the block inputs, B1's Fhat_m limit, O0/R3/R4, Brownian terminal-block
estimates, 4/pi, or the root K/Kv/OQ4 statements. The free rho is not
identified as a killed-kernel spectral eigenvalue. Independent review is
separate and is not self-signed here.
