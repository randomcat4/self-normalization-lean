# KernelAbsorption declaration ledger

Source SHA256:
`b11d2f68db3581ed61abab670e72234b950df669b379e98f65172f3097f5d168`.

The one explicit theorem `Shao.OQ4.kernel_finite_absorption` proves both
frozen conclusions with the actual normalized kernel quantities. It
retains the complete moment, threshold, floor/horizon, closed-source,
nonnegative A/B/E, two independent block, and exact smallness premises.

All four new module-owned constants were dynamically audited:

- `Shao.OQ4.kernel_finite_absorption`
- `Shao.OQ4.kernel_finite_absorption._proof_1_1`
- `Shao.OQ4.kernel_finite_absorption._proof_1_3`
- `Shao.OQ4.principalRate.eq_1`

The last is generated under an imported name. The audit selects declaration
ownership via `getModuleIdxFor?` and `header.moduleNames`, so no namespace
or root-name filtering excludes it. All four transitive axiom sets are
exactly `{propext, Classical.choice, Quot.sound}`.

The complete original log remains only on the server in
`repro_outputs/oq4-absorption/audit.log`. Local `summary.json` is a curated
hash/count/name/axiom-total summary, not a raw log.
