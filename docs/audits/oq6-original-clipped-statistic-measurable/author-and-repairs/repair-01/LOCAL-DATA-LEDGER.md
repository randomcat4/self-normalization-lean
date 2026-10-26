# Unit220 repair01 typed capture ledger

This is exactly the parent-frozen proof hunk at old lines94–96/new lines94–98. The complete source retains the same one public theorem,23header values and7proof data witnesses/lets. The full updated inventory and shifted source spans are in SOURCE-MAP.json; prior source/map/manifest bytes remain untouched.

The only added named item is the derived Prop proof hpair:

- Type: `Measurable (fun ξ : Fin n → Ω => (ξ i, ξ j))`.
- Exact value: `(measurable_pi_apply i).prodMk (measurable_pi_apply j)`.
- Binding context: inside the existing hrcoord proof, with its existing universal i j:Fin n.
- Captures: Ω,mΩ,n,bound i,bound j and the canonical Pi/product measurable structures.
- Classification: Prop; no new premise, assumed measurability, selected observation, data witness, local instance declaration or global head.

The explicitly typed function expression has type `(Fin n → Ω) → Ω × Ω` and value `fun ξ : Fin n → Ω => (ξ i, ξ j)`. Its direct data captures are Ω,n,i,j. Its source measurable structure is the same Pi of mΩ and its target is mΩ.prod mΩ. This is the same pair used implicitly by the old hunk; the new expected type anchors the composition metavariables. It is not an additional proof-local data let, hence the7data inventory stays fixed.

The existing hrcoord now closes by `exact hr.comp hpair`. The joint residual, actual coordinates, law, kernel, all normalization coefficients and all mathematical assumptions are unchanged. The named derived Prop count is49 instead of48. All later source spans shift by2lines; their formulas and captured values do not change. The frozen header's23values and the existing F,Lrow,pdel,Dret,Jret,Bret,E capture graph are inherited exactly from the bound complete-source inventory.

No Lean elaboration or new server/TYPE/VALUE/AX receipt exists for this repaired source. Same-reviewer affected source/interaction review and the parent's authorized new-source checks remain pending.
