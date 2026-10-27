# Unit220 repair-plan02 data and capture ledger

PROPOSAL ONLY; no implementation authority or .lean file. The exact five replacement blocks are in PATCHES.json and PROPOSED-PATCHES.diff. They retain all23frozen header values and all7existing proof data witnesses/lets. No global head, alias, local data let, instance, chosen datum, measure or mathematical premise is added.

The sole new named item is the local derived Prop hJfun, inside the existing hJ proof:

- Type: `J = (fun ξ : Fin n → Ω => (∑ i : Fin n, (Shao.OQ6.ResidualDeletion.rowSum (fun j k : Fin n => r (ξ j) (ξ k)) i) ^ 2) / ((n : ℝ) - 2) ^ 2)`.
- Proof value: `funext (fun ξ : Fin n → Ω => residualEnergyJ_eq_rowSqSum n r ξ)`. The proposed source expresses this as typed have / funext ξ / exact the same existing theorem.
- Sort: Prop; no new assumption.
- Direct type captures: Ω,n,J,r. Direct proof-value captures: Ω,n,r. Transitive original data captures: mΩ,μ,h,g through the already frozen J/r definitions.
- Universal sample binder: ξ:Fin n→Ω. Summation index i and matrix indices j,k all have type Fin n, as explicitly written.

The typed lambda on the equality's right side has type (Fin n→Ω)→ℝ and exactly the value shown above. Its data captures are Ω,n,r. It is the same existing pointwise row-square function from hrowsquares and the qualified residualEnergyJ identity. It is an expression inside a Prop, not a new function let, existential witness, model choice or replacement definition. The hJ function itself remains the literal frozen J.

The other four blocks add only named existing Pi representation rewrites to simp sets. Pi.mul_def has function inputs f,g:∀i,M i and value rfl under existing pointwise Mul. Pi.sub_def is the existing generated additive counterpart of div_def, also rfl. At these uses the domain is Fin n→Ω and target is ℝ, with existing canonical real Mul/Sub. No new local data binder is introduced by their source invocations. Existing bound i:Fin n remains the finite-sum index; g,r,V and the centered-row functions retain their exact values and captures.

Named derived Props become50from49; the new count is derived from the in-memory five-hunk preview. The earlier hpair, all7data witnesses/lets and every header value remain byte-identical. No new local instance is proposed. The unchanged classical/Pi/real implicit structures remain governed by the existing full source map. Any future elaboration-generated owners/values still require the normal independent actualTYPE/VALUE and recursiveAX audit.
