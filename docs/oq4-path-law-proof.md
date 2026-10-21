# Finite killed-kernel rows and unnormalized surviving endpoint laws

Let ν be any Borel probability measure on ℝ. For n≥0 let Πₙ be its product
law on the existing Shao.Path n. For arbitrary real h,z define Sₙ(h,z)
by |z+prefixSum(a,k)|≤h for every 1≤k≤n, and define
Eₙ(z,a)=z+prefixSum(a,n). No condition is imposed at time zero.

Every prefix sum is measurable. Countable intersection of the measurable
weak inequalities proves that Sₙ(h,z) is Borel; addition gives
measurability of Eₙ. The empty event S₀ is the whole empty-path space and
E₀ is the constant z.

Split a nonempty independent sample into its first increment y and tail a.
The standard finite-product measurable equivalence preserves the measures
Πₙ₊₁ and ν⊗Πₙ. The existing prefix sums satisfy exactly

    prefixSum(cons(y,a),k+1)=y+prefixSum(a,k).

Consequently Eₙ₊₁(z,cons(y,a))=Eₙ(z+y,a), and pointwise

    cons(y,a)∈Sₙ₊₁(h,z)
      iff |z+y|≤h and a∈Sₙ(h,z+y).

These are weak closed inequalities, including equalities and atoms.

We first prove the identity for every nonnegative measurable test F, by
induction on n. At n=0, the kernel row is δ_z and the product law is the
probability law on the unique empty path; both integrals are F(z).
For n+1 the genuine kernel composition first takes one killed step and
then n further steps. Its nonnegative integral is

    ∫ν(dy) 1{|z+y|≤h} ∫Pⁿ(z+y,dw) F(w).

Insert the induction hypothesis into the inner integral. Tonelli and the
measure-preserving first-coordinate/tail split, together with the two
pointwise identities above, give

    ∫Pⁿ(z,dw)F(w)
      = ∫Πₙ(da) 1{a∈Sₙ(h,z)} F(Eₙ(z,a)).

The one-step transformation here is exactly the existing translated ν row
restricted to [−h,h]. No normalization, conditional independence, or
moment assumption is used. Equality of all nonnegative measurable test
integrals gives the exact measure identity, for every n,h,z,

    Pⁿ(z)=map(Eₙ(z,·))(Πₙ restricted to Sₙ(h,z)).

For a bounded Borel real test f, its integral under the kernel row is
genuinely integrable by the certified finite-row bounded-test theorem.
The product-space truncated test is Borel. If |f|≤M, then necessarily
M≥0 and its truncation is also bounded by M; Πₙ is a probability measure,
so that test too is genuinely integrable. The map integral formula and
the indicator/restriction integral identity now give equality of the real
integrals. Taking f=1 yields

    killedMass(ν,h,n,z)=Πₙ.real(Sₙ(h,z)).

For any measurable mutually independent family X indexed by Fin n, with
every coordinate law ν on an arbitrary probability space (Ω,μ), the shared
FiniteIID theorem gives map(samplePath X)μ=Πₙ. Restriction commutes with
this measurable pushforward. Composing the endpoint map proves exactly

    Pⁿ(z)=map(ω↦Eₙ(z,samplePath X ω))
             (μ restricted to {ω:samplePath X ω∈Sₙ(h,z)}).

The sample-space truncated test is measurable and bounded, hence genuinely
integrable; the same map and indicator identities prove the corresponding
real test-integral formula. The constant test gives the real sample-space
survival probability. This transfers the unconditioned joint law once;
it makes no independence assertion after restriction to survival.

At z=0 and h≥0, monitoring the missing zero prefix adds the inequality
|0|≤h, which already holds. Therefore Sₙ(h,0) is pointwise equal to the
existing Shao.closedStrip h. Substitution in both product and arbitrary-iid
mass identities yields the common closed-strip survival probabilities.
The proof includes n=0, h=0, zero paths, and every endpoint equality. For
negative h the shifted interface still applies without a time-zero kill.

This proves only the exact finite path-law connection. It does not prove
O0/R3/R4/B1, Brownian approximation, any energy denominator assertion,
long-time limits, K/Kv, or OQ4.
