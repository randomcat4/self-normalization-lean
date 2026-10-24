# Unit 156: actual centered path and weak-event implication

Source: supplement.tex lines 5123–5130. The two exact frozen heads concern
literal finite coordinate paths, not a substituted scalar model. For every
natural n (including0), real path v and real mu, the full centered sum is
prefixSum(v,n)-n*mu and sqrt(energy(v-mu))<=sqrt(energy(v))+sqrt(n)*|mu|.
Under y>=0 and the source's exact sufficient condition
(sqrt(n)+y)*sqrt(n)*|mu|<=(a-y)*sqrt(energy(v)), the raw weak endpoint event
a*sqrt(energy(v))<=|prefixSum(v,n)| implies the true centered weak endpoint
event at levely. No parameter/rank/mean bound is silently supplied.

The first proof applies native finite Cauchy–Schwarz to the constant-one
vector and v, yielding |sum v|<=sqrt(n)*sqrt(raw energy). It expands the actual
centered square sum into rawenergy-2*mu*sum(v)+n*mu^2, bounds the cross term by
2*|mu|*|sum(v)|, then compares the two nonnegative square roots. The whole-sum
identity follows from the actual finite sum definitions and probability is
not involved. Zero length, zero energy and arbitrary mu are retained.

The second proof uses the true whole-sum identity, the real norm triangle
inequality, the first energy inequality multiplied by nonnegative y, and
(sqrt(n))^2=n. The literal displayed source shift condition then pays the
difference between the raw and centered thresholds. Weak inequalities retain
boundary equality and all zero-energy cases. No drift inequality or desired
event conclusion is introduced as a premise under another name.

All imports/context/two heads were frozen before proof implementation and
remain unchanged. Attempt001 is preserved: the sole elaboration error was an
untyped natural-cast nonnegativity proof inside an absolute-value rewrite.
Only its explicit Real type annotation changed. Attempt002 passed. The exact
all-owner audit has two public theorems, no private/generated owners or global
non-theorem values; all recursive axioms are propext, Classical.choice or
Quot.sound. No successful old proof/audit check was replayed.

Author writer/execution release is for fresh independent complete source,
proof, actual-type, interface, axiom and receipt review. The numerical source
threshold y_x, small drift and deterministic rank must still pay the shift
condition, and the centered law's legal C1 budget/probability transport and
full rare-suffix budget remain subsequent work. Original full roots OPEN.
