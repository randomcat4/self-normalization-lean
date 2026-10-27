# Data, binders and captures proposed for parent freeze

Universe: u. The only type parameter is implicit Omega : Type u. Its only
noncanonical space instance is mOmega : MeasurableSpace Omega. nu : Measure
Omega is an ordinary fixed argument, with hnu : IsProbabilityMeasure nu as
an instance argument. No BorelSpace Omega, coordinate independence, iid,
centeredness, atomlessness or choice of a coding witness is assumed.

The ordinary argument order is exactly n, hn, xi, hxi, hxi2, hxienergy, B,
Bdelete, hB, hBdelete, hBnonneg, hBdeletenonneg, hBint, hBdeleteint, z, hz
after nu. Every argument's complete type is in CANDIDATE-HEAD.txt. All arguments
are universally quantified; there is no existential data or witness choice.

The eleven ordinary head lets are V, Vdelete, C, Cdelete, H, Hdelete, rho, M,
Mdelete, kappa and Delta, in that order. Each has a full type and typed lambda
binders in the head. They are deterministic transparent expressions, not
independently chosen functions. DATA-AND-CAPTURE-MAP.json records direct and
transitive captures and the full equations. No measure changes with epsilon.

The integral notation's omega binder has type Omega and captures nu plus its
displayed integrand's data. A full finite sum j has type Fin n. In an erased
sum, j still has type Fin n with membership in Finset.univ.erase i; it is not
a Fin(n-1) or newly normalized family. Every i index is Fin n. All epsilon
and z binders are real. The metric norm, measurable/topological structures,
Bochner integral and MemLp exponent2 are the standard real/ENNReal instances
imported through the accepted module; no alternative instance is installed.

Two planned proof-only ordinary functions are proposed for the same freeze:

Hdom : Fin n -> Omega -> Real :=
  fun (i : Fin n) (omega : Omega) =>
    (1 + V omega) * (Real.sqrt (n : Real) + z * Cdelete i omega).

E : Fin n -> Omega -> Real :=
  fun (i : Fin n) (omega : Omega) => H omega - Hdelete i omega.

Hdom uses the SAME full xi, n, nu and its original energy1. It does not assume
deleted energy1. E permits the residual's epsilon limit to use scalar/absolute
integral operations already present in the accepted producer, without adding
an unverified order-squeeze API. These are derived proof data only. They add no
premise, public definition, witness or proof implementation in this packet.

The source envelope producer's implicit Omega/mOmega, explicit nu and its
probability instance are preserved in both instantiations. The full call uses
B/hB/hBnonneg/hBint; the per-i call uses Bdelete i/hBdelete i/
(fun (omega : Omega) => hBdeletenonneg i omega)/hBdeleteint i. Every other
argument, including xi and hxienergy, is identical. The producer's H has a
fresh bound real z' and is evaluated at this candidate's fixed z. It never
changes the ambient law or witness.

A : Omega -> Real and Adelete : Fin n -> Omega -> Real are result-level
universal arguments. Delta captures them along with epsilon,i,omega and M,
Mdelete, but the cancellation identity removes them. No A measurability/L1
fact is inferred for the original envelope costs themselves. kappa captures
the fixed law and functions, so it is not a model-independent rate constant.

The head's scalar constant4, square exponent2, MemLp exponent2 and literal0/1
are standard numerals at their displayed real/natural/ENNReal types. Fin n's
canonical Fintype and DecidableEq, real measurable/normed/Borel/topology
instances and proof-irrelevant membership proofs are the only automatically
resolved support. The preamble disables autoImplicit. No additional ordinary
value, section variable, existential witness or local instance is authorized
implicitly; any later substantive addition must be surfaced to the parent.
