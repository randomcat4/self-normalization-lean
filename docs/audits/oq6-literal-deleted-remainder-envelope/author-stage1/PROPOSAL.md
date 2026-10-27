# Unit225 Stage1: literal deleted remainder envelopes

STATUS: PROPOSED_HEAD_ONLY_PARENT_FREEZE_REQUIRED. No proof body, Lean elaboration,
kernel receipt, axiom receipt or independent qualification is supplied.

The proposed module is `Shao.OQ6.LiteralDeletedRemainderEnvelope`, with one
public theorem `literal_deleted_remainder_envelope_spec`. PREAMBLE.txt,
CANDIDATE-HEAD.txt and CLOSING.txt are separate exact text fragments. A later
implementation would insert a proof after the candidate head; these fragments
are deliberately not a compilable Lean source and contain no placeholder proof.

The inputs fix one probability law, the entire n-coordinate family with total
second moment exactly1, one full B and all Bdelete_i, and one z>=0 before epsilon
varies. Each B/Bdelete input is globally measurable, nonnegative and L1. No mean,
independence, fourth moment, mixed product moment or target-envelope L1 input is
assumed. n>=1 is exactly the accepted generic energy theorem's lower bound;
the source model's later n>=4 is stronger and need not be imported here.

The literal deletion uses `Finset.univ.erase i` in the original Fin n. Both
sqrt(n) and rho(epsilon)=4*epsilon*sqrt(n) retain that same n. No deletion
renormalization or n-1 substitution occurs. K_n=4*sqrt(n) is only the chosen
algebraic prefactor here, not a newly proved bound for Q_epsilon.

The new substantive content is global measurability and L1 of the literal
deleted H/M families, their exact linear integral coefficients and limits, and
the p51S25 algebraic residual. The full-envelope facts are reused from the
accepted generic producer, as are the full-V dominating envelopes built with
each Bdelete_i. The deleted family is never submitted to a theorem requiring
total second moment1. This proposal does not reopen or alter either accepted
producer.

The coefficient kappa_i is explicitly
4*sqrt(n)*(integral(H)+integral(Hdelete_i)). It depends on the fixed law nu,
xi, B, Bdelete_i, n and z, and is independent of epsilon. No uniform bound in
the model or moment budgets is asserted. The pair integral identity for
epsilon>=0 is the finite S25 payment with that coefficient. The head gives the
stronger signed/all-real-epsilon identity and absolute integral identity.

A and Adelete are universally quantified only in the residual conclusions.
They need no measurability/L1 assumption because they cancel exactly before
the residual's measurability and integrability are proved. This says nothing
about L1 of A+M or Adelete+Mdelete individually without later A/Adelete inputs.

Implementation remains blocked on a substantive parent freeze and resolution
of the explicitly listed missing primary API windows. Generic225 does not
mathematically depend on a qualified222 or implemented224; actual original-law
instantiation does. Unit224 must later supply the actual B/Bdelete packet on
the SAME222 witness, with its deletion measurability/factorization contract.
