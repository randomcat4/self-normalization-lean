# Unit223 stage1 proposal

Status: INCOMPLETE / PROPOSED_UNFROZEN_UNIMPLEMENTED_UNELABORATED. This is a declaration and architecture proposal, not a proof or kernel result. The lane lead must freeze the exact preamble/head/closing and complete data inventory before a later SAME-author implementation. Completing this proposal grants no implementation authority.

Proposed module: `Shao/OQ6/OriginalClippedCostIntegrability.lean`.
Proposed namespace: `Shao.OQ6.OriginalClippedCostIntegrability`.
One public declaration: `actual_original_clipped_cost_integrability`.
No new global definitions or helper declarations are proposed. All head values are local lets with complete types and right sides in CANDIDATE-HEAD.txt. No .lean file is produced.

The original probability space is arbitrary, with its existing measurable structure. The probability law, joint measurable symmetric L2 kernel, total mean zero and true projection second moment one are unchanged. The projection is literally the original integral of h; the residual is literally h-g-g; rho is the square root of its original product second moment. The product law is the literal Fin n iid product of the original mu. No observable reduction, extra observable w, countably generated space, standard Borel property, separation, selector, positive rho, explicit Nonempty instance, higher moment or mixed moment is assumed.

The substantive missing outputs are signed D and each signed Ddel in L2, J/Jdel in L1, the exact current B1/B1del in L1, and finite original deletion differences in L1. The current source B1 uses J divided by (1+rho)*sqrt n, with J retaining (n-2)^2 in its denominator. This is not an alias for the older UntiltedCompactCost B, which divides the unscaled row-square sum by (1+rho)*n^2*sqrt n. No source coefficient is changed.

A/Adel integrability and the needed measurability are already partly available in accepted/qualified bearing interfaces. They appear in the proposed consumer packet for direct use, with exact evidence reuse rather than new proof review. The packet is not aliases-only: the signed deleted L2 consequence, original deleted row-energy L1 consequence, exact current B1 deleted normalization, and unweighted finite deletion domination are genuinely absent from the inspected public heads.

The packet supports the original base-law assumptions of NormalizedRemainderEnvelope.actual_normalized_remainder_envelope_spec after the normalized projection family, coding Y, epsilon error, and any needed law pullback have separately been supplied. That theorem retains its input deletion envelopes. Neither this proposal nor that theorem constructs the explicit M_epsilon^(i) of p51 S24, proves the S25 analytic limit, pays the physical statistic comparison, proves a compact CDF bound, or closes S11/general S15/DC/OQ56. Planned222 has no L1 outputs and is not a dependency. Unqualified221 is not a dependency.

Original p51 remains UNCERTIFIED_REPAIR_CANDIDATE. p54's repairs, especially the missing arbitrary p-moment convergence rate and atom-safe upper event argument, remain in scope and unchanged. The external Shao-Zhou 2016 probability engine keeps its attribution. Original C1 immutablev85 and assigned C2/C12 completev112 remain accepted; OQ3 remains PAUSED_BY_USER. The finite integrability interface is not a root theorem.
