# Bearing reuse and exact missing interfaces

The accepted NormalizedRemainderEnvelope.actual_energy_envelope_integrability
already yields full V,C,H measurability, L2/L1 data and absolute linear epsilon
limits. It accepts arbitrary globally measurable nonnegative L1 B. Invoke it
once with B and once for each Bdelete_i, keeping the original full xi and energy1
in every call. No accepted proof needs modification or rechecking for Stage1.

The deleted-V energy is at most1, not generally1. The new declaration does not
pretend otherwise. The intended finite comparison uses the nonnegative
erased square sum and its sum_erase_add identity, then sqrt monotonicity.
Measurable finite erased sums and sqrt give global measurable Vdelete.
For z>=0, literal Hdelete_i is nonnegative and at most
(1+V)*(sqrt(n)+z*Cdelete_i), whose L1 was obtained using the full family.
The Integrable.mono' interface is then the only needed L1 domination transfer.

This is a dependency outline, not a proof implementation or qualification.
The exact public heads of both accepted NormalizedRemainderEnvelope theorems
are retained in BEARING-PUBLIC-HEADS.json. The second theorem is comparison-only:
its Aepsilon_delete=Adelete output does not supply literal S24 deleted M.
Their local-let definitions and complete ambient context are retained as data;
no new public definition or opaque witness is introduced by225.

The accepted NormalizedRemainderEnvelope source contains exact typed usages
for measurable finite sums/sqrt, sqrt monotonicity, Integrable.mono', scalar
L1 and integrals, and Tendsto scalar/absolute operations. The accepted
ActualUncenteredCompactCDF source contains a sum_erase_add usage in Fin n.
Their exact source bindings and windows are retained in API-MAP.json.
Where a full pinned Mathlib declaration with complete ambient binders has not
been located locally, API-REQUEST.json asks the parent for only those targeted
primary-source windows before implementation. Usage evidence is not mislabeled
as a complete Mathlib head or kernel validation.

There is no same-generic225 theorem in the directly bearing source. This is a
local, source-bound deduplication judgment only. No broad library survey or
literature novelty search is claimed. No network, Lean, API or server call was
made to prepare the proposal.
