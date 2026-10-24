# Unit 150: auxiliary energy tilt normalizer and mean drift

Source: the bounded/preprocessed auxiliary centered, unit-second-moment law in
the proof around supplement.tex lines 5094–5101 (S9 energy-only tilt).
This unit does not add a third-moment assumption to the original finite-second-
moment sample laws of units 145/147, and does not close the original C2 root.

For a probability measure nu on the reals with integrable square and absolute
cube, mean zero and second moment one, and every s >= 0, the literal native
measure rho = nu.tilted (fun z => -s * z^2) is a probability measure. Its
normalizer Z is positive and satisfies exp(-s) <= Z <= 1. The identity is genuinely
integrable under rho and its mean has absolute value at most
s * exp(s) * integral |z|^3 dnu. There is no bounded-support premise or global
s * support^2 restriction.

The positive weight V(z)=exp(-s*z^2) is bounded by one. Integrability follows by
domination. The integrated exponential tangent at -s, together with E_nu z^2=1,
gives the lower normalizer bound; positivity and the upper bound follow from
the native exponential integral and probability integral. Native tilted-measure
interfaces supply probability, integrability and the actual integral formula.
The finite second moment supplies integrability of the identity. Centering
rewrites the weighted first moment as integral z*(V(z)-1). The pointwise bound
0 <= 1-V(z) <= s*z^2 gives numerator absolute value <= s*E_nu |z|^3; division
by Z >= exp(-s) gives the stated drift estimate.

All four imports, full context and the single declaration head were frozen
before proof implementation. The exact frozen bytes remain unchanged. Server
attempt001 passed. The all-owner audit selected owners by getModuleIdxFor?,
not by namespace, and found exactly one public theorem, zero private/generated
theorems and zero non-theorem values. Its recursive axioms are only propext,
Classical.choice and Quot.sound. No previous successful gate was replayed.

Author source is released for a fresh independent complete source-to-statement,
proof, actual-type, native-interface and exact-receipt review. Subsequent work
must pay second/third moments and variance, and then the quantitative rare-suffix
budget; these conclusions are not asserted here.
