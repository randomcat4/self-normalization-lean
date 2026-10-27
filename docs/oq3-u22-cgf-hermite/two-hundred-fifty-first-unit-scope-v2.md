# FN251 revision 2: explicit safe recursor for genuine Gaussian Hermite polynomials

The complete new definition value and all three theorem declarations are
frozen before proof implementation. Define the same H0=1, H(n+1)=XHn-Hn'
polynomial family using the explicit kernel Nat.rec term. Add its public
recursion equation, then retain the exact earlier Rodrigues and H0..H3 goals.
No mathematical assumption changes, no free coefficient/derivative premise.

Concrete acceptance issue found in revision 1: native002 and the first-object
all-owner audit passed, but actual ownership included the equation compiler's
gaussianHermitePolynomial._unsafe_rec and its self-recursive VALUE. The audit
printed every owner and value; no separate safety-field observation is claimed.
To comply conservatively with the user's no-unsafe constraint, revision 1 is
NOT qualified. Its exact source, frozen value, failures, successful first
object, all9TYPE/5VALUE and receipts are retained without mutation or replay.
The old remote source/object/view remain at their old paths. Revision 2 uses
the separate module GaussianHermitePolynomialRecursor and fresh run/object;
it imports no revision-1 module and must generate no unsafe helper owner.

This is an explicit implementation-value repair of an unaccepted definition,
not a silent mathematical premise change or an accepted-proof rewrite. Exact
zero/successor equations show the same recurrence. The new accepted version
requires its own native and same-first-original-object full owner/TYPE/VALUE
and recursive-axiom evidence, plus one independent complete final review.
The reviewer must read every new actual VALUE and verify the safe recursion
term, complete public equations and derivative proof, as well as this version
transition. Do not replay revision 1's successful native/AX.

This remains the genuine polynomial side of report220–235's Hermite correction.
FM250's exact Gaussian integrals are separately qualified. Actual full-plane
CF integrability/density/inversion/Hermite identification/smoothing/exterior,
B–D and original root remain OPEN. Strict beta/p54/v_corr/Song attribution and
accepted counterexample remain. No new axiom/sorry/admit/unsafe/native_decide;
UTF-8 without BOM/LF, server-only Lean and the same resource/owner limits.
