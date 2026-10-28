# GG270 — Actual Gaussian bad-noise probability

Freeze three complete declarations and both complete v/gamma statement lets
before implementation. Derive the real centered Gaussian's subgaussian MGF
property from its actual everywhere-integrable exponentials and exact MGF,
then apply both signed Chernoff bounds and a union estimate to prove the
two-sided real tail bound 2*exp(-eps^2/(2*v)), eps>=0.

For b>0, actual v=toNNReal(2*b), and the same two-coordinate Gaussian product
gamma used by GC/GD/GE, prove gamma.real{eps<norm(noise)} <=
4*exp(-eps^2/(4*b)). This is the actual bad-noise event of GF269: the Prod
norm is max of the two real absolute values, so the event is exactly the
union of two coordinate-tail cylinders. Use actual product measure and
finite real-measure union rules; do not replace it by a Euclidean/Hilbert
norm event or a free desired tail assumption. The scalar statements include
v=0; their division is Lean's total real division, so the bound may then be
trivial but remains valid. The useful pair bound has b>0 explicitly.

This is a fixed-library Gaussian/Chernoff application, with no project
theorem dependency and no new hypothesis on the original nu. Actual noise
scale selection/asymptotics, canonical set expansion, desmoothing error,
exterior/B-D and original OQ3 positive root remain OPEN. Preserve strict
beta<2/5, p54/v_corr repair, Song uniform-in-law and the accepted counterexample.

Use UTF-8 LF; server-only phase40 OQ3 CPU36-39,44-47/c12-heavy.lock/native
-M8192-j4; exact first-object all-owned TYPE/required VALUE/transitive AX
and one independent complete final review. No old accepted check/proof
replay, cache write or lane merge.
