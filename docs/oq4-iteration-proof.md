# Finite iteration of a killed transition kernel

Let ν be any Borel probability measure on ℝ and let h be any real number.
Write P for the already constructed kernel whose row at z is the law of z+Y,
restricted to the closed interval [−h,h]. Define Qₙ=Pⁿ using the ordinary
Mathlib monoid of kernels, Uₙf(z)=∫f(w)Qₙ(z,dw), and Gₙ=Uₙ1. All the
integrals in the arguments below are ordinary real Bochner integrals.

## Measures, mass, and support

The monoid identity is the deterministic identity kernel, so Q₀(z)=δ_z.
The one-step result gives P(z,ℝ)≤1. The kernel Chapman–Kolmogorov identity
gives Qₙ₊₁(z,ℝ)=∫P(w,ℝ)Qₙ(z,dw)≤Qₙ(z,ℝ). Induction, starting with
δ_z(ℝ)=1, proves Qₙ(z,ℝ)≤1 for every n and z. Thus each Qₙ is a uniformly
finite kernel, with the explicit uniform bound 1. Applying the monotonicity
of ENNReal.toReal below the finite upper bound 1 proves the real mass bound.

Each P(w) gives full measure to the Borel set A={v:|v|≤h}. For n+1, write
Qₙ₊₁=P∘Qₙ. The almost-everywhere composition theorem transfers the
everywhere statement “P(w)-almost every v belongs to A” to Qₙ₊₁(z)-almost
every v. No condition on z is needed. For n=0 and z∈A, δ_z is supported
on A. This proves all-n support exactly for starts in A and positive-n
support for arbitrary starts. It makes no assertion of arbitrary-start
support at time zero.

## Bounded tests and parameter measurability

Let f be Borel and suppose |f(w)|≤M for all w, for a real M. Necessarily
M≥0, by evaluating this bound at 0. Since every Qₙ(z) is finite, the Borel
function f is genuinely integrable against every row, by the constant
norm majorant M. The standard strongly-measurable kernel-integral theorem
shows that z↦Uₙf(z) is Borel measurable. This theorem is applied to the
actual measurable kernel Qₙ, not to a hypothetical path distribution.

Integrating the constant 1 shows Gₙ(z)=Qₙ(z).real(ℝ). Consequently
0≤Gₙ(z)≤1. The norm bound on a finite-measure integral gives

    |Uₙf(z)| ≤ M Qₙ(z).real(ℝ) = M Gₙ(z) ≤ M.

Thus the image of every bounded Borel test is again bounded Borel, with
the same constant M; the sharper mass-weighted bound is retained. The
integrability statement is established before any use of integral
algebra, so no conclusion uses the default value of a nonintegrable
Bochner integral.

## Zero step, one step, and semigroup

The Dirac integral gives U₀f(z)=f(z), including starts outside A. Since
Q₁=P, the certified one-step theorem gives both actual integrability of
the translated killed test and the identity

    U₁f(z) = ∫ 1{|z+y|≤h} f(z+y) ν(dy).

For m,n≥0, commutation of powers of the same kernel gives
Qₘ₊ₙ=Qₙ∘Qₘ. The function f is integrable against the composite row by
the bounded-test result already proved. The standard Bochner integral
composition theorem therefore gives

    Uₘ₊ₙf(z) = ∫ [∫f(v)Qₙ(w,dv)] Qₘ(z,dw) = Uₘ(Uₙf)(z).

The inner action is Borel and bounded by M. Its outer integral is genuinely
integrable by the same bounded-test result. The interface records these
facts separately, including arbitrary m,n and zero steps.

## Linearity, absolute values, and order

For bounded Borel f and g, both row integrals are integrable, so the
standard integral_add identity gives Uₙ(f+g)=Uₙf+Uₙg. Real multiplication
uses the genuine integrability of f and of cf, followed by the scalar
integral identity. The absolute-value test is Borel and bounded by M,
hence genuinely integrable; the integral norm inequality gives
|Uₙf|≤Uₙ|f|.

For global pointwise f≤g, integral monotonicity applies directly using
the two established row integrabilities. For f≤g only on A and a start
z∈A, the all-n row support theorem converts this restricted comparison
into a Qₙ(z)-almost-everywhere comparison, and the same integral
monotonicity theorem applies. This includes n=0.

Every argument permits h=0 and atoms. When h<0, A is empty, so the
closed-source-domain statement is vacuous, while every positive-time row
is zero and Q₀ remains the identity. No moment, centering, density,
nonlattice, or bounded-jump assumption is used. These statements prove
finite kernel algebra only; they do not identify kernel powers with iid
paths, establish occupation inputs, or close R3/R4/O0/K/Kv/OQ4.
