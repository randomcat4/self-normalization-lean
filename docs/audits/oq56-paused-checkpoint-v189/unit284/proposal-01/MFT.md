# Mathematical feasibility and source fidelity

Status: INCOMPLETE — exact proposal only, not a proof or qualification. The author proposes the following dependency decomposition for lead freeze. The raw HEAD/RHS fragments control over this explanation.

## Original objects and quantifiers

Read p41 in full (including §5 and its surrounding original-statistic scope) and p51 in full. The bearing source is p41 lines 253–259 together with (9), lines 191–197; p51 S6, lines 325–343 confirms the same original conditional means and warns that ν need not canonicalize the original r. This unit stops before applying Bernstein at p41 (14).

The original objects are g(o)=∫h(o,y)dμ, r(o,y)=h(o,y)−g(o)−g(y), C={w≤R}, d=μ.real C, ν=(μ C)⁻¹•μ.restrict C, b=∫_{Cᶜ}w dμ and W2=sqrt(∫w²dμ). T02 retains all original global h and envelope hypotheses, including L²(h), symmetry, mean zero, projection variance one, positive exponential parameters, the a.e. lower envelope w≥1, original product-a.e. residual domination, and the original p-moment assumptions. It imposes only the existing cutoff d≥1/2. The factor c=b/d and energy factor M=W2²/d are literal output lets, with no unspecified C. In particular d≥1/2 entails c≤2b and M≤2W2², explaining the source's uniform constants without any new moment or cutoff assumption.

The finite index ι is arbitrary and need not be nonempty. For ι=Fin k, a:Fin k→Ω is the full vector of original anomalous observations; it is not a vector of envelope values. Its law is Pi(η) for η=(μ Cᶜ)⁻¹•μ.restrict Cᶜ. Validity is asserted for Pi(η)-almost every a. Background exceptional sections remain ν-a.e. The deterministic T01 requires the explicit D04 valid-row predicate and cannot promote arbitrary a values to valid ones.

## Qualified input actually reused

Qualified176 source SHA256 78762108ee542e89ea114a5f4047c53cad464a385e58ec7c20fd49a37537cbb8, 33321 B, has been read in full. Its complete source theorem HEAD and ambient declarations match the provided complete public actual TYPE: SHA256 fb0aa27d11246907aa1f47eb8be5f351bcf7629a584fe955a2b5a4053216b905, 237079 B, 2201 LF. All symbolic content of that TYPE was read, including explicit nested measures/typeclass expansions; some display chunks suppressed only leading indentation and added line numbers. The bound JSON/source bytes were never normalized or rewritten. The exact qualified proof, original object and all-owned axiom evidence are reused rather than rechecked.

At lam=0, the theorem still exposes the same original residual r and supplies ν probability/absolute continuity, measurable g, w∈L²(μ)∩L²(ν), ∫w²dν≤W2²/d, b≥0, d>0 and μ-a.e. original rows with L¹(μ), L¹(ν), their exact negative bad-tail integral identity and |a_R|≤(b/d)w. These are the only bearing parts of176. No projection-variance estimate, θ-bound, source asymptotic statement or root conclusion is needed. The accepted175 carrier source HEAD was read as context; no second direct175 theorem call or replay is proposed.

The residual itself is measurable from hh and measurable g using subtraction and product projections. Every fixed first-coordinate row is therefore measurable; the global product-a.e. envelope yields μ-a.e. valid row envelopes by one-way product sectioning, then ν≪μ transports their inner a.e. statements. This is new section assembly around176, not a second proof of176's accepted row integrals.

## Proposed proof dependencies, without Lean implementation

T01 first obtains ell≥0 and measurable/L¹ cA by finite sums of the valid rows. Intersect finitely many row-envelope exceptional sets to retain background-a.e. |cA|≤ell*w. Squaring on this a.e. set gives cA²≤ell²w². The nonnegative integrable majorant ell²w² and measurable cA² give integrable cA² and then cA∈L²(ν); integrating yields S2≤ell²M. This avoids asserting an unproved row L² premise.

Finite linearity of the actual integrals gives mA=Σ_i∫r(a_i,o)dν. Triangle inequality and valid-row mean bounds give |mA|≤c*ell. The background cutoff also gives |cA|≤ell*R. Since ν is a probability measure, integrating this bound gives |mA|≤ell*R. These are bounds on the actual conditional mean; it is never assumed zero.

Centering cA by its actual integral preserves measurability, L¹ and L² under the finite probability law. Expanding its square and using ν(univ)=1 gives V2=S2−mA². Nonnegativity of the squared integral yields mA²≤S2 and 0≤V2≤S2≤ell²M. Centered first moment is exactly zero. Triangle inequality gives both |cA−mA|≤ell*(R+c) and |cA−mA|≤2*ell*R ν-a.e. Thus a future variance-sensitive Bernstein consumer can use actual centered variance V2 and deterministic bound 2*ell*R, rather than substituting a noncentered sum or a worst-case squared range for variance.

T02 obtains the176 facts once, with unchanged source hypotheses. The normalized bad restriction η is absolutely continuous with respect to μ and is zero or a probability measure, hence finite and σ-finite. Transporting original row facts and the bad-set support through η≪μ gives η-a.e. valid anomalous observations. `Measure.quasiMeasurePreserving_eval` lifts each such coordinate predicate to Pi(η), even when η=0; a finite intersection gives an a.e. complete vector. The good restriction has ν-a.e. 1≤w≤R. Its probability property supplies at least one such point, deriving 1≤R and hence 0≤R. They are conclusions, not added assumptions. T01 then yields the stated actual moments, and finite linearity of the176 negative bad-tail identity yields T02's last mean identity.

T03 handles Fin0 directly: all finite sums, their means, second moments and centered moments vanish; D04 is vacuous; D05 remains true for arbitrary real c,R,M and arbitrary ν. The empty Pi law of η is Dirac on the unique empty vector. T04 handles a null anomaly factor only for nonempty ι: η=0, so its nonempty product has univ mass zero and is zero. T02's a.e. result is then vacuous under that zero product, while the empty case retains the nonzero Dirac product. No claim that η is a probability at μ(Cᶜ)=0 occurs.

T05 exchanges two finite sums using the literal qualified278 definitions. The first coordinate remains x(a), the second x(i); no symmetry, resampling, enlargement, projection or scaling changes r. Its companion identifies the same ell with qualified anomalyWeight. This algebra works for any B,n, including empty blocks, and does not claim a law for block coordinates.

## Edge cases and exclusions

| Case/risk | Required behavior in this proposal |
| --- | --- |
| k=0 | Exact zero sums/moments, empty-product Dirac; no fictitious positivity premise. |
| μ(Cᶜ)=0,k>0 | Exact zero anomaly law/product; the a.e. output has zero measure. |
| Arbitrary measurable Ω | Product measurability plus finite products/sectioning; no Standard Borel premise or disintegration theorem. |
| Exceptional original rows | Excluded only on a μ-null set, transferred to η then Pi(η); never claimed valid pointwise. |
| ν not canonical for r | The actual mean stays nonzero and bounded by (b/d)ell; centering uses that actual mean. |
| Envelope negative on a μ-null set | No pointwise replacement of w; row validity and background bounds remain a.e. |
| R≤0 candidate | Ruled out by deriving 1≤R from the existing positive good mass and w≥1 a.e. |
| ell=0 | All moments vanish ν-a.e.; no division by ell appears. |
| Duplicated observation values | Allowed; original finite indices and original observations remain unchanged. |
| Unit283 | SOURCE accepted but still unqualified at activation; not imported or relied on as proved. |

This is a row/moment producer. The actual fixed-mask joint-law/Fubini transport remains a later qualified consumer, followed by Bernstein (14), Δ (15), Mills (16), anomaly integration and the original tail-engine conclusions. No novelty or mathematical completion of PE-R/PE-L/NR/DC/OQ56/root is claimed.
