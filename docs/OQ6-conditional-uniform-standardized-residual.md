# Uniform conditional envelope for the actual standardized residual

The module `Shao.OQ6.ConditionalUniformStandardizedResidual` supplies the uniform second-moment and product-envelope component of p51, Section 6. Its public theorem is `actual_conditional_uniform_standardized_residual`. It uses the actual conditional probability measure and actual centered Hoeffding residual, rather than an abstract carrier with these properties assumed.

Under the original measurable, symmetric, centered, square-integrable kernel assumptions, normalized first projection, exponential envelope and integrable projection p-moment with `2 < p ≤ 3`, define

\[
M=\int w^2\,d\mu,\qquad W_2=\sqrt M,\qquad
C_{\rm env}=2(1+2W_2)^2,\qquad
R_{\rm bound}=4C_{\rm env}^2 M^2.
\]

The theorem proves the required integrability, `M ≥ 1`, `W₂ ≥ 1`, and positivity of both constants. It chooses one natural threshold `N₀` before every cutoff `R ≥ N₀` and every interpolation parameter `0 ≤ lam ≤ 1`. Thus all displayed constants and the threshold are independent of these two later parameters.

For `C = {o | w o ≤ R}`, `d = μ.real C`, and the genuine conditional measure `ν = (μ C)⁻¹ • μ.restrict C`, it proves `d ≥ 1/2`, that ν is a probability measure, ν and its product are absolutely continuous with respect to the corresponding original laws, and `1 ≤ w ≤ R` ν-almost everywhere. The conditional second moment `Mν = ∫ w² dν` is integrable and at most `2M`. The omitted first-moment mass `b = ∫_{Cᶜ} w dμ` satisfies `0 ≤ b ≤ W₂`; its normalized value `c = b/d` is at most `2W₂`. Genuine product integrability gives

\[
\int (w(o)w(y))^2\,d(\nu\times\nu)=M_\nu^2.
\]

Writing `g` for the original first projection and `r = h-g-g`, the actual interpolated kernel is `H = g+g+lam*r`. Its product mean κ, centered first projection G, variance σ², positive standard deviation σ, and residual `K = H-κ-G-G` are the values displayed in the theorem. The standardized residual is exactly `Kstd = K/σ`, with `ρ² = ∫ Kstd² d(ν×ν)`.

The result includes the variance bounds `1/2 ≤ σ² ≤ 3/2`, `σ ≥ 1/2`, measurability and square integrability of the actual quantities, symmetry, integrable canonical rows of Kstd with row integral zero, and zero product mean. Its envelope and second-moment conclusions are

\[
|K_{\rm std}(o,y)|\le C_{\rm env}w(o)w(y)
\le C_{\rm env}R^2\quad(\nu\times\nu)\text{-a.e.},
\qquad 0\le\rho^2\le R_{\rm bound}.
\]

The proof consumes the qualified `ConditionalTrueProjectionCarrier` and `ConditionalStandardizedLowEnergy` interfaces. It does not depend on `LogarithmicConditionalLowEnergy`. Their exact prior evidence is reused without recompilation or another full proof review.

The accepted source candidate is SHA256 `2dd4569985df4b849ec4f1cc1e0320754a9d2fcec1db9ef994dd007c6fc4ddb4` (26670 bytes, UTF-8/LF). The first source version's kernel failure is retained. The repair only supplies explicit function arguments to one integral-addition rewrite; the public declaration, mathematical assumptions, fixed values and threshold order are unchanged. Independent evidence comprises the original complete source review, the affected-block supplement, and the final exact-object review supplied alongside this note.

The repaired source's server kernel exited 0 in 16.859 seconds; the import-only whole-module-owner audit exited 0 in 5.379 seconds and preserved the same compiled object SHA256 `199e2d4c2ebc32e73eae9310a505f3b1bac14b9258c3e4fd1e7f74647f24e8b9`. Actual inventory is one public theorem, no generated theorems and no non-theorem definitions. Recursive axioms are only `propext`, `Classical.choice` and `Quot.sound`. Existing style/worktree warnings are retained; the strict runner's warning-sensitive `success=false` is not represented as an empty-output pass. Exact receipts and the final independent qualification control acceptance.

This is a source-attributed component, not a root theorem. It does not justify p54's rejected arbitrary polynomial standardized p-moment rate, exponential-envelope transport, stretched-exponential sum moments, row concentration, payment of the actual large remainder, the external Shao–Zhou premise, or the compact-relative root argument. C2/C12/OQ56 remain OPEN; OQ3 remains separately paused by the human.
