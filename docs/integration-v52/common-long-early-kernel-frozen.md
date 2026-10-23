# Root exact freeze: actual early and long-time full-space kernel bounds

Root fully read the complete public declaration, complete revised source/payment contract, original supplement LF621–641 and LF2464–2564 and main LF373–388. Author common_highfreq_author is authorized to implement only new Shao/Probability/SourceLongKernelBounds.lean, preserving the displayed actual conditional law, original raw normalization/mean/budget, actual D/E spatial derivatives, all m endpoints and all real w/q. The source allows a sufficiently small universal epsilon0; its explicit choices must genuinely pay both outside smallness and early L2*gamma²<=T. No local short-time w guard or supplied regional/kernel conclusion may be introduced.

The revised internal high-cone proof uses actual mark-v L1<=Cy|u|, actual full(c) zero-order bounds, and gamma<=sqrt(T); high outside retains the y factor. This is an approved coarser intermediate estimate with exactly the original final (i)/(ii) bounds, not a claim of the sharper source highlong intermediate expression. Complete final source/proof/all-owned actual-type/value semantic review and source-bound kernel/transitive-axiom evidence remain mandatory once; exact old evidence is reused. Short-time summation and the probability/C1/C2 roots remain separate active work.

drafts/c12-centered-characteristic/long-early-kernel-candidate-declarations.md SHA256 a8eee4f753641dbbef9fb56671f5ed2888fb74d75e80b1dda2b37e4311343fda

# Actual source conditional-law kernel: early and long-time full-space bounds

Status: CANDIDATE_PENDING_ROOT_FREEZE. Proposed module Shao/Probability/SourceLongKernelBounds.lean. One public theorem, no new public definitions. One common tuple of absolute constants serves both source realkernel(i)/(ii) bounds.

```lean
namespace Shao.Probability

open MeasureTheory ProbabilityTheory

theorem sourceTruncation_futureNoise_early_long_kernel_bounds :
    ∃ C epsilon0 L2 : ℝ, 0 < C ∧ 0 < epsilon0 ∧ epsilon0 ≤ 1 / 2 ∧
      (16384 : ℝ) ≤ L2 ∧
      ∀ (ν0 : Measure ℝ), IsProbabilityMeasure ν0 →
        ∀ n : ℕ, Integrable (fun a : ℝ => a ^ 2) ν0 →
          (n : ℝ) * (∫ a : ℝ, a ^ 2 ∂ν0) = 1 →
          (∫ a : ℝ, a ∂ν0) = 0 →
          ∀ x epsilon : ℝ, 0 ≤ x → 0 < epsilon → epsilon ≤ epsilon0 →
            Shao.truncationBudget ν0 n x ≤ epsilon ^ 3 / 8 →
            let ρ : Measure ℝ :=
              ProbabilityTheory.cond ν0 {a | |a| ≤ epsilon / (1 + x)}
            let mu : ℝ := ∫ a : ℝ, a ∂ρ
            let m2 : ℝ := ∫ a : ℝ, a ^ 2 ∂ρ
            let m3 : ℝ := ∫ a : ℝ, |a| ^ 3 ∂ρ
            let gamma : ℝ := m3 / variance (id : ℝ → ℝ) ρ
            ∀ y : ℝ, gamma ≤ y → y ≤ 2 →
              ∀ i : ℕ, 1 ≤ i → i ≤ n →
                let m : ℕ := n - i
                let T : ℝ := (m : ℝ) * m2
                let f : ℝ → ℝ → ℝ := fun q w => sourceFutureNoiseKernel ρ m y (w, q)
                let o : ℝ → ℝ → ℝ := fun q w => (f q w - f q (-w)) / 2
                let e : ℝ → ℝ → ℝ := fun q w => (f q w + f q (-w)) / 2
                (∀ w q : ℝ,
                  DifferentiableAt ℝ (o q) w ∧
                  DifferentiableAt ℝ (e q) w ∧
                  DifferentiableAt ℝ (fun r : ℝ => deriv (e q) r) w) ∧
                (i ≤ n / 2 → ∀ w q : ℝ,
                  |deriv (o q) w| ≤ C * ((n : ℝ) * |mu| + (n : ℝ) * m3) ∧
                  |deriv (fun r : ℝ => deriv (e q) r) w| ≤ C) ∧
                (n / 2 < i → max (L2 * gamma ^ 2) (y ^ 2) ≤ T →
                  ∀ w q : ℝ,
                    |deriv (o q) w| ≤ C * y *
                      ((n : ℝ) * |mu| / Real.sqrt T +
                        (n : ℝ) * m3 / (Real.sqrt T) ^ 3) ∧
                    |deriv (fun r : ℝ => deriv (e q) r) w| ≤
                      C * y / (Real.sqrt T) ^ 3)

end Shao.Probability
```

The last denominators are exactly T^(1/2) and T^(3/2) for the actual positive long-time T. Pointwise bounds for every real w,q express the source's full-space supremum claim. No short-time local w guard occurs. The universal differentiability assertion retains m=0; the late positive-clock branch excludes it by its actual hypotheses, rather than by dropping the endpoint from the quantifiers.


drafts/c12-centered-characteristic/long-early-kernel-source-contract.md SHA256 949b910427bba705b22996c6d57d842d4ab962d935553d94e267cad3f5665dd1

# Source contract: realkernel(i)/(ii), early and long-time full-space estimates

Read-only source: supplement LF621–641 (full realkernel(i)/(ii) statement), LF2342–2366 (actual Fourier transform and odd/even inverses), and LF2464–2564 (four-frequency decomposition and parameter payments). Main LF373–388 permits sufficiently small absolute epsilon0 and epsilon<=epsilon0/2. The actual conditional law is rho=cond nu0 {|a|<=epsilon/(1+x)}, with original probability nu0, finite second moment, n*int a^2=1 and original mean0. No mean0 or symmetry is asserted for rho. The candidate uses only the original truncationBudget<=epsilon^3/8 part of the source small-budget conditions. A sufficiently smaller common absolute epsilon0 will also pay early gamma-smallness; no extra source tail or kernel conclusion is assumed.

The one public result gives the actual sourceFutureNoiseKernel's true odd first and even standard nested second spatial derivatives, everywhere in w,q. For i<=n/2 it proves the source bounds C*(n*abs(mu)+n*m3) and C. For n/2<i with T>=(L2*gamma^2) max y^2 it proves C*y*(n*abs(mu)/sqrt(T)+n*m3/sqrt(T)^3) and C*y/sqrt(T)^3. The displayed denominators equal the source powers once the true long T>0 is proved. There is no abs(w)<=y/16 restriction; cos(u*w) is independent of the r/v integral and bounded by1, so the unshifted genuine k0 sine mark is used throughout.

Actual source parameter payments are explicit. Accepted sourceTruncation_law_data and variance_bounds supply probability rho, its real finite moments/support h_x=epsilon/(1+x), positive actual V, 3/4<=n*m2<=4/3 and m2 comparable to V. SourceFourierScale supplies gamma>0, m2<=gamma^2, gamma<=2*h_x, gamma comparable to n*m3 and the retained mean payment. Thus y>=gamma is genuinely positive. For the low-frequency rectangle use fixed kappa=1/128. For its outside-v region aStar=gamma/kappa=128*gamma; for the high-frequency outside cone use aStar=4*h_x. Both outside32 conditions are paid from the actual h_x<=epsilon, y<=2 and the universal epsilon threshold: if delta>0 is the accepted outside-tail constant, choose epsilon0<=delta/1024, giving (128*gamma)*y<=512*epsilon<=delta and (4*h_x)*y<=8*epsilon<=delta. No freely assumed h*y or gamma*y smallness remains.

Take the fixed frequency-clock threshold L2=16384 (or an equivalent larger fixed choice recorded in the proof), so20<=L2 and kappa*sqrt(L2)>=1. A further universal reduction of epsilon0 is explicitly permitted and will ensure L2*(2*epsilon0)^2<=3/8. For i<=n/2 the actual remaining clock satisfies T>=3/8, and gamma<=2*h_x<=2*epsilon0 then proves L2*gamma^2<=T. This is the complete early-scale payment; it does not silently use the separate source eta0 condition. Since the source allows shrinking its absolute epsilon0, its original epsilon choice satisfies this declared universal threshold. The candidate does not purport to derive a numerical epsilon choice that the paper did not fix.

The four actual frequency regions are the low rectangle L={abs(u)<=kappa/gamma,abs(v)<=kappa*abs(u)/gamma}, low-u outside L, high-u inside the genuine h_x cone C={u!=0,abs(v)<=abs(u)/(4*h_x)}, and high-u outside C. Their union covers the pair plane up to the null u0 line; no low region is silently replaced by the cone. The accepted actual odd-power normalized Gaussian bound and zero-order damping control D and E on L. Actual k0 mark global v-L1 and weighted-v-L1 give the low odd integral bound C*y*[m*abs(mu)*T^-3/2+m*m3*(T^-5/2+T^-3/2+y*T^-2)] and the even bound C*y*T^-3/2. Gaussian moment integrability is proved rather than assumed.

For high-u inside C use only the zero-order projection of accepted full(c), namely genuine signed raw powers times Xi bounded by C/(T^6*abs(u)^12), after sourceTruncation_fullNoise_highFrequency_derivatives pays m>=16 and all clock/frequency guards. Throughout use the genuine global mark bound min(y*abs(u),1+sqrt(y*abs(u)))<=y*abs(u). The resulting integer-power high-cone tail budgets are C*y*gamma^10/T^6 for odd and C*y*gamma^9/T^6 for even. They suffice for the final source(i)/(ii) bounds and do not claim the sharper displayed highlong subregion expression. For low-u/outside L, actual outside32 with aStar=128*gamma gives C*y*gamma^2 and C*y*gamma^3. For high-u/outside C, retain the actual sine factor min(y*abs(u),1)<=y*abs(u); outside32 with aStar=4*h_x then gives C*y*h_x^31*gamma^29 and C*y*h_x^31*gamma^28. These are genuine integrals of the actual marks and spectra, not free regional-budget assumptions.

To finish early, use3/8<=T<=4/3, y<=2, the explicit small h_x/gamma bounds and gamma comparable to n*m3. To finish long, use y^2<=T<=4/3, gamma<=y, m<=n and the sharper actual m<= (4/3)*T*n from n*m2>=3/4. For the high cone, gamma<=sqrt(T) gives gamma^9<=(sqrt(T))^9. Thus the even budget is at most C*y/sqrt(T)^3; the odd budget has the extra factor gamma<=2*n*m3. The actual outside contributions are absorbed using the paid h_x,gamma<=1, T<=4/3 and gamma comparable to n*m3. All constants precede the original law and source parameters.

This unit owns long/early realkernel(i)/(ii), not the short-time five-region estimates or time summation assigned to the other author. It consumes exact accepted old producers without redoing their proofs, and does not claim the regulator comparison, final C1/C2 theorem, large-y regime or source root closure.
