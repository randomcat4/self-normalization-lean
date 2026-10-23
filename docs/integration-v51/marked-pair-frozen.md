# Root exact declaration freeze: actual marked odd/even twice-IBP pair inverse

Root fully read both complete public declarations and the complete payment/source contract below, against original supplement LF2354–2366 and LF2570–2583. Author common_highfreq_author is authorized next to implement new Shao/Probability/SourceOddEvenMarkedIBP.lean after sealing the current whole-line module. Preserve every displayed binder, actual conditional-free law, actual D/uE, standard real derivatives, positive-v phase, both actual signed amplitudes/shifts, pair L1 statements and exact coefficients. All positive y/every m/q and |w|<=y/16 are the precise scope; no y<=2 or symmetry/mean-zero assumption is added.

The proof must first establish u/r Fubini at fixed v, then actual per-phase whole-u IBP, then genuine marked (u,v) pair L1 via the actual uniform-v B and actual mark-v norms. It must not claim triple absolute integrability from uniform B. Source support pays nonzero phases and y^-2 exactly. Existing qualified amplitudes, kernels and inverse proofs are reused. One fresh full final independent semantic review and the actual source-bound kernel/all-owned type/value/transitive-axiom evidence are required for this new module; old dependencies remain unchanged.

This is the equality connecting actual derivatives to post-IBP marked integrals, without a regional norm bound, probability comparison or C1/C2 closure. Continue the next source dependency after the completed unit.

drafts/c12-centered-characteristic/marked-ibp-candidate-declarations.md SHA256 415f404a0412ea57ea1c8e849ea9a10d58574fe28ca9120b365d58e68e0d2fdf

# Actual marked pair inverse identities after twice-u integration by parts

Status: CANDIDATE_PENDING_ROOT_FREEZE. Proposed module Shao/Probability/SourceOddEvenMarkedIBP.lean. Exactly two public theorems, no new public definitions.

```lean
namespace Shao.Probability

open MeasureTheory ProbabilityTheory

theorem sourceFutureNoiseKernel_odd_derivative_markedIBP
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (h3 : Integrable (fun a : ℝ => |a| ^ 3) ν)
    (hV : 0 < variance (id : ℝ → ℝ) ν)
    (h : ℝ) (hh : 0 < h) (hs : ∀ᵐ a : ℝ ∂ν, |a| ≤ h)
    (m : ℕ) (y : ℝ) (hy : 0 < y) (w q : ℝ) (hw : |w| ≤ y / 16) :
    let f : ℝ → ℝ := fun r => sourceFutureNoiseKernel ν m y (r, q)
    let o : ℝ → ℝ := fun r => (f r - f (-r)) / 2
    let D : ℝ → ℝ → ℂ := fun v u =>
      ((quadraticChar ν u v) ^ m - (quadraticChar ν (-u) v) ^ m) / 2 *
        quadraticFullNoiseChar ν u v
    let Aplus : ℝ → ℝ := fun r => sourceKernelCutoff r / (Real.sqrt r + w / y) ^ 2
    let Aminus : ℝ → ℝ := fun r => sourceKernelCutoff r / (Real.sqrt r - w / y) ^ 2
    let Gplus : ℝ × ℝ → ℂ := fun ξ =>
      Complex.exp ((((ξ.2 * q : ℝ) : ℂ)) * Complex.I) *
        sourceMarkSine Aplus y ξ.1 w ξ.2 *
          deriv (fun t : ℝ => deriv (D ξ.2) t) ξ.1
    let Gminus : ℝ × ℝ → ℂ := fun ξ =>
      Complex.exp ((((ξ.2 * q : ℝ) : ℂ)) * Complex.I) *
        sourceMarkSine Aminus y ξ.1 (-w) ξ.2 *
          deriv (fun t : ℝ => deriv (D ξ.2) t) ξ.1
    DifferentiableAt ℝ o w ∧
      Integrable Gplus (volume : Measure (ℝ × ℝ)) ∧
      Integrable Gminus (volume : Measure (ℝ × ℝ)) ∧
      ((deriv o w : ℝ) : ℂ) =
        (-Complex.I / (((2 * Real.pi) ^ 2 * y ^ 2 : ℝ) : ℂ)) *
          ((∫ ξ : ℝ × ℝ, Gplus ξ) + ∫ ξ : ℝ × ℝ, Gminus ξ)

theorem sourceFutureNoiseKernel_even_second_markedIBP
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (h3 : Integrable (fun a : ℝ => |a| ^ 3) ν)
    (hV : 0 < variance (id : ℝ → ℝ) ν)
    (h : ℝ) (hh : 0 < h) (hs : ∀ᵐ a : ℝ ∂ν, |a| ≤ h)
    (m : ℕ) (y : ℝ) (hy : 0 < y) (w q : ℝ) (hw : |w| ≤ y / 16) :
    let f : ℝ → ℝ := fun r => sourceFutureNoiseKernel ν m y (r, q)
    let e : ℝ → ℝ := fun r => (f r + f (-r)) / 2
    let E : ℝ → ℝ → ℂ := fun v u =>
      ((quadraticChar ν u v) ^ m + (quadraticChar ν (-u) v) ^ m) / 2 *
        quadraticFullNoiseChar ν u v
    let W : ℝ → ℝ → ℂ := fun v u => (u : ℂ) * E v u
    let Aplus : ℝ → ℝ := fun r => sourceKernelCutoff r / (Real.sqrt r + w / y) ^ 2
    let Aminus : ℝ → ℝ := fun r => sourceKernelCutoff r / (Real.sqrt r - w / y) ^ 2
    let Gplus : ℝ × ℝ → ℂ := fun ξ =>
      Complex.exp ((((ξ.2 * q : ℝ) : ℂ)) * Complex.I) *
        sourceMarkSine Aplus y ξ.1 w ξ.2 *
          deriv (fun t : ℝ => deriv (W ξ.2) t) ξ.1
    let Gminus : ℝ × ℝ → ℂ := fun ξ =>
      Complex.exp ((((ξ.2 * q : ℝ) : ℂ)) * Complex.I) *
        sourceMarkSine Aminus y ξ.1 (-w) ξ.2 *
          deriv (fun t : ℝ => deriv (W ξ.2) t) ξ.1
    DifferentiableAt ℝ e w ∧ DifferentiableAt ℝ (fun r : ℝ => deriv e r) w ∧
      Integrable Gplus (volume : Measure (ℝ × ℝ)) ∧
      Integrable Gminus (volume : Measure (ℝ × ℝ)) ∧
      ((deriv (fun r : ℝ => deriv e r) w : ℝ) : ℂ) =
        ((((2 * Real.pi) ^ 2 * y ^ 2 : ℝ) : ℂ)⁻¹) *
          ((∫ ξ : ℝ × ℝ, Gplus ξ) + ∫ ξ : ℝ × ℝ, Gminus ξ)

end Shao.Probability
```

The actual shifts of the inner sine mark are w and-w; the modified amplitudes contain theta=w/y and-theta. The positive v phase is retained. The coefficients are exactly-i/((2pi)^2*y^2) and+1/((2pi)^2*y^2). The outputs are actual standard spatial derivatives of the real odd/even kernels, and both post-IBP pair integrands are explicitly absolutely integrable.


drafts/c12-centered-characteristic/marked-ibp-source-contract.md SHA256 76b90fba208585b78a368cbf607d0336513fa43e69c87227e8e8968fc90d1493

# Source contract: actual marked pair twice-IBP inverse

Read-only source: supplement LF2354–2366 and LF2570–2583. Start from the accepted actual o'/e'' marked pair inverses with2i and-2 divided by(2pi)^2. The real identity sin(u*y*sqrt(r))*cos(u*w)=half sin(u*(y*sqrt(r)+w))+half sin(u*(y*sqrt(r)-w)) yields two positive source phases. The actual cutoff support lies in[1/16,4], so for y>0 and |w|<=y/16 both y*sqrt(r)+/-w>=3y/16 on the cutoff support. Actual D or W=uE satisfies the already frozen full-real-line twice-IBP identity at each of these genuine nonzero phases. Division by a^2 factors y^-2 and gives the actual amplitude chi(r)/(sqrt(r)+/-w/y)^2. No region estimate is claimed.

The two proposed public identities retain the complete original probability law hypotheses, every m including0, every q and all positive y with the exact local w guard. They do not assume mean0, increment symmetry, gamma<=2h, an inverse identity, a derivative envelope or any of the requested marked pair L1 conclusions. The actual common uniform-v derivative envelope B is produced by SourceOddEvenWholeLineIBP; its genuine k0/k1 moments, together with accepted actual amplitude-family C2 data and mark-v-L1 bounds, pay both true post-IBP pair integrands' absolute integrability. All derivatives on D and W are the standard nested u deriv of the actual displayed laws.

The order of integration is essential. The proof first fixes v. Actual compact cutoff amplitudes and the genuine B(u) pay u/r Fubini at that fixed v, before and after twice-u IBP. It establishes the exact fixed-v identity without claiming absolute integrability in(r,u,v) jointly. Then the already r-integrated actual mark Fourier v-L1 bounds and the common uniform-v envelope pay the genuine(u,v) pair L1 on each side. Finally integrate in v and use the justified pair u/v exchange. In particular, the common B alone is not used to infer triple absolute L1 after removing the unit v phase.

Both actual Aplus and Aminus are supplied by SourceKernelAmplitudeFamily at k2, theta=+/-w/y; the required bound |theta|<=1/16 follows from positive y and the source guard. Their global quotient functions and compact supports are actual, including all potential zero denominators outside the cutoff support. This module consumes that accepted producer; it does not redo its smooth family, outside decay, Region3/5 estimates or quantitative low/high-frequency budgets.

The resulting signs are odd -i/((2pi)^2*y^2) and even +1/((2pi)^2*y^2), each multiplying the sum of the two genuine marked pair integrals. No factor2, cos mark or source shift is silently discarded. The root probability/C1/C2 statements remain open.
