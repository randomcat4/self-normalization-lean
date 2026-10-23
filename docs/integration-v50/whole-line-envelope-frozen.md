# Root exact replacement freeze: actual uniform-v derivative envelope

Root fully read the complete declaration and complete source/payment contract below. This is the sole approved third public declaration in the current SourceOddEvenWholeLineIBP.lean, replacing the fixed-v moment proposal before its implementation. Preserve the original two frozen public types unchanged. B is genuinely constructed after fixed law/support/m and before every u/v; it dominates the actual six factors uniformly in v, has all natural polynomial L1 moments and is nonnegative. No envelope or decay premise may be introduced. One final exact-source object/kernel/all-owned type/value/axiom receipt and one full independent review cover the final three-public module; do not repeat unchanged old dependencies.

The subsequent actual marked pair-integral/IBP consumer must pay joint measurability and genuine Fubini using this uniform envelope and the actual amplitude/mark bounds. This statement alone does not identify probability contributions or close regional/C1/C2 roots.

Candidate SHA256 834ef0694192f0b3975d015a6c8a62ad910effdcedb405f1209e4be54571887e.

# Uniform actual envelope for the marked whole-line IBP consumer

Status: CANDIDATE_PENDING_ROOT_FREEZE. This replaces the unimplemented fixed-v moment candidate9436. The existing two public IBP declaration types stay byte-for-byte unchanged. Proposed sole additional public theorem in SourceOddEvenWholeLineIBP.lean:

```lean
namespace Shao.Probability

open MeasureTheory ProbabilityTheory

theorem quadraticFullNoise_odd_even_derivative_envelope
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (h3 : Integrable (fun a : ℝ => |a| ^ 3) ν)
    (hV : 0 < variance (id : ℝ → ℝ) ν)
    (h : ℝ) (hh : 0 < h) (hs : ∀ᵐ a : ℝ ∂ν, |a| ≤ h)
    (m : ℕ) :
    let D : ℝ → ℝ → ℂ := fun v u =>
      ((quadraticChar ν u v) ^ m - (quadraticChar ν (-u) v) ^ m) / 2 *
        quadraticFullNoiseChar ν u v
    let E : ℝ → ℝ → ℂ := fun v u =>
      ((quadraticChar ν u v) ^ m + (quadraticChar ν (-u) v) ^ m) / 2 *
        quadraticFullNoiseChar ν u v
    let W : ℝ → ℝ → ℂ := fun v u => (u : ℂ) * E v u
    ∃ B : ℝ → ℝ, (∀ u : ℝ, 0 ≤ B u) ∧
      (∀ k : ℕ, Integrable (fun u : ℝ => |u| ^ k * B u)) ∧
      ∀ u v : ℝ,
        ‖D v u‖ ≤ B u ∧
        ‖deriv (D v) u‖ ≤ B u ∧
        ‖deriv (fun t : ℝ => deriv (D v) t) u‖ ≤ B u ∧
        ‖W v u‖ ≤ B u ∧
        ‖deriv (W v) u‖ ≤ B u ∧
        ‖deriv (fun t : ℝ => deriv (W v) t) u‖ ≤ B u

end Shao.Probability
```

Source contract and immediate consumption: supplement LF2575–2583 justifies twice-u integration by parts for the actual D and uE by the smooth scalar noise's rapid decay. Commuting the true marked r/u/v integrals requires a bound uniform in v, because accepted mark-v-L1 grows as1+sqrt(y*|u|), bounded for each actual y by a constant times1+|u|. The proposed B is one genuine common nonnegative envelope for all six displayed actual derivatives at every u,v; it is not supplied as an assumption. Its k0/k1 L1 moments pay that marked pair-integrability. The stronger all-natural-k version is directly provided by the same actual Schwartz factor and preserves the source's rapid-decay mechanism.

Proof payment: bounded original/chord laws give u derivatives through order2 with norm bounds independent of both u and v. The v dependence occurs only in unit complex phases. Finite products, signed raw-law powers, reflection and half-sum/difference preserve such uniform C2 bounds, with constants depending only on the fixed law,m and support data. Actual gamma=(int|x|^3)/variance>0 is paid from h3 and hV, with no gamma<=2h assumption. The exact actual Sγ(u)=sourceScalarChar(gamma*u) is a Schwartz function after an explicit nonzero linear rescaling of the Fourier transform of the genuine scalar density. The actual u*Sγ is also Schwartz. Let their actual first/second Schwartz derivatives be S1/S2 and U1/U2. If C bounds both actual raw/chord prefixes and their first two u derivatives uniformly in v, one may take the explicit nonnegative function

  B(u)=C*(norm(S)+2*norm(S1)+norm(S2)+norm(u*S)+2*norm(U1)+norm(U2)).

The real product rules prove all six bounds, and SchwartzMap.integrable_pow_mul pays every genuine polynomially weighted B-L1 integral. No Fourier-L1, derivative bound, endpoint decay or symmetry/zero-mean conclusion is supplied as a hypothesis. Every m including0 and every u/v is retained. This is an actual common-envelope theorem, not a fixed-v slice statement and not a region estimate or final C1/C2 claim. The original two exact whole-line IBP theorem statements remain unchanged and already pass their source-bound targeted check.
