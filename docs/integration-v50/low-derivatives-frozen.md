# Root exact freeze: low-frequency actual D/W and marked regions 1/2

Root fully read all three complete inputs and original supplement LF2370–2397, LF2583–2638 and LF3419–3507. The current marked-outside author is authorized first to implement new Shao/Probability/QuadraticFullNoiseLowDerivatives.lean, then new Shao/Probability/QuadraticFullNoiseMarkedLowRegions.lean. Exactly one producer and two consumer public theorems are frozen below. Old frozen modules must remain byte-identical.

The explicit kappa<=1/128 is the declared fixed-small-frequency realization. h<=1 and 4*h*y<=delta in Region2 are explicit deterministic scope guards paid later by the original source choice h=epsilon0/(1+y); the raw law assumptions alone do not imply them. All constants precede the law/scale parameters. Preserve actual conditional law, D/W, standard second derivatives, moving two-dimensional region, integrability, y^-2, endpoints and the original region2 origin. No generic supplied D/W envelope or same-strength premise may replace the actual producer.

Reuse accepted odd-power Gaussian/low-frequency damping and noise/cone/global derivatives. The whole-real-line identity is a separate active producer. This freeze closes only the three displayed analytic source dependencies; source adapter, inversion assembly, time/probability bounds and original C1/C2 roots remain OPEN. Server-only targeted checks and the existing root lock/lease apply. One qualified final independent complete source/proof/all-owned actual-type/value review and exact kernel/transitive-axiom evidence per final module suffice; unchanged old dependencies are reused.

drafts/c12-cone-derivatives/region12-low-derivative-candidate-declarations.md SHA256 a9e74e1210c2cf94fcaa5d3ba0b6a303f64941fc4c8bf4ffdc11a5725034d948

# Actual low-frequency D/W derivative producer — complete candidate

State: AWAITING_ROOT_FREEZE; no production or new Lean gate started.
Proposed module: Shao.Probability.QuadraticFullNoiseLowDerivatives.
This pays the actual low-frequency product bounds needed by Region1/2.
The supplied premises are the original conditional source data and scale
guards; no derivative estimate, integrability or envelope is a premise.

```lean
import Shao.Probability.QuadraticCharacteristicOddPower
import Shao.Probability.QuadraticFullNoiseGlobalOddEven
import Shao.Probability.QuadraticFullNoiseConeDerivatives
set_option autoImplicit false
namespace Shao.Probability
open MeasureTheory ProbabilityTheory
theorem sourceTruncation_odd_even_fullNoise_lowFrequency_derivatives :
    ∃ C : ℝ, 0 < C ∧
      ∀ (ν0 : Measure ℝ), IsProbabilityMeasure ν0 →
        ∀ n : ℕ, Integrable (fun z : ℝ => z ^ 2) ν0 →
          (n : ℝ) * (∫ z : ℝ, z ^ 2 ∂ν0) = 1 →
          (∫ z : ℝ, z ∂ν0) = 0 →
          ∀ x epsilon : ℝ, 0 ≤ x → 0 < epsilon → epsilon ≤ 1 / 2 →
            Shao.truncationBudget ν0 n x ≤ epsilon ^ 3 / 8 →
            ∀ i : ℕ, i ≤ n → ∀ h kappa L2 : ℝ,
              epsilon / (1 + x) ≤ h → 0 < kappa → kappa ≤ (1 / 128 : ℝ) →
                20 ≤ L2 → 1 ≤ kappa * Real.sqrt L2 →
                let ρ : Measure ℝ :=
                  ProbabilityTheory.cond ν0 {z | |z| ≤ epsilon / (1 + x)}
                let m : ℕ := n - i
                let mu : ℝ := ∫ z : ℝ, z ∂ρ
                let m3 : ℝ := ∫ z : ℝ, |z| ^ 3 ∂ρ
                let T : ℝ := (m : ℝ) * (∫ z : ℝ, z ^ 2 ∂ρ)
                let gamma : ℝ := m3 / variance (id : ℝ → ℝ) ρ
                L2 * gamma ^ 2 ≤ T →
                ∀ u v : ℝ, |u| ≤ kappa / gamma → |v| ≤ kappa * |u| / gamma →
                  let A : ℝ := (m : ℝ) * |mu| * |u| +
                    (m : ℝ) * m3 * (|u| ^ 3 + |u| * |v|)
                  let B : ℝ := (m : ℝ) * |mu| + (m : ℝ) * m3 * (u ^ 2 + |v|)
                  let Q : ℝ := Real.sqrt T * (1 + Real.sqrt T * |u|)
                  let G : ℝ := Real.exp (-T * u ^ 2 / 256)
                  let D : ℝ → ℂ := fun r =>
                    (quadraticChar ρ r v ^ m - quadraticChar ρ (-r) v ^ m) / 2 *
                      quadraticFullNoiseChar ρ r v
                  let W : ℝ → ℂ := fun r => (r : ℂ) *
                    ((quadraticChar ρ r v ^ m + quadraticChar ρ (-r) v ^ m) / 2 *
                      quadraticFullNoiseChar ρ r v)
                  ‖deriv (fun r : ℝ => deriv D r) u‖ ≤ C * G *
                    ((m : ℝ) * m3 * |u| + (Q + gamma) * B +
                      (T * (1 + T * u ^ 2) + gamma * Q + h * gamma) * A) ∧
                  (u ≠ 0 → |v| ≤ |u| / (4 * h) →
                    ‖deriv (fun r : ℝ => deriv D r) u‖ ≤ C * G *
                      ((m : ℝ) * m3 * |u| + (Q + 1 / |u|) * B +
                        (T * (1 + T * u ^ 2) + Q / |u| + 1 / u ^ 2) * A) ∧
                    ‖deriv (fun r : ℝ => deriv W r) u‖ ≤ C * G *
                      (T * |u| * (1 + T * u ^ 2) + Q + 1 / |u|))
end Shao.Probability
```


drafts/c12-cone-derivatives/region12-marked-candidate-declarations.md SHA256 37583b05bf74f4ae847ef4ff692b0822d3ab941e337b94594bbf2c651d853b40

# Actual Region1/2 marked post-IBP — complete candidates

State: AWAITING_ROOT_FREEZE; no production module or Lean gate started.
Proposed module: Shao.Probability.QuadraticFullNoiseMarkedLowRegions.
The explicit kappa upper bound realizes the accepted low-frequency damping scale.
Region2 retains the actual outside smallness and bounded source h; its origin
is included by the exact set difference from the source cone.

```lean
import Shao.Probability.QuadraticCharacteristicOddPower
import Shao.Probability.SourceKernelMarkedOutside
import Shao.Probability.SourceMarkFourierNorms
set_option autoImplicit false
namespace Shao.Probability
open MeasureTheory ProbabilityTheory
theorem sourceTruncation_odd_even_fullNoise_region1_actual_marked_postIBP :
    ∃ C : ℝ, 0 < C ∧
      ∀ (ν0 : Measure ℝ), IsProbabilityMeasure ν0 →
        ∀ n : ℕ, Integrable (fun z : ℝ => z ^ 2) ν0 →
          (n : ℝ) * (∫ z : ℝ, z ^ 2 ∂ν0) = 1 →
          (∫ z : ℝ, z ∂ν0) = 0 →
          ∀ x epsilon : ℝ, 0 ≤ x → 0 < epsilon → epsilon ≤ 1 / 2 →
            Shao.truncationBudget ν0 n x ≤ epsilon ^ 3 / 8 →
            ∀ i : ℕ, i ≤ n → ∀ h kappa L2 y w sigma : ℝ,
              epsilon / (1 + x) ≤ h → 0 < kappa → kappa ≤ (1 / 128 : ℝ) → 20 ≤ L2 →
                1 ≤ kappa * Real.sqrt L2 → 0 < y → y ≤ 2 →
                |w| ≤ y / 16 → |sigma| = 1 →
                let ρ : Measure ℝ :=
                  ProbabilityTheory.cond ν0 {z | |z| ≤ epsilon / (1 + x)}
                let m : ℕ := n - i
                let T : ℝ := (m : ℝ) * (∫ z : ℝ, z ^ 2 ∂ρ)
                let gamma : ℝ := (∫ z : ℝ, |z| ^ 3 ∂ρ) / variance (id : ℝ → ℝ) ρ
                let mu : ℝ := ∫ z : ℝ, z ∂ρ
                let m3 : ℝ := ∫ z : ℝ, |z| ^ 3 ∂ρ
                L2 * gamma ^ 2 ≤ T → T < y ^ 2 →
                let a : ℝ → ℝ := fun r =>
                  sourceKernelCutoff r / (Real.sqrt r + sigma * w / y) ^ 2
                let B : ℝ → ℝ → ℂ := fun u v =>
                  ∫ r : ℝ, ((a r * Real.sin (u * (y * Real.sqrt r + sigma * w)) : ℝ) : ℂ) *
                    Complex.exp (-(((v * r : ℝ) : ℂ) * Complex.I))
                let D : ℝ → ℝ → ℂ := fun u v =>
                  (quadraticChar ρ u v ^ m - quadraticChar ρ (-u) v ^ m) /
                    2 * quadraticFullNoiseChar ρ u v
                let E : ℝ → ℝ → ℂ := fun u v =>
                  (quadraticChar ρ u v ^ m + quadraticChar ρ (-u) v ^ m) /
                    2 * quadraticFullNoiseChar ρ u v
                let W : ℝ → ℝ → ℂ := fun u v => (u : ℂ) * E u v
                let R : Set (ℝ × ℝ) := {p | |p.1| ≤ kappa / gamma ∧ |p.2| ≤ kappa * |p.1| / gamma ∧ p.1 ≠ 0 ∧ |p.2| ≤ |p.1| / (4 * h)}
                let Iodd : ℝ × ℝ → ℝ := fun p =>
                  ‖deriv (fun r : ℝ => deriv (fun t : ℝ => D t p.2) r) p.1‖ *
                    ‖B p.1 p.2‖ / y ^ 2
                let Ieven : ℝ × ℝ → ℝ := fun p =>
                  ‖deriv (fun r : ℝ => deriv (fun t : ℝ => W t p.2) r) p.1‖ *
                    ‖B p.1 p.2‖ / y ^ 2
                IntegrableOn Iodd R ∧ IntegrableOn Ieven R ∧
                  (∫ p in R, Iodd p) ≤ C / y ^ 2 * ((n : ℝ) * m3 + T * ((n : ℝ) * |mu|)) * (1 + Real.sqrt y * T ^ (-(1 / 4 : ℝ))) ∧
                  (∫ p in R, Ieven p) ≤ C / y ^ 2 * (1 + Real.sqrt y * T ^ (-(1 / 4 : ℝ)))

theorem sourceTruncation_odd_even_fullNoise_region2_actual_marked_postIBP :
    ∃ C delta : ℝ, 0 < C ∧ 0 < delta ∧ delta ≤ (1 / 16 : ℝ) ∧
      ∀ (ν0 : Measure ℝ), IsProbabilityMeasure ν0 →
        ∀ n : ℕ, Integrable (fun z : ℝ => z ^ 2) ν0 →
          (n : ℝ) * (∫ z : ℝ, z ^ 2 ∂ν0) = 1 →
          (∫ z : ℝ, z ∂ν0) = 0 →
          ∀ x epsilon : ℝ, 0 ≤ x → 0 < epsilon → epsilon ≤ 1 / 2 →
            Shao.truncationBudget ν0 n x ≤ epsilon ^ 3 / 8 →
            ∀ i : ℕ, i ≤ n → ∀ h kappa L2 y w sigma : ℝ,
              epsilon / (1 + x) ≤ h → h ≤ 1 → 0 < kappa → kappa ≤ (1 / 128 : ℝ) → 20 ≤ L2 →
                1 ≤ kappa * Real.sqrt L2 → 0 < y → y ≤ 2 →
                |w| ≤ y / 16 → |sigma| = 1 →
                let ρ : Measure ℝ :=
                  ProbabilityTheory.cond ν0 {z | |z| ≤ epsilon / (1 + x)}
                let m : ℕ := n - i
                let T : ℝ := (m : ℝ) * (∫ z : ℝ, z ^ 2 ∂ρ)
                let gamma : ℝ := (∫ z : ℝ, |z| ^ 3 ∂ρ) / variance (id : ℝ → ℝ) ρ
                let mu : ℝ := ∫ z : ℝ, z ∂ρ
                let m3 : ℝ := ∫ z : ℝ, |z| ^ 3 ∂ρ
                L2 * gamma ^ 2 ≤ T → T < y ^ 2 → (4 * h) * y ≤ delta →
                let a : ℝ → ℝ := fun r =>
                  sourceKernelCutoff r / (Real.sqrt r + sigma * w / y) ^ 2
                let B : ℝ → ℝ → ℂ := fun u v =>
                  ∫ r : ℝ, ((a r * Real.sin (u * (y * Real.sqrt r + sigma * w)) : ℝ) : ℂ) *
                    Complex.exp (-(((v * r : ℝ) : ℂ) * Complex.I))
                let D : ℝ → ℝ → ℂ := fun u v =>
                  (quadraticChar ρ u v ^ m - quadraticChar ρ (-u) v ^ m) /
                    2 * quadraticFullNoiseChar ρ u v
                let E : ℝ → ℝ → ℂ := fun u v =>
                  (quadraticChar ρ u v ^ m + quadraticChar ρ (-u) v ^ m) /
                    2 * quadraticFullNoiseChar ρ u v
                let W : ℝ → ℝ → ℂ := fun u v => (u : ℂ) * E u v
                let R : Set (ℝ × ℝ) := {p | |p.1| ≤ kappa / gamma ∧ |p.2| ≤ kappa * |p.1| / gamma ∧ ¬(p.1 ≠ 0 ∧ |p.2| ≤ |p.1| / (4 * h))}
                let Iodd : ℝ × ℝ → ℝ := fun p =>
                  ‖deriv (fun r : ℝ => deriv (fun t : ℝ => D t p.2) r) p.1‖ *
                    ‖B p.1 p.2‖ / y ^ 2
                let Ieven : ℝ × ℝ → ℝ := fun p =>
                  ‖deriv (fun r : ℝ => deriv (fun t : ℝ => W t p.2) r) p.1‖ *
                    ‖B p.1 p.2‖ / y ^ 2
                IntegrableOn Iodd R ∧ IntegrableOn Ieven R ∧
                  (∫ p in R, Iodd p) ≤ C / y ^ 2 * T * ((n : ℝ) * |mu| + (n : ℝ) * m3) ∧
                  (∫ p in R, Ieven p) ≤ C / y ^ 2 * (Real.sqrt T + gamma)
end Shao.Probability
```


drafts/c12-cone-derivatives/region12-marked-source-contract.md SHA256 a5f67737611638e48a361d3148bbc2290d69b7e6767d3f7886317a035f76f3ea

# Actual Region1/2 marked post-IBP source contract

Original supplement LF2354–2357 defines actual D and E; LF2370–2397 gives
the fixed small low-frequency kappa and actual odd-power difference.
LF2571–2590 gives the actual signed sine amplitude after whole-u IBP and
the five exact regions. LF2583–2638 and LF3419–3507 give the target Region1/2
post-IBP norm bounds, their low-frequency derivative tables, Gaussian moments
and the outside-v integration. Original read-only source and its full hash
remain those of the completed marked-outside source contract.

The two complete public statements are in region12-marked-candidate-declarations.md.
They concern actual two-dimensional positive norm integrals with amplitude
chi/(sqrt(r)+sigma*w/y)^2, actual conditional truncation law, actual nested
second u derivatives of D and W=uE, and the explicit y^-2 factor. They assert
neither whole-u IBP equality nor any probability/Fourier inversion identity.

The source low-frequency kappa is fixed sufficiently small. The explicit
0<kappa<=1/128 realizes the accepted quadraticChar_lowFrequency_damping
interface rather than silently allowing all positive kappa. L2>=20 and
1<=kappa*sqrt(L2) retain the original sufficiently large L2 scale. The guards
L2*gamma^2<=T<Ty^2 (written T<y^2 in Lean) retain the short source regime.
The conditional-law bridge pays probability, third moments, positive variance,
gamma>0, m2<=gamma^2, m>=20, n*m2 in [3/4,4/3], bounded n*|mu| and m2<=4V.
In particular T>0 and gamma<y are derived, never assumed as replacement data.

R1 is exactly L intersect C, including the source exclusion u!=0 and the
closed cone boundary. R2 is exactly L setminus C. Its origin (u,v)=(0,0)
is included; a proof may dispose of that singleton only via a real null-set
argument, not by silently changing the public region to a strict inequality.

For Region2 the source chooses h=epsilon0/(1+y) with epsilon0 sufficiently
small. The current deterministic interface retains explicit h<=1 and
(4*h)*y<=delta. These guards are a transparent way to pay the source's bounded
h and actual outside-v smallness; the later source adapter must pay them for
its chosen epsilon0. delta is chosen before every source/scale parameter and
is positive, <=1/16. No existing raw-law assumptions alone are claimed to
imply that additional smallness. Region1 uses global marked norms and does
not need this outside smallness.

The actual missing producer is declared completely in
region12-low-derivative-candidate-declarations.md. Accepted
quadraticChar_odd_power_lowFrequency_normalized already supplies the exact
odd-power table with Gaussian exp(-T*u^2/256). The new producer must multiply
the actual noise and differentiate the actual D/W, using accepted cone and
global noise derivatives. It must also pay the even-power Gaussian derivative
budget from the actual remaining powers and low-frequency damping. It cannot
assume any supplied D/W bound. This is a substantive source dependency,
to be frozen and implemented before the final marked consumers.

Region1 then uses actual global mark L1 and |v|-weighted L1, including the
sine minimum at u=0. Its Gaussian inverse-u moment must be proved using that
minimum; replacing the sine factor by 1+sqrt(y|u|) at u=0 would diverge.
The final factor is exactly 1+sqrt(y)*T^(-1/4), with raw n*m3 and T*n*|mu|.
Region2 uses the actual N0=32 outside sine estimates for weights0/1 and paid
u moments through degree5, with the source coefficients converted through
n*m2>=3/4. The even part may consume the accepted actual global D/W derivative
producer directly. Joint measurability and genuine moving-region Fubini are
required throughout, as in the completed Region3/5 and Region4 consumers.

No arbitrary amplitude, oscillatory premise, conclusion-equivalent envelope,
fixed-v integral product, new probability assumption, whole-u boundary equality,
de-smoothing, time summation or C1/C2 closure is asserted. Existing frozen
marked modules remain unchanged. Production ownership is requested first for
QuadraticFullNoiseLowDerivatives, then QuadraticFullNoiseMarkedLowRegions.
