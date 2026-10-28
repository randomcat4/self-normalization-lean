# Unit249 exact API and ambient context

Status: local interface reading only, no elaboration, kernel check, proof
implementation or new mathematical qualification. All source references below
are immutable local captures/snapshots. Pinned Lean4.36.0-rc1 and mathlib
807d3836b165983210ee2ecf3cd28f239436949c are recorded; no local toolchain was
probed or invoked.

## Qualified236 public head and complete ambient

The currently qualified source is cb1ed434c1029e674ddff14a1be07ab55b2fb064060acbe92bea389a93f7df8f,
11444 bytes. The same first original object is
99a8ccfe353e26adef88d524e78418952f840906bb0a63ba886156a88a53d716.
Current qualification binds successful native/all-owner audits, complete
independent review and all actual99LF TYPE/0VALUE. Those accepted proofs and
checks are reused exactly, not reviewed or executed again.

```lean
import Shao.Probability.GaussianTail
import Shao.OQ5.P51.BoundedPolylogWindow
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

set_option autoImplicit false

open Filter
open scoped Topology

namespace Shao.OQ6.OriginalExceptionalTailAbsorption

theorem eventually_original_exceptional_payment_absorbed
    (t0 cg : ℝ) (ht0 : 0 < t0) (hcg : 0 < cg) :
    let cWindow : ℝ := min (1 : ℝ) (Real.sqrt t0 / (2 : ℝ))
    0 < cWindow ∧
      ∀ᶠ n : ℕ in atTop,
        4 ≤ n ∧
          (1 : ℝ) ≤ cWindow * Real.rpow (n : ℝ) (1 / 6 : ℝ) ∧
          ∀ z : ℝ, (1 : ℝ) ≤ z →
            z ≤ cWindow * Real.rpow (n : ℝ) (1 / 6 : ℝ) →
            (6 : ℝ) *
                Real.exp (-Shao.OQ5.P51.boundedPolylogMomentOrder t0 n) +
              (2 : ℝ) * Real.exp (-cg * (n : ℝ)) +
              (8 : ℝ) * Real.exp (-(Real.sqrt (n : ℝ)) / (2 : ℝ)) ≤
              Real.exp (-(t0 / (2 : ℝ)) *
                Real.rpow (n : ℝ) (1 / 3 : ℝ)) *
                Shao.standardNormalTail z
```

The current entire actual TYPE follows, with its implicit real instances and literal RHS:

```lean
Shao.OQ6.OriginalExceptionalTailAbsorption.eventually_original_exceptional_payment_absorbed : ∀
  (t0 cg : Real)
  (ht0 : @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) t0)
  (hcg : @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) cg),
  have cWindow : Real :=
    @Min.min.{0} Real Real.instMin (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
      (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
        (Real.sqrt t0)
        (@OfNat.ofNat.{0} Real (nat_lit 2)
          (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
            (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
              (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))));
  And (@LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) cWindow)
    (@Filter.Eventually.{0} Nat
      (fun (n : Nat) =>
        And (@LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) n)
          (And
            (@LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) cWindow
                (Real.rpow (@Nat.cast.{0} Real Real.instNatCast n)
                  (@HDiv.hDiv.{0, 0, 0} Real Real Real
                    (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                    (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                    (@OfNat.ofNat.{0} Real (nat_lit 6)
                      (@instOfNatAtLeastTwo.{0} Real (nat_lit 6) Real.instNatCast
                        (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))
                          (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))))))))
            (∀ (z : Real),
              @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) z →
                @LE.le.{0} Real Real.instLE z
                    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) cWindow
                      (Real.rpow (@Nat.cast.{0} Real Real.instNatCast n)
                        (@HDiv.hDiv.{0, 0, 0} Real Real Real
                          (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                          (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                          (@OfNat.ofNat.{0} Real (nat_lit 6)
                            (@instOfNatAtLeastTwo.{0} Real (nat_lit 6) Real.instNatCast
                              (@Nat.instAtLeastTwoHAddOfNat
                                (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))
                                (@Nat.instNeZeroSucc
                                  (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))))))) →
                  @LE.le.{0} Real Real.instLE
                    (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                      (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                          (@OfNat.ofNat.{0} Real (nat_lit 6)
                            (@instOfNatAtLeastTwo.{0} Real (nat_lit 6) Real.instNatCast
                              (@Nat.instAtLeastTwoHAddOfNat
                                (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))
                                (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))))
                          (Real.exp (@Neg.neg.{0} Real Real.instNeg (Shao.OQ5.P51.boundedPolylogMomentOrder t0 n))))
                        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                          (@OfNat.ofNat.{0} Real (nat_lit 2)
                            (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                              (@Nat.instAtLeastTwoHAddOfNat
                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                                (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
                          (Real.exp
                            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                              (@Neg.neg.{0} Real Real.instNeg cg) (@Nat.cast.{0} Real Real.instNatCast n)))))
                      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                        (@OfNat.ofNat.{0} Real (nat_lit 8)
                          (@instOfNatAtLeastTwo.{0} Real (nat_lit 8) Real.instNatCast
                            (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))
                              (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))))))
                        (Real.exp
                          (@HDiv.hDiv.{0, 0, 0} Real Real Real
                            (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                            (@Neg.neg.{0} Real Real.instNeg (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast n)))
                            (@OfNat.ofNat.{0} Real (nat_lit 2)
                              (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                                (@Nat.instAtLeastTwoHAddOfNat
                                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                                  (@Nat.instNeZeroSucc
                                    (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))))))
                    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                      (Real.exp
                        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                          (@Neg.neg.{0} Real Real.instNeg
                            (@HDiv.hDiv.{0, 0, 0} Real Real Real
                              (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid)) t0
                              (@OfNat.ofNat.{0} Real (nat_lit 2)
                                (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                                  (@Nat.instAtLeastTwoHAddOfNat
                                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                                    (@Nat.instNeZeroSucc
                                      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))))
                          (Real.rpow (@Nat.cast.{0} Real Real.instNatCast n)
                            (@HDiv.hDiv.{0, 0, 0} Real Real Real
                              (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                              (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                              (@OfNat.ofNat.{0} Real (nat_lit 3)
                                (@instOfNatAtLeastTwo.{0} Real (nat_lit 3) Real.instNatCast
                                  (@Nat.instAtLeastTwoHAddOfNat
                                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                    (@Nat.instNeZeroSucc
                                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))))))
                      (Shao.standardNormalTail z)))))
      (@Filter.atTop.{0} Nat Nat.instPreorder))

```

## Pinned square-root full heads and namespace/ambient

Underlying source: {"physicalPath": "/root/rivermind-data/shao-lean-20261021/workspaces/lead-oq56/.lake/packages/mathlib/Mathlib/Analysis/Real/Sqrt.lean", "resolvedPath": "/root/rivermind-data/shao-lean-20261021/lean/.lake/packages/mathlib/Mathlib/Analysis/Real/Sqrt.lean", "sha256": "1f19e1d6722b2f51c2cd676d0b28ede856c7915ac815b597cef4b3919040c204", "bytes": 18522, "pinnedMathlib": "807d3836b165983210ee2ecf3cd28f239436949c"}

Exact pinned lines1–39:

```lean
/-
Copyright (c) 2020 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Floris van Doorn, Yury Kudryashov
-/
module

public import Mathlib.Topology.Instances.NNReal.Lemmas

/-!
# Square root of a real number

In this file we define

* `NNReal.sqrt` to be the square root of a nonnegative real number.
* `Real.sqrt` to be the square root of a real number, defined to be zero on negative numbers.

Then we prove some basic properties of these functions.

## Implementation notes

We define `NNReal.sqrt` as the noncomputable inverse to the function `x ↦ x * x`. We use general
theory of inverses of strictly monotone functions to prove that `NNReal.sqrt x` exists. As a side
effect, `NNReal.sqrt` is a bundled `OrderIso`, so for `NNReal` numbers we get continuity as well as
theorems like `NNReal.sqrt x ≤ y ↔ x ≤ y * y` for free.

Then we define `Real.sqrt x` to be `NNReal.sqrt (Real.toNNReal x)`.

## Tags

square root
-/

@[expose] public section

open Set Filter
open scoped Filter NNReal Topology

namespace NNReal

```

Exact pinned lines98–118:

```lean
alias ⟨_, sqrt_pos_of_pos⟩ := sqrt_pos

attribute [bound] sqrt_pos_of_pos

@[simp] theorem isSquare (x : ℝ≥0) : IsSquare x := ⟨_, mul_self_sqrt _ |>.symm⟩

end NNReal

namespace Real

/-- The square root of a real number. This returns 0 for negative inputs.

This has notation `√x`. Note that `√x⁻¹` is parsed as `√(x⁻¹)`. -/
@[irreducible] noncomputable def sqrt (x : ℝ) : ℝ :=
  NNReal.sqrt (Real.toNNReal x)

-- TODO: replace this with a typeclass
@[inherit_doc]
prefix:max "√" => Real.sqrt

variable {x y : ℝ}

```

Exact pinned lines118–264:

```lean
variable {x y : ℝ}

@[simp, norm_cast]
theorem coe_sqrt {x : ℝ≥0} : (NNReal.sqrt x : ℝ) = √(x : ℝ) := by
  rw [Real.sqrt, Real.toNNReal_coe]

@[continuity, fun_prop]
theorem continuous_sqrt : Continuous (√· : ℝ → ℝ) := by unfold sqrt; fun_prop

@[simp]
lemma map_sqrt_atTop : map (√·) atTop = atTop := by
  unfold sqrt
  simp_rw [← Function.comp_def]
  simp [← map_map]

@[simp]
lemma comap_sqrt_atTop : comap (√·) atTop = atTop := by
  unfold sqrt
  simp_rw [← Function.comp_def]
  simp [← comap_comap]

lemma tendsto_sqrt_atTop : Tendsto (√·) atTop atTop := map_sqrt_atTop.le

theorem sqrt_eq_zero_of_nonpos (h : x ≤ 0) : √x = 0 := by simp [sqrt, Real.toNNReal_eq_zero.2 h]

@[simp] theorem sqrt_nonneg (x : ℝ) : 0 ≤ √x := by
  unfold sqrt
  exact NNReal.coe_nonneg _

@[simp]
theorem mul_self_sqrt (h : 0 ≤ x) : √x * √x = x := by
  rw [Real.sqrt, ← NNReal.coe_mul, NNReal.mul_self_sqrt, Real.coe_toNNReal _ h]

@[simp]
theorem sqrt_mul_self (h : 0 ≤ x) : √(x * x) = x :=
  (mul_self_inj_of_nonneg (sqrt_nonneg _) h).1 (mul_self_sqrt (mul_self_nonneg _))

theorem sqrt_eq_cases : √x = y ↔ y * y = x ∧ 0 ≤ y ∨ x < 0 ∧ y = 0 := by
  constructor
  · rintro rfl
    rcases le_or_gt 0 x with hle | hlt
    · exact Or.inl ⟨mul_self_sqrt hle, sqrt_nonneg x⟩
    · exact Or.inr ⟨hlt, sqrt_eq_zero_of_nonpos hlt.le⟩
  · rintro (⟨rfl, hy⟩ | ⟨hx, rfl⟩)
    exacts [sqrt_mul_self hy, sqrt_eq_zero_of_nonpos hx.le]

theorem sqrt_eq_iff_mul_self_eq (hx : 0 ≤ x) (hy : 0 ≤ y) : √x = y ↔ x = y * y :=
  ⟨fun h => by rw [← h, mul_self_sqrt hx], fun h => by rw [h, sqrt_mul_self hy]⟩

theorem sqrt_eq_iff_mul_self_eq_of_pos (h : 0 < y) : √x = y ↔ y * y = x := by
  simp [sqrt_eq_cases, h.ne', h.le]

@[simp]
theorem sqrt_eq_one : √x = 1 ↔ x = 1 :=
  calc
    √x = 1 ↔ 1 * 1 = x := sqrt_eq_iff_mul_self_eq_of_pos zero_lt_one
    _ ↔ x = 1 := by rw [eq_comm, mul_one]

@[simp]
theorem sq_sqrt (h : 0 ≤ x) : √x ^ 2 = x := by rw [sq, mul_self_sqrt h]

@[simp]
theorem sqrt_sq (h : 0 ≤ x) : √(x ^ 2) = x := by rw [sq, sqrt_mul_self h]

theorem sqrt_eq_iff_eq_sq (hx : 0 ≤ x) (hy : 0 ≤ y) : √x = y ↔ x = y ^ 2 := by
  rw [sq, sqrt_eq_iff_mul_self_eq hx hy]

theorem sqrt_mul_self_eq_abs (x : ℝ) : √(x * x) = |x| := by
  rw [← abs_mul_abs_self x, sqrt_mul_self (abs_nonneg _)]

theorem sqrt_sq_eq_abs (x : ℝ) : √(x ^ 2) = |x| := by rw [sq, sqrt_mul_self_eq_abs]

@[simp, grind =]
theorem sqrt_zero : √0 = 0 := by simp [Real.sqrt]

@[simp, grind =]
theorem sqrt_one : √1 = 1 := by simp [Real.sqrt]

@[simp]
theorem sqrt_le_sqrt_iff (hy : 0 ≤ y) : √x ≤ √y ↔ x ≤ y := by
  rw [Real.sqrt, Real.sqrt, NNReal.coe_le_coe, NNReal.sqrt_le_sqrt, toNNReal_le_toNNReal_iff hy]

@[simp]
theorem sqrt_lt_sqrt_iff (hx : 0 ≤ x) : √x < √y ↔ x < y :=
  lt_iff_lt_of_le_iff_le (sqrt_le_sqrt_iff hx)

theorem sqrt_lt_sqrt_iff_of_pos (hy : 0 < y) : √x < √y ↔ x < y := by
  rw [Real.sqrt, Real.sqrt, NNReal.coe_lt_coe, NNReal.sqrt_lt_sqrt, toNNReal_lt_toNNReal_iff hy]

@[bound]
theorem sqrt_le_sqrt (h : x ≤ y) : √x ≤ √y := by
  rw [Real.sqrt, Real.sqrt, NNReal.coe_le_coe, NNReal.sqrt_le_sqrt]
  exact toNNReal_le_toNNReal h

@[gcongr]
theorem sqrt_monotone : Monotone Real.sqrt :=
  fun _ _ ↦ sqrt_le_sqrt

theorem strictMonoOn_sqrt : StrictMonoOn sqrt (Ici 0) :=
  fun _ ha _ _ h => (sqrt_lt_sqrt_iff ha).mpr h

@[gcongr, bound]
theorem sqrt_lt_sqrt (hx : 0 ≤ x) (h : x < y) : √x < √y :=
  (sqrt_lt_sqrt_iff hx).2 h

theorem sqrt_le_left (hy : 0 ≤ y) : √x ≤ y ↔ x ≤ y ^ 2 := by
  rw [sqrt, ← Real.le_toNNReal_iff_coe_le hy, NNReal.sqrt_le_iff_le_sq, sq, ← Real.toNNReal_mul hy,
    Real.toNNReal_le_toNNReal_iff (mul_self_nonneg y), sq]

theorem sqrt_le_iff : √x ≤ y ↔ 0 ≤ y ∧ x ≤ y ^ 2 := by
  rw [← and_iff_right_of_imp fun h => (sqrt_nonneg x).trans h, and_congr_right_iff]
  exact sqrt_le_left

theorem sqrt_lt (hx : 0 ≤ x) (hy : 0 ≤ y) : √x < y ↔ x < y ^ 2 := by
  rw [← sqrt_lt_sqrt_iff hx, sqrt_sq hy]

theorem sqrt_lt' (hy : 0 < y) : √x < y ↔ x < y ^ 2 := by
  rw [← sqrt_lt_sqrt_iff_of_pos (pow_pos hy _), sqrt_sq hy.le]

/-- Note: if you want to conclude `x ≤ √y`, then use `Real.le_sqrt_of_sq_le`.
If you have `x > 0`, consider using `Real.le_sqrt'` -/
theorem le_sqrt (hx : 0 ≤ x) (hy : 0 ≤ y) : x ≤ √y ↔ x ^ 2 ≤ y :=
  le_iff_le_iff_lt_iff_lt.2 <| sqrt_lt hy hx

theorem le_sqrt' (hx : 0 < x) : x ≤ √y ↔ x ^ 2 ≤ y :=
  le_iff_le_iff_lt_iff_lt.2 <| sqrt_lt' hx

theorem abs_le_sqrt (h : x ^ 2 ≤ y) : |x| ≤ √y := by
  rw [← sqrt_sq_eq_abs]; exact sqrt_le_sqrt h

theorem sq_le (h : 0 ≤ y) : x ^ 2 ≤ y ↔ -√y ≤ x ∧ x ≤ √y := by
  constructor
  · simpa only [abs_le] using abs_le_sqrt
  · rw [← abs_le, ← sq_abs]
    exact (le_sqrt (abs_nonneg x) h).mp

theorem neg_sqrt_le_of_sq_le (h : x ^ 2 ≤ y) : -√y ≤ x :=
  ((sq_le ((sq_nonneg x).trans h)).mp h).1

theorem le_sqrt_of_sq_le (h : x ^ 2 ≤ y) : x ≤ √y :=
  ((sq_le ((sq_nonneg x).trans h)).mp h).2

@[simp]
theorem sqrt_inj (hx : 0 ≤ x) (hy : 0 ≤ y) : √x = √y ↔ x = y := by
  simp [le_antisymm_iff, hx, hy]

@[simp]

```

The supplement explicitly closes NNReal and opens namespace Real before
the captured `variable {x y : ℝ}`. Therefore the adopted head is
`Real.tendsto_sqrt_atTop : Filter.Tendsto (Real.sqrt : ℝ → ℝ) atTop atTop`,
not an NNReal theorem. The chosen guard route is this theorem composed with
the exact natural-cast theorem below. It does not need any positivity of rho.
`Real.sqrt_sq (h : 0 ≤ x) : √(x^2) = x` is used only for the auxiliary236
nonempty-window normalization. `Real.le_sqrt_of_sq_le` is captured but not
needed by the chosen route; it remains a genuine fallback, not a new premise.

## Pinned natural-cast and eventual-atTop heads/ambient

# Exact pinned nat-cast filter API reference

{"mathlibHEAD": "807d3836b165983210ee2ecf3cd28f239436949c", "source": {"physical_path": "/root/rivermind-data/shao-lean-20261021/workspaces/lead-oq56/.lake/packages/mathlib/Mathlib/Order/Filter/AtTopBot/Archimedean.lean", "sha256": "0ba4137bb8d0837d43b1140379163e3cdf89e88675c26807c51f5e801ad31df3", "bytes": 12631, "mtime_ns": "1792382595000000000"}}

contexts lines8-8

```lean
public import Mathlib.Algebra.Order.Archimedean.Basic
```

contexts lines9-9

```lean
public import Mathlib.Order.Filter.AtTopBot.Group
```

contexts lines10-10

```lean
public import Mathlib.Order.Filter.CountablyGenerated
```

contexts lines12-12

```lean
import Mathlib.Algebra.Order.Group.Basic
```

contexts lines23-23

```lean
public section
```

contexts lines26-26

```lean
variable {α R : Type*}
```

contexts lines28-28

```lean
open Filter Set Function
```

ranges lines41-57

```lean
    Tendsto (fun x : ℕ+ => f x) atTop l ↔ Tendsto f atTop l := by
  exact tendsto_comp_val_Ioi_atTop

theorem tendsto_natCast_atTop_atTop [Semiring R] [PartialOrder R] [IsOrderedRing R]
    [Archimedean R] :
    Tendsto ((↑) : ℕ → R) atTop atTop :=
  Nat.mono_cast.tendsto_atTop_atTop exists_nat_ge

lemma tendsto_PNat_val_atTop_atTop : Tendsto PNat.val atTop atTop :=
  tendsto_atTop_atTop_of_monotone (fun _ _ h ↦ h) fun a ↦ ⟨Nat.succPNat a, Nat.le_succ a⟩

theorem Filter.Eventually.natCast_atTop [Semiring R] [PartialOrder R] [IsOrderedRing R]
    [Archimedean R] {p : R → Prop}
    (h : ∀ᶠ (x : R) in atTop, p x) : ∀ᶠ (n : ℕ) in atTop, p n :=
  tendsto_natCast_atTop_atTop.eventually h

@[simp] theorem Int.comap_cast_atTop [Ring R] [PartialOrder R] [IsStrictOrderedRing R]
```



# Exact pinned standard API source reference

{"mathlibHEAD": "807d3836b165983210ee2ecf3cd28f239436949c", "source": {"physical_path": "/root/rivermind-data/shao-lean-20261021/workspaces/lead-oq56/.lake/packages/mathlib/Mathlib/Order/Filter/AtTopBot/Basic.lean", "sha256": "7b467c049ee486339022e2d65a13ee22c37df2625fabeb2c92c0190c7c8aeb1c", "bytes": 18146, "mtime_ns": "1792382595000000000"}}

contexts lines8-8

```lean
public import Mathlib.Order.Filter.AtTopBot.Tendsto
```

contexts lines9-9

```lean
public import Mathlib.Order.Filter.Bases.Basic
```

contexts lines10-10

```lean
public import Mathlib.Order.Nat
```

contexts lines12-12

```lean
import Mathlib.Tactic.Subsingleton
```

contexts lines20-20

```lean
public section
```

contexts lines24-24

```lean
variable {ι ι' α β : Type*}
```

contexts lines26-26

```lean
open Set
```

contexts lines28-28

```lean
namespace Filter
```

contexts lines30-30

```lean
section IsDirected
```

contexts lines31-31

```lean
variable [Preorder α] [IsDirectedOrder α] {p : α → Prop}
```

contexts lines64-64

```lean
variable [Nonempty α]
```

ranges lines77-102

```lean
  atTop_basis.mem_iff.trans <| exists_congr fun _ => iff_of_eq (true_and _)

@[to_dual (attr := simp)]
lemma eventually_atTop : (∀ᶠ x in atTop, p x) ↔ ∃ a, ∀ b, a ≤ b → p b := mem_atTop_sets

@[to_dual]
theorem frequently_atTop : (∃ᶠ x in atTop, p x) ↔ ∀ a, ∃ b, a ≤ b ∧ p b :=
  atTop_basis.frequently_iff.trans <| by simp

@[to_dual]
alias ⟨Eventually.exists_forall_of_atTop, _⟩ := eventually_atTop

-- `to_dual` cannot translate `forall_ge_iff`
lemma exists_eventually_atTop {r : α → β → Prop} :
    (∃ b, ∀ᶠ a in atTop, r a b) ↔ ∀ᶠ a₀ in atTop, ∃ b, ∀ a, a₀ ≤ a → r a b := by
  simp_rw [eventually_atTop, ← exists_comm (α := α)]
  exact exists_congr fun a ↦ .symm <| forall_ge_iff <| Monotone.exists fun _ _ _ hb H n hn ↦
    H n (hb.trans hn)

@[to_dual existing]
lemma exists_eventually_atBot {α : Type*} [Preorder α] [IsCodirectedOrder α] [Nonempty α]
    {r : α → β → Prop} : (∃ b, ∀ᶠ a in atBot, r a b) ↔ ∀ᶠ a₀ in atBot, ∃ b, ∀ a ≤ a₀, r a b :=
  exists_eventually_atTop (α := αᵒᵈ)

@[to_dual]
theorem map_atTop_eq {f : α → β} : atTop.map f = ⨅ a, 𝓟 (f '' { a' | a ≤ a' }) :=
```


At `R=ℝ`, the Semiring/PartialOrder/IsOrderedRing/Archimedean instances in the
nat-cast head are standard imported real instances, not new hypotheses.
The Filter.eventually_atTop head includes Preorder, IsDirectedOrder and
Nonempty ambient conditions; ℝ satisfies them. Its reverse direction gives
the actual real threshold set `∀ᶠ x:ℝ in atTop, 1+rho≤x` from the witness
`1+rho`. Pulling this set back through the composed Tendsto supplies the
guard. Eventual intersection and specialization are logical Filter operations;
no new analytic API or per-unit execution wrapper is proposed.

## Exact curated scale definitions and positivity heads


Source {"path": "C:/game/shao lean/library/Shao/OQ5/P51/BoundedRemainderPayments.lean", "sha256": "c0102fa13835fb22b01148e42d66cf8ff5704d682b9a6142eb508d7172d95cc9", "bytes": 28173}

```lean
/- Source-bound unit197 implementation of the eleven parent-frozen declarations.
   Qualification remains pending the designated server and independent review. -/

import Shao.OQ5.P51.BoundedPolylogConcentration
import Shao.OQ5.P51.BoundedStudentizerGeometry
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Measure.Real
set_option autoImplicit false
universe u
open Filter MeasureTheory
open scoped BigOperators ENNReal
open Shao.OQ6.BoundedProductEnvelopeTails (tailScale)
open Shao.OQ6.CanonicalDoubleGhostRowMoments (sampleLaw originalRows)
open Shao.OQ6.CanonicalDoubleGhostScalarMoments (originalUpper)
namespace Shao.OQ5.P51
noncomputable section
```

```lean
def remainderWindowScale (K t0 : ℝ) : ℝ :=
  min (1 : ℝ)
    (min (1 / ((32 : ℝ) * (K + 1) * (t0 + 1)))
      (1 / Real.sqrt ((32 : ℝ) * (studentizerGeometryScale K + 1) *
        (1 + Real.sqrt t0 + t0))))

-- D02
```

```lean
theorem remainderWindowScale_bounds
    (K t0 : ℝ) (hK : 0 ≤ K) (ht0 : 0 < t0) :
    0 < remainderWindowScale K t0 ∧
      remainderWindowScale K t0 ≤ 1 ∧
      remainderWindowScale K t0 ≤ 1 / ((32 : ℝ) * (K + 1) * (t0 + 1)) ∧
      remainderWindowScale K t0 ≤
        1 / Real.sqrt ((32 : ℝ) * (studentizerGeometryScale K + 1) *
          (1 + Real.sqrt t0 + t0))
```


Source {"path": "C:/game/shao lean/library/Shao/OQ6/BoundedProductEnvelopeTails.lean", "sha256": "43367b3ce14f174a8c8e3db4152e3db3b553ab0dbc9c4521565a1db8ddac1b14", "bytes": 40651}

```lean
/- Unit193 original bounded-product statistics. Author source; server validation pending. -/

import Shao.OQ6.BoundedMeanSumMoments
import Shao.OQ6.CanonicalDoubleGhostRowMoments
import Shao.OQ6.CanonicalDoubleGhostScalarMoments
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.Complex.Exponential

set_option autoImplicit false
universe u
namespace Shao.OQ6.BoundedProductEnvelopeTails
noncomputable section
```

```lean
def commonMomentScale
    (M : ℝ) :
  ℝ :=
  64 * (M + 1)
```

```lean
def envelopeTailScale
    (M : ℝ) :
  ℝ :=
  4 * M + 8
```

```lean
def squareTailScale
    (M : ℝ) :
  ℝ :=
  Real.exp 1 * (M + 1)
```

```lean
def scalarTailScale
    (M : ℝ) :
  ℝ :=
  8 * Real.exp 1 * envelopeTailScale M
```

```lean
def rowTailScale
    (M : ℝ) :
  ℝ :=
  8 * (Real.exp 1) ^ 2 * (envelopeTailScale M) ^ 2
```

```lean
def tailScale
    (M : ℝ) :
  ℝ :=
  max (squareTailScale M) (max (scalarTailScale M) (rowTailScale M))
```

```lean
theorem bounded_scales_pos
    (M : ℝ)
    (hM0 : 0 ≤ M) :
  0 < commonMomentScale M ∧ 0 < envelopeTailScale M ∧
  0 < squareTailScale M ∧ 0 < scalarTailScale M ∧
  0 < rowTailScale M ∧ 0 < tailScale M
```

Historical “pending” source comments do not supersede current qualified
evidence. Unit237's interface is used only as a reference for common-window
geometry and literal definitions; no235/237/239 selector, law or theorem is
consumed. All32 imported actual definitions, including residual denominators,
jackknife square, clipping1 and the exact Gaussian-tail RHS, are reproduced
with full parameter/result types in INTERFACE-INVENTORY.json.

## Prospective248 full interface

The exact entire46589B public head is retained as the prefix of
CANDIDATE-HEAD.txt, up to its one theorem-name change. LOCAL-VALIDATION.json
records the byte restoration check. The original16 telescope, every145 old
ordinary type/RHS/scope, full producer/model choice propositions, the11 old
unique contexts and all32 old typed reference facts remain in the inventory.
The248 sealed dbe4 source is hash checked only; no248 proof is reviewed here.
Its qualification remains false at this immutable activation boundary.

## Ordinary scalar operations

The payment comparison uses only z≥1 and sqrt(n)≥0 followed by exponential
monotonicity. Fee identity and final factorization are real polynomial
identities. No guessed new named scalar API, density/CDF identity, positive
Psi denominator, source-cost sign or stochastic independence fact is needed.
These are proposed explicitly typed local obligations in the inventory, not
new theorem assumptions and not implemented Lean proofs.
