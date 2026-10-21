# Frozen public interfaces — finite OQ56 foundations

Source freeze31 SHA d8de5d9a007cea7ff0bfcc077b76a1f127b8f69759ee155ca88f6bf9a2540b88 (3defs+6theorems), source freeze32 SHA815903e3fc72ee0ac4139e882363849f7a8127db40bd35be8df38c63ff4ae80e (4defs+5theorems). Both were independently translated from original sources before implementation. The catalogs below intentionally omit proofs; actual complete proofs are in the two Lean modules. All actual public definition bodies and theorem types remain these exact interfaces; private proof helpers do not enlarge the public interface.

## Shao.OQ5.P50, module Shao/OQ5/P50/ThreeStateLayer.lean

```lean
def layerWeight (p q : ℝ) (a : Fin 3) : ℝ :=
  if a = 0 then 1-p-q else if a = 1 then p else q

def layerKernel (N : ℕ) (t p q : ℝ) (a b : Fin 3) : ℝ :=
  if a = 0 then
    if b = 0 then 0 else if b = 1 then t else -p*t/q
  else if a = 1 then
    if b = 0 then t else if b = 1 then -((N : ℝ)-4)*t
    else -t*(1-p-q-p*((N : ℝ)-4))/q
  else
    if b = 0 then -p*t/q
    else if b = 1 then -t*(1-p-q-p*((N : ℝ)-4))/q
    else p*t*(2-2*q-p*((N : ℝ)-2))/q^2

def twoTargetState {N : ℕ} (J : Finset (Fin N)) (i : Fin N) : Fin 3 :=
  if i ∈ J then 1 else 0

theorem layerKernel_symmetric (N : ℕ) (t p q : ℝ) (a b : Fin 3) :
  layerKernel N t p q a b = layerKernel N t p q b a

theorem layerKernel_weighted_row_zero (N : ℕ) (t p q : ℝ) (hq : q ≠ 0) (a : Fin 3) :
  (∑ b : Fin 3, layerWeight p q b * layerKernel N t p q a b) = 0

theorem twoTarget_row_sum (N : ℕ) (hn : 3 ≤ N) (t p q : ℝ)
  (J : Finset (Fin N)) (hJ : J.card = 2) (i : Fin N) :
  (∑ l ∈ Finset.univ.erase i,
    layerKernel N t p q (twoTargetState J i) (twoTargetState J l)) = 2*t

theorem twoTarget_pair_sum (N : ℕ) (hn : 3 ≤ N) (t p q : ℝ)
  (J : Finset (Fin N)) (hJ : J.card = 2) :
  Shao.OQ5.P35.unorderedPairSum (fun i l =>
    layerKernel N t p q (twoTargetState J i) (twoTargetState J l)) = (N : ℝ)*t

theorem twoTarget_layerU (N : ℕ) (hn : 3 ≤ N) (t p q : ℝ)
  (J : Finset (Fin N)) (hJ : J.card = 2) :
  (Shao.OQ5.P35.pairCount N)⁻¹ *
    Shao.OQ5.P35.unorderedPairSum (fun i l =>
      layerKernel N t p q (twoTargetState J i) (twoTargetState J l)) =
    2*t/((N : ℝ)-1)

theorem twoTarget_centered_row_zero (N : ℕ) (hn : 3 ≤ N) (t p q : ℝ)
  (J : Finset (Fin N)) (hJ : J.card = 2) (i : Fin N) :
  Shao.OQ5.P35.center
    (fun k => ((N : ℝ)-1)⁻¹ * ∑ l ∈ Finset.univ.erase k,
      layerKernel N t p q (twoTargetState J k) (twoTargetState J l)) i = 0
```

## Shao.OQ6.FiniteRows, module Shao/OQ6/FiniteRows.lean

```lean
import Shao.OQ5.P35.RowIdentity

set_option autoImplicit false

namespace Shao.OQ6.FiniteRows

noncomputable section

open scoped BigOperators

variable {n : ℕ}

/-- Average every unordered off-diagonal pair exactly once. -/
def uStatistic (H : Fin n → Fin n → ℝ) : ℝ :=
  (n.choose 2 : ℝ)⁻¹ * Shao.OQ5.P35.unorderedPairSum H

/-- Mean of row i excluding the diagonal entry. -/
def rowMean (H : Fin n → Fin n → ℝ) (i : Fin n) : ℝ :=
  ((n : ℝ) - 1)⁻¹ * ∑ j ∈ Finset.univ.erase i, H i j

/-- The original centered-row jackknife square. -/
def jackknifeSq (H : Fin n → Fin n → ℝ) : ℝ :=
  (4 * ((n : ℝ) - 1) / ((n : ℝ) - 2) ^ 2) *
    ∑ i : Fin n, (rowMean H i - uStatistic H) ^ 2

/-- The source uncentered row square s_*². -/
def uncenteredSq (H : Fin n → Fin n → ℝ) : ℝ :=
  (((n : ℝ) - 1) / ((n : ℝ) - 2) ^ 2) *
    ∑ i : Fin n, rowMean H i ^ 2

theorem sum_rowMean (H : Fin n → Fin n → ℝ)
    (hH : ∀ i j, H i j = H j i) (hn : 3 ≤ n) :
    (∑ i : Fin n, rowMean H i) = (n : ℝ) * uStatistic H

theorem sum_centered_rowMean_sq (H : Fin n → Fin n → ℝ)
    (hH : ∀ i j, H i j = H j i) (hn : 3 ≤ n) :
    (∑ i : Fin n, (rowMean H i - uStatistic H) ^ 2) =
      (∑ i : Fin n, rowMean H i ^ 2) - (n : ℝ) * uStatistic H ^ 2

theorem jackknifeSq_nonneg (H : Fin n → Fin n → ℝ) (hn : 3 ≤ n) :
    0 ≤ jackknifeSq H

theorem uncenteredSq_nonneg (H : Fin n → Fin n → ℝ) (hn : 3 ≤ n) :
    0 ≤ uncenteredSq H

theorem uncenteredSq_eq_jackknifeSq_add
    (H : Fin n → Fin n → ℝ)
    (hH : ∀ i j, H i j = H j i) (hn : 3 ≤ n) :
    uncenteredSq H = jackknifeSq H / 4 +
      (((n : ℝ) - 1) / ((n : ℝ) - 2) ^ 2) *
        (n : ℝ) * uStatistic H ^ 2
```

The source catalogs use the immutable imported RowIdentity finite definitions; their bodies and generic theorem signatures were checked independently. The literal choose normalization in32 and pairCount normalization in31 agree through the accepted generic pairCount_eq_choose. All N/n subtract in real numbers after casting. Only actual weighted-row zero assumes q≠0. No hidden iid, law, convergence, tail, rank or strict-positive Studentizer premise/conclusion is present. Unit32 square roots and positive-R event conversion remain outside these frozen targets.
