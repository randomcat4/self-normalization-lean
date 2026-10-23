# Actual probability Spitzer declaration freeze

Root freezes the exact five public heads in candidate sections4-5 below, with no new public definitions. Production module: Shao/Probability/SpitzerLaplace.lean in namespace Shao.Probability. The actual iid reorder and head/tail integrals, true recurrence, genuine bounded-recurrence analytic solution and final actual maximum generating identity are one source-bound production goal. A generic recurrence solver alone does not close probability Spitzer.

Finite upstream is the exact SpitzerFinite commit e2b8b5c8552fa5861d56b25c670dc5512199e717, source59ee31957ffec68aaff56d4eee5e833ef28fcb549bdce5f0649bf83216b1224c, original object4835dbd16604620afe282ac4cd5e4f75db74acb7fadffa3dae778875946db067. Production authority activates only after the fresh finite complete review is CORRECT and its old writer is released. No CDF/SP/atomless/centering/moment/symmetry premises may be added. Actual independence, integral bounds, absolute convergence, differentiations, multiplication and uniqueness must be proved. n=0/k=n/empty products retained. No OQ4 implementation/adapters changed. All source fidelity and independent complete final types/values/proof/axiom review requirements remain.

Private helper theorem statements may implement these heads. Any additional global definitions including private require literal value addendum first; proof-local definitions are allowed. Server-only evolving-source targeted checks, shared root-heavy.lock CPU10-13 -M8192 -j4 -DautoImplicit=false, direct rc captured immediately, first whole success emits reusable -o. Exact qualified old dependencies must be reused without recompilation.

CandidateSHA66da3b6ff329a1f33def94c10dcc48c2322f0db201592cdd342730bea83b6974; source-contractSHA4dfa91e06d237e56943d72789fb4be5cebbcc3de17f43310d4bdd39caee5d383; proof-routeSHA2d89d05c6c6b040b54c7f17e1b57c64d1747fe27e22c333b24fe19f33eb751cf. Root has read the full route/contract and these complete exact heads. All root groups stay OPEN.

## 4. 实际乘积概率与实际递推

以下签名位于 `namespace Shao.Probability`，并有 `open MeasureTheory ProbabilityTheory Finset`、`open scoped BigOperators Topology`。概率文件所需 imports 候选为：

```lean
import Shao.Probability.SpitzerFinite
import Shao.OQ4.FiniteSurvivalLaplace
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Normed.Ring.InfiniteSum
```

```lean
theorem spitzer_reordered_maximum_integral (ν : Measure ℝ)
    [IsProbabilityMeasure ν] (n : ℕ) {L : ℝ} (hL : 0 < L)
    (σ : Equiv.Perm (Fin n)) :
    (∫ a : Shao.Path n,
      Real.exp (-Shao.maxWithZero (Spitzer.reorder a σ) / L)
      ∂Measure.pi (fun _ : Fin n => ν)) =
        Shao.OQ4.maxLaplaceMean ν L n

theorem spitzer_head_tail_integral (ν : Measure ℝ)
    [IsProbabilityMeasure ν] (n k : ℕ) (hk : k ≤ n)
    {L : ℝ} (hL : 0 < L) :
    (∫ a : Shao.Path n,
      Real.exp (-max (Shao.prefixSum a k) 0 / L) *
        Real.exp (-Shao.maxWithZero (Spitzer.tail a k hk) / L)
      ∂Measure.pi (fun _ : Fin n => ν)) =
        Shao.OQ4.endpointLaplaceMean ν L k *
          Shao.OQ4.maxLaplaceMean ν L (n - k)

theorem actual_maximum_laplace_recurrence (ν : Measure ℝ)
    [IsProbabilityMeasure ν] {L : ℝ} (hL : 0 < L) (n : ℕ) :
    ((n + 1 : ℕ) : ℝ) * Shao.OQ4.maxLaplaceMean ν L (n + 1) =
      ∑ j ∈ Finset.range (n + 1),
        Shao.OQ4.endpointLaplaceMean ν L (j + 1) *
          Shao.OQ4.maxLaplaceMean ν L (n - j)
```

实际递推必须从第3节有限恒等式积分得出，不能作为新假设。对每个置换使用真正的乘积律不变性，并对实际头尾分块使用乘积测度分解。随后约去 `Fintype.card (Equiv.Perm (Fin (n + 1))) > 0`。不需要计算这个数等于阶乘。

## 5. 解析闭合与最终无 SP 输入的生产者

有界递推的求解是可复用解析引理，不是概率 Spitzer 的替代交付。它的 `hrec` 将由上一个实际定理实例化。

```lean
theorem laplace_identity_of_bounded_recurrence (a b : ℕ → ℝ)
    (ha0 : a 0 = 1)
    (ha : ∀ n : ℕ, 0 ≤ a n ∧ a n ≤ 1)
    (hb : ∀ n : ℕ, 1 ≤ n → 0 ≤ b n ∧ b n ≤ 1)
    (hrec : ∀ n : ℕ,
      ((n + 1 : ℕ) : ℝ) * a (n + 1) =
        ∑ j ∈ Finset.range (n + 1), b (j + 1) * a (n - j))
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) :
    Shao.OQ4.laplaceG a s = Real.exp (Shao.OQ4.laplaceW b s)

theorem actual_maximum_spitzer_laplace (ν : Measure ℝ)
    [IsProbabilityMeasure ν] {L s : ℝ}
    (hL : 0 < L) (hs0 : 0 < s) (hs1 : s < 1) :
    Shao.OQ4.laplaceG (Shao.OQ4.maxLaplaceMean ν L) s =
      Real.exp (Shao.OQ4.laplaceW (Shao.OQ4.endpointLaplaceMean ν L) s)
```

最终声明只接受一个真实概率律、正 Laplace 尺度和 `0 < s < 1`。无需 `hCDF`、`hSP`、`hSPneg`、均值、方差、矩、对称性或无原子条件。反射律的同一声明由 `IsProbabilityMeasure (reflectedLaw ν)` 直接实例化；本候选阶段不增加 OQ4 adapter。
