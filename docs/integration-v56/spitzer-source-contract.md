# 真实概率 Spitzer 候选：来源到实际对象合同

状态：候选研究，未冻结、未实现、零 Lean。外部结果仅保留归属，不能替代 Lean 证明。作者为 `/root/common_spitzer_author`，按任务指定使用 `gpt-6.1-sol / xhigh`；未启动其他代理。

## 1. 原始材料与不变范围

已读只读源 `C:/game/shao/current/c12/supplement.tex` 的 origin proof 中完整 Spitzer/ordinary-survival 段（约1073–1150行），以及对应参考文献条目。该段定义非中心 iid 增量 `B_j`，`S_k^B = Σ_{j=1}^k B_j`，`M_m^B = max(0,S_1^B,…,S_m^B)`。源等式 `h:supp:spitzer` 使用正 Laplace 参数 `s`、母函数变量 `0 < z < 1`：

    Σ_{m≥0} z^m E exp(-s M_m^B)
      = exp(Σ_{k≥1} z^k/k · E exp(-s (S_k^B)^+)).

本候选变量对应为：源 `z` = Lean `s`；源正 Laplace 参数 `s` = Lean `1 / L`。因此库中的 `-M / L` 与源的 `-s M` 完全相同。不能把源中随后用于 Berry–Esseen 的均值、非零方差和三阶中心矩条件误当作恒等式本身的条件。

源对一般增量律采用有界截断后格点化：`B_N = floor(N · max(-N,min(B,N))) / N`，先应用离散版本，然后以有限路径连续性、变换的界1和几何级数支配取极限。候选改用有限带标签路径恒等式，再直接对任意乘积概率律积分；这改变证明方法，不改变对象、假设或结论。

原始 survival lemma 的完整结论还含 `min(1,(a + m_{3,c}/τ_B²)/(τ_B sqrt(m+1)))` 及 `exp(C |μ_B| sqrt(m)/τ_B)`。本候选不把当前库的标准化、无漂移 CDF 消费结果说成这条原始 survival lemma 已全部完成。它只生产其中此前缺失的、对所有增量律有效的原 Spitzer 等式。

## 2. 已核对的字面定义

实际库使用的名称如下，不增加有相似名称但不同含义的对象。

```lean
abbrev Shao.Path (n : ℕ) := Fin n → ℝ
```

`Shao.prefixSum a k` 是 `Finset.univ.filter (fun i : Fin n => i.val < k)` 上坐标之和；`Shao.maxWithZero a` 是所有 `k ∈ Finset.Icc 0 n` 的 `prefixSum a k` 的有限最大值。`prefixSum` 在超过 `n` 时饱和，但本候选的每个切割都显式满足 `k ≤ n`。

`library/Shao/OQ4/FiniteSurvivalLaplace.lean` 的四个相关定义字面为：

```lean
noncomputable def maxLaplaceIntegrand {j : ℕ} (L : ℝ) (a : Shao.Path j) : ℝ :=
  Real.exp (-Shao.maxWithZero a / L)

noncomputable def endpointLaplaceIntegrand {k : ℕ} (L : ℝ) (a : Shao.Path k) : ℝ :=
  Real.exp (-max (Shao.prefixSum a k) 0 / L)

noncomputable def maxLaplaceMean (ν : Measure ℝ) (L : ℝ) (j : ℕ) : ℝ :=
  ∫ a : Shao.Path j, maxLaplaceIntegrand L a ∂Measure.pi (fun _ : Fin j => ν)

noncomputable def endpointLaplaceMean (ν : Measure ℝ) (L : ℝ) (k : ℕ) : ℝ :=
  ∫ a : Shao.Path k, endpointLaplaceIntegrand L a ∂Measure.pi (fun _ : Fin k => ν)
```

这里所有定义都在 `namespace Shao.OQ4`。`laplaceW` 与 `laplaceG` 在 `LaplaceGenerating.lean` 中的完整字面为：

```lean
noncomputable def laplaceW (A : ℕ → ℝ) (s : ℝ) : ℝ :=
  ∑' n : ℕ, s ^ (n + 1) * A (n + 1) / (n + 1)

noncomputable def laplaceG (a : ℕ → ℝ) (s : ℝ) : ℝ :=
  ∑' j : ℕ, s ^ j * a j
```

库已证明 `maxLaplaceMean ν L 0 = 1`、实际变换和实际均值均在 `[0,1]`、实际最大值均值随长度反单调，以及上述两条实际级数收敛。此候选重用这些结果；不会把 `tsum` 的默认值当成收敛证明。

## 3. 原始输入与现有消费界面

已完整读取 `FiniteSurvivalLaplace.lean`、`LaplaceGenerating.lean` 和 `ReflectedSurvival.lean`。当前缺口不是这些消费结论的代数推导，而是下列实际输入还没有生产者：

```lean
∀ L : ℝ, 0 < L → ∀ s : ℝ, 0 < s → s < 1 →
  Shao.OQ4.laplaceG (Shao.OQ4.maxLaplaceMean ν L) s =
    Real.exp (Shao.OQ4.laplaceW (Shao.OQ4.endpointLaplaceMean ν L) s)
```

`maxLaplaceMean_bound_of_cdf_and_original_sp` 和 `closedUpper_bound_of_cdf_and_original_sp` 还分别要求 `C_BE ≥ 0`、`β ≥ 1` 和完整的实际 CDF 前提：

```lean
∀ k : ℕ, 1 ≤ k → ∀ x : ℝ,
  |(Measure.pi (fun _ : Fin k => ν)).real
      {a : Shao.Path k | Shao.prefixSum a k / Real.sqrt k ≤ x} -
    Shao.OQ4.standardNormalCDF x| ≤ C_BE * β / Real.sqrt k
```

它们的输出分别是，给定 `d ≥ 0`、`m ≥ 1`：

```lean
Shao.OQ4.maxLaplaceMean ν (d + β) m ≤
  Real.sqrt 2 * Real.exp (5 + 3 * C_BE) * (d + β) / Real.sqrt m
```

和

```lean
(Measure.pi (fun _ : Fin m => ν)).real (Shao.closedUpper d) ≤
  Real.sqrt 2 * Real.exp (6 + 3 * C_BE) * (d + β) / Real.sqrt m
```

`maxLaplace_original_sp_to_normalized` 只在收到一个给定 `L,s` 的原等式后，把 `finiteSumLaplacePayment = 1 - endpointLaplaceMean` 和真正收敛的对数级数代入，得到归一化形式。它不生产原等式。

`iidOneSidedSurvival_of_cdf_and_two_original_sp` 与 `iid_survival_and_concentration_of_cdf_and_two_original_sp` 需要上述 `hCDF`、原律 `hSP` 和反射律 `hSPneg`。后者字面为：

```lean
∀ L : ℝ, 0 < L → ∀ s : ℝ, 0 < s → s < 1 →
  Shao.OQ4.laplaceG
      (Shao.OQ4.maxLaplaceMean (Shao.OQ4.reflectedLaw ν) L) s =
    Real.exp (Shao.OQ4.laplaceW
      (Shao.OQ4.endpointLaplaceMean (Shao.OQ4.reflectedLaw ν) L) s)
```

候选最终定理对 `ν` 和 `reflectedLaw ν` 各实例化一次便分别支付 `hSP`、`hSPneg`；`hCDF` 仍是独立未支付问题。本次不写任何消费 adapter，不触碰 OQ4 模块。

## 4. 原论文与本路线的归属

- Spitzer, F. (1956), *A combinatorial lemma and its application to probability theory*, Trans. Amer. Math. Soc. 82, 323–339, [DOI](https://doi.org/10.1090/S0002-9947-1956-0079851-X)。源直接引用此文。本轮访问 AMS PDF/DOI 遇403/不可访问；没有声称完整读到其原证明。
- Janssen–van Leeuwaarden, *Spitzer's identity for discrete random walks*, [作者预印本](https://arxiv.org/pdf/1710.09670)，Proposition 2 的已读前提为整数增量、支撑下方有界，`|u| < 1, |z| ≤ 1`。`z = exp(-1/L)` 给离散 Laplace 情形。源引用的 published version 为 ORL 46 (2018), 168–172，[DOI](https://doi.org/10.1016/j.orl.2017.12.003)。不能把离散命题无说明地套给所有实概率律。
- Abramson–Pitman, *Concave Majorants of Random Walks and Related Poisson Processes*, [作者预印本 v2](https://arxiv.org/pdf/1011.3262)，已读 Lemma 2、§8 Theorem 26 的定义、3214 变换及逆向说明。这为候选有限变换提供归属。本候选拟在 Lean 中重新证明带标签双射，并另外证明连续性消除 generic 条件，不把文中 theorem 当作 Lean 输入。

这是经典结果的形式化生产任务，无新颖性主张。

## 5. 精确读取字节

本地只读快照 SHA256：

| 文件 | SHA256 |
|---|---|
| `library/Shao/Basic/FinitePath.lean` | `898262898f9c088e2d10e6238e411b4397387b21b1b71a2b545c5edef936e1bb` |
| `library/Shao/Probability/MeasurablePath.lean` | `827dc47b74dae67101a4d874f412e4cb55bafe1e67b9ba767c6896c0b7e58b41` |
| `library/Shao/Probability/FiniteIID.lean` | `d1b565489199d55af70a27c31a0f803a2b7433e78c9197a361b3c10c0598845b` |
| `library/Shao/OQ4/LaplaceGenerating.lean` | `eab53afb87248fc0f9b94ddf84e986eedae51f2446e9b7ea176e517c4a861ed8` |
| `library/Shao/OQ4/FiniteSurvivalLaplace.lean` | `49241958f2ae692b56db5fe0aa021a5e88b0020ac6487ddb463d05efb69518cb` |
| `library/Shao/OQ4/ReflectedSurvival.lean` | `b54b2300ef77375782e60a541bcffd6bed05ac4de61a776c6e0fd5e189568809` |
| `C:/game/shao/current/c12/supplement.tex` | `b99f2ac4d2f39dd39772d98a5702b7a923c2f10f8730a08fc1b4cd6bba4742bd` |

这些是候选阅读绑定，不能替代最终生产代码的服务器内核/全部所属声明传递公理收据。新声明不扩大任何原始根的完成范围。
