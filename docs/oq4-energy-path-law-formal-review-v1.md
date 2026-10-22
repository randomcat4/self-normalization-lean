# E3 EnergyPathLaw v1 独立形式终审票

STATUS: CORRECT
CHECK_STATUS: FULLY_CHECKED
FORMAL_STATUS: LEAN_FULLY_CHECKED
TICKET_STATE: FROZEN
REVIEW_DATE: 2026-10-22
SCOPE: 仅冻结式 (7) 的实际能量倾斜有限路径身份第一叶
E3_STATUS: OPEN
ROOT_STATUS: OPEN

## 裁决

固定源码在指定服务器独立 no-o 检查、完整源码标准输入审计和实际 33 个 OQ4 模块导入共存检查中均通过。完整源码按 `getModuleIdxFor? = none` 无名称或命名空间过滤实测得到 22 个新常量：9 个源码公开定理、4 个源码私有定理、1 个定义、8 个生成定理。22 项完整实际类型及逐项传递公理均审查通过；与作者已输出模块按实际模块归属抽取的 22 项类型、公理也逐项相同。没有关键数学或形式缺口。

本票只认证上述有限身份、真实可积性、真实有限乘积密度及 iid 拉回；不关闭完整 E3、E2、OQ4 或任何根组。本轮没有重新审查或改动原始来源、冻结陈述、匿名 proof、既有数学票，也没有读取作者 receipt、summary、checkpoint、ledger、translator/intake 或其他审稿票。

## 输入、版本和字节锁定

本地 `drafts/oq4/energy-path-law/EnergyPathLaw.lean` 与服务器 `Shao/OQ4/EnergyPathLaw.lean` 均为 15246 字节，严格 UTF-8、无 BOM，SHA256 同为：

`4feb2d7024c75f6cabeab4f46bf81d5430f70a5d30cc86de8dde3250b3191536`

本轮结束后本地只读核对下列固定输入仍与数学门时完全一致：

| 文件 | 字节数 | SHA256 |
|---|---:|---|
| `drafts/oq4/frozen-energy-path-law-v1.md` | 4292 | `dcc050f7c229bbe6410dd5b9562bc4f349d6466b2e82ceeb70956dae7e545899` |
| `drafts/oq4/energy-path-law/proof.md` | 15016 | `6262f545ddd10fe868db3386b426d417cb53940fc1e3ab55375f79147dafc601` |
| `drafts/oq4/review/energy-path-law-math-review-v1.md` | 11115 | `5d16459c67934758ffb5c54d2dae3c6998fe68d1cced9b8555087712e9c98894` |

服务器实际工作树：`/root/rivermind-data/shao-lean-20261021/workspaces/lead-oq4`。只读确认分支 `feat/oq4-centering-and-path`、HEAD `1695839731c586cbeb34f157f9aec2246ec00c7a`。实际工具版本：

- Lean `4.36.0-rc1`，提交 `c9afcddf514a6772bd4d649f7cfc04eff0b9f15e`，Release。
- Lake `5.0.0-src+c9afcdd`。
- mathlib `807d3836b165983210ee2ecf3cd28f239436949c`。

所有 Lean 均先激活指定服务器环境，再进入该工作树，并绑定 `taskset -c 0-3`。未使用 `-o`，未重新编译旧目标、修改 Git、缓存或任何源文件，未安装任何内容；独立脚本及原始日志只存服务器。

## 独立执行记录

服务器审计目录：

`/tmp/oq4-energy-path-law-independent-v1-14gj0lq3`

| 检查 | 实际命令 | 退出码 | 秒数 |
|---|---|---:|---:|
| 精确目标 no-o | `taskset -c 0-3 lake env lean Shao/OQ4/EnergyPathLaw.lean` | 0 | 4.531 |
| 完整实际源码及全新常量审计 | `taskset -c 0-3 lake env lean --stdin` | 0 | 5.201 |
| 实际全部 33 模块共存及模块归属公理门 | `taskset -c 0-3 lake env lean --stdin` | 0 | 25.816 |

目标 no-o 的标准输出、标准错误均为空。成功的完整源码输入为原文件全部字节后接独立审计命令；没有导入目标模块代替重读完整证明，也没有使用名称前缀筛选新常量。实际新常量集合为：

`env.constants.toList.filter (fun p => (env.getModuleIdxFor? p.1).isNone)`。

对每一项打印完整类型并调用 `Lean.collectAxioms`，逐项拒绝标准三公理以外的依赖。审计使用当前钉死 Lean 的实际 `CollectAxioms.lean` 接口；当前源码声明的类型与证明值被遍历，导入依赖经 Lean 的已导出公理记录递归供应。

成功输入和输出的 SHA256：

| 服务器审计文件 | SHA256 |
|---|---|
| `fullsource-audit-v2.stdin.lean` | `25961d6acdf29b2831ca3bcaf61b023b726dc311728050d038799fea52c30d81` |
| `fullsource-audit-v2.stdout.log` | `584b4547aa802156ed2d98c2e402f1d62ac9b374a8a8bebe93ac7fc347d82c58` |
| `coexist-all33.stdin.lean` | `6c05c199c93c21cfb07c559985b50e6be80c09df3bd2cb6deb297643fea1c341` |
| `coexist-all33.stdout.log` | `43aeaff621f244e46a4896b33288af1a51206c02b87a6c93436b2f8630a8607b` |

完整实际签名保留全限定名和宇宙参数，位于这两份成功 stdout；对应结果记录分别为 `fullsource-audit-v2.result.json` 与 `coexist-all33.result.json`。首次独立打印脚本使用了本版本不存在的 `pp.width` 选项，退出 1；只删除该打印选项后成功重跑，没有修改目标源码。首次失败记录 `fullsource-audit.*` 保留，不能作为目标源失败或最终通过记录。

另行对两份成功日志中的 22 项名称、完整实际类型及公理集合逐项比对，只规范化空白和标准输入产生的私有名前缀：`_private._stdin.0.` 对应 `_private.Shao.OQ4.EnergyPathLaw.0.`。结果 `sourceCount=22`、`compiledCount=22`，`namesIdentical=true`、`allTypesIdentical=true`、`allAxiomsIdentical=true`，记录在 `source-vs-compiled-signatures.result.json`。没有规范化、删除或替换任何类型前提。

## 全 22 常量及公理账

下表 S 精确表示 `[propext, Classical.choice, Quot.sound]`；P 精确表示 `[propext]`。私有前缀 PVT 精确表示 `_private.Shao.OQ4.EnergyPathLaw.0.Shao.OQ4.`，不是按该前缀筛选常量的依据。

| 实际常量名 | 分类 | 实际传递公理 |
|---|---|---|
| `Shao.OQ4.energyPathIntegrand` | 定义 | S |
| `Shao.OQ4.finitePi_withDensity` | 公开定理 | S |
| `Shao.OQ4.energyPathIntegrand_nonneg` | 公开定理 | S |
| `Shao.OQ4.energyPathIntegrand_measurable` | 公开定理 | S |
| `Shao.OQ4.energyPathIntegrand_le` | 公开定理 | S |
| `Shao.OQ4.energyPathIntegrand_integrable` | 公开定理 | S |
| `Shao.OQ4.energyPathLaw_withDensity` | 公开定理 | S |
| `Shao.OQ4.energyPathLaw_real_apply` | 公开定理 | S |
| `Shao.OQ4.energyPathLaw_integral` | 公开定理 | S |
| `Shao.OQ4.energyPathLaw_integral_iid` | 公开定理 | S |
| `PVTfinitePi_withDensity_lintegral` | 私有定理 | S |
| `PVTenergyPath_energy_le` | 私有定理 | S |
| `PVTenergyPath_density_integrable` | 私有定理 | S |
| `PVTenergyPath_closed_density` | 私有定理 | S |
| `Shao.OQ4.energyPathIntegrand.eq_1` | 生成方程定理 | S |
| `PVTenergyPath_closed_density._simp_1_1` | 生成定理 | P |
| `PVTenergyPath_closed_density._simp_1_2` | 生成定理 | P |
| `PVTenergyPath_closed_density._simp_1_3` | 生成定理 | P |
| `PVTenergyPath_closed_density._simp_1_4` | 生成定理 | P |
| `PVTenergyPath_closed_density._simp_1_5` | 生成定理 | P |
| `PVTenergyPath_closed_density._simp_1_6` | 生成定理 | S |
| `PVTenergyPath_closed_density._simp_1_7` | 生成定理 | P |

全部 22 项为 21 个 theorem 常量和 1 个 def 常量；S 有 16 项、P 有 6 项。没有新增 axiom、opaque、inductive 或其他被漏审类别。实际 33 个 OQ4 模块所属全部 637 个常量也逐项通过相同传递公理白名单门。

## 实际签名忠实性

以下是核验过的源码签名记法；所有前提均保留。全限定名及宇宙参数的完整实际输出在上列成功日志中，生成项也被打印和比对。

```lean
private theorem finitePi_withDensity_lintegral
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (d : ℝ → ENNReal) (hd : Measurable d)
    [IsProbabilityMeasure (ν.withDensity d)]
    (n : ℕ) (F : Shao.Path n → ENNReal) (hF : Measurable F) :
    (∫⁻ a, F a ∂Measure.pi (fun _ : Fin n => ν.withDensity d)) =
      ∫⁻ a, (∏ i, d (a i)) * F a ∂Measure.pi (fun _ : Fin n => ν)

theorem finitePi_withDensity
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (d : ℝ → ENNReal) (hd : Measurable d)
    [IsProbabilityMeasure (ν.withDensity d)] (n : ℕ) :
    Measure.pi (fun _ : Fin n => ν.withDensity d) =
      (Measure.pi (fun _ : Fin n => ν)).withDensity (fun a => ∏ i, d (a i))

noncomputable def energyPathIntegrand {n : ℕ} (h s : ℝ)
    (a : Shao.Path n) : ℝ := by
  classical
  exact if a ∈ Shao.closedStrip h then
    Real.exp (s * (Shao.energy a - (n : ℝ)) / h ^ 2) else 0

theorem energyPathIntegrand_nonneg {n : ℕ} (h s : ℝ) (a : Shao.Path n) :
    0 ≤ energyPathIntegrand h s a

theorem energyPathIntegrand_measurable {n : ℕ} (h s : ℝ) (hh : 0 ≤ h) :
    Measurable (energyPathIntegrand (n := n) h s)

private theorem energyPath_energy_le {n : ℕ} (h : ℝ)
    (a : Shao.Path n) (ha : a ∈ Shao.closedStrip h) :
    Shao.energy a ≤ 4 * (n : ℝ) * h ^ 2

theorem energyPathIntegrand_le {n : ℕ} (T h s : ℝ)
    (hT : 0 ≤ T) (hh : 1 ≤ h) (hs : |s| ≤ T) (a : Shao.Path n) :
    energyPathIntegrand h s a ≤
      Real.exp (-s * (n : ℝ) / h ^ 2) * Real.exp (4 * T * (n : ℝ))

theorem energyPathIntegrand_integrable (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (n : ℕ) (T h s : ℝ) (hT : 0 ≤ T) (hh : 1 ≤ h) (hs : |s| ≤ T) :
    Integrable (energyPathIntegrand (n := n) h s)
      (Measure.pi (fun _ : Fin n => ν))

theorem energyPathLaw_withDensity (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (n : ℕ) (T h s : ℝ) (hT : 0 ≤ T) (hh : 1 ≤ h) (hs : |s| ≤ T)
    (hSq : Integrable (fun x : ℝ => x ^ 2) ν)
    (hsecond : (∫ x : ℝ, x ^ 2 ∂ν) = 1) :
    Measure.pi (fun _ : Fin n => energyTiltedLaw ν h s) =
      (Measure.pi (fun _ : Fin n => ν)).withDensity
        (fun a => ENNReal.ofReal
          (∏ i, energyWeight h s (a i) / energyNormalizer ν h s))

private theorem energyPath_density_integrable
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (n : ℕ) (T h s : ℝ) (hT : 0 ≤ T) (hh : 1 ≤ h) (hs : |s| ≤ T) :
    Integrable (fun a : Shao.Path n =>
      ∏ i, energyWeight h s (a i) / energyNormalizer ν h s)
      (Measure.pi (fun _ : Fin n => ν))

theorem energyPathLaw_real_apply (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (n : ℕ) (T h s : ℝ) (hT : 0 ≤ T) (hh : 1 ≤ h) (hs : |s| ≤ T)
    (hSq : Integrable (fun x : ℝ => x ^ 2) ν)
    (hsecond : (∫ x : ℝ, x ^ 2 ∂ν) = 1)
    (A : Set (Shao.Path n)) (hA : MeasurableSet A) :
    (Measure.pi (fun _ : Fin n => energyTiltedLaw ν h s)).real A =
      ∫ a in A, (∏ i, energyWeight h s (a i) / energyNormalizer ν h s)
        ∂Measure.pi (fun _ : Fin n => ν)

private theorem energyPath_closed_density (ν : Measure ℝ) (n : ℕ) (h s : ℝ)
    (hZ : 0 < energyNormalizer ν h s) (a : Shao.Path n)
    (ha : a ∈ Shao.closedStrip h) :
    (energyNormalizer ν h s) ^ n *
        (∏ i, energyWeight h s (a i) / energyNormalizer ν h s) =
      Real.exp (s * Shao.energy a / h ^ 2)

theorem energyPathLaw_integral (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (n : ℕ) (T h s : ℝ) (hT : 0 ≤ T) (hh : 1 ≤ h) (hs : |s| ≤ T)
    (hSq : Integrable (fun x : ℝ => x ^ 2) ν)
    (hsecond : (∫ x : ℝ, x ^ 2 ∂ν) = 1) :
    Integrable (energyPathIntegrand (n := n) h s)
        (Measure.pi (fun _ : Fin n => ν)) ∧
      (∫ a, energyPathIntegrand h s a ∂Measure.pi (fun _ : Fin n => ν)) =
        Real.exp (-s * (n : ℝ) / h ^ 2) * (energyNormalizer ν h s) ^ n *
          (Measure.pi (fun _ : Fin n => energyTiltedLaw ν h s)).real
            (Shao.closedStrip h)

theorem energyPathLaw_integral_iid {Ω : Type*} [MeasurableSpace Ω]
    (p : Measure Ω) [IsProbabilityMeasure p]
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (n : ℕ) (T h s : ℝ) (hT : 0 ≤ T) (hh : 1 ≤ h) (hs : |s| ≤ T)
    (hSq : Integrable (fun x : ℝ => x ^ 2) ν)
    (hsecond : (∫ x : ℝ, x ^ 2 ∂ν) = 1)
    (X : Fin n → Ω → ℝ) (hX : ∀ i, Measurable (X i))
    (hIndep : iIndepFun X p)
    (hLaw : ∀ i, IdentDistrib (X i) (id : ℝ → ℝ) p ν) :
    Integrable (fun ω => energyPathIntegrand h s
        (Shao.Probability.samplePath X ω)) p ∧
      (∫ ω, energyPathIntegrand h s (Shao.Probability.samplePath X ω) ∂p) =
        Real.exp (-s * (n : ℝ) / h ^ 2) * (energyNormalizer ν h s) ^ n *
          (Measure.pi (fun _ : Fin n => energyTiltedLaw ν h s)).real
            (Shao.closedStrip h)
```

这里乘积体是 `∏ i, (w(a_i)/Z)`，不是错误的 `(∏ i, w(a_i))/Z`；有限乘积商规则才把总分母化为 `Z^n`。公开主定理没有密度、Z 正性、μ 概率性或生存概率正性的额外输入。泛化的 `finitePi_withDensity` 只把一维 `ν.withDensity d` 的概率性作为其通用接口条件；实际应用点第 166–176 行由既有实际 energy-law 定理建立该条件，并未假设路径密度。

其余 8 个生成项的完整类型也已逐项审查：

- `energyPathIntegrand.eq_1`：对所有 `{n} h s a`，实际定义等于 `if a∈closedStrip h then exp(s*(energy a-(n:ℝ))/h^2) else 0`。
- `_simp_1_1`：`∀ {α : Type u} [Zero α] [OfNat α 2] [NeZero (2 : α)], ((2 : α)=0)=False`。
- `_simp_1_2`：`∀ {α : Type u} [Zero α] [OfNat α 3] [NeZero (3 : α)], ((3 : α)=0)=False`。
- `_simp_1_3`：`∀ {α : Type u} [Zero α] [OfNat α 4] [NeZero (4 : α)], ((4 : α)=0)=False`。
- `_simp_1_4`：`∀ {M₀ : Type u} [Mul M₀] [Zero M₀] [NoZeroDivisors M₀] {a b : M₀}, a≠0 → b≠0 → (a*b=0)=False`。
- `_simp_1_5`：`∀ {M₀ : Type u} [MonoidWithZero M₀] {a : M₀} [IsReduced M₀] (n : ℕ), a≠0 → (a^n=0)=False`。
- `_simp_1_6`：`∀ {G₀ : Type u} [GroupWithZero G₀] {a : G₀} (n : ℤ), a≠0 → (a^n=0)=False`。
- `_simp_1_7`：`∀ {R : Type u} [AddMonoidWithOne R] [CharZero R] (n : ℕ), ((n:R)+1=0)=False`。

## 源码推导与边界审查

1. **实际有限 π 密度，源码第 15–82 行。** 私有非负测试公式对自然数归纳，零长度使用实际 `Measure.pi_of_empty`，无 `n>0`。归纳步逐项构造 `Fin.cons` 的联合可测性、尾密度乘积可测性、联合 H 及参数积分 G 可测性，再应用实际 `path_pi_lintegral_cons`、一维 `lintegral_withDensity_eq_lintegral_mul` 与 `lintegral_const_mul`。ν 及实际 `ν.withDensity d` 均为概率测度，所需有限／σ 有限前提存在。全程非负无穷积分，不假定 F 真可积或有限。测度等式随后经 `Measure.ext_of_lintegral` 推出，未另造路径律。
2. **Φ 的真正可积性，第 85–157 行。** 定义是实际闭条带上的真实中心能量指数；可测性调用实际闭事件桥及 `measurable_energy`。只在 `ha:a∈closedStrip h` 内使用共享坐标界，得到 `Q≤4*n*h²`；使用 Q 非负、h² 正及 s≤T，给全空间上界 `exp(-s*n/h²)*exp(4*T*n)`。`Integrable.of_bound` 独立支付 Φ 真可积，不要求原律平方指数矩。
3. **实际能量路径密度，第 160–185 行。** 直接展开实际 `energyTiltedLaw`，其一维密度及概率性来自已认证接口。`ofReal_prod_of_nonneg` 所需每因子非负由 w 非负与 Z 正提供。密度实乘积的真可积性先用实际一维 w 真可积除常数，再用 `Integrable.fintype_prod` 在实际有限乘积律上得到；没有把路径律密度作为新输入。
4. **实质量有限性，第 188–203 行。** 先供应上述真可积性与非负性，限制于可测 A 后才使用 `ofReal_integral_eq_lintegral_ofReal`。实积分已有限且非负，`toReal_ofReal` 转换合法。实际倾斜律概率性和实际有限 π 概率性也保证事件质量不为无穷；没有靠 `toReal ∞=0` 制造身份。
5. **只在事件内删截断，第 205–227、243–255 行。** 私有闭密度式显式携带 `ha`，逐坐标调用共享 `abs_coordinate_le_two_mul_of_mem_closedStrip`，所以保留等号端点。`Real.exp_sum` 处理有限乘积，`Finset.prod_div_distrib`、空乘积基数及 Z 正性处理 `Z^n`。A 外用指示为零，没有在全空间删除 w 的截断。
6. **最终真实积分，第 230–265 行。** 主结论同时返回 Φ 的真可积性；积分值是精确 `exp(-s*n/h²)*Z^n*Π_n(μ).real A`。实积分运算在已证明可积后使用。没有除以生存概率，生存质量为零仍有效。
7. **iid 拉回，第 268–291 行。** Ω 只需可测结构。实际 `samplePath` 可测性和 `iid_samplePath_map_eq_pi` 给真实 map 等式；先从路径侧可积性经 `integrable_map_measure` 转移真正可积性，再给积分等式。没有新增抽象联合律、密度或不同的事件／能量输入。
8. **边界。** n 的类型始终为任意 ℕ；空指标归纳基及所有有限和／乘积恒等式覆盖 `n=0`，A 为全集、Q=0、Φ=1、`Z^0=1`，两侧为 1。h=1 仍有正分母。负 s 的上界方向正确；T=0 强制 s=0，不除以 T。s=0 的 μ 是归一化闭截断律，通常不是 ν，本实现没有作该错误化简。弱闭端点、原子、格点、零路径与 Q=0 均被保留。不增加中心、原第三／第四矩、对称性、原有界支持、原指数矩、正能量、方差下界或正生存概率条件。

导入 `EnergyLinearTiltCentering` 只是现有依赖链的一部分；本叶公开实际签名与证明均未消费 θ 存在或 E2 共同方差假设。数学票中冻结的完整论证与本实现对应，没有静默改变前提。

## 实际 33 模块共存与源稳定性

从服务器实际 `Shao/OQ4/**/*.lean` 枚举得到 33 个文件，全部真实导入；不是仅使用旧 31 名单。实际模块所属常量数如下：

| 模块 `Shao.OQ4.` 后缀 | 所属常量数 |
|---|---:|
| AveragedResidual | 8 |
| BoundaryOccupation | 41 |
| CosineCoefficients | 11 |
| CosinePowers | 25 |
| DelayedRecurrence | 8 |
| EnergyE1Bounds | 7 |
| EnergyLinearTiltCentering | 10 |
| EnergyLinearTiltComparisons | 10 |
| EnergyLinearTiltDerivatives | 17 |
| EnergyLinearTiltLaw | 24 |
| EnergyLinearTiltVarianceWindow | 15 |
| EnergyLogNormalizer | 17 |
| EnergyPathLaw | 22 |
| EnergyTiltedLaw | 54 |
| FiniteSurvivalLaplace | 30 |
| Foundations | 0 |
| IntervalConcentration | 13 |
| KernelAbsorption | 4 |
| KernelRecurrence | 37 |
| KilledBlockBounds | 23 |
| KilledCosine | 9 |
| KilledIteration | 33 |
| KilledKernel | 15 |
| KilledPathLaw | 35 |
| LaplaceGenerating | 25 |
| LaplaceTail | 29 |
| OccupationPayment | 4 |
| OvershootMoment | 5 |
| OvershootSum | 6 |
| ReflectedSurvival | 29 |
| SpitzerKernelBounds | 7 |
| TruncatedEnergy | 50 |
| VarianceScaling | 14 |
| **合计** | **637** |

检查前后对 33 个 OQ4、全部 8 个 Basic 和全部 24 个 Probability 源文件逐文件记录路径、字节数、完整 SHA256、UTF-8 BOM 标记，并严格 UTF-8 解码。实际路径集合与每一行元数据均完全相同；完整 65 行清单在服务器 `sources-before.json`、`sources-after.json`，两文件逐字节 SHA256 同为：

`0d7fcd6f22aaed570db3af4a052907151354fb2be1f2d60c6619f228412ac528`

按同一排序和 JSON 编码分组的前后相同指纹为：

| 源组 | 文件数 | 前后相同的完整清单 SHA256 |
|---|---:|---|
| OQ4 | 33 | `94fc1475ae22517468168bd918ef7ba782f0df214edd7aadfd63f728d6370438` |
| Basic | 8 | `7c0ae6eafeb435ff68841f88b7b66cb4f234052ab94a3d4ee26acbf5b2892ae4` |
| Probability | 24 | `c41d6756c0252a779edfc35d3d24460a715aa7a31fa29d43544f8816635faa01` |

其中实际 `EnergyLinearTiltCentering.lean` 的 SHA256 为 `82f48c2123d499eed5a7ac8974ff7d51d18e09987539f8323dece141e08bbe16`，目标 EnergyPathLaw 指纹如上。检查前后 `Shao/OQ4/EnergyE2Bounds.lean` 均 ABSENT。对全部 65 份实际源按单词边界扫描 `sorry`、`admit`、`axiom`、`unsafe`、`native_decide`，命中为空。稳定性与禁词结果在 `sources-stability.result.json`。

全部服务器检查结束时 `liveLeanLake=[]`。初始清单采集时短暂观测到的其他进程已在首次 no-o 前退出，未修改本次锁定的源。此后本审稿人不再运行 Lean 或源稳定性检查，已明确通知 lead 可放行 E2 第二 canonical 写入窗口。该后续窗口不追溯改变本票锁定的 33 模块检查范围。

## 最终边界

本票独立确认冻结源码与冻结数学陈述一致、实际证明经钉死工具链核验、全部本叶新常量的实际类型和标准公理依赖完整、既有实际 33 个 OQ4 模块共存。既有数学票保持 MATH_ONLY / LEAN_NOT_RUN 的原始历史状态；本票独立增加本叶完整形式检查证据。

CORRECT / FULLY_CHECKED 仅限精确 SHA256 `4feb2d7024c75f6cabeab4f46bf81d5430f70a5d30cc86de8dde3250b3191536` 的式 (7) 第一叶。式 (8)–(10)、相对渐近、E4、K/Kv、随机分母及完整 E3/OQ4 仍在后置范围，本票不作其完成认证。
