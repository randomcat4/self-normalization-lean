# 真实三角弦噪声特征函数与锥内谱隙比较

STATUS: PROPOSED_FOR_INDEPENDENT_DECLARATION_REVIEW。

本文件是本轮唯一交付。尚未实施候选、运行 Lean、生成对象、探测新缓存或修改
任何既有源码/根导入/manifest/锁。OddPower 固定实现保持不变。以下拟冻结四个定义、
四个公开定理；先交独立声明审查，由 root 冻结后才能实施。

## 1. 最近缺口与消费关系

原文比较对象是反射路径与端点的平滑测试。其 Fourier 因子为真实未来幂
`φ(u,v)^ℓ` 与适配同一真实条件增量 law 的噪声特征函数 `Ξ(u,v)`。
已接受 OddPower 证明了乘 Ξ 之前的真实幂差及零/一/二阶 jet；Power 给出实际幂的
全局导数，LowFrequencyDamping 给出闭低频域中的真实方差阻尼。

接近这些结果的下一项未建真实对象是正文的 **方差偏置 pair → 三角弦 law → K →
锥内谱隙比较**。正文650–707行先构造 K，随后才以 `K(u,v)^8 K(−u,v)^8` 为高频
乘子。补充3461–3467行的 OddPower 消费还需要 Ξ 的导数，且整个四/五频区分割
需要这个真实 K 的谱隙支付。因此本提案先关闭单弦构造和比较，保留完整噪声、
噪声导数、振荡积分为下一层；不把任意自由乘子或所需 Fourier 差界当作输入。

本单元在源证明顺序中先于已完成的 odd-power 表，但它是该表之后继续迈向真实
Fourier 比较时最近的、可独立闭合的未建 law 桥。

原始只读 source SHA256（本轮原文定位沿用同一固定字节）：

```text
main.tex       beb00f718487e36de433175c97f1d500cb48e7a92ce5bd5ad5d62bb132122d06
supplement.tex b99f2ac4d2f39dd39772d98a5702b7a923c2f10f8730a08fc1b4cd6bba4742bd
```

实际读取和绑定：

- `main.tex:610–625`：实际平滑测试、真实固定条件 law 的 μ/m2/m3/V/γ。
- `main.tex:650–670`，`biasedpair/chord/fullnoise`：以
  `D²/(2V)` 偏置独立对，在独立三角 V 下取 `(VD,V(A²−A'²))`，再用两组各8份
  与独立标量平滑噪声构造 Ξ。本提案只构造单弦 K 所需的真实概率 law。
- `main.tex:673–707`，`charfunctions/Kexact/gap`：实际 K 期望、
  `V⁻¹ E[(1−cos(Dθ))/θ²]` 的连续零值和锥内 `4/9,4` 比较。
- `main.tex:708–721`：未来以 K 的相应因子、幂谱隙优化推出
  `|φ(±u,v)^ℓ Ξ|≤C T^(−8)|u|^(−16)`；这不是本单元已证结论。
- `supplement.tex:1988–2042`：弦噪声的真实支撑与矩计算；最后明确把三角特征
  函数、偏置 pair 平均、Ξ 乘积式和锥比较交回正文。当前只取其单弦 law/支撑部分。
- `supplement.tex:2343–2367,2473–2522,2593–2617`：实际反演中的 D/E、四频区
  与噪声导数需求，防止把 K 这一步报成完整 Fourier 比较。
- `supplement.tex:3325–3357,3420–3467`：后续 K/Ξ 导数和已完成 OddPower 的实际
  连接位置。本提案不假设这些导数界，也不声称已经证明它们。

## 2. 固定对象和既有依赖

ν 始终是一个固定在条件层的真实 `Measure ℝ`，在对 u/v 取值时不改变。
`V=variance(id:ℝ→ℝ)ν` 是实际方差，均值允许非零。全部新 law 都从 ν 的真实
独立产品及密度构造，原始未截断 ξ 的全局第三矩不在本提案中。

已读并复用的已接受声明和固定源码：

| 模块 | 源SHA256与实际复用 |
|---|---|
| QuadraticCharacteristic | `8fd7815191dbd1ba9180159effe8c353d8b82d998d4d0d50bb6f957355b628f5`；原样使用 quadraticChar 与概率 norm≤1；不重定义 φ。 |
| QuadraticCharacteristicPower | `5a51275c796d3bd0cc59b496a15b21e1c6bd5afd101b72f66a4c5e83511164c8`；实际 finite-iid/幂导数桥仍为后续消费者，本单元不重复幂求导。 |
| LowFrequencyDamping | `ffdeace2421a3c0fdf63def48eb96b882f9dc98014e5614d226a07f87a02bb65`；直接用 quadratic_pair_square_moment 的真可积性及 ∫D²=2V 归一化偏置 law，直接用 quadraticChar_gap_identity 连接同一真实 φ。 |
| QuadraticCharacteristicOddPower | `d526459c86cab6fdd8d4fc207e4950e03993bac0a26e7c2c6a7567f747b1b838`；已通过独立完整 proof review，保持0定义/3定理；本单元补其尚未供应的真实噪声桥。 |
| SourceTruncationBridge | `05321c22d1b2ea178fbc116178af345f4186bfce51011c8242b4ccfd2e0dd7d1`；law_data 实际给条件ρ为概率、闭 cutoff 支撑和h3，variance_bounds 实际给相同ρ的V>0。无须重新建立条件化产品或把ρ中心化。 |

公共 bridge 的实际实例化为 `ρ=cond ν₀ {|z|≤ε/(1+x)}`、`h=ε/(1+x)>0`。
在 SourceTruncationBridge 的完整原有 N/M/小预算条件下，其 law_data/variance_bounds
支付这里所有 law/支撑/正方差输入。提案不删那些来源条件，不声称任意未截断 law
自动满足它们。本单元的泛化 law 级结论仅把已支付的真实ρ明确作为输入。

## 3. 拟冻结精确 API：四定义、四定理

未来文件：`Shao/Probability/QuadraticChordNoise.lean`。
namespace `Shao.Probability`；`open MeasureTheory ProbabilityTheory`；
`set_option autoImplicit false`。数学 constants `4/9,4` 是正文实际数值。

### 四个真实 law/特征积分定义

```lean
noncomputable def quadraticTriangleLaw : Measure ℝ :=
  volume.withDensity (fun t : ℝ =>
    ENNReal.ofReal (if |t| ≤ 1 then 1 - |t| else 0))

noncomputable def quadraticBiasedPairLaw (ν : Measure ℝ) : Measure (ℝ × ℝ) :=
  (ν.prod ν).withDensity (fun p : ℝ × ℝ =>
    ENNReal.ofReal ((p.1 - p.2) ^ 2 /
      (2 * variance (id : ℝ → ℝ) ν)))

noncomputable def quadraticChordLaw (ν : Measure ℝ) : Measure (ℝ × ℝ) :=
  Measure.map
    (fun z : (ℝ × ℝ) × ℝ =>
      (z.2 * (z.1.1 - z.1.2), z.2 * (z.1.1 ^ 2 - z.1.2 ^ 2)))
    ((quadraticBiasedPairLaw ν).prod quadraticTriangleLaw)

noncomputable def quadraticChordChar (ν : Measure ℝ) (u v : ℝ) : ℂ :=
  ∫ z : ℝ × ℝ, Complex.exp
    (((u * z.1 + v * z.2 : ℝ) : ℂ) * Complex.I) ∂quadraticChordLaw ν
```

三角 law 是相对于 Lebesgue measure 的实际固定密度 `(1−|t|)1[-1,1]`，不是一项
输入的“有正确特征函数的 law”。偏置 law 的方差分母是源 `2V`，不是 raw m2。
Chord map 的两个坐标共用同一个三角变量和同一对样本，保持源的真实依赖。
这些定义在Lean全域为total；认证只对下列明确 hV>0 的 law 使用，不赋予V=0时
默认除法任何 source 噪声含义。没有新的公共条件 law 或路径定义。

### 1. 三角 law 的真实概率质量与特征函数

```lean
theorem quadraticTriangle_probability_char :
    IsProbabilityMeasure quadraticTriangleLaw ∧
      ∀ t : ℝ,
        (∫ r : ℝ, Complex.exp (((t * r : ℝ) : ℂ) * Complex.I)
          ∂quadraticTriangleLaw) =
        ((if t = 0 then 1 else 2 * (1 - Real.cos t) / t ^ 2 : ℝ) : ℂ)
```

必须由真实密度积分证明，不把右侧作为概率分布定义或假设。t=0精确值1；
在其它实频率的表达式是实非负平方sinc核，允许其为0。

### 2. 实际偏置 pair/单弦 law 的概率、支撑与真正相位可积性

```lean
theorem quadraticChord_law_data (ν : Measure ℝ)
    [IsProbabilityMeasure ν]
    (h3 : Integrable (fun a : ℝ => |a| ^ 3) ν)
    (hV : 0 < variance (id : ℝ → ℝ) ν)
    (h : ℝ) (hh : 0 < h)
    (hsupport : ∀ᵐ a : ℝ ∂ν, |a| ≤ h) :
    IsProbabilityMeasure (quadraticBiasedPairLaw ν) ∧
      IsProbabilityMeasure (quadraticChordLaw ν) ∧
      (∀ᵐ z : ℝ × ℝ ∂quadraticChordLaw ν,
        |z.1| ≤ 2 * h ∧ |z.2| ≤ 2 * h * |z.1|) ∧
      ∀ u v : ℝ,
        Integrable (fun z : ℝ × ℝ => Complex.exp
          (((u * z.1 + v * z.2 : ℝ) : ℂ) * Complex.I))
          (quadraticChordLaw ν)
```

这里只给单弦原始支撑，不提前给完整Ξ的34h/64h²或γ矩预算。|Y1|≤2h|Z1|
保留比|Y1|≤4h²更直接的源关系。正方差与源支撑是同一ν的事实；不要求ν有密度、
无原子、对称或均值零。偏置概率质量本可在无支撑条件下证明，实施可用共享private
helper，但本law_data签名选择完整源支撑语境以同时交付支撑数据。

### 3. 同一真实 K 的精确 quotient，连续零值与实[0,1]界

```lean
theorem quadraticChordChar_exact (ν : Measure ℝ)
    [IsProbabilityMeasure ν]
    (h3 : Integrable (fun a : ℝ => |a| ^ 3) ν)
    (hV : 0 < variance (id : ℝ → ℝ) ν) (u v : ℝ) :
    let V : ℝ := variance (id : ℝ → ℝ) ν
    let Q : ℝ × ℝ → ℝ := fun p =>
      if u + v * (p.1 + p.2) = 0 then (p.1 - p.2) ^ 2 / 2
      else
        (1 - Real.cos ((p.1 - p.2) * (u + v * (p.1 + p.2)))) /
          (u + v * (p.1 + p.2)) ^ 2
    Integrable Q (ν.prod ν) ∧
      quadraticChordChar ν u v =
        (((∫ p : ℝ × ℝ, Q p ∂ν.prod ν) / V : ℝ) : ℂ) ∧
      (quadraticChordChar ν u v).im = 0 ∧
      0 ≤ (quadraticChordChar ν u v).re ∧
      (quadraticChordChar ν u v).re ≤ 1
```

这个结论本身证明源的精确K，公开输入中没有quotient恒等式、谱隙界、K导数界或
所需Fourier差界。Q的真正可积性须证明，可由全域 `0≤Q≤D²/2` 与已接受pair-square
真可积性支付。θ=0的值必须是D²/2，不能用Lean默认0除法抹掉正质量的退化相位。
当D=0也不除D；这一集合在偏置密度下权重为0，积分换算须真实证明。

本声明不要求 bounded support，证明只使用真实h3⇒二矩、正方差、独立产品和
已定义的三角密度。它因而在源的有界条件law下可直接用；不会增加第四矩需求。

### 4. 锥内实际 characteristic-gap 比较

```lean
theorem quadraticChordChar_cone_gap (ν : Measure ℝ)
    [IsProbabilityMeasure ν]
    (h3 : Integrable (fun a : ℝ => |a| ^ 3) ν)
    (hV : 0 < variance (id : ℝ → ℝ) ν)
    (h : ℝ) (hh : 0 < h)
    (hsupport : ∀ᵐ a : ℝ ∂ν, |a| ≤ h)
    (u v : ℝ) (hu : u ≠ 0) (hv : |v| ≤ |u| / (4 * h)) :
    (4 / 9 : ℝ) * (1 - ‖quadraticChar ν u v‖ ^ 2) /
        (variance (id : ℝ → ℝ) ν * u ^ 2) ≤
      (quadraticChordChar ν u v).re ∧
      (quadraticChordChar ν u v).re ≤
        4 * (1 - ‖quadraticChar ν u v‖ ^ 2) /
          (variance (id : ℝ → ℝ) ν * u ^ 2)
```

锥条件闭在v方向，u≠0与h>0、V>0明确保护分母。对真实产品几乎处处
`|A+A'|≤2h`，故 `|u|/2≤|θ|≤3|u|/2`。非负余弦分子与既有真实
quadraticChar_gap_identity给源4/9和4。ν、h、u、v保持原源量词；特别不对χ、K、
D或gap取倒数，不排除gap=0或χ=0。

## 4. 声明阶段的可闭合性检查与实现义务

这不是候选proof的认证；下列是供独立声明审查核对的有限链条和实施约束：

1. 三角密度可测非负、真正积分质量1；利用偶性使相位虚部积分为0，真实有限区间
   积分算出 `2(1−cos t)/t²`，t=0分开处理。不得定义一个自由的characteristic函数
   后假定存在其law。需处理真实 `withDensity` 与 Bochner integral 的对应。
2. 用已接受 `∫D²=2V` 和hV>0规范化偏置pair；真实乘积使三角变量独立。Chord map
   可测；概率性由真实map/prod给出。ν的几乎处处支撑传至ν.prodν、其withDensity
   和实际pushforward，不能把原law的AE不等式当成全域逐点条件。
3. 原始相位在真实概率law下norm1，先证明真可积再换map/prod/withDensity积分。
   第1条在 `t=Dθ` 处平均；乘偏置权重后，θ≠0处恰消去D²、给V⁻¹Q，θ=0处
   由特征函数1给V⁻¹D²/2。D=0另核对，不借未说明的0/0消去。
4. 对Q用 `1−cos r≤r²/2` 得积分支配。第1条非负实值且norm≤1可证明K的实[0,1]
   界；这些性质必须是结论，不能提前写进任何public premise。
5. cone内以真实几乎处处θ界比较Q与 `(1−cos(Dθ))/u²`，再积分、除正V；用已接受
   gap identity合成第4条。此处不需重复低频阻尼或任何iid幂导数。

本轮未运行Lean/API probe，所以不宣称缓存或某个具体积分lemma已可用。实施前仍须
读取项目钉死工具链，并在server只读核对所需 `withDensity`/map/prod及有限区间实/复
积分API；如缺精确模块，向root报告，不运行lake update、不重建Mathlib或写共享cache。

## 5. 必查边界与不能删除的条件

**B1：连续零值是实质条件。** 在u=v=0时，真实K(0,0)=1。若Q的θ=0分支改为0，
则其所有点都为0，右侧积分为0；当前签名的D²/2分支恰由∫D²=2V给出1。

**B2：去掉cone会给显式反例。** 令ν在{0,1}上等概率，V=1/4，u=1、v=−1。
此时a²=a，真实φ(1,−1)=1；偏置pair只保留异点，且弦上Y1=Z1，所以K(1,−1)=1。
gap为0，全平面版本的上界会强迫1≤0。该点确不满足h=1时的cone输入。

**B3：单弦K本身未获u偶性。** 同一{0,1}law使K(u,v)等于三角特征函数在u+v的值。
K(−u,u)=1而一般K(u,u)≠1。源完整Ξ以两组反向family的乘积获得u偶性；不能把
这项未来性质暗移到当前K或假定quadraticChordLaw在单独Z反号后不变。

**B4：格点共振仍保留。** 对ν在{−a,a}公平分布、a>0、v=0、u=π/a，|φ|=1，
偏置pair的D=±2a给K=0；它位于cone且当前比较两侧都为0。这说明本桥真实提供
适配噪声的谱隙消失机制，同时不宣称χ在全频率有高斯阻尼。

**B5：非中心与原子不被排除。** {0,1}law均值1/2即有正方差，所有前三矩有限，
可直接进入当前签名。源ρ本来可能非中心。AE支撑、closed cutoff与三角端点±1
全部保留；没有密度、对称增量、无原子、正gap或非零χ假设。

**B6：正方差边界。** Dirac law的V=0不在源γ定义域内，本单元明确hV>0；
withDensity定义的total 0/0行为不被当成有效偏置概率law。h=0与hV>0和支撑条件
不相容，但当前source语境中直接使用真实正cutoff h，避免cone的0分母。

## 6. 明确尚未关闭的 Fourier 层

本单元一旦通过，只交付真实单弦law、三角特征积分、精确K和锥内gap比较。
它没有构造两组各J=8份的完整噪声及标量ρ，不证明其u偶性/支撑/γ矩预算或Ξ的
实际乘积式；不证明K/Ξ导数、gap优化及高频幂乘子衰减。源差值odd-power与本K
之间的连接仍要通过那些独立步骤完成。

还未关闭真实H_y卷积/Fourier变换/反演、两次u分部积分、marknorms和各频区积分、
复杂频率倾斜、时间网格求和、smoothed proposition的 `Λ_y Phibar(y)` 误差、严格CDF
去平滑、最终Gaussian比较或C1/C2。现有源truncation和clock桥不被当成这些结论。
此提案重现明确源中的技术依赖，不声称研究新颖性或完整根解决。

## 7. 接受门

最小下一步是新的独立声明审查：核对真实三角密度、偏置归一化2V、map方向、
quotient的连续零值、全原子与非中心law、4/9和4的cone量词，以及其源消费范围。
在root冻结前，不实施任何四定义/四定理，不把提案当作已证库结果。

实施后的接受须另有实际server目标、全部module-owned（含private/generated与跨
namespace）传递公理白名单、完整实际依赖门、禁用项/版本锁/精确源码SHA，以及
新的独立source-to-statement和完整proof审查。root拥有后续根导入、manifest、
集成gate和merge。本提案只提供声明，不冒充任何机械认证。
