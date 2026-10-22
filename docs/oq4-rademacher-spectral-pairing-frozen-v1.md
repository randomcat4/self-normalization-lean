# OQ4 S2 前置薄叶：有限正负模态精确配对冻结接口 v1

STATUS: FROZEN_PENDING_STATEMENT_REVIEW
CANDIDATE_STATE: ADOPTED_AS_FROZEN_V1
REVIEW_STATUS: NOT_REVIEWED
PROOF_STATUS: NOT_WRITTEN
IMPLEMENTATION_AUTHORIZATION: HOLD_PENDING_UPSTREAM_FORMAL_CERTIFICATION_AND_MATH_GATES
S2_STATUS: OPEN
S3_S5_STATUS: OPEN
SPECTRUM_STATUS: OPEN
ROOT_STATUS: OPEN

Lead 明确采纳候选中的 P1/P2、归一化分母合法性及列明的时间端点为正式冻结 v1；原 candidate 00a765789cba12af29a78641676327aa2f211e03a2ff1cc25c84190552fe9ffc 保持原字节。固定将来模块 Shao/OQ4/RademacherSpectralPairing.lean，namespace Shao.OQ4.RademacherSpectralPairing。当前待全新独立来源语义审查，不是数学证明或 Lean 认证。第5节后续统一余项界不在本冻结范围；P1/P2 及其全部时间/小 m 端点为本叶强制范围。不能据此启动数学证明或 Lean 实施；先过相应独立门并由 lead 明确授权。

## 1. 来源与选择范围

唯一原始数学来源为 `C:/game/shao/current/oq4/c01/spectrum01.md`，commit `35d4580b61e22e7145f47730045a09874ef93259`，SHA256 `b65f9e0c2f9b40a28d092491b479bd20d0b8ee8a9ac940c3c4760cfff7d2670b`，4306 bytes。

本候选选取第36–55行 S2 之前实际缺失的有限配对身份：首正模态与最负模态的精确系数、全部其余正负模态的配对，以及中心零模态的时间端点。原第38–43行的双尺度渐近和第46–55行的统一指数余项估计均不纳入本叶。P1 是唯一原始数学义务；P2 是同一身份的主项抽取输出形式，不按编号计算新的独立定理数。

直接固定上游是 `C:/game/shao lean/drafts/oq4/frozen-rademacher-finite-s1-v1.md`，SHA256 `e2e9240f739e737c83195f177dcd54707c023151cf3e4faf7f1d862e87b585fe`，特别是第100–112行 C4。其余固定上游接口的 SHA 为：AllModes `dac2fd30e7c759137e14ebd64c4d7457155a201da04a7226449304d0b4abbe10`；FiniteBasis `4672baa6bc550de2a97ca9adc0730b5633f71458b2c3da8b02c2318131e05a7f`；Iteration `15851002ccadaa118035107c8b9b8266dd825fdebdf36728f3ac7a97f7330b80`。后三者只是 S1 的固定传递依赖，本叶不重新交付其内容。

上述冻结数学接口在本文件中仅是未来精确承诺，不是已经成立的新假设。派发时 lead 给出的当前状态为：Iteration／FiniteBasis 已完整认证并发布 PR82／PR86；AllModes 仅 private Source/no-o ready、尚未最终形式认证；S1 只有匿名证明且在 fresh mathematical review 中。本 intake 未读取相应证明、审查或私有实施，也未自行认证这些状态。未来使用须接实际认证声明，不能把本候选写成以 S1 为自由假设的替代定理。

## 2. 固定真实对象、量词与记号

概率律固定为现有 `ν_R := Shao.OQ4.RademacherCosine.law = (1/2 : ℝ≥0∞) • δ_1 + (1/2 : ℝ≥0∞) • δ_(-1)`，使用其内部概率实例。对每个 n:ℕ，

- `Path n := Fin n → ℝ`；
- `P_n := Measure.pi (fun _ : Fin n => ν_R)`；
- `S_k(a) := Shao.prefixSum a k`；
- `A_n(h) := Shao.closedStrip h = {a : Path n | ∀k:ℕ, k≤n → |S_k(a)|≤h}`；
- `p(n,h) := P_n.real A_n(h)`。

p 始终是这个实际路径概率，不改成谱和的定义。n=0 的空路径事件概率按原文为1。

量化所有 m:ℕ 且 `1≤m`，全部 h:ℝ 且 `(m:ℝ)≤h ∧ h<(m:ℝ)+1`，全部 n:ℕ，包含0。记同一吸收位置 `H_N:=m+1`、`H:=(m:ℝ)+1`；H 不是独立实参数。原 h≥1 的 floor 解释是 m=⌊h⌋₊；整数 h=m 的弱端点仍保留 ±m，吸收在 ±(m+1)。

对 ℓ∈Finset.range(m+1) 记

`α_m,ℓ := ((2*ℓ+1:ℕ):ℝ)*π/(4*H)`，
`β_m,ℓ := 2*α_m,ℓ = ((2*ℓ+1:ℕ):ℝ)*π/(2*H)`。

`cot x := Real.cos x / Real.sin x`，`tan x := Real.sin x / Real.cos x`。在配对下半部使用的角度严格属于 (0,π/4)，所以这些分母非零；不增添分母非零的自由前提。

固定下半部索引和反射：

`K_m := {ℓ∈Finset.range(m+1) | 2*ℓ < m}`，
`ι_m(ℓ) := m-ℓ`。

K_m 含0。其源频率 r=2*ℓ+1 满足 1≤r<H_N；反射频率为 `2*H_N-r`，反射 S1 索引为 m-ℓ。若 m 为偶数，唯一未配对奇数频率是 j=H_N，对应 ℓ=m/2；若 m 为奇数，不存在未配对奇数频率。不得把自然数减法用于越出这些已固定索引的情况。

记

`ε_m(n) := (-1:ℝ)^(n+m)`，
`a_m := (1/H)*cot(π/(4*H))`，
`ρ_m := Real.cos(π/(2*H))`，
`Z_m(n) := if Even m then ((-1:ℝ)^(m/2)/H)*(0:ℝ)^n else 0`。

Z_m 是中心零特征值的实际贡献，不是概率修补项。自然数幂约定 `0^0=1`。必须由固定范围验证 `a_m>0`、`0<ρ_m<1` 及 `a_m*ρ_m^n>0`；这些是定义对象的必需 helper 结论，不是附加假设。不以 p(n,h) 作分母。

## 3. P1：全时间精确配对身份

对第2节的全部 m、h、n，要求原 S1 全部索引在反射 ι_m 下的确切分解，并要求实际概率满足

p(n,h)
 = (1/H) * ∑ ℓ∈K_m,
     (-1:ℝ)^ℓ
       * (cot(α_m,ℓ) + ε_m(n)*tan(α_m,ℓ))
       * (Real.cos(β_m,ℓ))^n
   + Z_m(n)。

有限和是未归一化计数和。原全奇数索引是 K_m、其反射像、以及仅当 Even m 时的唯一中心点的互不重叠覆盖；不能只写一个未绑定原 S1 的新配对谱和。

首对 ℓ=0 必须精确等于

`a_m*ρ_m^n * (1 + ε_m(n)*(tan(π/(4*H)))^2)`。

因此最负模态自身的系数是 `((-1:ℝ)^m/H)*tan(π/(4*H))`，其带时间因子是该系数乘 `(-ρ_m)^n`。它并非独立的正主模态，也不能丢掉时间或 m 的奇偶性。

## 4. P2：同一身份的显式归一化余谱输出

对全部 n:ℕ 定义一个只依赖 m、n 的明确有限表达式，不引入自由误差变量：

R_m(n)
 := ∑ ℓ∈(K_m.erase 0),
      (-1:ℝ)^ℓ
        * ((cot(α_m,ℓ) + ε_m(n)*tan(α_m,ℓ)) / cot(π/(4*H)))
        * (Real.cos(β_m,ℓ)/ρ_m)^n
    + Z_m(n)/(a_m*ρ_m^n)。

同一目标可输出为

`p(n,h) = a_m*ρ_m^n * (1 + ε_m(n)*(tan(π/(4*H)))^2 + R_m(n))`。

n≥1 时 Z_m(n)=0，故 R_m(n) 恰为显示式中的余谱有限和，所有余谱频率均满足奇数 r=2*ℓ+1≥3 且 r<H_N。n=0 时保留显示的 Z_m(0) 项，完整右侧必须恢复1。本候选不把 n=0 并入任何“零谱无贡献”的陈述。

m=1（H_N=2）或 m=2（H_N=3）时 K_m.erase 0 为空；此时 n≥1 的 R_m(n)=0。m=2 的 n=0 仍有中心零模态，不得因正时间的空尾和而删除它。

## 5. 时间、常数、误差与极限的明确排除

P1/P2 是所有自然时间的精确等式，不含 O/o 项、极限、未定常数或长时间阈值。n≥1 仅用于中心零模态消失的准确特化，不是本叶整体的时间前提。不得加 `n/H^2≥1`、H→∞、奇偶匹配、正生存、全谱为正、非零谱、无周期、混合、非格点或正概率条件来缩小本叶。

后续完整 S2 尚须另叶证明下列来源绑定候选强度，本文件不予冻结或认证：存在一个绝对常数 C>0，独立于 m、h、n 与奇偶性，使对所有上述 m、h 和 n:ℕ，若 `H^2≤(n:ℝ)`，则

`|R_m(n)| ≤ C * Real.exp(-π^2*(n:ℝ)/H^2)`。

该时间阈值来自原第55行的 n/H²≥1，不准只在任意更强阈值上证明后仍称原范围完成。原 S2 第38–43行的极限是 H→∞ 且 n/H²→∞；完整的统一界与该双尺度解释须以后由全新来源语义审查确认，不能由此精确配对身份直接宣称。

## 6. 依赖、边界与下一门

直接所需数学接口只有固定 S1 C4 的实际概率恒等式及其对象定义。S1 C5 的 0≤h<1 分支已经另行冻结，当前不消费、不扩成 m=0 配对谱。Iteration／FiniteBasis／AllModes 的支持、基与有限幂通过 S1 传递，不重新以自由 λ_j、新矩阵递推、归一化链或新 law 取代。精确三角反射、有限索引划分以及归一化分母的合法性属于本新叶待证明内容；不是可以假定的外部引理。

负谱全部通过反射项保留；中心零谱在 n=0 保留；弱 h=m 端点不改为 strict；起点固定0，不扩到其他实 coset。布朗 U 的定义／尾部展开、对数比、n/h³ 的格点位移、critical subsequence／cluster set、strict 事件及一般 OQ4 均不在本候选范围。S2–S5、Spectrum 与 OQ4 root 继续 OPEN。

本文件没有数学证明或 Lean 实施。来源仅为原始 spectrum01.md、四个明确许可的固定数学接口，以及 lead 的派发状态信息；未读其他 intake/candidate 历史、任何 anonymousproof、math/formalreview、作者过程、未认证新实施或 private Source。没有意外暴露受限推理。只修改本候选及配套 intake 两个获分配文件。
