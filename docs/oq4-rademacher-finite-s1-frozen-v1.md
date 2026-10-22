# OQ4 零起点显式有限 S1 与低阈值分支：冻结数学接口 v1

STATUS: FROZEN_PENDING_STATEMENT_REVIEW
REVIEW_STATUS: NOT_REVIEWED
PROOF_STATUS: NOT_WRITTEN
IMPLEMENTATION_AUTHORIZATION: HOLD_PENDING_UPSTREAM_FORMAL_CERTIFICATION_AND_MATH_GATES
SPECTRUM_STATUS: OPEN
ROOT_STATUS: OPEN

Lead 明确采纳本文件 C1–C5 并冻结为 v1；原候选 90ad40eebdef764a385385ace3720318a9fa9634661ab523c1c81499424d26c5 保留原字节。固定将来模块 Shao/OQ4/RademacherFiniteS1.lean，namespace Shao.OQ4.RademacherFiniteS1。当前仍待全新独立来源语义核验，不是数学证明或 Lean 认证；下列结论是待证目标，不是可作为新假设输入的关系。第4节 floor 总述可作导出helper，C4和C5完整覆盖全部h>=0是强制范围，不得只交一支。

## 1. 来源与最小范围

固定 `C:/game/shao/current/oq4/c01/spectrum01.md`，commit `35d4580b61e22e7145f47730045a09874ef93259`，SHA256 `b65f9e0c2f9b40a28d092491b479bd20d0b8ee8a9ac940c3c4760cfff7d2670b`，4306 bytes。

本冻结命题仅接已固定 AllModes D1/D2 的 F=1 实际 raw mass sum，处理原第 22–34 行：零起点模态值、奇数有限正弦和、奇数重编号、真实 closedStrip 的 S1，以及 0≤h<1 的独立分支。原第 11–21 行特征基与全部模态幂由既定上游分别交付，不重造。逐原子核谱、任意有限数据或任意实测试函数的谱、S2–S5 渐近、strict 事件与一般 OQ4 均不在此冻结命题。

固定上游数学接口：

- `frozen-rademacher-iteration-v1.md`，SHA256 `15851002ccadaa118035107c8b9b8266dd825fdebdf36728f3ac7a97f7330b80`。
- `frozen-rademacher-finite-basis-v1.md`，SHA256 `4672baa6bc550de2a97ca9adc0730b5633f71458b2c3da8b02c2318131e05a7f`。
- `frozen-rademacher-all-modes-v1.md`，SHA256 `dac2fd30e7c759137e14ebd64c4d7457155a201da04a7226449304d0b4abbe10`。

lead 派发确认 Iteration canonical39 已独立最终 LEAN_FULLY_CHECKED，PR82、head `db692904c6977b2a783184838bb7a4d4acd98c77`；FiniteBasis canonical40 已 AUTHOR_CANONICAL_READY、独立最终形式审查中；AllModes 匿名数学独审已 CORRECT，但后两者尚未全部形式认证。冻结数学接口只是后继的精确承诺，不能以它们冒称本冻结命题已证或导入未认证实施。

## 2. 固定真实 law、路径概率与谱对象

真实概率律唯一固定为

ν_R := Shao.OQ4.RademacherCosine.law
     = (1/2 : ℝ≥0∞) • Measure.dirac (1:ℝ)
       + (1/2 : ℝ≥0∞) • Measure.dirac (-1:ℝ)。

使用其已有内部 `law_isProbabilityMeasure` 实例，不额外量化一个 law 或概率性假设。对每个 n:ℕ，固定

Path n := Fin n → ℝ，
P_n := Measure.pi (fun _ : Fin n => ν_R)，
S_k(a) := Shao.prefixSum a k
        = ∑ i∈Finset.univ.filter (fun i:Fin n => i.val<k), a i，
A_n(h) := Shao.closedStrip h
        = {a : Path n | ∀k:ℕ, k≤n → |S_k(a)|≤h}，
p(n,h) := P_n.real A_n(h)。

p 是真实乘积路径概率的实值，不是新矩阵的总质量定义。只对 h≥0 作最终概率声明；此时 A_n(h) 与原文的 `M_n≤h`（1≤k≤n 的弱生存）一致。n=0 按原文空路径事件概率 1 解释，不依赖空集最大值的未定约定。

高阈值部分量化所有 m:ℕ 且 1≤m，定义同一个吸收位置的三种数值类型

H_N:=m+1，H_Z:=(m:ℤ)+1，H:=(m:ℝ)+1。

它们不是独立参数。量化全部 h:ℝ，满足 `(m:ℝ)≤h ∧ h<(m:ℝ)+1`；量化所有 n:ℕ，包括 0。真实起点固定为 0。

沿用同一有限对象，不另造自由特征值：

I_m := Finset.Icc (-(m:ℤ)) (m:ℤ)，
J_m := Finset.Icc (1:ℕ) (2*m+1)，
θ_m,j := (j:ℝ)*RademacherCosine.angle m = (j:ℝ)*π/(2*H)，
μ_m,j := Real.cos θ_m,j，
φ_m,j(w) := Real.sin (θ_m,j*(w+H))，
v_m,j(s) := φ_m,j((s:ℝ))，
q_m,j := (1/H)*∑ s∈I_m, v_m,j(s)。

有限和为未归一化计数和；1/H 来自已固定范数 H。记 cot(x):=Real.cos(x)/Real.sin(x)，只使用本冻结命题所列的非零角度。

后继所接的 AllModes D2 数学接口为同一真实核上的

killedMass ν_R h n 0
  = ∑ j∈J_m, q_m,j*(μ_m,j)^n*v_m,j(0)。

此行只是引用尚待上游认证的承诺，不是本文件的已证前提；未来实施必须接其实际认证声明，不得变成自由假设、新公理或新矩阵递推。真实概率桥已存在：对 0≤h，`killedMass ν_R h n 0=p(n,h)`。

## 3. 冻结的精确结论

以下 C1–C5 只分解语义交付，不按编号预先计算公开 Lean 定理数。

### C1. 全部指标的零起点值

对全部 m:ℕ、1≤m，及每个 j∈J_m，

v_m,j(0) = sin((j:ℝ)*π/2)。

其中偶数指标精确为 j=2*k，k∈Finset.Icc (1:ℕ) m，其值为 0；奇数指标精确为 j=2*ℓ+1，ℓ∈Finset.range(m+1)，其值为 `(-1:ℝ)^ℓ`。不得先假设 j 为奇数而省略全 J_m 的起点核对。

### C2. 仅奇数模态所需的有限正弦和与系数

对全部 m:ℕ、1≤m，及每个 ℓ∈Finset.range(m+1)，令 j=2*ℓ+1，则

∑ s∈I_m, v_m,j(s) = cot((j:ℝ)*π/(4*H))，
q_m,j = (1/H)*cot((j:ℝ)*π/(4*H))。

等价量词为“对每个奇数 j∈J_m”。本目标不要求额外公开偶数 j 的有限正弦和公式；它们在零起点 raw mass sum 中由 C1 的实际起点值消去。cot 参数属于 (0,π/2)，不引入分母为零的未定义解释。

### C3. 源全指标与奇数指标的精确对应

J_m={1,…,2*H_N−1}；奇数子集与 Finset.range H_N 的双射为

ℓ ↦ 2*ℓ+1，逆向 j ↦ (j−1)/2。

逆向自然数除法只在奇数 j∈J_m 上使用。奇数首末分别为 j=1 与 j=2*m+1，对应 ℓ=0 与 ℓ=m；偶数补集为 {2*k | 1≤k≤m}。不得循环重标号、漏掉末模态或多算一个吸收端点。只需要足以把 D2 的同一有限和重编号的精确身份，不扩张完整核谱。

### C4. 实际路径概率的完整有限 S1

对第 2 节的所有 m、h、n，

p(n,h) = killedMass ν_R h n 0
 = (1/H) * ∑ ℓ∈Finset.range(m+1),
     (-1:ℝ)^ℓ
       * cot(((2*ℓ+1:ℕ):ℝ)*π/(4*H))
       * (Real.cos (((2*ℓ+1:ℕ):ℝ)*π/(2*H)))^n。

乘法与幂均在 ℝ 中；两个指数 ℓ、n 都是自然数。求和恰是原 S1 的 ℓ=0,…,H_N−1。不能只给 raw mass sum、只给加权余弦积分、只给主模态或以渐近／上下界替代此等式。

n=0 在同一显示式内，且右侧必须等于 1。对每一个 μ，包括 μ=0，使用自然数幂 μ^0=1；不删除零谱项以另算 n=0。

### C5. 原文独立低阈值分支

对全部 h:ℝ，若 0≤h<1，则对全部 n:ℕ，

p(n,h) = killedMass ν_R h n 0
       = if n=0 then 1 else 0。

这是原第 33–34 行的单独交付，不使用 C4 的显示式、不声称建立 m=0 的完整谱基或全部模态幂。已有 RademacherCosine.killedKernel_row 的签名允许 m=0，可作为此分支的已认证真实核依赖；不需要把主余弦定理的 1≤m 前提改掉。

## 4. 实阈值／floor 的总述与覆盖判据

对所有 h≥1，取 `m=⌊h⌋₊:ℕ`（非负实数的自然数 floor）；它与原文整数 floor 的非负值相同，满足 1≤m 和 m≤h<m+1。于是 C4 就是原有限 S1；H_N=m+1、H=(m:ℝ)+1。整数 h=k≥1 时 m=k、H=k+1，不用 ceil(h)，也不吸收在 ±h。

记 F(m,n) 为 C4 的同一有限和，则可选的导出总述是：对所有 h≥0、n:ℕ，

p(n,h) = if h<1 then (if n=0 then 1 else 0) else F(⌊h⌋₊,n)。

C4+C5 语义上足以覆盖原文全部 0≤h 的有限生存部分；只交 C4 或只交 m=0 则都不足。上式没有把 S1 显示式扩到低阈值，亦不声称 h<0、strict 事件或其他 coset 的结果。

## 5. 零谱、负谱与弱边界的不可变要求

1. 全谱的零特征值位置是 j=H_N=m+1。若 H_N 为奇数（m 为偶数），它在奇数和中对应 ℓ=m/2，cot 参数为 π/4。其 n=0 贡献为 `(-1:ℝ)^(m/2)/H`，必须保留；n≥1 才有 0^n=0。若 H_N 为偶数，该 j 是偶数，只因 C1 的 v(0)=0 而消去，不能援引“零谱从不贡献”。
2. j>H_N 的负 μ 全部保留，特别是 j=2*m+1、ℓ=m。使用有符号 μ^n，不以 |μ|^n 代替，不用正主模态 rho^n 代完整生存。
3. 不加正生存、正特征值、非零特征值、无周期、混合或非格点前提；不加 n 与模态／状态的奇偶匹配前提。有限谱的消去按原有精确和发生。
4. h=m 保留 ±m 的弱端点；边界行向外丢失的概率不重新归一化。真实 killedMass 可以为零；任何一步都不把它用作分母。
5. 起点固定为 0。非整数实起点可达其他 coset，不属于本冻结命题；strict 事件 M_n<h 也不属于本冻结命题。n=0 的空路径约定不删除其他时间的真实事件。

## 6. 依赖、认证门与未关闭范围

已认证基础依赖：RademacherCosine（PR72／source `c0ba478f9ed6b5aa75d7010d70835b37065a92e9878c65b086d3c3ff24e7f861`）的 law、概率实例、angle、rho、integer_closed_iff、killedKernel_row；KilledKernel 的真实闭区间限制，KilledIteration 的真实有限幂／mass 定义与零步 Dirac，KilledPathLaw 的实际乘积路径概率桥。完整公开签名及只读源指纹见配套 intake 第 3 节，不读取它们的证明体。

本冻结不是数学证明。先全新独立来源翻译审查 CORRECT，再由新作者给匿名数学证明和全新匿名数学独审。来源与数学阶段可使用固定上游数学引理接口，不读取未认证实施或其他审查推理；实际 Lean 实施须全部上游完整形式认证、接口一致、独立数学 CORRECT 且 lead 明确授权。之后 canonical 唯一写入／作者唯一 olean emit 窗口还须另行释放；独立 canonical target no-o、完整原 source 的全部 getModuleIdxFor?=none 无 name/namespace 筛选、actual 全冻结 imports owner OR namespace 全量审计 private/generated/outside-name 常量，source/import 原名/kind/universe/fullExprtype/axioms/定义体/实例标记 exact，lead import-only；旧source/common/root/pins/产物哈希守恒。所有 Lean/重计算只在指定server，shell workdir C:/game/shao lean；原日志/Expr/二进制仅服务器。禁止 sorry/admit/new axiom/unsafe/native_decide，标准公理白名单仅 propext、Classical.choice、Quot.sound。后续作者不得修改 law、概率对象、阈值、相位、指标、范数、端点、起点类或时间量词；必要更改须 lead 另立版本。

在完整门完成前不得把本叶标记 PROVED 或 LEAN_FULLY_CHECKED；单独来源／数学门的 CORRECT 必须明确限定证据类型。即使本有限叶最后通过，S2 的配对／统一余项、S3 布朗基准、S4 格点位移渐近、S5 临界子列、strict 边界分类、sharp01 与一般 OQ4 仍不由此叶关闭；Spectrum/OQ4 根维持 OPEN。

PROVENANCE: 仅原始来源、三个固定数学接口及已认证透明定义／公开签名的独立只读规范化；未读取匿名证明、未认证实施源码或审查推理。
