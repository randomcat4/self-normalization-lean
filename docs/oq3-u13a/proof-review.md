# U13a NormalLayerFourier 完整独立证明审查

STATUS: CORRECT

审查者：独立 reviewer，lease 1。仅本新报告及获授权的远端同名报告可写；不修改实现、旧票、共享文件或缓存，不编译、不生成实例。此前已审声明，存在声明上下文；以下翻译仍先从本次实际实现公开定义体和完整类型独立提取，未读取本次证明体、scope 说明、receipt 或机械日志。本节先落盘，然后才继续后续阶段。

## 1. 实际公开声明的先行盲译

实际文件：`drafts/oq3/NormalLayerFourier.lean`，预期 SHA256 `063b6c5ce50e6c5ee33b53301cdfcd36a63a4ea06f9c3de729756513ca736fa3`。公开导入为 SampleBoundary、FiniteFarArc、Mathlib.Analysis.SpecialFunctions.Integrals.Basic、Mathlib.MeasureTheory.Integral.Pi；namespace Shao.OQ3，open MeasureTheory，scoped BigOperators Matrix，noncomputable。以下尚未以 scope 或 receipt 判断匹配。

记 Path n=Fin n→ℝ，M_q(z)=normalDeviation q z，R_a(z)=Σ_i z_i−na，λ_n=⊗_{i∈Fin n}μ。实际定义的样本空间与 M 的展开语义将在下一阶段读取真实前置核对。

1. `normalLayerIntegrand q a d s n z`：事件 `{w | M_q(w)=d}` 的指标乘以 `exp(i·s R_a(w)/sqrt(n))`。参数 q,a,d,s 任意实数，n 任意自然数，值为复数。sqrt(0) 和除法在 Lean 实数域中总化；定义没有 n>0 门，也没有对该除法作非零消去。
2. `normalLayerCharacteristic μ q a d s n`：上述复函数对真实 n 重乘积测度 λ_n 的 Bochner 积分。定义本身不要求 μ 为概率、不要求层有正质量；这是一项未归一化层积分。
3. `normal_lattice_character_orthogonality h hh k`：对任意 h>0 与整数 k，`(h/(2π))∫_{[-π/h,π/h]}exp(i t h k) dt` 等于 k=0 时的 1，否则为 0。积分测度显式为 ℝ 的 volume，系数嵌入 ℂ。
4. `iid_centeredNormalTangentCharacteristic_power μ q a t s n`：μ 为概率时，对任意实数 q,a,t,s 与任意 n，真实乘积积分 `E_{λ_n} exp(i[t M_q(z)+s R_a(z)])` 等于 `centeredNormalTangentCharacteristic μ q a t s` 的 n 次幂。类型未要求中心确为均值、任何矩存在、n>0 或非退化。
5. `normalLayerIntegrand_integrable μ q a d s n`：μ 为概率时，上述层指标相位函数对 λ_n 真正 Integrable；任意实参数与所有 n 均有效。
6. `normal_layer_Fourier_identity μ q a h d s hh hgrid n hlayer`：μ 为概率，h>0，μ 几乎处处 `normalValue x=h k`（某整数 k，零偏移格点）；另给层相容性 `d+nq=h k₀`。则同一 μ 的未归一化层积分恰等于

   `(h/(2π)) ∫_{[-π/h,π/h]} exp(−i t d) · centeredNormalTangentCharacteristic μ q a t ((sqrt n)⁻¹s)^n dt`。

   相位为负号；切向频率为 s/sqrt n；q,a 任意，n 包括 0；不要求层概率正、中心等于均值、μ 的矩或最小格距。
7. `finite_atomic_normal_layer_Fourier_identity ell q p r J hM hc hp hr d s n hlayer`：同一 ell,q,p,r,J 下，约束矩阵行列式非零且 M p=target q，有限修正基权每项非负、所有 r_j 非负。取实际 μ=`atomicMeasure (finiteMass ell p r J)`，中心 q 与 q/4，h=`dyadicMesh J`；若 `d+nq∈hℤ`，则上一精确反演恒等式对该实际 μ 成立。类型不要求 Summable r、J>0、n>0、所有权严格正或另选参数族。

盲译阶段范围：两定义及五完整公开定理；没有以定理名推断真可积、概率、格点或独立性。后续必须分别核实这些语义与所有证明。

## 2. 来源、冻结声明和范围核对

实际源码 SHA256 已核为 `063b6c5ce50e6c5ee33b53301cdfcd36a63a4ea06f9c3de729756513ca736fa3`（248 行）。v2 scope SHA256 `024110d50ff7fa8638a063be0ac0825c9b17b0259f95c23e694ea0f1cdc3695a`；原 v2 声明票 SHA256 `3c6c667269fa12ffe8ccbcfa56132e59589d61fd04f19fa66fd22ad5084a182e`。从实际源逐声明剥离 proof 后，两定义体及五完整公开类型与 v2 Lean fence 白空格规范比较逐项及整体相同。v1/v2 的 Lean fence 逐字相同；v2 显式增加 Integral.Pi 导入，其源码第 8 行公开转导 Integral.Prod。实际实现采用 v2 的四个 imports。

真实 R1 原件 SHA256 `3473d34ff20bd0d334b9ef3ea3c3ee167fba4d5cc3a742849820ce54d639e662` 已核。309–345 中 318–319 定义 M_n、R_n，332–337 仅在 Y 上作格点反演并使用真实联合中心特征的 n 次幂。本单元给其精确有限样本反演恒等式，不给 339–344 的最大性远弧收缩、二阶展开、渐近高斯积分或 Lévy 步骤。真实 `normalValue x=8x−x²`（FiniteConstraints:28），`normalDeviation q z=ΣY(z_i)−nq`（SampleBoundary:19–20），`Path n=Fin n→ℝ`（FinitePath:18），`centeredNormalTangentCharacteristic` 是同一 μ 的真实单坐标指数积分（FiniteFarArc:21–23）。因此盲译中的 M、R、μ 和相位均与来源相符。

勘误（只记在本新报告）：旧 scope 说明及旧声明票所写 `intervalIntegral.integral_exp_mul_complex` 的命名空间不正确。固定库实际定理名为**全局 `integral_exp_mul_complex`**；源码第 64 行也实际调用这个名字。`intervalIntegral.integral_of_le` 才属于 intervalIntegral。此前静态可用性判断和本次实际数学公式不变；本报告如实更正，旧票和 scope 不追改。

一般 μ 目标没有正定协方差、均值或最大格距门，因为这里只用零偏移 hℤ 支撑与层相容性；不是声称每个 h 都是最大格距，也不是已证明条件概率归一化。有限实例使用实际 π_J=`atomicMeasure(finiteMass ...)`，未替换为逆倾斜原律 P_J。所有根 A/B/C/D 仍 OPEN。

## 3. 全部实现及固定数学语义

### 3.1 逐段证明核对（在读取 TYPE、receipt 或机械绿灯之前作出）

- **13–20，两定义**：层事件指标、相位与同一真实有限乘积测度如盲译。无正层质量除法，零层质量合法。
- **22–65，整数正交**：27–34 由 h>0、π>0 得端点顺序；连续相位确立真实 `IntegrableOn Icc volume`，不是依赖总化积分。k=0 时积分是 Lebesgue 区间真实长度 2π/h，复标量归一化为 1。k≠0 时 c=(hk)i，由 h≠0、整数嵌入 k≠0、i≠0 得 c≠0。55–62 用整数 k 的真周期 `exp(x)=exp(y) ↔ ∃m∈ℤ,x=y+2πim`，端点差恰为 2πik，包含负 k。63–65 只去掉 Lebesgue 零质量端点，按有序端点转成有向区间积分，再用真实复指数原函数公式；分子为零而 c 非零，给 0。没有对实频率擅用整数正交。
- **67–99，iid 幂恒等式**：单坐标 f 连续（Y 是多项式），复指数范数恒为 1；概率门使 `Integrable.of_bound` 得真可积。80–82 在使用产品积分公式前以 `Integrable.fin_nat_prod` 证真实 n 坐标乘积可积。86–96 展开 M、R 为各坐标同一 q,a 的中心相位和，有限和常数为 nq、na，cast 和 exp(sum)=prod 正确。97–99 使用同一 μ 的有限产品公式，指数恰为 card(Fin n)=n。库产品公式本身对总化积分适用，但本实现另有 `_hprod` 真可积凭据，未借总化零值假装概率分解。
- **101–117，层可积**：M 连续，等值层是闭集因而可测；切向相位连续且范数 1，对真实产品概率真可积；再用可测 indicator 保可积。sqrt n 是固定实常数，不需要在这里消去或假定 n>0。
- **129–149，反演的联合可积先行**：B 是有限紧 Icc，Lebesgue 对 B 的限制有限；ν 是真实 μ^Fin n 概率。F(t,z)=exp(i t(M−d))·exp(i sR/sqrt n) 在 ℝ×Path n 上连续，范数恒 1。限制体积 × ν 是有限测度，所以 145–149 给真实 joint Integrable，**先于**任何 Fubini。并非在全无限体积上仅凭 norm≤1 声称可积。
- **150–165，真实产品 AE 格点提升**：`Measure.tendsto_eval_ae_ae` 把给定单坐标 hgrid 提升至每个实际产品坐标；`ae_all_iff` 在有限 Fin n 上合取。选整数 k_i 后由 hlayer 的整数 k₀，实际 M−d=h(Σk_i−k₀)。d+nq 中的正号与 M−d 中的负号精确抵消，没有丢掉非整中心偏移，也没有把任意 affine offset 当作零 offset。
- **166–197，AE 层指标正交**：h≠0 使所得整数 k=0 当且仅当 M=d，含不可达但相容层。点态用第一定理得到 indicator；切向相位是 t 的常数，以 `integral_mul_const` 拉出。固定 z 的相位在有限 B 真可积（连续且模 1），同上 F 的切片也真可积，非以积分总化代替积分存在。
- **198–220，真实内积分与合法换序**：将 F 的相位重写为 `−td + tM + (sqrt n)⁻¹s R`，与切向 `sR/sqrt n` 仅用域的乘法恒等式，**没有消 sqrt n**。因此 n=0 时同样合法。198–209 使用本单元真实 iid 幂恒等式，保留 exp(−itd) 负相位与同一 μ。210–220 先 AE 积分相等、常数移出，再凭已给 hF 使用 `integral_integral_swap`。这是正确定向的 `(volume.restrict B).prod ν` 联合可积门；hF 也保证换序后的迭代积分真可积，hinner 的逐 t 等式将其识别为 RHS Fourier 被积函数。没有隐含未证明的乘积换测度。
- **234–245，有限原子实例**：w 为同一个 finiteMass ell p r J。hp/hr 给整个 AtomicIndex 非负；hM/hc 经真实有限补偿矩阵等式给四个 HasSum。第 0 行 constraintFeature=1、target=1 提供真实 HasSum w 1，`atomicMeasure_isProbabilityMeasure` 于是给真正概率。实际 `atomicMeasure_finiteMass_ae_range` 去除所有 j≥J 的零质量项，取活跃 Fin4⊕FinJ 的 stageAtom；`stageAtom_normalValue_lattice` 给该点属于 mesh_Jℤ，mesh_J=(2^J)⁻¹>0。最后仅实例化一般反演。没有用全无限索引上的严格正质量、最大格距或 Summable r。

### 3.2 承重前置的实际语义与闭包

从实际 source 的 Shao imports 递归独立枚举出 14 项此前已独立审查的前置：12 个 OQ3 源 FiniteConstraints、SourceStarter、SummableAtoms、AtomicMeasure、InverseTilt、FiniteStageMeasure、AtomProjection、ResonanceArithmetic、FiniteNormalSpan、SampleBoundary、JointNonlattice、FiniteFarArc，加共享 FinitePath、FiniteIID。没有 U12b/c/d/e/f 依赖。最后机械阶段再把这个独立闭包与 receipt 及真实服务器逐源 hash 比较。

本次重读了实际消费的定义及证明：constraintMatrix 的行 k/列 i、target=[1,0,0,q]；finiteBase=p−M⁻¹addedMoment；finiteMass 对 AtomicIndex=Fin4⊕ℕ 作未来零延拓；finiteMass_constraints 的有限 HasSum 和 M·M⁻¹ 消去真实消费 hM；非负权与 HasSum1 给 sum-dirac 概率；AE_range 通过每个 Dirac 和未来零权取得真实活跃有限支撑。`stageAtom_normalValue_lattice` 的前置 scaled_integer 分别取基点 Y=[−9,7,6,12] 和 addedAtom j 的 Y=6+2^{−(j+1)}；j<J 保证 j+1≤J，乘 2^J 后整数，除回给 mesh_Jℤ。没有从“支撑看似有限”臆测概率或格点。共享 FiniteIID 的真实 μ^Fin n 与 FinitePath 的样本类型相同；本单元直接对真实 Measure.pi 积分，未调用未经验证的抽象 iid 替代物。

### 3.3 固定库真实语义

通过共享 broker 只读实际 pinned Mathlib 源，未运行 Lean/API 探针或构建：

| API 与实际位置 | 本次检查的前提及用途 | 源 SHA256 |
|---|---|---|
| Integrals/Basic:242–250 `integral_exp_mul_complex` | 全局名字，c≠0；真复指数原函数的有向实积分式 | `9f989cc31de77616c518e6b435d1af387596c6c6ab317b1c4b979c5f8f73f022` |
| Complex/Log:172–173 `Complex.exp_eq_exp_iff_exists_int` | 差为真正整数倍 2πi，端点周期 | `991a8c873c89b62bd9724a88b91e7ca17f5947c736dd6b026b5fac0a5913dbeb` |
| Integral/Pi:8,33–39,119–122 | public import Prod；各坐标 SigmaFinite 与真可积给真产品可积；实际积分乘积/n 次幂 | `43c50a9d9a683b2050e145154410a7260c3dd84f3ec3010630cc6b90572afcd9` |
| Constructions/Pi:303–313,425–426 | 有限产品概率实例，真实 eval 的 AE 滤子提升；空 Fin0 合法 | `bb89dee63d412cd1cc1f7f9fd7a81d64074139571960b2f0fcb66d8b763cd6ef` |
| Integral/Prod:443,466,471–483 | 真 joint Integrable 才可交换两个 Bochner 积分；这里实/有限维实样本，复值完备 | `8ccfbcad5fffde3f8d0dfa3167b80dacfb524bc10790f1744b8b8a9b3f4c3a05` |
| IntervalIntegral/Basic:677 | a≤b 时有向积分等于 Ioc setIntegral | `bf8558a4cb789e3505cfb08a6712ce83017719be2523e862d5e52f082433814c` |
| Bochner/Set:669–671,697–700 | NullSingletonClass 的真实端点去除，不改变 Lebesgue 积分 | `e4d90b9fde463a9123e1ac3321ce25c0714e19ce92e172f297e062d9de16be75` |
| Lebesgue/Basic（经 FiniteFarArc 可见） | ℝ 的 actual volume，紧区间有限、单点零、真实区间长度 | `4955d3400a03ba9d525206fcf1cff8592497dfff06674ca13d68d3bdcabb964d` |

另逐源码核 `Integral/IntegrableOn:171–172` 的 `Integrable.of_bound` 明确要求有限测度与 AEStronglyMeasurable，353–355 的 `Integrable.indicator` 明确要求可测集合；`Function/LocallyIntegrable:595–597` 的连续紧 Icc 真可积用于首目标。实际 μ 的概率和限制体积有限实例正好满足，Borel 实空间及有限乘积的连续相位提供强可测性。没有以未归一化无限 Lebesgue 常数界代替可积。

### 3.4 边界与独立数学阶段结论

n=0：真实空乘积概率总质量 1，空和为 0，M=R=0，sqrt0 的逆及除法总化为 0，切向相位 1。hlayer 变为 d∈hℤ；d=0 两侧为 1，d≠0 两侧为 0。证明没有用 n≠0，或非法约掉 sqrt0。J=0：mesh0=1、Fin0 添加支撑为空，只有四个基点整数 Y；未来权全零，有限 HasSum/概率/AE_range 仍成立。零活跃权和零层质量均允许；一般层相容但不可达时正交严格给零。q,a 任意是代数中心，类型并未假装任意中心是真均值。有限实例虽然给 q/q4，恒等式本身不需再消费均值结论。

**独立数学阶段结论：未发现声明/来源/全证明语义缺口。** 这句话在任何 actual TYPE 或作者机械绿灯读取前落盘；最终 STATUS 尚待所有实际声明和机械绑定核验。以上没有声称 LLT、层概率归一化、条件 Lévy、实际 hW 或根闭合。

## 4. 全部实际 owned TYPE

数学阶段结论落盘后，才通过只读服务器查询提取 Audit.log 的 DECL/TYPE 块及**全部缩进续行**，没有先读 receipt、AXIOMS 或 PASS。实际共 12 块；逐项如下（顺序为日志真实顺序）：

| # | 实际常量（共同前缀 Shao.OQ3） | 完整类型的语义检查 |
|---|---|---|
| 1 | `normal_layer_Fourier_identity` | μ 概率，∀q,a,h,d,s，h>0，μ-AE Y∈hℤ，∀n，d+nq∈hℤ → 本文精确负相位 Fourier 恒等式。长续行保留同一 μ、完整 `(sqrt n)⁻¹s` 与 n 次幂；无额外隐藏非退化/正层门。 |
| 2 | `iid_centeredNormalTangentCharacteristic_power._simp_1_1` | `∀ {α : Type u} [Preorder α] (a:α), (a≤a)=True`；一般自反序命题的命题等式，非新概率或积分假设。 |
| 3 | `normalLayerIntegrand.eq_1` | ∀q,a,d,s,n,z，实际函数等于真实层 indicator 与 `exp(i s(Σw_i−na)/sqrt n)` 的定义展开。逐续行核定义参数/空间与源码；generated equation 不改中心或引入正层质量。 |
| 4 | `finite_atomic_normal_layer_Fourier_identity` | ∀ell,q,p,r,J，hM、hc、∀i finiteBase_i≥0、∀j r_j≥0，∀d,s,n，d+nq∈mesh_Jℤ → 同一 finiteMass 实际 μ、中心 q/q4 的精确恒等式。长续行两个 μ 完全一致，无 Summable 或 J/n>0 门。 |
| 5 | `iid_centeredNormalTangentCharacteristic_power` | ∀μ概率,q,a,t,s,n，真实 Path n 上 Measure.pi μ 的完整样本相位积分等于同一单坐标 char^n；无替代抽象 iid 或额外矩门。 |
| 6 | `normalLayerCharacteristic` | `Measure ℝ → ℝ → ℝ → ℝ → ℝ → ℕ → ℂ`；依次 μ,q,a,d,s,n，与实际定义绑定。 |
| 7 | `normal_lattice_character_orthogonality` | ∀h>0，∀k:ℤ，h/(2π) 倍真实 Icc 积分 = if k=0 then1 else0；实 volume 由固定实例，未把 k 扩为实数。 |
| 8 | `normalLayerIntegrand_integrable` | ∀μ概率,q,a,d,s,n，真实层 integrand 对同一 μ^Fin n 的 Integrable；不是只含可测性或总化积分式。 |
| 9 | `iid_centeredNormalTangentCharacteristic_power._simp_1_2` | `∀ {ι} {R} [NonUnitalNonAssocSemiring R] (s:Finset ι) (f:ι→R) (a:R), Σ_{i∈s} a*f i = a*Σ_{i∈s}f i`；有限和乘法分配，未添加无限交换义务。 |
| 10 | `normalLayerIntegrand` | `ℝ → ℝ → ℝ → ℝ → (n:ℕ) → Path n → ℂ`；q,a,d,s,n,z 的依赖函数类型，与 eq_1 及公开定义一致。 |
| 11 | `normal_layer_Fourier_identity._simp_1_1` | 与 #2 一样的任意 Preorder 自反命题等式；独立实际常量已逐项读完。 |
| 12 | `normalLayerIntegrand_integrable._simp_1_1` | 与 #2 一样的任意 Preorder 自反命题等式；独立实际常量已逐项读完。 |

因此实际是 2 def、5 public theorem、5 generated theorem（1 定义方程、4 tactic simp：3 自反序等式和 1 有限和分配）。没有 authored private、额外公理声明、隐藏概率门或未审的 generated helper。所有 248 行实际实现中的局部 h*、B/C/ν/T/F/f/c 都在 §3 随调用核对；不把“没有 private 名字”当作省略局部证明审查的理由。至此完整数学与 TYPE 审查无缺口；作者 receipt 和机械事实仍尚未读取。

## 5. 最后机械绑定

完成上述独立数学及全部 TYPE 阶段后，才读取作者 receipt、Audit 源码和现有机械结果。仅通过共享 `tools/server.py` 只读远端实际文件；未复编成功 target/Audit，未把完整原始日志下载或写入本地。本报告与作者门分开：receipt 状态原为 `AUTHOR_KERNEL_AND_AXIOM_CHECKED_AWAITING_INDEPENDENT_PROOF_REVIEW`；本次 CORRECT 是独立审查所得，不是转述该状态。

实际远端工作树 `/root/rivermind-data/shao-lean-20261021/workspaces/lead-oq3`；run `/root/rivermind-data/shao-lean-20261021/runs/oq3/u13a-20261021`。

| 实际产物 | 字节数 / SHA256 与检查 |
|---|---|
| 工作树 `Shao/OQ3/NormalLayerFourier.lean`；run 同名快照；本地实际源 | 三者 SHA `063b6c5ce50e6c5ee33b53301cdfcd36a63a4ea06f9c3de729756513ca736fa3`，248 行，run 12147 bytes |
| run `scope-v2.md` 与本地冻结 v2 scope | 6841 bytes，`024110d50ff7fa8638a063be0ac0825c9b17b0259f95c23e694ea0f1cdc3695a` |
| run 历史 `scope.md`（v1） | 6544 bytes，`1c2b098c06c66f579ec9fda025cafee256dee053056d3b4005c0e47a9ecabc2f`；未覆盖为 v2 |
| run `statement-review.md` 与本地 v2 声明票 | 14786 bytes，`3c6c667269fa12ffe8ccbcfa56132e59589d61fd04f19fa66fd22ad5084a182e` |
| run `receipt.json` 与本地 `U13a-receipt.json` | 4264 bytes，`17f4ef3823bd766f0a45e0b9c00f8825b456945921a8d10cbd1c19ac6a2beb36` |
| run `Audit.lean` | 1731 bytes，`b4c207cc25714e95d0e26525220138e522d5c6cf4411a02ba92e759b6b040215`；实际源码全文只读核验 |
| run `Audit.log` | 4323 bytes，`f1d0d7a2c007afcf92e718abc0d8b7c3c88aef0249f98d8ac2586707f02597f4`；先 TYPE 后读计数/公理结果 |
| run `build-07.log` | 实际 0 bytes，空文件 SHA `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`；receipt 记录既有该 build exit_code=0，无新构建 |
| 实际已存在 `.lake/build/lib/lean/Shao/OQ3/NormalLayerFourier.olean` | 592824 bytes，`44e6db4c6a47e839d4f3f2e50d4a69255cb825b35bec82935e4e12420eb4eeb2`；只读查看 |

实际 Audit 源先检查五冻结目标确为 theorem；stems 覆盖两公开定义和五公开目标的全部后代，并覆盖 `_private.Shao.OQ3.NormalLayerFourier` 前缀。每项先拒绝新 axiom，再 `Lean.collectAxioms` 收集全部传递依赖并逐项对 `{propext,Classical.choice,Quot.sound}` 白名单检查。实际 12 DECL 与 §4 完全一致，各 AXIOMS 列表均为该白名单的子集；输出真实 `U13A_FROZEN_THEOREMS 5`、`U13A_ALL_THEOREMS 10`、`U13A_ALL_DECLARATIONS 12`、`U13A_AXIOM_GATE PASS`。源码本身仅七个顶层公开声明，所有生成项在其 stems 下；无遗漏额外顶层源码声明。receipt 的 Audit exit_code=0 是作者既有进程记录；本审查不冒称重新运行了内核。

### 5.1 真实 14 项目前置逐源绑定

独立从本地实际 import 链与远端工作树 import 链递归枚举，均恰为这 14 项，与最后才读的 receipt keys 集合完全相等；每项**本地实际源、远端实际源、receipt hash 三方逐一相等**：

| 项目前置（工作树相对路径） | SHA256 |
|---|---|
| Shao/Basic/FinitePath.lean | `898262898f9c088e2d10e6238e411b4397387b21b1b71a2b545c5edef936e1bb` |
| Shao/OQ3/AtomProjection.lean | `0d369052c7f87122765612efdeaca5d9ac71abca861e7785c86d1f9edcc74d22` |
| Shao/OQ3/AtomicMeasure.lean | `59ddc48fb7b395f362939e58cbd9d7911685a6ed6e6574142e8a6d4ab3ee0c39` |
| Shao/OQ3/FiniteConstraints.lean | `800d9db8cb6749a31ecfe611409de92b10ea8bb2aef955bfd825ede7324f0ef0` |
| Shao/OQ3/FiniteFarArc.lean | `3a0b05d0789e53320009a44499c9c40d0fb3d892427085052c65c04456b6cf71` |
| Shao/OQ3/FiniteNormalSpan.lean | `0374da4860edf8af8bbbb9172e4e93bfe9b6c37ac57672b85a4f58392475b7de` |
| Shao/OQ3/FiniteStageMeasure.lean | `1a32fb904e6ee9d2b0b48d92c4ebb3568452bb02500ce52a1a03eb01ae0256b1` |
| Shao/OQ3/InverseTilt.lean | `c7e7d19e8b70481b663bec1fd12ea9301d73313faaf35997e85aa9ba99f21811` |
| Shao/OQ3/JointNonlattice.lean | `51ce939232610353215fc3b7377e19b894451a9a108125e1828bf2fe8ec81559` |
| Shao/OQ3/ResonanceArithmetic.lean | `cd21a264d637bab30fed765bdc25ed09bb4ff56f6efb9c88ee09be4ca6e1648b` |
| Shao/OQ3/SampleBoundary.lean | `7660e23b71ce28ab43a4ad1d8df1862cf8a507b6bb9b41255e961f0bee0b93e2` |
| Shao/OQ3/SourceStarter.lean | `0e2a081619976f88149707c2ef9311dc909003e61d3d0f7c4e21e6c3dbbc5a6d` |
| Shao/OQ3/SummableAtoms.lean | `0ea4c64fe9ef9b45fbf44d24312771a1dbfbcc5de8448564e3e87bdf17c7178b` |
| Shao/Probability/FiniteIID.lean | `d1b565489199d55af70a27c31a0f803a2b7433e78c9197a361b3c10c0598845b` |

### 5.2 固定版本与扫描

实际只读 git：branch `feat/oq3-normal-layer-fourier`，HEAD `a50eb9d8b7b3dc479e183ba66f7b3da64cb13317`；工作树仅 `?? Shao/OQ3/NormalLayerFourier.lean`。实际 `lean-toolchain` 为 `leanprover/lean4:v4.36.0-rc1`（文件 SHA `d581a24b57a4ae9e0b2132ca8ac7cc3ac336a9fc2751fe6b29414e2d434d54c4`）；manifest SHA `40e8e3385f2b0c8ae56fa9de6947301472379cb62eeb83247944827c38b8af6e`。manifest mathlib rev 与真实 mathlib git HEAD 同为 `807d3836b165983210ee2ecf3cd28f239436949c`。

仅执行版本查询，实际 Lean `4.36.0-rc1`、commit `c9afcddf514a6772bd4d649f7cfc04eff0b9f15e`，Lake `5.0.0-src+c9afcdd`；没有 elaboration、API 探针或目标重编。源码 LF 无 CR、无尾空白，禁止项词界扫描 `sorry/admit/axiom/unsafe/native_decide/implemented_by` 均无命中；完整源码人工检查也未见替代内核或添加前提的设施。两定义/五目标冻结匹配已由 §2 独立重做，并非只读 receipt 的 PASS。

receipt 的 nonclaims 内仍有关于 U12f 在 author-check 时 pending/未提交的历史文字；本票不把这段当作实时 U12f 状态。本单元真实依赖闭包没有 U12f，实际 HEAD 如上，U13a 的判定绑定本源、实际前置与 pins；无需追改作者 receipt 或旧票。

## JUSTIFICATION

**STATUS: CORRECT。** 本次依次完成实际两定义/五完整类型先行盲译落盘、冻结 v2/source 对照、248 行全部证明与局部辅助/固定库语义、所有 12 actual owned TYPE（含全部 5 generated theorem）、最后真实服务器源码/14 前置闭包/pins/现有 build 与传递公理审计的绑定。未发现须修订的数学、声明或源对应缺口。

核心承重处均有真实前提：整数正交的 c≠0 与周期、产品积分的真可积、可测层与真实产品 AE 格点、有限限制体积×同一产品概率的联合可积先于 Fubini、负相位和 s/sqrt n、同一 finiteMass 的真非负 HasSum1 与活跃有限格点支撑。J=0、n=0、零权和零层质量合法，不消费 Summable r，不进行 sqrt0 消去。旧声明 API 命名空间笔误已在本新报告明确纠正，不改旧历史。

这是精确、未归一化的有限样本层 Fourier 恒等式及其同源 π_J 实例。没有证明 Fourier 渐近、完整混合 LLT、条件归一化/Lévy、实际 hW 或最终对角构造；根 A/B/C/D 全部 **OPEN**。未修改实现/旧票/公共文件/缓存，未 spawn、构建、commit 或 PR。最终报告交付到本地 `drafts/oq3/u13a-proof-review.md` 与获授权 run `proof-review.md`；两端最终 SHA256 随交付消息独立核验。


---

## U13a 收据 v2 纠错绑定附记（新最终版本）

STATUS: CORRECT

本文件以旧完整终审报告的全部 **24584 原始字节**逐字节原样为前缀；前缀 SHA256 为 `66856b2a0ca50ee1aa7d483f51ab04a4b6e52e85803fb2fd8b6ef230d5ee8efc`。旧 `u13a-proof-review.md` / run `proof-review.md` 及旧收据均作为原始历史证据保留，不追改。此附记仅审查收据标签纠错与绑定，不重复已经完成的数学、来源、全部 TYPE 或任何构建/Audit。

### 纠错事实与精确差异

本地旧 `U13a-receipt.json` 与远端旧 `receipt.json` 同为 4264 bytes，SHA256 `17f4ef3823bd766f0a45e0b9c00f8825b456945921a8d10cbd1c19ac6a2beb36`。本地新 `U13a-receipt-v2.json` 与远端新 `receipt-v2.json` 同为 4264 bytes，SHA256 `4ecaab82cf20b645393fc2d591e10e24fc831eb673a952037deb3e576d054583`。审查者通过共享 broker 独立只读核验两端文件，JSON 递归差异恰为下列两项：

1. `nonclaims[0]`：`Final independent U12f review pending at author-check time` → `Final independent U13a review pending at author-check time`。
2. `nonclaims[2]`：`No U12f commit/PR/merge at author-check time` → `No U13a commit/PR/merge at author-check time`。

另作原始字节比较：旧文件中的 `U12f` 恰出现两次，把这两个 ASCII 标签替换为 `U13a` 后与 v2 **全部字节相同**；JSON 去掉 nonclaims 后的所有字段逐项完全相同，nonclaims 中间一条完全相同。因此状态、源码/依赖/版本、命令、build/Audit hash、计数、公理白名单等均未改变。没有因为该文字修正重新生成编译或审计结果。

### 时间语义与旧报告解释的更正

这两个旧 `U12f` 标签是作者生成 U13a 收据时复制上一单元标签造成的**笔误**，不是关于 U12f 的真实历史状态。旧报告 §5.2 将其称为“关于 U12f 在 author-check 时 pending/未提交的历史文字”，此解释由本附记明确纠正；保留前缀是保存原审查历史，不表示继续采纳该标签解释。

新标签所述的是 **U13a 的 author-check 时点**，而不是本附记交付后的实时状态：作者门已成功、完整独立 U13a 终审尚待本实例完成，收据本来就明确记录 `AUTHOR_KERNEL_AND_AXIOM_CHECKED_AWAITING_INDEPENDENT_PROOF_REVIEW`。本实例随后才按既定顺序完成并交付旧完整终审报告，故 `Final independent U13a review pending at author-check time` 的时间限定和单元对象正确。该时点尚未发布 U13a commit/PR/merge；这一点与当时明确的“完整终审前不发布”流程及本次实际仓库状态一致，`No U13a commit/PR/merge at author-check time` 的对象与时间限定也正确。旧 U12f 已完成的状态不应被这两个复制标签覆盖。

本次实际只读服务器再次确认：branch `feat/oq3-normal-layer-fourier`，HEAD `a50eb9d8b7b3dc479e183ba66f7b3da64cb13317`，工作树仍仅 `?? Shao/OQ3/NormalLayerFourier.lean`，git 跟踪表尚无该源；实际源 SHA256 仍为 `063b6c5ce50e6c5ee33b53301cdfcd36a63a4ea06f9c3de729756513ca736fa3`。旧远端终审报告和旧远端收据 hash 也均保持原值。本次没有修改源/旧票/共享文件/缓存，没有 spawn、编译、Audit 重跑、commit 或 PR，也未读取任何后继 scope。

### 新最终裁决与权威绑定

**最终 STATUS: CORRECT。** 原完整数学/来源/实际 TYPE 与机械判定保持有效；附记独立确认 v2 仅透明修正两个单元标签，且修正后关于 U13a author-check 时点的含义正确。后续本单元发布所用 **authoritative receipt 为 `U13a-receipt-v2.json` / run `receipt-v2.json`，SHA256 `4ecaab82cf20b645393fc2d591e10e24fc831eb673a952037deb3e576d054583`**；本新 `u13a-proof-review-v2.md` / run `proof-review-v2.md` 是包含旧完整审查与本纠错附记的新最终报告。旧收据和旧完整报告继续只读保留。

本修正不增加任何数学主张；精确有限样本未归一化 Fourier 恒等式的范围不变。没有完整混合 LLT、条件 Lévy、实际 hW 或根闭合；根 A/B/C/D 全部 **OPEN**。新报告的本地/远端最终 SHA256 随交付消息独立核验。
