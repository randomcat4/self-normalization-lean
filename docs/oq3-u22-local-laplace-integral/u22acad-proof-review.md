# OQ3 U22ac / U22ad 独立完整最终证明审查

STATUS: CORRECT
AC_CHART_MEASURE_INTEGRAL: CORRECT
AC_RECTANGLE_IMAGE: CORRECT
AD_HALFSPACE_SCALING: CORRECT
AD_RECTANGLE_SCALING: CORRECT
AD_GENERATED_SIMP: CORRECT
BATCH_INTERFACE: CORRECT
PRECISE_CRITICAL_GAPS: NONE_IN_FROZEN_HELPER_SCOPE
NONBLOCKING_DOCUMENTATION: AC_SCOPE_SECTION_LOCATOR

本报告是本批唯一 fresh、作者分离的独立完整最终审查。任务显式分配 gpt-6.1-sol / xhigh / fresh；未派生其他上下文、未切换模型。工具没有提供可独立读取的运行时模型签名，也没有 input、cached input、output、reasoning-subset 分项 token 计数；这些实际用量均为 unavailable，不作订阅百分比分摊。采用 math-theorem，不使用 math-ultra。

完整覆盖 AC 全部 76 行、AD 全部 119 行、两份完整冻结声明、全部 5/5 实际归属声明的完整实际类型、所有新证明和所有局部 let 值。全局定义 0/0，无待补读 definition value。完整读取两份 Audit.lean、成功 build 日志、全部 audit.log、build-history、audit-record、audit-environment 和 receipt；核验本地、服务器当前源及保存成功源的精确哈希。仅复用既有源绑定 kernel / 全归属递归公理证据，本上下文没有运行 Lean、lake 或本地编译。唯一写入是本报告。

## 1. 约束、所有权及版本

已读工作区 AGENTS.md、SERVER.md、math-theorem/SKILL.md 及 prompt-library、openai-workflow、lean-verification 必要引用、streamlined-acceptance-current.md，并定向核对 TEAM / REGISTRY 的当前 OQ3 字段。有效作者为 chat 01a1669a-bca1-75e0-9d87-d07baee7b90a；旧写者释放、新写者激活均为 true，OQ3 子上下文 lease 为 1。本审查仅有 drafts/oq3/u22acad-proof-review.md 写权，没有源码、审计、共享、协调、缓存或版本锁写权；没有复活旧所有者或新建 SOURCE / preflight / grant 仪式。

本地工件目录：C:/game/shao lean/drafts/oq3/。
服务器工作树：/root/rivermind-data/shao-lean-20261021/workspaces/lead-oq3。
只读核对 branch 为 feat/oq3-boundary-integral，HEAD 为 0159001050a4f026d5f82c9bb5ab11425718d678，tree 为 0b0ba431d7230da22e98f42dd1b2012fbfda9381。
工具链文件为 leanprover/lean4:v4.36.0-rc1；Mathlib HEAD 为 807d3836b165983210ee2ecf3cd28f239436949c。当前 Y/Z/AA/AB/AC/AD 六个延续模块为 untracked；没有把它们误当作已发布提交。

| 单元 | 模块 | 行 / 字节 | 精确源码 SHA256 |
| --- | --- | --- | --- |
| AC | Shao.OQ3.BoundaryLaplaceCoordinates | 76 / 3727 | aac7544f3494ce2cbc50ed36af5375aa19788e44eea997278895e2d829726e46 |
| AD | Shao.OQ3.BoundaryLaplaceScaling | 119 / 6345 | 9205185457b94d9720723ca24bc4d04f7ecae11ba3ca26f10c74bdbe9406752d |

两源均为严格 UTF-8 / LF，CR=0。本地 u22ac-source.lean、服务器当前 BoundaryLaplaceCoordinates.lean、run/source-03.lean 三者同哈希；AD 本地源、当前 BoundaryLaplaceScaling.lean、run/source-02.lean 同哈希。
AC 冻结 hundred-tenth-unit-scope.md 为 27 行 / 2749 B，SHA256 10398beb976027c2c81663906097ed139e33078ca2f4600b13c16d5eaf4db9e7。
AD 冻结 hundred-eleventh-unit-scope.md 为 31 行 / 2871 B，SHA256 f24c56a0ef91ce4714352ab22c8f7a318dc7d7ec94da3cd751d7bbbb27360a1e。
服务器 scope.md 分别同哈希。四个声明逐字义对照其实施前冻结版本，并作仅规范化空白的精确比较，四项均 true；没有改变对象、量词、条件或结论。两源禁止项扫描无 sorry、admit、axiom、unsafe、native_decide。

## 2. 全归属、完整类型与定义值覆盖

| 实际归属声明 | 精确源码覆盖 | 实际类型覆盖 |
| --- | --- | --- |
| Shao.OQ3.boundary_rate_chart_measure_and_integral | AC10–50 | AC actual-types1–10 完整 |
| Shao.OQ3.boundary_rate_chart_rectangle_image | AC52–73 | AC actual-types11–16 完整 |
| Shao.OQ3.boundary_anisotropic_halfspace_scaling | AD9–62 | AD actual-types14–24 完整 |
| Shao.OQ3.boundary_cutoff_rectangle_integral_scaling | AD64–116 | AD actual-types4–13 完整 |
| Shao.OQ3.boundary_anisotropic_halfspace_scaling._simp_1_1 | AD44 的逆向 inv_pow 简化生成物 | AD actual-types1–3 完整 |

AC1–9、51、74–76 和 AD1–8、63、117–119 的 imports、namespace、noncomputable section、空行及收尾也完整读过。两份审计以 getModuleIdxFor? 枚举实际模块归属，而不是只查公开目标清单；结果 AC 恰 2 个 theorem，AD 恰 3 个 theorem，均无全局定义。合计 195 行、4 个公开 theorem、5 个实际归属 theorem，其中 1 个 generated theorem、0 个 authored private theorem、0 个全局 definition。此计数来自实际 owner 输出，不以旧单元描述推算。

AC actual-types.txt：16 行 / 943 B，SHA256 7800fb952d6eabe58259cf7ce36261cd7c174b868614c5dc38a6ba9b8ca38d94。
AD actual-types.txt：24 行 / 1421 B，SHA256 8e17572d8f73c3aca71ab0560e6dc9b02fb57ab4bb83ce1d3844fb5e74645716。
本地、服务器保存文本与完整 audit.log 中 DECL / TYPE / AXIOMS 一致。实际类型中的 have 是打印 let 的形式，所绑定值与冻结源码一致，没有隐藏参数或结论性实例。

AC 两次出现的局部 m 都是 full volume.prod volume；两次 G 都是 (r,z) ↦ (a0+r,(a0+r)^2/level^2-z)。局部 e 的 toFun 正是 G，invFun 是 (a,b) ↦ (a-a0,a^2/level^2-b)，两边逆关系及连续性分别有实际证明。
AD 首定理的 m 是 volume.prod(volume.restrict(Ici 0))，T 是 (u,v) ↦ (t*u,t^2*v)；e1、e2 分别是非零乘数 t、t^2 的 Homeomorph.mulLeft₀。第二定理的 m 相同，m0 是 full product Lebesgue，R 是 {|r|≤rho ∧ 0≤z ∧ z≤rho}，H 是冻结的精确缩放 if 核；S 是 {|r|≤rho ∧ z≤rho}，cut 是 S.indicator f 的同一 if 表达式。以上全部局部值均逐项核对；没有用其它测度、其它截断、有限测度替身或假设性积分值替换。

生成 theorem 的完整实际类型是：
```lean
∀ {α : Type u_1} [inst : DivisionMonoid α] (a : α) (n : ℕ),
  (a ^ n)⁻¹ = a⁻¹ ^ n
```
它是固定库 inv_pow 的对称方向：库定理为 a⁻¹^n=(a^n)⁻¹，AD44 的 simp only [← inv_pow] 生成该方向。DivisionMonoid 条件足够，n=0 由 inv_one / pow_zero，后继由 inverse-of-product 与两种 pow_succ 递推；没有额外的实数正性结论或项目假设。实际递归公理仅 [propext]。裁决 CORRECT。

## 3. 原源到冻结辅助陈述

完整阅读只读 repair01.md（226 行），SHA256 9d2e554838aa15b645aaf74a42468d423fed606aa91c1181d0dddf4e87c57cfd；另读 report.md42–75 的原尾域及正性背景，report.md SHA256 572e74aa9c12e2771f5543a5709a2807666eeea0a4076e7a3263e5c7bcf87f55。

repair01.md122–134 定义 w=(a,q)、r=a-a0、z=a²/x²-q 以及 F(r,z)=I(a0+r,(a0+r)²/x²-z)。AC 的 G 正是这一逆坐标图，将源 x 命名为 level、q 命名为第二坐标 b；没有变更公式或不等号方向。AC 给真实乘积勒贝格保测及 exact image，不要求把“绝对 Jacobian 为一”作为输入。以保测陈述实现源文的单位绝对 Jacobian 换元效应是忠实且更直接的辅助形式；它没有单独声明可微矩阵行列式定理。

源 report.md47–64 的应用有固定 x∈(0,1)，尾域 D_x={q>0, a≥x√q}。repair01.md129 明说先缩小 U 使 a>0。只有在这些应用正性 / 邻域条件下，a≥x√q 才与 q≤a²/x²、即 z≥0 对应。AC 的精确 strip identity 本身没有 q>0、a>0、U 或原样本事件，不能据此直接宣称 G(R)=D_x∩U；小矩形足够落在该正性邻域及与原尾事件的等价关系仍须在实际消费者中证明。任意 rho 的 strip 也可能包含负 b，此事实没有被隐藏。

AC 将 a0、level、rho 量化为任意实数是正确代数推广。level=0 使用 Lean 实数的 totalized division，x²/0=0；图变成 (a0+r,-z)，仍为保测 homeomorphism。它没有在源 x=0 时声称原自归一化尾问题成立。负 level 不影响这些辅助公式；原正 level 特化可直接使用，不增添源假设。

repair01.md183–200 的 r=u/√n、z=v/n，对应 AD 的 r=t*u、z=t²*v 且 t=1/√n。AD 严格保留 t>0，给真实半平面乘积勒贝格 pushforward t⁻³、对应可积性双向等价和固定 rectangle 的 t³ 积分换元；没有直接声称 n>0 或 sqrt(n) 特化已经组装。源文 n/(2π)、exp(-nΛ0)、实际振幅 / 率函数的代入和最后相对误差归一化不在 AD 结论中。

非阻断性定位笔误：AC scope 第 3 行写 “repair01.md section5-6”，而该文件实际相关位置是第 3 节、122–134 行（坐标及图），后续缩放在183–200行。冻结公式、源哈希及式号均明确，故不构成数学或证据缺口；可在后续文档整理时纠正定位，不为此改动已经验证的 Lean 字节。

## 4. AC 首定理：真实保测、嵌入与任意集合积分

声明 AC10–17 是对任意 a0、level 的真实 G：
MeasurePreserving G m m ∧ MeasurableEmbedding G，并对每个任意集合 s、任意实值函数 f 同时给出 IntegrableOn f (G''s) m ↔ IntegrableOn (f∘G) s m 和准确 setIntegral 等式。没有 measurability(s)、measurability(f)、目标积分恒等式或有限 / 概率测度的隐藏输入。

AC22–24 的 hshift 是 first-coordinate translation (r,z) ↦ (a0+r,z)，由勒贝格左平移保测与第二坐标 id 的 product 得到，作用于同一 full m。AC25–28 的 hneg 使用 Real.map_volume_mul_left(-1)，系数为 ofReal|(-1)⁻¹|=1，因此 x↦-x 保测；hflip 为 (a,z)↦(a,-z)。负号的绝对值没有遗漏。

AC29–36 的 hshear 是 (a,z)↦(a,a²/level²+z)。联合可测性由实际连续二元函数推出；对每个 a，第二坐标确为固定实数 a²/level² 的左平移，因此 map 等于 full volume。调用 skew_product 的 base 为 id，两个源因子都为 sigma-finite full Lebesgue，AE 条件由 forall 推出。没有用任意相关变量都可保测之类错误推论。

AC37–38 按 shear ∘ flip ∘ shift 的顺序复合，得到 (a0+r,(a0+r)²/level²-z)，恰为 G；若把 shear 放到 shift 前会错误，此处顺序正确。由三段真实保测推出 full product 的保测，不只是有限矩形的数值面积相同。

AC39–46 构造完整 homeomorphism。代入 invFun 后首坐标 a0+(a-a0)=a，第二坐标 a²/level²-(a²/level²-b)=b；反向同理恢复 r,z。ring 只消去同一多项式 / 常数分母项，没有约去可能为零的 level。连续性使用除以固定常数，level=0 时也是连续函数，故没有缺失 level≠0 前提。homeomorphism 的闭嵌入转成 Borel 可测嵌入。

AC47–50 通过 restrict_image_emb 得到 G 对 m|s 到 m|G''s 的真实保测，再用 integrable_comp_emb 并取 symm 得到声明方向的 IntegrableOn equivalence；setIntegral_image_emb 给同一 G、s、f 的准确积分式。固定库嵌入版本适用于任意 s，不要求额外证明 s 可测。任意 f 的 totalized integral 身份在库中有依据，可积性双向关系也已单独证明，故并未用“非可积时积分为零”逃避所需积分分析。

裁决：CORRECT。覆盖 full measure、任意 s/f、level=0、负 level、任意 a0 和全部两向可积性；无关键缺口。

## 5. AC 第二定理：精确闭矩形像

AC52–59 中 G 与首定理相同。左侧 R={|r|≤rho,0≤z,z≤rho} 是闭矩形；右侧是原坐标 parabolic strip，三个端点均保持 ≤，无把闭集改开集的 AE 代换。

AC60–69：给 u∈R，G(u) 的 first-distance 为 |(a0+u₁)-a0|=|u₁|；下界 Q-rho≤Q-u₂ 来自 u₂≤rho，上界 Q-u₂≤Q 来自 u₂≥0，其中 Q=(a0+u₁)²/level²。两条 linarith 含义准确。

AC70–73：给右侧点 (a,b)，明确选取 (a-a0,a²/level²-b)。第二坐标非负来自 b≤a²/level²，第二坐标≤rho 来自 a²/level²-rho≤b；首坐标条件直接复用。将候选代入 G 通过两向代数抵消精确返回 (a,b)，不存在选择不连续、分母约去或缺少 surjectivity 的问题。

rho<0 时两侧都因绝对值≤负数而空；rho=0 时为对应单点，结论仍为集合精确等式；level=0 时同样正确。无需添加 rho>0。

裁决：CORRECT。它证明精确 strip，而非未经正性验证的整个原尾域。

## 6. AD 首定理：半平面真实测度缩放

AD9–16 的 m 是无限的 volume⊗(volume|[0,∞))，T=(t*u,t²*v)，唯一条件 t>0。结论的 pushforward 系数 c=ofReal((t³)⁻¹)，积分方向为 ∫ f(Tp) dm=(t³)⁻¹∫f dm，可积性为 Integrable(f∘T)m ↔ Integrable f m。pushforward 与普通换元 Jacobian 的倒数关系正确。

AD21–25：ht2=0<t²，故 t、t² 都非零；e1、e2 是这两个非零乘数的真实 homeomorphism，product homeomorphism 的 map 正是 T。he2、hEmb 给全空间的可测嵌入，而不是只在 support 上的假设性嵌入。

AD26–28：t²*x≥0 ↔ x≥0 由 t²>0 得到，因此 (t²·)⁻¹'[0,∞)=[0,∞)，包括 0 端点。AD29–39：第一坐标 map volume=ofReal(t⁻¹)•volume；第二坐标先通过 he2.restrict_map 将 halfline 限制移到 map 后，再用相同 preimage 与 restrict_smul，得到 ofReal((t²)⁻¹)•(volume|[0,∞))。abs_of_pos 使用逆数的正性，未把负倍数误当保留半直线。

AD40–45：ofReal(t⁻¹)*ofReal((t²)⁻¹)=ofReal((t³)⁻¹)；ofReal_mul 的非负条件为 inv_nonneg ht.le，随后 inverse powers 与 ring 合并三次幂。AD46–51：map_prod_map 的可测 / SFinite 条件在真实全 Lebesgue 与 restricted Lebesgue 上成立；prod_smul_left、prod_smul_right、smul_smul 按实际两个因子合并 c。这里没有把真实 m 换成 probability measure。

AD54–56：c≠0 由 t³>0 及其逆为正明确给出；c≠∞ 由 ofReal_ne_top 给出。小的正 t 虽使实系数很大，仍是有限非零实数，条件充分。AD57–60：measurable embedding 的 integrable_map_iff 允许任意 f，用 hmap 替换并应用 integrable_smul_measure c≠0 c≠∞，得到需要方向的双向可积性。

AD61–62：先从 ∫ f(Tp) dm 反向改写为 ∫ f d(map T m)，再替换 map=c•m，应用 integral_smul_measure；toReal_ofReal 所需非负性由 t>0 推出，最终实标量就是 (t³)⁻¹。积分恒等式和可积性等价都来自实际测度映射，不是假定目标结论。

t=0 被 ht 正确排除，负 t 会使 first-coordinate 的绝对 Jacobian 与 t³ 的符号不一致，故不能删去正性；本声明未删除。t>1 仍正确；无暗含 t≤1。任意 f 情形由 measurable embedding 的库定理处理非强可测分支，配套可积性等价避免空洞的应用结论。

裁决：CORRECT。无限半空间的 t⁻³ map、非零有限系数、端点、嵌入、积分系数及量词均完整。

## 7. AD 第二定理：同一截断与固定闭矩形积分

AD64–81 的 m、m0、R、H、S、cut 均按第2节列明的真实值。特别地，H 的 if 中没有 v≥0；这不是遗漏输入，因为积分的第二因子本身是 volume|[0,∞)。它也没有假设 f 或 H 的可积性。

AD82–85：S 的两个条件分别是连续函数 |first|≤rho 和 second≤rho，均为 Borel 可测集，交集可测。AD86–93：prod_restrict(univ,Ici0) 给 m=m0|{v≥0}，首因子 restrict_univ 正确消去；univ×[0,∞) 与 second≥0 的集合等式逐点验证。

AD94–99：利用 restrict_restrict(hS)，m|S=m0|(S∩{v≥0})；该交集的完整逻辑条件为 ((|r|≤rho ∧ z≤rho) ∧ 0≤z)，经重排正好是 R。没有缺掉 lower endpoint、增加 q 正性或把不同 cutoff 当成相同。此步是 exact measure equality，强于仅说“负半平面无质量”。

AD100–106：cut=S.indicator f 是逐点等式；integrable_indicator_iff(hS) 把 Integrable cut m 与 Integrable f (m|S) 等价，后者通过 hrestr 等于 Integrable f (m0|R)，即 IntegrableOn f R m0。对任意 f 成立，无额外可测性前提。

AD107–110：同一 indicator 与 hrestr 给 ∫cut dm=∫R f dm0。AD111 将首定理用在同一 cut；cut(T(u,v)) 在定义展开后恰等于 H(u,v)，包括乘法顺序、t²、同一 rho 和 false branch=0。因此 hK 与 hKI 的 defeq 转换忠实，没有另一个近似截断或仅 AE 的未证替换。

AD112–114 组合 Integrable H m ↔ Integrable cut m 与上一等价，得到声明的完整 iff。AD115–116 将同一 ∫cut 替换成 ∫R f，再乘 t³ 并用 t³≠0 消去其逆，得到 ∫R f=t³∫H；未将逆系数乘错侧。任意 rho、任意 f、t>0 的量词保持。rho<0 时 R 空且 H 恒零，rho=0 时退化集合的等式与可积性也由精确 measure / indicator 推导覆盖。

裁决：CORRECT。这是实际 full product rectangle 积分到真实 halfspace 缩放 cutoff 积分的换元，不是由假设的欲证可积性或 desired identity 反推。

## 8. 固定主库接口核查

所用主 API 均从服务器固定 Mathlib checkout 的实际源读取；涉及下列文件的工作区字节另与 git show HEAD:<path> 比较，全部 true，故 build 中 “mathlib repository has local changes” 警告没有在这些承重接口中隐藏数学源码修改。

| 固定主源（相对 Mathlib/） | 核对接口及条件 |
| --- | --- |
| MeasureTheory/Group/Measure.lean48–51、86–95 | map_add_left_eq_self / measurePreserving_add_left 的 to_additive 来源；真实左平移不变测度 |
| MeasureTheory/Measure/Lebesgue/Basic.lean319–323 | Real.map_volume_mul_left：a≠0，系数 ofReal|a⁻¹| |
| MeasureTheory/Measure/Prod.lean794–802、870–881、899–927 | prod_restrict、map_prod_map、prod_smul_left、skew_product、MeasurePreserving.prod；SFinite 和联合可测条件 |
| MeasureTheory/Measure/WithDensity.lean753–759 | prod_smul_right；真实 product scalar 关系 |
| Dynamics/Ergodic/MeasurePreserving.lean81–100 | restrict_preimage_emb、restrict_image_emb 与 comp；嵌入使任意集合 restriction 可用 |
| MeasureTheory/Measure/Restrict.lean193–206、892–894 | restrict_smul、restrict_restrict、MeasurableEmbedding.restrict_map |
| MeasureTheory/Function/L1Space/Integrable.lean325–330、371–394 | 非零有限测度缩放的 Integrable iff、embedding map iff、preserving comp iff |
| MeasureTheory/Integral/Bochner/Basic.lean1047–1058、1088–1098 | integral_smul_measure 与 embedding integral_map；任意函数的非强可测分支 |
| MeasureTheory/Integral/Bochner/Set.lean181–183、557–575 | indicator integral 与任意集合 image setIntegral |
| MeasureTheory/Integral/IntegrableOn.lean324–342 | image IntegrableOn 来源及 measurable indicator iff |
| Topology/Algebra/GroupWithZero.lean284–287 | Homeomorph.mulLeft₀ 非零乘数及连续正逆函数 |
| Topology/Constructions/SumProd.lean671–681 | product homeomorphism 的实际 map 为 Prod.map |
| Topology/Homeomorph/Defs.lean298–299、MeasureTheory/Constructions/BorelSpace/Basic.lean683–685 | homeomorphism 闭嵌入与 Borel measurable embedding |
| Algebra/Group/Basic.lean419–422 | inv_pow 完整 generic DivisionMonoid 类型及递推证明 |

ℝ 与 ℝ×ℝ 的 Borel / normed real 结构和 full / restricted Lebesgue 的 SFinite 条件满足上述专门化。没有引用外部未经证实的 Jacobian、Laplace 定理或概率上界来完成新声明。

AD 导入的 Z（BoundaryLaplaceIntegral）当前服务器 / 本地源 SHA256 仍为 1de2b65b14b26d0e5a564c9bce5a673f662187b1461633ddb6bfce4da6b9ac12；既有完整 Y/Z 终审 u22yz-proof-review.md SHA256 996b9b5eb911990ebfaaac35b84836b8f32f462b5978c34c29d27013d626115e，其 CORRECT 与原辅助范围不变。本批 AD 证明没有调用 Z 的项目 theorem，只利用其导入的环境；故没有重审或重跑 Z 的已接受证明。AD 也没有调用 AC 的 project theorem，import 仍在本批环境内；本报告独立完整审查 AC 的新增证明，而不把 AD 编译成功视为 AC 的数学审查。

## 9. 精确服务器证据与全归属递归公理

run 路径为 /root/rivermind-data/shao-lean-20261021/runs/oq3/u22ac-20261023 和 u22ad-20261023。核验其 scope、receipt、Audit、actual-types、audit-environment、audit-record、build-history、成功 source 和成功日志的实际字节；完整读过成功日志 / 全 audit 输出及完整 history。保存的失败尝试仍在原 run，没有覆盖、删除或重放。

| 证据 | AC | AD |
| --- | --- | --- |
| receipt.json SHA256 | a884ea0356489bbf529c2266031f63d46a20d0e0dec0884891f8e6ec56cbd2f7 | 349fbbffa6c7f10b1633ab911dba3ad06e7f7118effd9424fbf4bbc19f47d582 |
| 成功 kernel | source-03 / build-03，exit0，5.340627353638411s | source-02 / build-02，exit0，5.156094146892428s |
| 成功 build 日志行 / 字节 | 2 / 133 | 6 / 397 |
| 成功 build 日志 SHA256 | fe9a6b741bba0630c9977614157f0259907b0b7ebce576a9400b542ee4518626 | 9ec59193118e02afabb2f7cbc31b5ce5d3ddfe62ae92105a501883018a5fd6f3 |
| Audit.lean SHA256 | 9e48fb97d47638390f7f7efeeabe9f7976751951cb8c672867c8f36b09998c69 | 80bb359f18f726fbe476fb85d303d58fb686be63b657b23f4366b34c55093e31 |
| audit.log 行 / 字节 | 23 / 1195 | 31 / 1673 |
| audit.log SHA256 | 7a12b9e95688c741d135fe9719687ea9690bca35e2dec2af84b166817a8e5fed | 32464d651cb82df65c0fa6bff549dcb16497238bc0ccfc769d362f455f75fcd8 |
| audit-record.json SHA256 | a7b0f811a0f5485a01e9760975030d73981b2ae3c5fdf9e439aaf0c4bcff66b1 | 931a1db45894a54ac3f7869e7f5d9e5449fda3ed4e14ecb3f57696fd459ada3e |
| audit-environment.json SHA256 | c7232844169fb6f2f7ab453b3a82c559cf8988e1092e989d8daeb5b2b546457a | 9c0a6dafb210418e107b309592409075bf0971aac38d5422cb86a58024b84d22 |
| build-history.json SHA256 | 10bd3e71051a5c18df879d6c70bd4bb95ec5eaf4bd3f52dbced2f259c0ff9d39 | 08f225f2e59feabc622e7ad30106f21806d842a3cb956cc4798ca1c9a66b6fcf |
| 实际 owner gate | 2 declarations / 2 theorems / PASS | 3 declarations / 3 theorems / PASS |

AC build01、02 为两次保存的完整失败，成功在03；AD build01 为保存失败，成功在02。history 的每次源哈希、exit、日志哈希与 run 文件一致；本次不把失败当成功，也不为已成功的精确源重跑检查。AC 成功日志仅既有 Lake mathlib thin-view local-change warning；AD 另有 AD102 Set.mem_setOf_eq 的弃用提示，没有数学错误或新增公理，未为消除提示而改动冻结源。

两份 audit-record 都 source-hash-bound 到本批精确成功源，exit0，分别用时 6.0977292358875275s / 6.027369638904929s；CPU14–17、native-M8192、jobs4、autoImplicit=false。manifest 复用 /runs/oq3/accepted-source-view 的只读 view，仅加各自工作树的新 .olean，无 shared cache 写入 / 二进制复制 / pin 改动。manifest 的旧 baseline 字样只说明沿用环境，未将旧模块数量充作当前新归属计数。

Audit.lean 先核对两名冻结公开目标确为 theorem，再枚举 actual module owner 的每个 constant，拒绝新 axiom，逐项 Lean.collectAxioms 并检查白名单。AC 两项、AD 两项公开声明的递归依赖均为 [propext, Classical.choice, Quot.sound]；AD generated simp 为 [propext]。没有未覆盖的私有或生成归属，没有新 project axiom。此机械证据只认证本批精确源码编码；第3–8节另行完成源到声明与证明的独立数学核对。

## 10. 最终裁决及未闭合范围

AC chart measure/integral：CORRECT。
AC exact rectangle image：CORRECT。
AD halfspace scaling：CORRECT。
AD exact rectangle cutoff scaling：CORRECT。
AD generated inverse-power simplification：CORRECT。
Batch interface：CORRECT。冻结辅助范围内 PRECISE_CRITICAL_GAPS=NONE。

可在上述精确哈希、既有服务器 kernel / 全 owner recursive AX 及本报告完整独立语义审查共同绑定的辅助范围内记 LEAN_FULLY_CHECKED；该术语不能扩大到原论文根目标。结果属于经典测度换元工具的源特定辅助实现，不提出数学新颖性认证。

本批真实消除了原坐标图的保测 / embedding / exact strip 换元，以及真实半平面到同一固定 rectangle 的 anisotropic t³ 换元障碍。后续仍须实际组合：原尾事件 q>0、a>0、level>0 与局部 U / rectangle 的等价；将实际率函数 / 振幅代入并验证对应正性、可测性、局部余项与可积性接口；n>0 时 t=1/√n 的精确系数特化；外部 n/(2π) 和 exp(-nΛ0) 因子及最后相对归一化；原文真实外区概率 rate-gap 消耗，以及统一 Edgeworth / cells 到实际概率的完整链。本报告未把 formal strip identity 当作这些概率桥。

OQ3 B/D 保持 OPEN；已经验收的 corrected A、bounded C、p54 修正范围与外部结果归属不变。没有因辅助恒等式、编译通过或新 theorem 数量而新增原根闭合。本审查至此完成；输出本报告最终字节数、行数、SHA256 后停止工具和写入，不接受自行推断的下一个任务。
