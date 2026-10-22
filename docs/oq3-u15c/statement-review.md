# U15c 独立声明与来源审查

STATUS: CORRECT

本票仅审查冻结声明/source/environment，尚无实现。审查者沿用唯一 lease 1，只拥有本报告及服务器对应 statement-review.md，不改 scope、源码、旧报告、公共文件或缓存，不 spawn、Lean/API probe 或构建。根 A/B/C/D 与 WC 均保持 OPEN。

## 第一阶段：仅精确 Lean fence 的完整公开类型盲译

输入 thirty-sixth-unit-scope.md，SHA256 d2d980d0c91aba2b420bf969817c081649380b5804ad843b1e9a47160d0b9ec6。仅提取 Lean 块；实际无新定义、两个公开完整目标。以下翻译在读取 scope 动机、真实来源或库接口之前独立写入。

1. `exists_compact_parameter_box (K : Set (ℝ × ℝ)) (hK : IsCompact K) (u0 v0 : ℝ)`：对任意实际实数二重积中的紧集 K，以及任意参考实系数 u0,v0，存在一个共同实数 L≥0，使每个 p∈K 的两个坐标分别满足 |p.1−u0|≤L、|p.2−v0|≤L。L 可依赖 K 与参考坐标，但在所有 p 外一次选择；不要求 K 非空，也不要求参考点属于 K。空 K 时仍须有 L，不能在证明中未经条件选取 K 的元素。

2. `exists_compact_quadratic_tilted_domination (mu : Measure ℝ) [IsProbabilityMeasure mu] (M : ℝ) (hM : 0 ≤ M) (hb : ∀ᵐ x ∂mu, |x| ≤ M) (K : Set (ℝ × ℝ)) (hK : IsCompact K) (u0 v0 : ℝ)`：对任意同一真实实数概率测度、M≥0 及其 AE 支撑界、任意紧参数集 K 和任意参考系数，存在一个共同实数 m>0，使对每个 p∈K，同时有 (a) ENNReal.ofReal m 倍真实参考二次势 tilted≤真实 p 坐标二次势 tilted；(b) 对所有实频率 s,t，m² 乘参考律同律二重积下 K_st(x,y)=1−cos((x−y)(s+t(x+y))) 的实际实积分≤p 倾斜律同核二重积积分。存在的同一个 m 在所有 p、所有频率 s,t 之前，两个结论共享 m；不能逐参数或逐频率另选。m 没有显式公式要求，也未附加倾斜概率/可积假设，须由实际前置合法建立。K 可空、M 可零，u0,v0 不要求落在 K。

两个目标没有声称余弦积分已经等于特征函数缺口，没有 WC、标准化或根闭合。此盲译先落盘，尚不预设数学或环境批准结论。


## 第二阶段：冻结范围、实际前置与来源

盲译先落盘后才读取完整 scope、实际前置接口与 R2。scope 本地及指定服务器 run/u15c-20261021/scope.md 的实际 SHA256 均为 `d2d980d0c91aba2b420bf969817c081649380b5804ad843b1e9a47160d0b9ec6`。来源 `C:/game/shao/current/oq3/proofs/r2/report.md` 实际 SHA256 `572e74aa9c12e2771f5543a5709a2807666eeea0a4076e7a3263e5c7bcf87f55`，直接读取第 343–369 行。

R2 第 345–352 行明确要求紧参数集上同一 m>0 与 theta 无关，式 (20) 为正密度下界；式 (21)–(22) 使用真实二样本非负核和平方因子。U15a/b 的盒宽 L 是输入；本候选第一目标补上从真正紧集到共同 L 的选择，第二目标产出同一 m 的测度与实际余弦核积分下界，量词正好服务这一来源步骤。未把一般二维向量代替 W=(X,X²)，核仍是 `(x−y)(s+t(x+y))=s(x−y)+t(x²−y²)`。

实际已接受项目接口及两端源码散列：

- `TiltedMeasureDomination.lean`（U15a）SHA256 `5445a68da1ac8302f174bfe2144eb8271a0af740fd6b91a87355abb41fed739b`。其 quadratic_exp_integrable_of_ae_abs_le 对同一 mu 的真实 AE 支撑界给任意参考/新二次指数真可积；quadratic_tilted_measure_domination 在同一共同 M,L 下给 ofReal(exp(−2L(M+M²))) 倍参考真实 tilted≤新真实 tilted。完整类型保留 M,L 非负和各参数差门。
- `ProductMeasureDomination.lean`（U15b）SHA256 `9f05af79e47b9f778cbce7a0d19c0addea6d457eab5f088a69bf372f660c5a3f`。其 quadratic_tilted_cosine_pair_domination 消费上述同一门，给 exp(−4L(M+M²)) 的实际二重积余弦积分下界，对全部 s,t 成立。它在证明中先从 U15a 真可积性建立两个真实 tilted 概率实例，private 核可积引理用真实概率下 0≤1−cos≤2 的界，有限标量测度积分门和 m² 转换已完整独立接受。

已实际读取这些公开完整类型并核对消费语义，不重做已接受 proof 门或旧构建。拟导入 ProductMeasureDomination，其真实项目闭包恰为该模块及 U15a；U15a 没有 Shao 前置。当前缺失的根公共特征恒等式既未被导入，也不充当本候选数学前提。

## 第三阶段：独立量词、数学与边界核查

### 目标一：不要求非空的共同盒宽

对任意固定参考 u0,v0，令 F(p)=|p.1−u0|+|p.2−v0|。该实函数在整个实二重积上连续；K 紧，因此下节核对的真正标准接口给 ∃C:ℝ，∀p∈K，‖F(p)‖≤C。这个接口没有 Nonempty K 门，也不要求先给 K 的一个元素。

令 L=max C 0，则 L≥0。不需要假定 C≥0：对任意 p∈K，每个坐标绝对差≤两者之和 F(p)，而 F(p)≤|F(p)|=‖F(p)‖≤C≤L。因此两个坐标均被同一 L 控制。若 K=∅，上述全称门全为空，接口仍产出 C，max 保证 L 非负；证明没有选取 K 元素或调用需非空的最大值定理。参考点可以在 K 外，甚至离 K 很远，因连续函数本来是相对任意 u0,v0 定义。退化单点紧集也无需特殊前提。

因此第一目标可直接使用实际导入中的接口证明，不需补 K.Nonempty 或 (u0,v0)∈K；两种补假设都会无谓缩窄冻结声明。

### 目标二：同一严格正 m 同时消费两个实际接口

先只依赖固定 K、参考 u0,v0 选择上一步的同一 L≥0；令 B=L(M+M²)≥0、m=exp(−2B)>0。M,L,B 是有限实数，m 因而严格正且有限，ofReal m≠∞。B≥0 还给 m≤1，但目标不要求额外输出此事实。

在引入任意 p∈K、s,t 之前就一次选择 m。对任意 p∈K，盒宽给 hu=|p.1−u0|≤L、hv=|p.2−v0|≤L。实际 U15a 的相同 mu,M,hM,hb,u0,v0,p.1,p.2,hu,hv 产生第一支 measure domination，系数正是 ofReal m；没有每个 p 自己的归一化常数进入 m。

同一盒宽和同一 p 再对全部频率 s,t 消费已完整接受的实际 U15b 结论。它的系数是 exp(−4B)。真实指数恒等式

`m²=exp(−2B)²=exp((−2B)+(−2B))=exp(−4B)`

给出第二支恰为同一 m² 的积分比较。这是同一个存在见证 m，同一参考实际倾斜律与同一目标实际倾斜律，不是分别为两个合取分支或每个频率另选常数。

真实可积/概率门未被隐藏：基准 mu 概率非零，实际 U15a 对任意二次参数先给 exp 势真可积；库 isProbabilityMeasure_tilted 消费真可积与 NeZero，才给两个真实倾斜概率。U15b 的实际产品测度为真正 SFinite 产品，其余弦核连续且全局 0≤核≤2，在两边真实产品概率下真可积；其积分序门、有限 NNReal/ENNReal 标量转换均已逐项独立核对。候选可以直接调用这一已证公开接口，无需假定名为 tilted 的任意对象必为概率或将总化积分当真可积。

M=0 时 hb 强制 x=0 AE，B=0、m=1，对任何参考点及紧 K 都有效；不除 M 或要求正半径。若所得 L=0（或盒宽可取 0），同样 m=1；K 中相关参数与参考一致，两个分支合法。若 K=∅，后续关于 p 的 measure/integral 合取全称门为空，但本构造选出的 exp 常数仍真正 >0；没有把空集当非空去提取见证。

全部量词均正确：m 允许依赖已经固定的 mu,M,K,u0,v0，但绝不依赖后面的 p,s,t；实际上此构造甚至不依赖 mu。不存在频率/参数相关阈值或二次不同参数族的替换。第二目标只要求非严格积分下界，即使核恒为零也成立，未错误要求严格正积分。

## 第四阶段：固定库实际 API、静态环境与缓存

仅通过共享 server.py 对指定服务器只读核查，未 Lean、#check/API probe、构建、缓存写入或原始日志下载。本轮无实现、receipt 或作者 proof 路线可作为批准证据。

`Mathlib/Analysis/Normed/Group/Bounded.lean` 实际 SHA256 `7ff0b64a69f6e44ea002c3f21fac6011801737d81629fc9c2d4280e4b8846042`。该文件第 8 行 public import Normed.Group.Continuity，第 20 行 public section。第 91–95 行明确

`@[to_additive IsCompact.exists_bound_of_continuousOn]`

由实际乘法版 IsCompact.exists_bound_of_continuousOn' 生成本候选所需加法标准定理：对 TopologicalSpace α、IsCompact s 和到 SeminormedAddGroup E 的 ContinuousOn f s，得到 ∃C，∀x∈s，‖f x‖≤C。原始声明及其证明都不含 Nonempty s：证明使用紧连续像有界再套 norm bound。取 α=ℝ×ℝ、E=ℝ 完全匹配，无矩阵范数或隐含非空环境。第 69–74 行相应有界 iff∃norm bound 与 exists_norm_le 的源也直接核读，支持空集情形；本次不靠名字猜接口。

U15a/b 已接受的真正倾斜/产品接口通过拟导入 ProductMeasureDomination 及其实际首行导入 TiltedMeasureDomination 可见；其公开 theorem 完整类型已逐一读取且两个实际 SHA 与冻结值相同。基本概率、连续绝对值、实二重积、真实余弦和测度积分实例沿既有实际导入链可见。Real.exp_pos、exp_add 和平方恒等式由 U15a 的 Exp 导入，之前已读取固定库真实类型；本次不新增私自假设。

实际缓存存在：Normed.Group.Bounded.olean 86248 字节；Tilted.olean 78048、Prod.olean 342936、Bochner.Basic.olean 688952；项目 U15a olean 231752、U15b olean 149352 字节。六个明确 tactic 缓存也存在：FieldSimp 1681840、Ring 1648、Positivity 1832、Linarith 2536、FunProp 2488、NormNum 2496 字节。显式 open scoped ENNReal NNReal 与冻结的有限 NNReal/ENNReal 记号意图一致。不存在新的库缓存或未知范数/默认测度门要求。

实际 pins：lean-toolchain 内容 `leanprover/lean4:v4.36.0-rc1`，文件 SHA256 `d581a24b57a4ae9e0b2132ca8ac7cc3ac336a9fc2751fe6b29414e2d434d54c4`；lake-manifest.json SHA256 `40e8e3385f2b0c8ae56fa9de6947301472379cb62eeb83247944827c38b8af6e`。Mathlib manifest rev 与实际 git HEAD 均为 `807d3836b165983210ee2ecf3cd28f239436949c`。这是静态声明环境绑定，不声称尚不存在的实现已编译成功。

## 最终声明/source 裁决

STATUS: CORRECT

JUSTIFICATION: 两个精确冻结类型真实成立；实际不需非空的紧连续像取界接口给共同非负 L，进而单一严格正 m 在全部参数及频率前固定，且同一 m 与 m² 精确对应已接受的真实倾斜测度和余弦产品积分支配。空 K、参考点不在 K、退化紧集、M=0/L=0 均无隐藏缺口；实际可积性/概率性与固定库/缓存门齐备，未发现声明级、来源级或静态环境关键缺口。

本票只批准声明进入实现，不证明已经通过 Lean 内核。候选仍是标准充分的紧参数共同常数选择及测度/明确余弦核积分传递，不识别实际特征函数模平方缺口，不关闭 WC、除二常数/标准化，不扩成无界版本，不证明最优性、新颖性、KL、Lévy/LLT、hW 或任何根闭合。根 A/B/C/D 与 WC 全部保持 OPEN。
