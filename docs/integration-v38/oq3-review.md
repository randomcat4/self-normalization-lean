STATUS: CORRECT
JUSTIFICATION: PR148、PR151、PR152 的三个冻结公开命题及完整证明均正确；没有发现关键缺口。结论严格限于各冻结命题。canonical domK / EReal 全局率、全局极小点及原 OQ3 根组装未因此闭合。

# v38 OQ3 独立验收

验收者：/root/v38_oq3_accept，非作者，新鲜上下文，按指定 gpt-6.1-sol / xhigh 执行。时间：2026-10-22 20:18 UTC 后。
所有权仅本报告及同名 JSON；未修改源代码、状态、Git 引用、缓存、版本锁或他人文件。本轮没有启动 Lean、lake、probe、build、Audit 或新的重型任务。服务器只读命令均经 tools/server.py，显式 taskset CPU10–13。未操作外部 CPU0–9 / 80GiB 任务。

已读 AGENTS.md、SERVER.md、coordination/TEAM.md 及 math-theorem 的主协议、提示词、OpenAI 工作流和 Lean 核验协议。TEAM.md 实际位于 coordination/；仓库根同名文件不存在，未据此漏读。
本次机械证据是对既有作者成功门的源绑定复核，后续统一整合编译与全库所有权/公理/覆盖门仍由根协调执行。

## 冻结对象与基线

| PR | 冻结 head | 源文件 | SHA256 |
| --- | --- | --- | --- |
| 148 | 0e29e2642e22edf7da734817a2fc8909a304a4b8 | Shao/OQ3/SourceGeometricScale.lean，102 行 / 4365 字节 | 6361d54e22501bf85a6c683a7e85d9df05082bd6190cad73a8d03dc00f3e7470 |
| 151 | a8991280cab24bd1fdd25d97d2404e414f5b9bce | Shao/OQ3/SourceLogPartitionDerivatives.lean，253 行 / 13173 字节 | 18c42fc0bea7cdaf1fb69acba96caf452a35eddc9819e29d211fe94a4aa32f07 |
| 152 | 5a82f9e0587a93fc413f83f22713f7e6ec1d8ec5 | Shao/OQ3/SourceFixedLawCounterexample.lean，103 行 / 5065 字节 | 3d402b62362c4394eb50a6ade2f512ab90c3d19982ce19ca143c706257c5c571 |

三个 head 均以只读 git show 精确读取。每个相对父提交恰为一个新增源和五个新增文档，均无既有文件改动。PR148 父为 v36 accepted f2a39a09ebd50648bd61d68d7018aa01a9810ea0；PR151/152 父为 v37 accepted ded5b45059cf80861712f61c86170243d5e87fc2。各完整公开声明与冻结 scope 的唯一 Lean 代码块去空白后匹配，包括全部 let 绑定。

只读解析确认 v37 main 3989ef9a7ad4809d9c0e48194e9b1c88125b8ab7 与 accepted ded5b45059cf80861712f61c86170243d5e87fc2 同树 b5e2b9ed3b4e1493da5e3eaeb22b83f2bc2c4b60。本地 receipt-v37.json SHA256 为 0ca757d0c30a8a0d7239de0631e018ae79aacdb8bee1faa836df7ce5cf8a8ae8，吻合指定基线。
三个 head 的 lean-toolchain / lake-manifest.json 与 v37 相同：Lean leanprover/lean4:v4.36.0-rc1，mathlib 807d3836b165983210ee2ecf3cd28f239436949c；只读核实共享 mathlib 实际 HEAD 同值。

## 原命题和实际对象

原文为 C:/game/shao/current/oq3/proofs/r1/report.md，SHA256 3473d34ff20bd0d334b9ef3ea3c3ee167fba4d5cc3a742849820ce54d639e662。直接核对原文 1–159、161–305、431–443、484–558，涵盖固定有界中心律、真实联合非格点与远频近共振、鞍点参数、协方差/曲率以及式(31)的单个固定律缩放余项。当前任务验证源码对这些片段的具体承重接口，不重新作历史优先性裁决。

已核原始定义：sourceEll = log(31/30)；normalValue(x)=8x−x²；四个约束为质量 1、Eπ(X²−4X)=0、Eπ[X exp(−ell Y)]=0、EπX²=q。atomicMeasure w 是 Σ_i ofReal(w_i)·δ_fixedAtom_i，originalMeasure sourceEll w 是它的真实规范化逆指数倾斜，且正向重倾斜回到同一 atomicMeasure w。

normalizedTailCoefficient 的定义为
C_n = sqrt(2πn) exp(n·saddleRate(ell,q,w)) · P^{⊗n}(sourceTail(q,n))。
sourceTail 是正能量且 ΣX_i ≥ (sqrt(q)/4)·sqrt(n ΣX_i²) 的实际可测事件；没有自由系数序列或用户给定渐近输入。correctedInverseScale 是既有实际值 (ell·sqrt(S−(32ell/q)detD))^{-1}，其中 S=Varπ(8X−X²)，D=Covπ(X,X²)。saddleRate 的既有定义是 ell·q + log(inverseNormalizer ell w)，尚须 canonical 全局率桥才能将它作为相应 canonical 对象使用。

## PR148：实际几何尺度

公开命题 source_corrected_scale_geometric_identity 正确。完整读取源 1–102 行及唯一 private helper、全部七个 generated 项的实际完整类型。

1. 源 37–54：hm 第零行给 HasSum w 1，真实 π 为概率。AE 有界支撑和四个真实正 base 原子质量满足 parabolaCovariance_det_pos 的全部条件，得到 detD>0。
2. 源 55–79：q>1 给 sqrt(q)>0、x0²=q/16，故 v=(1,8)，2(−ell)/x0²=−32ell/q。private inverse_tangent_quadratic 用实际二阶伴随矩阵公式，并要求 D10=D01；在实际协方差定义下该对称性为 rfl。normalVariance_eq_covariance 给 S=64D00−16D01+D11，因此 curvature=S/detD−32ell/q。
3. 源 80–95：调用原实际 atomic_curvature_pos 得严格正曲率；detD·curvature=S−(32ell/q)detD。真正 detD>0 后使用 sqrt_mul，结合 ell>0 得几何乘积严格正。
4. 源 96–99：展开已有 correctedInverseScale 得精确同律等式，不引入新尺度定义。没有利用奇异矩阵的全定义逆或 Real.sqrt 负值总化获得正性。

已完整核对承重依赖 RegularCovariance 的定义、det 正性证明、normalVariance 等式和 atomic_curvature_pos；CorrectedScaleContinuity 的尺度定义、正被开方数接口及其实际假设。hq 的严格窗口、w 非负、四 base 严格正和四条 HasSum 均与冻结类型一致。

## PR151：真实 K 的梯度与完整 Hessian

公开命题 source_log_partition_first_and_second_derivatives 正确。完整读取源 1–253 行，包括六个 private 定义、六个 private 定理和十个 generated 项的实际完整类型。

1. 源 20–103：M_k(theta)=∫x^k exp(theta0·x+theta1·x²)dP 是真实积分。固定支撑使每个 M_k 在所有实参数下可积；M_0 严格正。F' 是完整连续线性 Fréchet 导数，其算子范数在参数闭单位球×固定样本区间的紧集上有共同有限上界。概率性使该常数可积；可测性、共同邻域、AE 统一界和逐点导数逐项提供给实际 ParametricIntegral 206–226 的 API。没有只在一点的形式展开。
2. 源 105–131：用 M_0≠0 的真实逆函数及对数微分，得到归一化矩和 log M_0 在每个 theta 处的导数。normalizedSlope 的两个系数是归一化协矩；无额外正则性输入。
3. 源 133–159：theta0=(8ell,−ell) 的指数恰为 ell·normalValue。actual originalMeasure_retilt 与 integral_tilted 把 M_k/M_0 识别为同一 atomicMeasure w 的原始矩。前面已证明概率、可积性及分母严格正，未通过不定积分的零值取得身份。
4. 源 178–219：hm0 给同一 P/π 概率；hm 给 EπX=q/4、EπX²=q。实际有界 L² 条件满足 variance_eq_sub / covariance_eq_sub，四个矩阵项分别为 M2−M1²、M3−M1M2、同一交叉项、M4−M2²。
5. 源 220–250：梯度作用于 h 为 h0·q/4+h1·q；Hessian 作用于 h,k 为 Σ_ij h_i D_ij k_j。两个非对角系数均实质核对。关键在源 239：先由所有 theta 处的真实导数得到全函数等式 fderiv K = partitionGradient，再对该函数微分。因此第二结论确实是 HasFDerivAt (fderiv K)，没有用一次方向导数或局部值展开冒充。

冻结类型允许所有实 q、非负权重和可能退化的 D。证明没有额外 q 窗口、base 正质量、非退化、C² 或指定 Hessian 前提。K 是同一 P 的实际二次指数积分的实对数；没有公开新 K 定义。已核 pinned ParametricIntegral、Log/Deriv 和 integral_tilted 的实际源码条件。

## PR152：同一个最终概率律和严格递增见证

公开命题 exists_source_fixed_law_counterexample 正确。完整读取源 1–103 行及唯一 private helper；两条全部实际类型均完整读取，无 generated 项。

1. 源 62–69 只解包一次已接受的 exists_source_fixed_law_unbounded_scaled_remainder。之后 w 始终是 limitingMass sourceEll p r，q、P 及四条 HasSum 固定；未从另一个存在族重选非格点律。
2. 源 70–79：实际原子正质量由相同 w 的 originalMeasure_atom_pos 推出。固定原子 1 真在 Ioi 0 内，概率测度上的 measureReal_mono 推出 P(X>0)>0，未用无限测度 toReal 的无效单调性。
3. 源 80–90：相同 q 窗口给 0<x0<1/2；同一 w 的严格正权重及四约束给实际 saddleRate>0，既有同律正被开方数给 correctedInverseScale>0。
4. 源 96–100：联合非格点调用的是对这个 P 的所有正 fixedAtom 质量的通用定理。近共振调用的是对这个 P 的真实 AE fixedAtom 支撑的通用主导收敛定理。二者均不是不透明存在族；频率恰是同一 resonanceXi/resonanceEta，且已证明 L1 频率逃逸与特征函数模长趋于 1。
5. private helper 源 19–35 从 U(K,N) 对每个自然 J,N 选 pick(J,N)，以 nseq(0)=pick(0,1)、nseq(J+1)=pick(J+1,nseq(J)+1) 定义。hpick_ge 给相邻严格递增，strictMono_nat_of_lt_succ 和 hmono.tendsto_atTop 给两个真实输出；零/后继两个分支证明每个 nseq(J)>0 且 J<G(nseq(J))。该步骤未再选择概率律，包含 J=0 边界。
6. 输出每个 J 的 G 是实际 sqrt(n)(normalizedTailCoefficient−correctedInverseScale)。因此是一个固定概率律上的严格递增真概率余项见证，不是有限模型、三角阵列或任意函数序列。

直接完整核对 v37 SourceFixedLawRemainder 1–235（其公开定理无外加渐近/连续性前提）、ResonantLimit 1–99、JointNonlattice 1–118、InverseTilt 1–174、AtomicMeasure 1–139、PositiveRate 1–189、ResonanceArithmetic 1–89，以及 SampleChangeOfMeasure 和 SampleBoundary 的真实定义与证明。旧的有限阶段/转移链作为已接受基线使用，其 66 个项目依赖字节哈希均重新与精确 frozen head 和 v37 accepted 绑定；本次不把它描述成再次证明整个旧库。

## 证据绑定和实际声明

对三个冻结 head 的全部六个工件分别计算 SHA256。源、scope、statement-review 与作者 receipt 字段一致；proof-review 与本地 handoff 所列值一致。服务器 run 的成功源码快照、成功 source-NN.lean、Audit.lean、receipt.json、proof-review.md 与相应冻结工件字节相同。每个历史 source-NN 和 build-NN.log 的哈希吻合历史记录，成功日志仅有警告，无错误。失败历史保留，不将首次失败描述成通过。

| PR | 首次完整成功 | 成功 build SHA256 | Audit log SHA256 | actual-declarations SHA256 | author receipt SHA256 |
| --- | --- | --- | --- | --- | --- |
| 148 | 02，4.1707s，2 warnings | e81311040cb9a556d9e60dc2f9fc17200248c8176efa745d7b712b85ba8d231f | 1754a5eeba9fad949082c1a53e92f53dd87794fda7617fde4fde9973bd3a4105 | 81fd11d992bba421c5b5213259fb6fff522ec2c15c1b9e121c1d084fdd13a5f1 | 17823c7285a1dc88566e1742c51bde29063bb85af19314e3812a6f115fcccd06 |
| 151 | 02，5.6088s，23 warnings | acb4088ba6995447f238ac26d758f9678d821798b4592b7badaf844171a05d50 | 7ec6611f64589bfbc09ad563a781b1dbbdf585c52c0ea2f5aaa9da43142cbc83 | 3a448fce8e660993cbe82076464c6420ed66e4a78ad5d21c9b5324f1afd46a97 | 6e61368fed021ce463371c837e051072074889173be8c276e3472fe67431ce78 |
| 152 | 01，4.5295s，1 warning | 2ee1b5947d0462ab569dd7523dcb6216e528e49f62be333d844d6e0a54865972 | 33b738bde270930847abf38e65550d397d9f2d760220171b3e48c69592e8219f | 4e0f9ed3416336bcc50e2ac252928ac70ae887676585493ede00f762df440ac2 | e69f55873e4dca2f9c981de398ec83c0916eb7c8244818596436dd28c1d4e74f |

成功作者命令均为服务器 CPU14–17、-M8192 -j4 -DautoImplicit=false；本轮未重跑。148 的第一次完整失败是常数等式证明，151 的第一次完整失败是紧集表达式解析；其 source/log 哈希及退出码完整保留在 JSON。没有弱化证明设置。

全部实际声明数为 9 / 23 / 2，共 34；其中公开定理 3、private 定义 6、private 定理 8、generated 定理 17，合计 theorem 28。核对实际完整 TYPE 的名集与 receipt 中逐项公理名集一致。
PR148 七个 generated 项均为具体 simp 命题；PR151 十项包括六个定义等式及 ContinuousAdd、SMulCommClass、ContinuousConstSMul、NeZero 实例证明，均与真实源码相符。逐项传递公理仅 propext、Classical.choice、Quot.sound；新源去注释后无 sorry/admit/axiom/unsafe/native_decide。
148/151 的原作者 Audit 采用目标/private 前缀选择，152 采用精确 module owner。这里没有把前缀门冒称根统一覆盖门；根协调仍须在后续整合门按精确所有权确认完整覆盖。

依赖源码图中的 17 / 8 / 66 个项目路径逐一以对应 head 读取并哈希，全部匹配 receipt，也全部与 v37 accepted 同字节。排序紧凑映射 SHA256 分别为 a1f4b5aa595cc437fb511345cdcd4b9d3471b3f88bcc50fbc7ea90247e421766、07ac7a5a474ea797a09196c33283033d7200dec1693cd15350e53abb6f39181a、58e653fb52d5e8da7a8f35ad6fbeb5c33ff0416ea46ba6cef7d6447dd28e81de。PR152 不依赖148/151，后续可对它输出的同一 w/q 直接应用148/151。
完整路径、全部工件哈希、依赖哈希映射、历史快照绑定和全部实际声明类型见 oq3-review.json；原始完整日志留在服务器各 runs/oq3/{u19b,u19c,u20a}-20261021 目录。

## 关键缺口与未闭合范围

本次三个冻结命题内：CRITICAL GAPS = []。

原根范围仍保留：
- canonical K 与 literal K 的实际接口应用、canonical domK / extended-real supremum / 全局率与 saddleRate 的识别。
- canonical 全局最小值/唯一性、mean-map 逆邻域，以及实际几何常数与 canonical vCorr 的最终组装。
- 标准 Mathlib IsBigO 否定尚非 PR152 的公开类型；该 PR 导出更具体的严格递增带符号缩放余项见证。不得把后续 Landau 接口模块提前计入本批。
- 本批没有证明可选式(14a)的每个多项式 weak-Cramér 失败速率，也没有新增原 A/B/C/D 根闭合。
- 根统一编译、精确 module owner、公理及覆盖门待根协调执行。本验收不合并、不发布、不改分线状态。

最终裁决：三个冻结公开命题 CORRECT；可进入根协调后续整合门。原 OQ3 A/B/C/D 按现有账保持 OPEN。
