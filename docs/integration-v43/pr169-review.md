# PR169 独立根验收

STATUS: CORRECT

本裁决针对冻结的 U21c 模块及其明确声明的局部义务。已独立读取完整 495 行实现、103 行冻结范围、全部 121 行实际类型，完成下述数学推导后才读取旧证明审查查漏。未实现或修复证明；未运行 Lean、远程命令或 Git；未改动作者文件、缓存、版本锁或共享协调文件。

审查者：/root/pr169_acceptance；协调者：01a16680-f408-7391-8c52-d1d5041bda8b。审查时间：2026-10-23 02:17 UTC。工作流为 math-theorem；没有启用 math-ultra。

## 冻结对象与实际核验

| 项目 | 冻结值 |
|---|---|
| PR | https://github.com/randomcat4/shao-lean/pull/169 |
| head | c06e026254837782a706bcde0b8c7218c7f71eb4 |
| parent | b3362fcb26bda08f5027ef3118ad6c759f0f5138 |
| tree | 8e9e9fe74b41db079f31bd8232ae9a3e93e9ce4a |
| 模块 | Shao/OQ3/CovarianceWhitening.lean |
| 本地源 | drafts/oq3/CovarianceWhitening.lean |
| 源 SHA256 | d1f90abf2ecd59032dc5f934dbedbe9c3ab9e468f73b0d4f40b24b4a7851eec8 |
| 源大小 | 495 行，24907 字节 |
| scope SHA256 | 0952e68e7cc354ebc1e6fd379f68caf8a27fd75b52ed9865dbac4576caecbfc8 |
| actual-types SHA256 | ea9e1e1f4713e5937b4e36dab2ea6dfb19fe9d9fd457fa1237d277620b522855 |
| author-receipt SHA256 | fbead0b13fe38468fa7bb5343c791611267f7629bddcc8747c27e2abc11bdff8 |
| Audit 源 SHA256 | 64383ec3d306c68f7fcfb1bf30b7922479c9170877d826ff57c93964c737990f |

以上本地文件哈希实际重新计算。两个公开声明从当前实现抽出，和冻结 fence 去空白逐字比较均为 true；三个 import 也与冻结范围一致。源码手写 theorem 为 5 个，其中 private 为 3 个；实际类型和声明清单各 6 项，名称集合完全相同。禁止标记 sorry/admit/axiom/unsafe/native_decide/implemented_by/set_option 在当前源中均无匹配。

head/tree/parent 的发布绑定来自 u21c-pr-verification.json、u21c-commit-state.json、u21c-api-publication.json 和交接记录；本次未重新查询 GitHub 实时状态。根协调仍应在集成时确认实时远端 head 与此冻结对象一致。这不是一次新的构建收据。

## 来源到声明的忠实性

原来源为 C:/game/shao/current/oq3/proofs/r2/report.md，实际 SHA256 为 572e74aa9c12e2771f5543a5709a2807666eeea0a4076e7a3263e5c7bcf87f55。本次直接读取其 1–145、321–405 行，承重范围是 38–60 的实际统一谱、83–92 的标准化以及 343–373 的有界倾斜稳定性。

来源的 W=(X,X²)、真实中心 m 和正协方差标准化，在本节点中落实为同一 mu 的两个积分、实际 parabolaCovariance mu 和 mu.map Y。RegularCovariance.lean:20–24 的定义确为 [[Var(X),Cov(X,X²)],[Cov(X,X²),Var(X²)]]；没有自由协方差矩阵。源 217–219、310–321 的 m/Y/nu/Phi 都由这些真实对象确定。

第一公开定理只输入真概率、X 与 X² 的真 L² 和任意实矩阵 A。第二公开定理输入共同有界支撑、实际协方差的共同谱以及原始特征函数的一致弱 Cramér 界；它不再输入任意 A 或频率比较结论。hspec 是来源 (2) 的明确假设，既未隐藏，也未声称已由具体紧倾斜族自动生产。

本库没有名为 UniformWeakCramer 的 Lean 声明；当前接口直接写全量化不等式。审查的是源 307–309、343–345 和 AffineWeakCramer.lean:84–98 的实际 forall 界。JointNonlattice.lean:20–24 将 jointCharacteristic 定义为同 mu 下 exp(i(xi X+eta X²)) 的积分，因此这里没有任意代理函数或同名空壳谓词。

第二定理给出的矩阵是明确正对称白化，并不声称已绑定到另一个库 Matrix.rpow 定义或证明了相应唯一性。对当前冻结结论，这一边界忠实：所需对称性、正性、ADA=I、单位真实协方差及频率界全部实际证明。它尚未证明来源中的一般倾斜 Hessian 等于 covariance，或均值映射的局部逆。

## 全部证明的独立评估

### 私有连续性与半径界

源 12–21 将 Y 的每个坐标展开成两个实多项式项，continuous_pi 与有限和给真实连续性，故后续 map、积分和 AE 推送都具备真实可测性。这一证明允许任意 A 和中心，未依赖 A 可逆或概率假设。

源 23–27 两边先证非负，再平方；x²+y²≤(|x|+|y|)² 由 |x||y|≥0 得到。因此结论是实际欧氏半径界，未将 Fin2 函数空间的默认最大值范数误用成欧氏范数。

### 私有谱数据：源 29–210

令 a=D00、b=D01、d=D11、delta=ad-b²。源 62–69 在 (1,0)、(0,1) 使用 lo>0 的谱下界，给 a,d>0。源 70–78 在 (-b,a) 使用同一下界，给 a*delta≥lo*(b²+a²)>0；由 a>0 推 delta>0。于是 79–84 给 s=sqrt(delta)>0、t=sqrt(a+d+2s)>0 及 st≠0。后面的每次分母消去均在此之后。

源 85–87 用 D10=D01 恢复完整对称矩阵，避免仅有上三角二次型而未控制 D10 的漏洞。令 N=[[d+s,-b],[-b,a+s]]。源 88–109 的四条多项式恒等式，代入 s²=delta 和 t²=a+d+2s 后，逐项给 NDN=(st)²I；110–119 覆盖全部四个矩阵分量。120–133 利用 A=N/(st) 和 st≠0 得 Aᵀ=A、ADA=I。没有以相同迹或行列式代替矩阵恒等。

源 134–154 另证 A 的正性。对非零 u=(xi,eta)，r²=xi²+eta²>0；谱下界在 (-eta,xi) 给 q_D(-eta,xi)>0，而 uᵀAu=[s*r²+q_D(-eta,xi)]/(st)>0。该步骤实际排除了负白化矩阵，不能只用 ADA=I 替代。

源 155–167 对 v=Aᵀu 证明 q_D(v)=uᵀADAᵀu=||u||²。使用 dotProduct 的转置身份和 A 对称性，方向正确；176–179 还原 v 的两个坐标正是 xi*A00+eta*A10、xi*A01+eta*A11。180–201 将原谱界用于这个 v，得到 lo*rA²≤r²≤hi*rA²。两边非负后开平方，再只除正 sqrt(lo/hi)，202–210 得 L*r≤rA≤U*r，其中 L=1/sqrt(hi)、U=1/sqrt(lo)。未除 r 或 rA，故零频率完整保留。

### 第一公开定理：源 212–289

源 227–237 固定 W=(X,X²)、同 mu 的真实中心 m 和 Z=W-m。h1/h2 分别给两个 W 坐标 L²，减去有限测度常数后仍为 L²。238–241 先由 L² 得 L¹，再使用积分相减与概率质量 1 得 E Z_i=0；没有操纵不可积总化积分。

242–250 将 Y_i 写成两个 A_ik Z_k 的有限和，以真 L² 的标量乘和加法给 Y_i 真 L²。251–254 通过实际连续可测 Y，得到 nu=mu.map Y 为真概率。273–274 以真实可测坐标和 map 的 MemLp 传输，将该 L² 结论交给同一个 nu；275–280 的 integral_map 与实际可积项的积分线性给 E_nu y_i=0。

255–267 去掉中心常数后，四个 covariance(Z_i,Z_j) 分别匹配实际 parabolaCovariance 的四个条目；对角由 covariance_self 连接到 variance，反序交叉项由 covariance_comm。281–289 先 map 回同 mu，再对两个真 L² 有限和展开 covariance，提出标量后得到 sum_kl A_ik D_kl A_jl，即 (ADAᵀ)_ij。输入 L² 保证全部居中乘积积分真实有限。定理对退化 mu、零或奇异 A 也有效，没有偷借第二定理的正谱假设。

### 第二公开定理：源 291–491

源 346–381 的局部 let 与公开结论相同，未重选 law、中心、矩阵或频率常数。382–385 在 p 之前统一给 L,U>0、Q≥0；386–406 将实际 parabolaCovariance 的定义对称性及 hspec 交给谱 helper，真正生产所有 p∈K、所有实频率的 hfreq。

407–409 调用已接受的 AffineWeakCramer 公开传递定理，参数为同 K/mu/A/m 和刚生产的 hfreq。该依赖的 24–69 证明真实 map 积分的相位分解，频率为 Aᵀu，平移相位的模为 1；其 120–148 由 r>R/L 得 rA>R，再由 rA≤U*r 与 beta≥0 得 rA^(-beta)≥(U*r)^(-beta)。因此源 407–409 的 cA=c*U^(-beta)、RA=R/L 及不变 beta 方向和因子都正确。

412–421 在每个 p∈K 建立真概率实例，并由 |X|≤M、|X²|≤M² 给两个真实 L²。422–428 消费第一定理，再用 A 对称及 ADA=I 交付同 nu 的零均值、坐标 L² 及所有真实 covariance(y_i,y_j)=if i=j then 1 else 0。实际有限矩已在代入 covariance 之前给足。

429–434 由同 mu 下的实际支撑界给 |m0|≤M、|m1|≤M²。435–448 将已生产频率上界作用于 e0/e1，得到 A 每一行欧氏长度≤U，再给全部 |Aij|≤U。450–469 在源 AE 事件上用 |X-m0|≤2M、|X²-m1|≤2M² 得 |Y_i|≤2U(M+M²)；两个乘积均正确取绝对值。470–472 由欧氏半径界给 rho(Y)≤Q=4U(M+M²)。

473–476 对真实可测半径次水平集使用 ae_map_iff，将该源 AE 界推到同一个 nu。477–489 对任意自然 k 先给 ||rho^k||≤Q^k，再以真概率和强可测性给 Integrable，最后由积分范数界得到实际积分≤Q^k。这里不是以不可积积分的默认值冒充矩；k=0 及 Q=0 的幂约定均保留。490–491 汇总的是同一 nu/Phi 的所有输出。

### 生成项与量词边界

Shao.OQ3.parabolaCovariance.eq_1 的完整实际类型是旧真实定义的四条目等式，与 RegularCovariance.lean:20–24 一致。它未引入概率、正定性或有限性，当前证明另行提供这些门。该项虽处旧定义的 namespace，实际 owner Audit 将其计入本模块并审计，不按名称错误排除。

K 可以为空，所有共同常数仍在 p 之前定义并满足全局符号结论；无需 Nonempty K。M 不作分母，M=0 无非法消去；非空族时严格谱与该退化情况不相容只表示输入不可同时满足。beta=0、R=0、零频率和 k=0 均未删去。第一定理允许非中心原分布及奇异 A。参数类型没有拓扑或可测空间要求，因为没有对 p 积分；常数不依赖 p、k 或频率。未静默加入 lo≤hi、紧性、联合可测性、目标白化性质或标准化弱 Cramér 结论作为输入。

## 传递公理、覆盖及既有机械证据

已直接读取 u21c-audit.lean 的全部 45 行。它按 env.getModuleIdxFor? 的真实模块 owner 遍历 env.constants，拒绝新项目 axiom，并对每个所属常量运行 Lean.collectAxioms，逐项拒绝白名单外传递公理。它还验证两个冻结公开目标确为 theorem，非按名称或源文件正则猜覆盖。

actual-types、u21c-declarations.json 和 receipt 的集合对应为 2 public + 3 authored private + 1 generated = 6 theorem，0 definition。六项均记录 [propext, Classical.choice, Quot.sound]，无 sorryAx 或额外公理；本次独立比较名称集合和白名单均无差异。实际类型完整保留了所有输入、let、Type universe 和输出，无省略号。

机械证据来自现存服务器收据，非本审查新执行：当前源首次完整成功是 attempt 3，2026-10-23T00:10:23.885784Z，exit 0，15.623900 秒；构建日志 SHA256 为 0025579dcc9925eb65e19dd71dd4f03f73c5718f829992d0cb0d3cd0af2030fa，1102 字节，记录 4 条样式建议而非空日志。attempt 1/2 的失败被保留，未当成当前成功。

首次模块 owner Audit 于 00:11:26.589310Z 完成，exit 0，5.417973 秒；日志 SHA256 为 d5d7e6f486eb59c7a03f57caa15a37b6853c9be8d458f6050b296ec85bf25943，8072 字节。两项均绑定当前源 d1f90abf...；CPU14–17、原生 8192MiB、j4、autoImplicit=false。Audit 的打印选项只控制类型输出，不弱化证明设置。原始日志按项目政策保留在服务器，本次未下载或新造日志。

library/lean-toolchain 和 lake-manifest.json 确认 Lean v4.36.0-rc1、Mathlib 807d3836b165983210ee2ecf3cd28f239436949c。u21c-prerequisite-hashes.json 的 11 个项目依赖条目与已接受 v42 receipt 的 source_files_sha256 字典逐项一致；这里仅比较现有字典，未重建依赖或重哈希旧稳定缓存。v42 收据的 SHA256 实核为 2ad04589996e9e8600ee1cb7add8d7fab9d34edf4ec0f7f19454bcc5edf7bd00，记录构建、所有声明传递公理及模块覆盖门均 exit 0。

本次以已接受、钉死版本的 Mathlib API 为证明依赖边界，没有声称重新阅读本机并不存在的完整 Mathlib checkout，也没有独立重跑其内核。对真实数据的本地展开、所有 API 使用前提和数学推理已逐项核验；当前静态结论与现存源绑定服务器成功证据相互吻合。

## 阅读依赖、独立性与剩余范围

直接读过的证明/定义依赖：library/Shao/OQ3/AffineWeakCramer.lean 全文 1–152；RegularCovariance.lean 全文 1–305（本模块实际使用定义在 20–24）；JointNonlattice.lean 1–100（本模块承重定义在 20–24）；CompactTiltWeakCramer.lean 全文，仅用于确认下游接口和未完成装配边界。另读 u21c-audit.lean、u21c-compile.py、全部实际类型和声明清单、作者/审计/发布/交接证据、11 项前置哈希字典、v42 收据的相关字段与 OwnedAudit 源。

先独立完成上述证明判断后，才完整读取 327 行 u21c-proof-review.md，SHA256 实核为 b9fd1c10e8f948e46e45a8aa4a80cc3962a4f687abd2166ba8a90a99e52724f9。未发现其提出的 API、转置、分母、总化积分、生成项或边界风险有本次推导遗漏。旧票只用于查漏，其 API 直接原型阅读和远程日志读取归属于旧审查者；本次不冒领那些操作，也不以其 CORRECT 替代上述独立论证。

已消除的实际义务：给定真实共同谱后的明确正对称协方差白化、真实像律零均值/单位协方差、有界情况下统一欧氏全自然阶矩、从实际谱生产完整频率双界并保持同 beta 的统一弱 Cramér 界。这些不应再记成该节点的未证结论。

仍未完成：具体紧倾斜族的共同实际谱生产；与 PR159 的真实倾斜 WC 装配；一般 tilted mean=gradient 与 covariance=Hessian、均值局部逆；一般无界 B、Edgeworth/细胞/Laplace/远域概率以及 D 的后续见证等原根义务。本模块不自动关闭 OQ3 B/C/D。原 A 的 v40 闭合范围保持原记录；没有新增原根闭合或新颖性认证。

本地必要证据均存在；未发现需要补造证书的证据缺失。CORRECT 为此冻结模块的完整静态数学/Lean 源验收，根集成构建和实时远端一致性由根协调负责。
