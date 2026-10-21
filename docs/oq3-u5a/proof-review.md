# U5a 最终独立声明、来源与证明审查

## 第一阶段：实际定义与导出签名盲译

本节在本次读取最终实现证明体、scope、R1、statement review、receipt/Audit 或作者 notes/API 之前落盘。只读取 `PositiveRate.lean` 的导入、两定义与九个实际导出签名；实测源码 SHA256=`8e727078d3a4f1db2392384b84cc31235ff69efa13dd5e44b23eac818a788f7b`，189 行。前序声明审查上下文存在，本次从实际导出重新核对语义；未读取作者 U5aAPI 或笔记。

两定义为 `saddleRate(ℓ,q,w)=ℓq+log(inverseNormalizer(ℓ,w))`，以及完整原子索引上的实数 tsum `Σ_i w_i log(w_i / originalMeasure(ℓ,w).real{fixedAtom i})`。后一名称不自动保证可和、真实概率或熵含义，须由目标准备。

九目标的实际独立翻译：

1. 任意 ℓ、w，originalMeasure 几乎处处集中在 fixedAtom 值域；无概率、正性或求和假设。
2. 若 w 非负且四个实际特征均真实 HasSum 到 constraintTarget(q)，则 normalValue 对 atomicMeasure(w) 真实可积，积分为 q。
3. 若 w 非负、HasSum w 1，且指定 i 的 w_i>0，则该原子 log(w_i/P{a_i}) 精确等于 `ℓ normalValue(a_i)+log Z`；分母使用实际测度 singleton 的实质量。
4. 若全索引 w_i>0 且四特征均真实 HasSum，则加权 log 比序列真实 HasSum 到 saddleRate，不能仅通过不可和时的总化 tsum 获得该结论。
5. 同样前提下 entropy 定义的 tsum 等于 saddleRate。
6. 增加 ℓ≠0 后，真实 Z 严格大于 exp(−ℓq)；ℓ 不限正负，全原子正质量仍是明确前提。
7. 相同门下 saddleRate 严格正。
8. 相同门下 entropy 严格正。
9. 存在同一 p>0、q∈(1,103/100)、eps>0 及 sourceEll 下四旧点矩阵方程，使其后每条正、可和、总和<eps 的完整 r 都产生同一组定义对应的原律 P：真概率、恒等函数可积且均值0、entropy=saddleRate 且两者严格正。p/q/eps 在 ∀r 前固定，P 可随整条 r 改变，但不能在同一 r 下随 J 或 n 改变。

本节未读完整证明，尚未形成证明裁决。下一阶段须核查真实 π/P、离散相对熵顺序、真实可和、严格非恒定性与源所承诺的有限覆盖。

## 第二阶段：冻结、真实来源及 π/P 对应

盲译先落盘后，才读取冻结 scope、既有独立声明报告、真实只读 R1 146–159 及真实导入定义。实测 scope SHA256=`1de636f4c3d8cbd7d4fafd715ab8af5fad0e65e5d3a138d239c69b51a91d6eeb`；声明报告 SHA256=`fa1eb29d0bc1fe4071e72c4d2cf38018e57bc21a7ee54e0e80d049d1fa042169`；真实 R1 SHA256=`3473d34ff20bd0d334b9ef3ea3c3ee167fba4d5cc3a742849820ce54d639e662`，均与委派值相符。独立空白规范化比较实际两定义的完整定义体及九目标的完整签名，11/11 相同、无差异项，没有增加/删减条件。

实际定义是 `Y(x)=8x−x²`，四特征为 `(1,x²−4x,x exp(−ℓY),x²)`、目标 `(1,0,0,q)`；全索引为 Fin 4⊕ℕ，fixedAtom 单射，值域可数且有统一紧界。真实 π=`atomicMeasure w` 是带权 dirac 和，非负门下 π{a_i}=w_i；真实 P=`originalMeasure ℓ w` 是 π 以 −ℓY 倾斜，`Z=inverseNormalizer ℓ w=∫exp(−ℓY)dπ`。已独立完整 CORRECT 的 U4 给真实指数可积、Z>0、P 真概率和实际 singleton

```text
P{a_i}=w_i exp(−ℓY(a_i))/Z。
```

上述公式指实轴测度的真实单点实质量，没有把索引质量当成可能有重数的测度质量。U3a 已证 fixedAtom 单射；U3b 与本单元 26–29 的 AE range 结论分别保证 π、P 无值域之外的剩余质量。

| 真实 R1 行 | 实际声明/证明的覆盖 |
| --- | --- |
| 149–151 | EπX=q/4 已由 `atomicMeasure_mean` 给出。本单元另外证明 EπY=q；这是 `Y=x²−2(x²−4x)` 的结果，未将 π 的均值错误写为0。有限 π_J 不在本单元目标中。 |
| 152–153 | 本单元不证明鞍点方程、x0 范围或全局极小/唯一性；saddleRate 只是源所用率的命名，不能替代这些证明。 |
| 154–157 | 两定义和 58–101 行逐原子 log 比/真实 HasSum 精确给 D(π∥P)=ℓq+log Z，方向、正负号、分子分母正确。 |
| 158–159 | 非恒定 Y 与 ℓ≠0 提供严格 Jensen，推出严格正率及熵；没有将一般非负 Jensen 直接改成严格结论。 |

## 第三阶段：189 行完整证明与局部辅助审查

完整读取固定哈希 `PositiveRate.lean` 1–189 行。在读取本单元 receipt、Audit、build 日志之前，独立数学判断为 CORRECT，无关键缺口。未读取作者 U5aAPI、notes 或 frontier。

| 实现行 | 精确逐步核查 |
| --- | --- |
| 20–24 | 率定义为 ℓq+log Z；熵以 π 的 w_i 加权 log(w_i/P{a_i})。两个全定义对象只在后续明确概率/可和门下解释为真实率和有限离散相对熵。 |
| 26–29 | tilted 对原测度无条件绝对连续，把 π 的 AE range 支撑传给 P。即使任意 w/ℓ 落在总化零测度分支，单纯 AE 支撑结论仍成立；该分支未用于任何概率或熵结论。 |
| 36–43 | hm 第0坐标真实给 HasSum w 1，hw 非负使 π 真概率。连续多项式 Y 与实际 AE 紧上界满足 U4 的连续可积桥，所以 hY 是真实 Integrable。ℓ 无正号限制。 |
| 44–49 | 前序原子约束积分接口给 boundaryFeature 真实可积且积分0，以及 x² 真实可积且积分q。不是只读取两个总化积分值。 |
| 50–56 | 逐点 ring 证 `Y=x²−2boundaryFeature`；integral_sub 显式消费 x² 和 2boundaryFeature 可积，线性积分后得 EπY=q。 |
| 62–67 | U4 给 hZ>0，实指数 he>0；同一 i 的 hi>0 使实际 P singleton 比值>0。先代入真实 singleton 公式，再对外层商、内层商及乘积分别合法取 log，所有非零门明确；log(exp(−ℓY))=−ℓY，最终 ring 得 ℓY+log Z。未取消零权重或忽略零分母。 |
| 75–80 | 从全部 HasSum 约束取得真实质量和、boundary 加权和0、平方加权和q，适用完整索引而非有限截断。 |
| 81–86 | 对 HasSum 作精确线性组合 `hq−2hb`，逐索引展开 Y 与 boundary 后 ring 得加权 Y 的 HasSum q；没有从 tsum 等式倒推 Summable。 |
| 87–94 | 对 hY 乘 ℓ，对 hmass 乘 log Z，再相加。每个 i 使用前项正确的 log 比公式，把真实可和序列逐项改写成熵项；极限值正是 ℓq+log Z。这是目标序列的 HasSum，保证真正可和。 |
| 96–101 | 仅在刚证 HasSum 后取 tsum_eq，得到定义的 entropy=saddleRate，未依赖不可和时 tsum 默认0。 |
| 108–115 | 严格部分先取得同一 π 的概率实例、EπY=q 与 Y 可积；T=−ℓY 可积由常数倍给出，exp(T) 可积由 U4 在实际紧支撑上对任意实 ℓ 的指数可积性给出。 |
| 116–119 | 指数在整个实线严格凸且连续，闭集合为 univ，AE 值域门自动成立。严格 Jensen 二择一的全部条件均显式传入：T 几乎处处等于其同一 average，或 exp(average T)<average(exp T)。没有把 strictly convex 的结论用于一个缺少可积性的期望。 |
| 120–127 | 在常量分支，对任意实际索引 i，若 T(a_i)≠同一平均值，则 singleton {a_i} 包含于 AE 等式的异常集。hpoint 的平均值没有依赖 i 重新选择。 |
| 128–136 | hconst 明确给异常集测度0，单调性使该 singleton 质量0；通过实际 `atomicMeasure_real_singleton` 化为 w_i=0，与 hw_i>0 矛盾。这正确把 AE 等式提升到指定正原子，未提升到任意点或整个拓扑支撑。 |
| 137–139 | 选择真实旧原子 −1 和1，其 Y 值分别为−9、7。两 hpoint 共享同一平均值，故9ℓ=−7ℓ，精确线性算术给 ℓ=0，与 hell 矛盾。两个值确实不同；严格性不来自“原子数多”或收敛性。 |
| 140 | 排除常量分支后，π 概率性允许 average=integral，T 积分以 hY.2 化为−ℓq，exp(T) 积分正是同一 Z，于是 exp(−ℓq)<Z。 |
| 147–154 | 真实质量门再次给 Z>0，exp 的值也>0，满足 log 在正半轴严格递增的两个条件。取 log 得−ℓq<log Z，因此ℓq+log Z>0，符号正确。 |
| 156–162 | 精确使用已证 entropy=rate，再用率正性给实际离散熵正性，没有独立假定 KL 正。 |
| 175–181 | 一次取得 `exists_source_limit_family` 的同一 p、q、eps，输出见证后才引入任意 r。该 r 的全索引正质量、四 HasSum 和总质量门来自同一个 hfamily，没有更换 witness。 |
| 182–186 | 对同一 w 组合 U4 真概率与 P 均值0、当前熵等式与两项严格正性。`sourceEll_pos.ne'` 明确给 sourceEll≠0。不存在随 r、J 或 n 变化的 p/q/eps，亦未把 π 均值q/4赋给P。 |

全部局部辅助（hmass、hY、hb、hq、hfun、hZ、he、hsum、hnonneg、hf、hg、hsupp、hpoint、hsub、hnull、hzero、hreal、heq、hlog、hpos）均覆盖。源没有顶层私有定理；源外生成声明仍须在最后机械阶段核查真实审计记录。

### 标准离散 D 对应、边界与非声明

在熵目标的显式门下，π 与 P 是同一可数、无重复原子族上的概率测度，π 的全部质量是 w_i>0，P 的全部质量是 `w_i exp(−ℓY_i)/Z>0`；双方几乎处处落在该值域。因此当前求和正是标准离散 D(π∥P)。没有重复计数、漏掉连续质量、交换 D 的方向或将 ENNReal.top 的 toReal 误作质量。log 比为 ℓY_i+log Z，Y 在支撑上有界；结合真实概率质量还独立保证加权绝对值可和，与 69–94 行直接给出的 HasSum 一致。这不声称建立任意测度的通用 RN-KL 框架。

ℓ=0 时 Z=1、P=π、率及熵为0，所以严格正目标的 hell 不能删；实现没有删。任意负 ℓ 同样满足真实可积性与严格非恒定性，证明未暗加 ℓ>0。一般 log 比目标允许其他权重为0，但只对指定 hi>0 的项取 log；熵/严格 Jensen 则明确要求全索引严格正。不把可行性之外的任意有符号、不可求和 w 的总化定义解释成有限相对熵。

当前仅完成已构造无限原律的正离散熵与指数率。有限阶段律、鞍点方程/全局唯一性、协方差正定、LLT、尾渐近、曲边界常数、尖点和对角不在本单元中；根 A/B/C/D 保持 OPEN。

本阶段独立数学裁决：CORRECT。以下机械证据必须在此判断之后读取，且不以作者回执代替真实服务器产物核对。

## 第四阶段：真实服务器机械证据

在上述数学判断落盘后，才完整读取 `U5a-receipt.json` 与 `U5aAudit.lean`。实测两者 SHA256 分别为 `954d29222c6664c3718da8c177ca06709465f6fa9076c53b7c6ac2d0fb4f2588`、`e09d71b033c8ea6c523feccf046dc89e67101984515d7e5de087f9b5bc0a471b`，与委派值相同。实际源扫描未见 sorry、admit、新 axiom、unsafe、native_decide；源为规范 LF，无 CR 字节。

已完整审查 Audit 源：逐一要求九个冻结目标存在且为 theorem，两定义存在；遍历全部十一源声明前缀与模块私有前缀，拒绝新增公理，对每项用 `Lean.collectAxioms` 核查全部传递依赖，只允许 `propext`、`Classical.choice`、`Quot.sound`。脚本输出各实际 TYPE，并要求冻结目标数为9。

随后通过共享 `tools/server.py` 对指定服务器进行一次只读源/依赖哈希、Git、pin/版本和既有日志核对，实际远端 exit 0、stderr 为空。没有重复目标编译或 Audit，没有写 cache、共享代码或既有报告。

- 实际 worktree=`/root/rivermind-data/shao-lean-20261021/workspaces/lead-oq3`，branch=`feat/oq3-positive-rate`，HEAD=`15127f6041741db7e89a05dc841d4fb982be6893`，与作者回执基线相同。本报告绑定冻结源与 pin，不声称 main 已集成。
- 真实 `PositiveRate.lean` SHA256=`8e727078d3a4f1db2392384b84cc31235ff69efa13dd5e44b23eac818a788f7b`，与本地完整审查源及 receipt 相同。
- 真实导入 U1、U2、U3a、U3b、U4 SHA256 依次为 `800d9db8cb6749a31ecfe611409de92b10ea8bb2aef955bfd825ede7324f0ef0`、`0e2a081619976f88149707c2ef9311dc909003e61d3d0f7c4e21e6c3dbbc5a6d`、`0ea4c64fe9ef9b45fbf44d24312771a1dbfbcc5de8448564e3e87bdf17c7178b`、`59ddc48fb7b395f362939e58cbd9d7911685a6ed6e6574142e8a6d4ab3ee0c39`、`c7e7d19e8b70481b663bec1fd12ea9301d73313faaf35997e85aa9ba99f21811`，均与 receipt 和已独立完整 CORRECT 的前序相同；U4 明确绑定已审 LF 版本。
- receipt 记录目标命令 `lake env lean -o .lake/build/lib/lean/Shao/OQ3/PositiveRate.olean Shao/OQ3/PositiveRate.lean` 原执行 exit 0；真实 `runs/oq3/u5a-20261021/build-02.log` 为0字节，SHA256=`e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`，与回执相同。
- 真实 Audit.lean 为1933字节，SHA256=`e09d71b033c8ea6c523feccf046dc89e67101984515d7e5de087f9b5bc0a471b`，与本地已完整阅读的脚本相同；receipt 记录原 Audit 命令 exit 0。
- 真实 Audit.log 为5452字节，SHA256=`bac86ea74f365afef6c9de66f455b2b1ea12fdadb8fee55c726708090b2e4b10`，与回执相同。实际日志已完整读取，九个目标 TYPE 与冻结接口一致，特别保留真正 HasSum、严格正 hw、ℓ≠0、实际 singleton、以及最终先存在 p/q/eps 再 ∀r 的全部门。
- 实际日志输出 `U5A_FROZEN_THEOREMS 9`、`U5A_ALL_THEOREMS 9`、`U5A_ALL_DECLARATIONS 11`、`U5A_AXIOM_GATE PASS`。本模块无额外顶层私有或生成声明；hpoint 等全部局部辅助已在完整源证明内审查，并包含于这九个 theorem 的公理闭包。全部十一声明和传递导入依赖只含标准白名单。
- 实际 Lean=`4.36.0-rc1`，commit=`c9afcddf514a6772bd4d649f7cfc04eff0b9f15e`；Lake=`5.0.0-src+c9afcdd`。实际项目 pin=`leanprover/lean4:v4.36.0-rc1`，manifest mathlib revision=`807d3836b165983210ee2ecf3cd28f239436949c`，与冻结凭据相同。

STATUS: CORRECT

机械覆盖：LEAN_FULLY_CHECKED，仅指固定哈希 U5a 两定义、九目标及其传递依赖的既有真实成功构建/公理审计。本次另完成实际声明—源码—真实 R1 忠实性、完整证明和所有局部辅助审查，没有根集成构建或其他旧目标重编。

JUSTIFICATION: 两定义与九签名精确匹配冻结接口；真实 π/P 的离散 D 顺序、实际 singleton、Z>0、HasSum 真可和、严格 Jensen 的 hpoint 正原子提升与两原子非恒定性、ℓ 非零、率/熵严格正及固定 source p/q/eps 均有完整证明。真实服务器源、承重导入、TYPE、成功日志及传递公理白名单全部匹配，无关键缺口。有限阶段、全局鞍点唯一性、LLT、尾渐近、对角和通用 RN-KL 框架未在此证明；根 A/B/C/D 保持 OPEN。
