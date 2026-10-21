# U5b 最终独立声明、来源与证明审查

## 第一阶段：实际导出签名盲译

本节在本次读取最终证明体、scope/R1、既有声明报告、receipt/Audit 或作者笔记前落盘。只读取实际 `FiniteStageRate.lean` 的导入和七个导出签名；实测 SHA256=`e654bed5e1e132af328eb6763078c7eb84f740999b146cfb5aaa9ae7ed90e29f`，164行，零新定义。前序声明审查上下文存在，本次从实际签名重新核对，未读作者 notes/API/frontier。

1. 非负真实概率权重（hw≥0、HasSum w1）下，每个原子的整体加权 log 比等于 `w_i(ℓY_i+log Z)`，允许 w_i=0；没有无条件未加权 log 比结论。
2. 非负 w 与四个真实 HasSum 约束下，加权 log 比序列真实 HasSum 到同一 saddleRate，包含零项。
3. 同一门下定义的 entropy tsum 等于 saddleRate。
4. 增加 ℓ≠0，给定两个权重严格正且 Y 值不同的实际原子 i、j，就有 exp(−ℓq)<Z。其他权重允许0；不只要求两个 X 点不同。
5. 同样条件下，rate与entropy同时严格正。
6. 任意ℓ≠0、有限阶段J，在非奇异矩阵、旧矩方程、全部有限旧质量正和整条r非负的门下，该 finiteMass 的entropy=rate且二者>0；不要求未来无限零延拓项正。
7. 先存在同一p>0、q∈(1,103/100)、eps>0和sourceEll旧矩方程，再对所有后选正可和、总量<eps的r，同时给极限P真概率、entropy=rate与rate>0，以及每一个J的有限P_J真概率、entropy_J=rate_J与rate_J>0。同一组p/q/eps在r/J前固定。

盲译未读证明，尚无证明裁决。后续必须核查零权分支只作整体乘0、实际正分母、真实HasSum、指定正原子hpoint与ℓ非零消去，以及J=0/共同参数的有限组合。

## 第二阶段：冻结接口、实际定义与真实 R1

盲译先落盘后，才读取 scope 解释和真实只读 R1 137–159、251–258。实测 scope SHA256=`f7d2180ec279d73d4775e3e92bb828a98d9d567eada6123198347b933bc57376`；既有声明报告 SHA256=`171c82c9b4d72d06df84e21286a10a81899eda244484c3840ab7ad7ffea03a73`；真实 R1 SHA256=`3473d34ff20bd0d334b9ef3ea3c3ee167fba4d5cc3a742849820ce54d639e662`，均匹配。独立空白规范化比较七个实际完整签名与scope，7/7相同，无新增或删减前提。

实际读取承重定义：π=`atomicMeasure w=Σ_i ofReal(w_i)·δ_(a_i)`，P=`originalMeasure ℓ w=π.tilted(−ℓY)`，Z=`∫exp(−ℓY)dπ`，Y=8x−x²；四特征为 `(1,x²−4x,x exp(−ℓY),x²)`、目标 `(1,0,0,q)`。已有熵定义为 `Σ_i w_i log(w_i/P.real{a_i})`、rate=ℓq+logZ。finiteMass是同一AtomicIndex上的有限阶段零延拓，旧侧finiteBase，新增j<J时r_j、否则0。U5a/U3c已完整独立CORRECT的源哈希在本次实际定义读取时未变。

| R1 锚点 | 当前实际覆盖及非声明 |
| --- | --- |
| 137–145 | 沿用实际π/P及π_J/P_J同一逆倾斜归一化与再倾斜关系；真实概率/中心化在既有U4/U3c门下成立。 |
| 149–151 | π/π_J的均值仍为q/4；用于严格Jensen的是Y均值q，不是P的0均值。实现未交换这两个律。 |
| 154–159 | 新加权接口允许零项，给标准离散D(π∥P)=ℓq+logZ，严格性由两个正质量异Y原子与ℓ≠0给出。 |
| 251–258 | 256行明确同一源证明适用于有限阶段，当前落实其中有限熵/率部分；251–255的Λ1和257的v_corr不在七目标中，不因本审查升级。 |

## 第三阶段：164 行完整证明与所有局部辅助

完整读取固定哈希 `FiniteStageRate.lean` 1–164行后，在读取本单元 receipt、Audit 或日志前形成独立数学判断：CORRECT，无关键缺口。未读作者notes/API/frontier。

| 源行 | 精确逐步检查 |
| --- | --- |
| 23–24 | 先按w_i=0分支；simp在两边的整体外因子0上消去加权项，只得到0=0。未声称未加权的log(0/0)满足正权似然公式，源码没有在此调用log_div。 |
| 25 | 非零分支由hw_i≥0及w_i≠0得到w_i>0，满足已审U5a `original_log_atom_ratio` 的指定正项门。该前序定理明确用真实P singleton和Z>0，故分母正；将其等式重写到整体加权项合法。 |
| 33–38 | 从hm第0、1、3坐标取得真实HasSum w1、加权boundary和0、加权平方和q；没有对w全正作假设。 |
| 39–44 | hq减2hb，逐项用 `Y=x²−2boundaryFeature` 的精确环恒等，给加权Y的真实HasSum q。 |
| 45–52 | 对hY乘ℓ、hmass乘logZ并相加，再逐项调用新的整体加权等式，输出熵项真实HasSum到ℓq+logZ。零权项仍只作为整体0处理；不是从tsum值倒推可和。 |
| 54–59 | 仅在前项HasSum后用tsum_eq，定义的entropy=rate不落在不可和时实数总化tsum的默认0分支。 |
| 67–73 | hm0及hw≥0给同一π真概率。U5a的通用 `atomicMeasure_normalValue`（仅非负门）给Y真实可积、EπY=q；T=−ℓY由常数倍可积，exp(T)由U4在共同紧支撑上的指数可积性取得，ℓ不限正负。 |
| 74–77 | T取值于闭实全集，指数严格凸且连续，AE值域、T与exp(T)可积三项门均显式满足，正确调用严格Jensen二择一。 |
| 78–85 | 常量分支的hpoint明确只接受指定k及其hk:w_k>0。若该点不等于同一平均值，则singleton包含于AE等式的异常集；平均值没有随k重新选择。 |
| 86–94 | hconst给异常集μ质量0，单调性使singleton质量0；通过实际 `atomicMeasure_real_singleton w hw k` 得w_k=0，严格与hk矛盾。这是正确的正原子AE提升，无“其余所有原子也正”隐藏前提。 |
| 95–96 | 用两个给定hi/hj调用hpoint，得 `−ℓY_i=−ℓY_j`。`neg_ne_zero.mpr hell`明确使左乘因子非零，`mul_left_cancel₀`得到Y_i=Y_j，与hne矛盾；没有把X不同当作Y不同或除以可能为0的ℓ。 |
| 97 | 严格分支在π概率下把average化成integral，使用真实Y积分q与同一Z定义，得到exp(−ℓq)<Z。 |
| 105–116 | hmass保证Z>0，exp值也>0，满足log严格递增的正域门；取log得rate>0。熵正性用新非负熵等式，而非旧全正定理，适用于零质量项。 |
| 126–127 | 对finiteMass先用U3c非负与完整四HasSum接口，hp只用于旧权重、hr可非负。没有构造全无限严格正质量的假证据。 |
| 128–131 | 固定两个旧完整索引Sum.inl0和Sum.inl1，其有限权重分别由hp0/hp1严格正。实际点−1、1的Y值−9、7经精确化简确实不同；对任意J成立，包括J=0。 |
| 132–133 | 对该同一finiteMass组合新非负熵等式和两正原子严格率/熵接口；未直接调用U5a要求全w>0的熵或严格率目标。 |
| 147–150 | 一次取得U3c同时有限/极限族的同一p、q、eps，先输出见证再引入任意完整r。hpos、hm、hstages来自同一次hfamily消费，有限与极限不更换参数。 |
| 151–156 | 极限hpos真实覆盖全索引，所以此处合法使用旧U5a全正entropy_eq/saddleRate_pos；hm0给总质量1并用U4给真P概率。sourceEll_pos.ne'给明确ℓ≠0，没有新源前提。 |
| 157–161 | 后引入任意J，取同一hstages J的有限旧正性与真P_J概率；调用本单元新有限率接口，使用同一hc、source非奇异性及hr非负门，输出该阶段的熵等式与正率。p/q/eps/r没有随J重选。 |

全部局部辅助hi、hmass、hb、hq、hY、hsum、hf、hg、hsupp、hpoint、hsub、hnull、hzero、hreal、heq、hlog、hrate、hw、hm、hj、hne、hpos、hstages、hpJ、hprobJ、hentropy均已审查。无顶层新定义或私有数学引理；源外生成声明须最后依据实际机械TYPE/计数核对。

### 标准离散 D、退化与有限阶段边界

在非负/HasSum1门下，π与P都真概率、集中于单射fixedAtom的同一可数值域；真实单点公式为 `P_i=w_i exp(−ℓY_i)/Z`。w_i>0时P_i>0，w_i=0时P_i=0。所以对有效正质量子集求标准离散D(π∥P)，并对剩余项约定0，恰为当前整体加权求和；没有连续剩余质量、重复原子或正分子零分母。新HasSum保证真实可和且和有限，紧支撑与log比在正质量处有界也给加权绝对值可和。

一般ℓ=0时rate和entropy都为0；新熵等式仍成立，严格性签名正确保留hell。仅两个正原子足够排除AE常量，其余权重任意为0不妨碍该论证。若两个X不同却Y相同，严格性可能不成立，实际hne明确是Y值不同。

J=0时finiteBase=p，所有新增质量为0，但两旧正原子仍存在；J>0时未来j≥J为0、新增活跃前缀也允许0。实现始终使用新非负/两原子接口处理有限律，未虚构全无限正性。最后族的entropy正性由entropy=rate>0自动蕴含，即使未单独重列；有限与极限的π均值q/4和P均值0未交换。

本单元完成非负质量离散熵接口及共同参数族的有限/极限正率，不证明全局鞍点唯一性、协方差、LLT、尾渐近、产品TV、尖点或后选尾对角，根A/B/C/D保持OPEN。

本阶段独立数学裁决：CORRECT。以下机械凭据在该判断之后读取，不以作者本地回执代替真实服务器核对。

## 第四阶段：真实服务器机械证据与哈希绑定

完整数学判断落盘后，才读取 `U5b-receipt.json`、`U5bAudit.lean`；本地实测 SHA256 分别为 `f0b6b69597467f6903bed864b99f36147bba9df7930538c51dbda6b8fb791c4f`、`34c46cbe78ea20262ed509b10ef2f615ad64e2ac2c478c7558efc7865144d110`，均匹配委派冻结值。实际源码无sorry、admit、新axiom、unsafe、native_decide，无CR字节或尾空白。

已完整审查Audit源：逐一确认七个目标存在且为theorem，遍历七目标名前缀及模块私有前缀，拒绝项目新公理，并对每项用 `Lean.collectAxioms` 核查全部传递依赖，只允许 `propext`、`Classical.choice`、`Quot.sound`；打印各TYPE和计数，要求冻结目标数为7。

随后经共享 `tools/server.py` 对指定服务器作只读核对，实际远端exit0、stderr为空。未执行目标或旧目标编译、Audit重跑、源码修改或缓存写入。

- 真实worktree=`/root/rivermind-data/shao-lean-20261021/workspaces/lead-oq3`，branch=`feat/oq3-finite-rate`，HEAD=`cc4af50f026ba37f66379dadbdf07e69b8bc6c1c`，与作者凭据基线相同；不声称本单元已集成main。
- 真实目标SHA256=`e654bed5e1e132af328eb6763078c7eb84f740999b146cfb5aaa9ae7ed90e29f`，与本地完整审查源及receipt相同。
- 真实导入U1/U2/U3a/U3b/U4/U5a/U3c的SHA256依次为 `800d9db8cb6749a31ecfe611409de92b10ea8bb2aef955bfd825ede7324f0ef0`、`0e2a081619976f88149707c2ef9311dc909003e61d3d0f7c4e21e6c3dbbc5a6d`、`0ea4c64fe9ef9b45fbf44d24312771a1dbfbcc5de8448564e3e87bdf17c7178b`、`59ddc48fb7b395f362939e58cbd9d7911685a6ed6e6574142e8a6d4ab3ee0c39`、`c7e7d19e8b70481b663bec1fd12ea9301d73313faaf35997e85aa9ba99f21811`、`8e727078d3a4f1db2392384b84cc31235ff69efa13dd5e44b23eac818a788f7b`、`1a32fb904e6ee9d2b0b48d92c4ebb3568452bb02500ce52a1a03eb01ae0256b1`，全部与receipt和已完整独立CORRECT的前序源相同。U4为已审LF版本。
- receipt记录原目标命令 `lake env lean -o .lake/build/lib/lean/Shao/OQ3/FiniteStageRate.olean Shao/OQ3/FiniteStageRate.lean` exit0。真实 `runs/oq3/u5b-20261021/build-01.log` 为0字节，SHA256=`e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`，与回执一致；未重复此成功目标。
- 真实Audit.lean为1716字节、SHA256=`34c46cbe78ea20262ed509b10ef2f615ad64e2ac2c478c7558efc7865144d110`，与本地已完整读脚本相同；receipt记录原Audit命令exit0。
- 真实Audit.log为5397字节、SHA256=`94f403731435b86d4171af54553337e914f767efad09a7bb4e588a4998ee4cf8`，与回执相同。日志已完整读取，七个真实TYPE均与冻结接口一致，保留非负/HasSum、指定hi/hj、异Y、ℓ≠0、finite旧正质量及共同参数的量词。
- 真实汇总为 `U5B_FROZEN_THEOREMS 7`、`U5B_ALL_THEOREMS 7`、`U5B_ALL_DECLARATIONS 7`、`U5B_AXIOM_GATE PASS`。本模块无新定义、额外私有或生成声明，所有局部hpoint/消去与求和证明在这七个已审theorem内；全部传递依赖只含标准白名单。
- 实际pin=`leanprover/lean4:v4.36.0-rc1`，manifest mathlib revision=`807d3836b165983210ee2ecf3cd28f239436949c`。同一指定服务器会话已实际探测Lean `4.36.0-rc1`（commit `c9afcddf514a6772bd4d649f7cfc04eff0b9f15e`）、Lake `5.0.0-src+c9afcdd`，本次pin未变。

STATUS: CORRECT

机械覆盖：LEAN_FULLY_CHECKED，仅指固定哈希U5b全部七目标及其传递依赖的既有真实成功构建/公理审计。本次另完成独立实际声明—源码—真实R1忠实性、所有证明/局部辅助检查，没有根集成构建。

JUSTIFICATION: 七签名与冻结接口一致；零权整体归零、正权真实P分母、真实HasSum与标准离散D、指定正原子hpoint、ℓ非零精确消去、finite J=0及共同p/q/eps对全r/J均有完整证明。真实源/承重导入/TYPE/成功日志和传递公理白名单全部匹配，无关键缺口。全局鞍点唯一性、协方差、LLT、尾渐近、产品TV和对角未在此证明；根A/B/C/D保持OPEN。
