# U7 最终独立声明、来源与证明审查

## 第一阶段：实际定义及十二导出签名盲译

本节在本次读取最终证明、私有辅助、scope/R1、既有声明报告、receipt/Audit或作者笔记前落盘。只读取实际 `RegularCovariance.lean` 的导入、三个定义和十二个公开签名；实测源SHA256=`0add3476cc949edc593e15dc195934a6df78a41a55f4a2281f66095733d4c853`，305行。此前声明审查上下文存在，本次从实际导出重新核对，未读作者u7-api-notes或其他思路文件。

实际三个定义：Δ=parabolaCovariance是对角为库Var(X)、Var(X²)、两非对角均为库Cov(X,X²)的实2×2矩阵；normalVariance是库Var(normalValue)；transverseVariance=detΔ/normalVariance。后两个分别是方差和方差之比，均不是平方根。

十二目标的独立精确翻译：

1. 概率μ及AE |x|≤4+√10下，任意实a,b的实际居中平方积分 `E[(a(X−EX)+b(X²−EX²))²]` 等于Δ的二次型a²Δ00+2abΔ01+b²Δ11。
2. 再加全部四旧点的实际单点实质量>0，任何(a,b)至少一个非零时该积分严格正。
3. 同样概率、界和正旧原子门下，detΔ>0。
4. 概率及同一界下，normalVariance=64Δ00−16Δ01+Δ11。
5. 加正旧原子门后，normalVariance>0。
6. 同样门下，transverseVariance>0。
7. 同样门下，transverseVariance≤库Var(X)。
8. 对非负w与四个真实HasSum约束，atomicMeasure(w)下Var(X)=q−q²/16。
9. 固定sourceEll<1/30。
10. 对q∈(1,103/100)、非负w、四旧索引权重严格正和source四HasSum，实际π的transverseVariance>0、≤q−q²/16且q/(32transverseVariance)>1/30。
11. 同一门下，normalVariance/detΔ−32sourceEll/q>0。
12. 先存在同一p>0、q∈(1,103/100)、eps>0及source矩方程，再对任意后选正可和、总量<eps的r，给极限π以及所有有限π_J真概率、normalVariance>0、detΔ>0与第11项正曲率表达式。p/q/eps在r/J之前，矩对象作用于atomicMeasure的π而非originalMeasure的P。

本节尚未审实际证明。后续必须排除方差toReal总化、确认真实积分/L²、实际正原子AE提升和三点非退化、τ²而非τ、32系数及全部J含0的同一族参数；不能从det正或已有正KL推出源全局唯一性。

## 第二阶段：冻结、真实 R1 与固定库定义

盲译先落盘后，才读取scope解释和真实只读R1 238–258。实测scope SHA256=`0fd62d524bbe643f076f153b9b7a898b5eb34d756fc631c483ded0508ed44ee8`，既有声明报告SHA256=`528daa7a715e959dab76ade3be92d829e282e9ad748e22819235486227066472`，真实R1 SHA256=`3473d34ff20bd0d334b9ef3ea3c3ee167fba4d5cc3a742849820ce54d639e662`。独立空白规范化比较实际三个完整定义体与十二完整签名，15/15一致，无前提、类型、量词或定义差异。

在本单元机械凭据之前，经指定服务器只读核对实际固定Mathlib源。manifest revision为 `807d3836b165983210ee2ecf3cd28f239436949c`；Covariance.lean SHA256=`7f261bcecb104697357f2c51f1c66154153236f3266264ba7c5dd7b8519665fd`，Variance.lean SHA256=`0bcf0e00025e061b358fbde009fc35cd2e6dc28749d724513d08caa76e69415e`，与先前声明审查的固定库相同。实际covariance（44–45）定义为居中乘积的实积分；evariance（58）为居中扩展范数平方lintegral，variance（64）为其toReal。实际variance_eq_integral（157–159）只要求AE可测，是包含总化分支的实积分等式，不能单独当作可积性证据；实际variance_eq_sub（226–228）要求概率与MemLp2。源按这些真实条件使用，而非假定方差总化永远有效。

| R1锚点 | 实际覆盖 |
| --- | --- |
| 239–241 | 三定义中的Δ为真实π下(X,X²)协方差，32–107先绑定实际居中积分并证明全非零二次型正；109–130才推出det>0，未把任意det>0当作正定。 |
| 243–245 | normalVariance=σ²，transverseVariance=detΔ/σ²=τ²；实现无τ²再平方或误取平方根。 |
| 247 | 172–198给真实τ²≤Var(X)，并从实际原子矩取得Var(X)=q−q²/16。 |
| 249–250 | 200–228精确给sourceEll<1/30和q/(32τ²)>1/30；32与严格号均保留。 |
| 252–254 | 230–257输出真实σ²/detΔ−32ℓ/q>0，未更换倒数。 |
| 256–258 | 273–302对同一p/q/eps同时处理极限π与全部有限π_J；未在此定义v_corr或完成其他全局结论。 |

## 第三阶段：305 行全部证明、私有与局部辅助

完整读取同一固定哈希1–305行，并核对上述所消费Mathlib定义后，在读取本单元receipt/Audit/build日志前形成独立数学判断：CORRECT，无关键缺口。没有读取作者u7-api-notes或其他思路文件。

| 实现行 | 全步骤与适用条件 |
| --- | --- |
| 20–30 | 实际矩阵两个非对角元素同为真实Cov(X,X²)，对角为真实Var(X)、Var(X²)；σ²与τ²均是约定的方差量。定义本身全定义，后续明确证明分母正，未借0分母除法。 |
| 37–47 | X、X² AE可测；两居中平方及居中交叉乘积全为连续多项式，在明确AE紧界与概率门下分别通过U4连续可积桥取得真实Integrable。特别X²的居中平方次数为4，没有只检查X的二阶矩就忽略四阶项。 |
| 48–66 | 化简矩阵索引后，合法使用实际variance_eq_integral和展开实际covariance定义。逐点ring给精确平方展开；hsum及每个常数倍的Integrable满足两次integral_add条件，最后提出常数。真实交叉项系数是2ab，绑定的确是实际Δ。 |
| 68–78（唯一私有数学引理） | 若AE f=0而某个实际正实质量点x的f(x)≠0，则singleton{x}包含于异常集；异常集测度0，单调性使μ{x}=0，进而μ.real{x}=0，与hx矛盾。此引理不需概率假设也成立；它只提升指定正原子，不把AE变成任意点逐点等式。 |
| 85–98 | 实际居中平方由紧支撑桥真实可积；非负给积分≥0，“不严格正”遂给精确0。integral_eq_zero_iff_of_nonneg显式消费hint，得到平方AE0，再用sq_eq_zero_iff与私有正原子引理取得每个旧点的精确居中式0。没有从不可积总化零积分推出AE常量。 |
| 99–107 | 实际选base索引0、1、3，即−1、1、2。两次相减分别给2a=0及a+3b=0，精确得到a=b=0，与至少一项非零的hne矛盾。没有以只两个抛物线点或仅X不同代替三点非退化。 |
| 113–124 | (a,b)=(1,0)的真实正积分/展开给A=Δ00>0。然后取(−B,A)，其第二坐标由A>0保证非零；实际二次型给AD>0的代数内容。矩阵对称是定义上的rfl，det_fin_two精确给D=AC−B²。 |
| 125–130 | 把上述二次型精确整理为A·D>0，再由A>0排除二者同负分支，推出D>0。没有预设协方差矩阵正定或det正。 |
| 136–155 | 显式取得X、X²真实可积，积分线性给EY=8EX−EX²；Y AE可测。variance_eq_integral后逐点ring把Y居中平方写为(8,−1)的实际居中平方，再调用已审展开得S=64A−16B+C。对应平方同样是紧支撑下真实可积的四次多项式。 |
| 161–170 | 在非零系数(8,−1)处消费真实正二次型，结合实际S展开得S>0；D/S>0由刚证D>0、S>0合法给出。 |
| 176–180 | 先用S>0合法交叉相乘，展开det及S；差 `A·S−D=(8A−B)²≥0` 精确给τ²≤Var(X)。该恒等式连接真实A/B/C，没有把横向上界加入假设。 |
| 187–198 | hm0和hw≥0给π真概率。明确以AE支撑界和MemLp.of_bound构造X∈L²，再调用实际variance_eq_sub；hm3给EX²=q，既有atomicMeasure_mean给EX=q/4，ring得q−q²/16。此处无需全w>0或ℓ≥0。 |
| 201–205 | 实际sourceU=31/30>0且≠1，两门均精确norm_num证明；log严格切线界给log(sourceU)<sourceU−1=1/30。没有浮点近似或把≤误写成<。 |
| 214–225 | hm0使同一π真概率；实际AE界由fixedAtom界继承。每个旧索引的真实μ.real{baseAtom i}通过fixedAtom(Sum.inl i)及actual singleton公式等于w(Sum.inl i)，所以hbase权重门真实满足通用hbase。得到τ²>0及τ²≤q−q²/16。 |
| 227–228 | 32τ²>0允许lt_div_iff；用τ²≤q−q²/16和q>1（及精确平方非负）证明32τ²<30q，等价1/30<q/(32τ²)。上界q<1.03在该步可冗余但未被改动；严格性来自q>1，无丢失常数。 |
| 236–247 | 再次为同一实际π建立概率、AE界、真实四旧单点正性；由先前定理取得S>0、D>0、τ²>0和ℓ<1/30<q/(32τ²)。 |
| 248–257 | 在正32τ²、S、q、D上依次合法交叉相乘。展开τ²=D/S后精确得到32ℓD<qS，最后除正qD给32ℓ/q<S/D，即Λ1>0。符号、倒数和32系数正确。 |
| 273–288 | 一次取U3c同一p/q/eps，先输出见证才引入任意完整r。该r的极限全权重正、四HasSum给同一π概率；旧singleton通过实际w(Sum.inl i)建立真实hbase，组合S/D/Λ1正性。对象为atomicMeasure的π，不是P。 |
| 289–302 | 最后引入任意J，消费同一hstages J的有限旧正性与四HasSum。finiteMass_nonneg只要求旧正及r非负，未来保持0；hmJ0给该π_J真概率，旧singleton实际等于hpJ，故通用S/D正性和atomic曲率门全部满足。没有对有限律虚构全无限正质量或重选p/q/r。 |

全部局部辅助hm1、hm2、h1、h12、h2、hfun、hsum、hsub、hnull、hzero、hreal、hint、hnonneg、hae、hpoint、h0/h1/h3、ha、hbzero、hA、hq、hsymm、hD、hprod、hmean、hmeas、hLp、hmass、hbpos、ht、hle、hfrac、hmul、hdiv、hcross、hpos、hmJ、hwJ、hmassJ、hprobJ、hbposJ均覆盖。源外生成辅助在最后机械阶段逐个查看实际TYPE，不能只接受十二目标签名。

### 总化、严格性及源族边界结论

covariance定义是总化实积分，variance定义经过evariance.toReal；但本实现显式给居中平方/交叉项真实可积、用于零积分判据的hint，以及用于方差减均值平方公式的MemLp2。所有未单独命名的X²/Y二阶量也由同一概率AE紧界下连续多项式平方有界保证有限，因此evariance不是∞，没有依赖toReal(∞)=0假通过。

前两目标与定义对称矩阵一起给对所有非零实向量的实际二次型严格正，是源正定含义；det正仅是后果。S是真Varπ(Y)=σ²，t=D/S是真τ²。通用μ允许额外连续支撑，但实际四旧原子正质量足以非退化；源族的这些门均从真实w单点公式建立。

J=0时finiteMass只有四个正旧点，−1、1、2三点仍在，故正定/S/D/Λ1链不需新增原子；J>0未来零延拓也不影响旧点门。全部阶段与极限共享U3c先取的p/q/eps及同一整条r，未在r/J/n之后换q或测度。有限率/正KL不被用于替代此正定证明，本单元也不把局部正曲率和正KL升级成全局极小唯一性。

本阶段独立数学裁决：CORRECT。此时尚未读取本单元receipt/Audit或机械日志。根A/B/C/D保持OPEN；全局唯一性、二元累积母函数微分、LLT、尾渐近、曲边界常数、尖点、产品TV和对角未在本单元证明。

## 第四阶段：作者门、真实机械产物与十八声明 TYPE 核对

上述独立数学判断落盘后，才完整读取本地 `U7-receipt.json`、`U7Audit.lean`。receipt实测SHA256=`ecac8c02964f4fbfee2bd4eadfaaa7b4438101ca7c802e325fafa254935441a0`，Audit源实测SHA256=`e5945c7af8a57968153d7f5cd8bdd6197fd6d2f064cf1bf5e6c4f670fb444721`。实际目标源码禁用项扫描为空，无sorry/admit/新axiom/unsafe/native_decide，无CR或尾空白。

Audit源已完整审查：逐一要求十二冻结目标存在且为theorem；遍历十五公共源名字前缀及模块私有前缀，对每个匹配声明拒绝新增公理并用 `Lean.collectAxioms` 核查全部传递依赖，只允许 `propext`、`Classical.choice`、`Quot.sound`，打印实际TYPE及计数。定义存在和类型由下面真实十八声明日志另独立核对，不只依赖目标数断言。

随后通过共享 `tools/server.py` 实际只读核对指定worktree的源、七份承重导入、pin/版本/Git和服务器 `runs/oq3/u7-20261021/{receipt.json,Audit.lean,Audit.log,build-03.log}`，远端命令exit0、stderr为空。没有执行Lean目标或Audit重跑，没有把日志下载到本地，也未写源、cache、旧报告或作commit/PR。

真实worktree=`/root/rivermind-data/shao-lean-20261021/workspaces/lead-oq3`，branch=`feat/oq3-covariance`，HEAD=`4e5522a6c94c2b5f43f9cbc2d099752e02491c61`，与作者凭据基线一致。

| 真实远端源 | 实测 SHA256 |
| --- | --- |
| RegularCovariance.lean | `0add3476cc949edc593e15dc195934a6df78a41a55f4a2281f66095733d4c853` |
| U1 FiniteConstraints.lean | `800d9db8cb6749a31ecfe611409de92b10ea8bb2aef955bfd825ede7324f0ef0` |
| U2 SourceStarter.lean | `0e2a081619976f88149707c2ef9311dc909003e61d3d0f7c4e21e6c3dbbc5a6d` |
| U3a SummableAtoms.lean | `0ea4c64fe9ef9b45fbf44d24312771a1dbfbcc5de8448564e3e87bdf17c7178b` |
| U3b AtomicMeasure.lean | `59ddc48fb7b395f362939e58cbd9d7911685a6ed6e6574142e8a6d4ab3ee0c39` |
| U4 InverseTilt.lean | `c7e7d19e8b70481b663bec1fd12ea9301d73313faaf35997e85aa9ba99f21811` |
| U5a PositiveRate.lean | `8e727078d3a4f1db2392384b84cc31235ff69efa13dd5e44b23eac818a788f7b` |
| U3c FiniteStageMeasure.lean | `1a32fb904e6ee9d2b0b48d92c4ebb3568452bb02500ce52a1a03eb01ae0256b1` |

全部真实源与本地已审冻结源、前序独立CORRECT报告和receipt绑定一致。U4正确使用已审规范LF版本。

真实服务器receipt.json为3330字节，SHA256=`ecac8c02964f4fbfee2bd4eadfaaa7b4438101ca7c802e325fafa254935441a0`，与本地回执逐字节哈希相同，内容已完整读取。它记录原目标命令 `lake env lean -o .lake/build/lib/lean/Shao/OQ3/RegularCovariance.olean Shao/OQ3/RegularCovariance.lean` exit0；真实build-03.log为0字节，SHA256=`e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`。原Audit命令也记录exit0。真实Audit.lean为2499字节，SHA256=`e5945c7af8a57968153d7f5cd8bdd6197fd6d2f064cf1bf5e6c4f670fb444721`；真实Audit.log为8460字节，SHA256=`0497d4c1f25f163b58ba262ed28606f6c7149ea5315ba5cf5cc200ed293e0193`，与回执相同。日志已完整读取，逐项TYPE检查如下（公开目标的全部前提/量词同时与源签名核对，表内仅精简记载）：

| 真实声明（省略公共 Shao.OQ3 前缀） | 实际 TYPE 核对 |
| --- | --- |
| parabolaCovariance | `Measure ℝ → Matrix (Fin 2) (Fin 2) ℝ`，真实矩阵定义。 |
| normalVariance | `Measure ℝ → ℝ`，真实Var(Y)定义。 |
| transverseVariance | `Measure ℝ → ℝ`，真实D/S定义。 |
| centered_parabola_integral_eq | 概率/AE界下，∀a,b的实际居中平方积分=实际矩阵二次型，全部索引/2ab系数一致。 |
| centered_parabola_integral_pos | 概率/AE界/四旧实际单点正门，∀非零(a,b)实际积分>0。 |
| parabolaCovariance_det_pos | 同一概率/界/旧实际正质量门下det>0。 |
| normalVariance_eq_covariance | 概率/AE界下S=64Δ00−16Δ01+Δ11。 |
| normalVariance_pos | 概率/AE界/四旧实际正门下S>0。 |
| transverseVariance_pos | 同样门下D/S>0。 |
| transverseVariance_le_variance_id | 同样门下D/S≤实际库Var(X)。 |
| atomic_id_variance | 非负w/全部真实HasSum下实际Varπ(X)=q−q²/16；没有全w>0隐含门。 |
| sourceEll_lt_one_div_thirty | `sourceEll < 1/30`，无额外假设。 |
| atomic_transverse_bounds | q范围、非负w、四旧权重正与source四HasSum下，0<t≤q−q²/16及1/30<q/(32t)。 |
| atomic_curvature_pos | 同样门下实际S/D−32sourceEll/q>0。 |
| exists_source_finite_and_limit_regular_family | 先∃同一p/q/eps，再∀合格r，极限π真概率/S/D/Λ1正且∀J同样有限π_J结论；所有括号、对象及量词与冻结源一致。 |
| 私有 ae_zero_at_positive_atom | 完整TYPE为 `∀μ f, (μ-AE x, f x=0) → ∀x, 0<μ.real{x} → f x=0`，没有概率门或结论额外前提；68–78完整证明已审。 |
| normalVariance.eq_1（生成） | `∀μ, normalVariance μ = ProbabilityTheory.variance normalValue μ`，仅定义展开。 |
| transverseVariance.eq_1（生成） | `∀μ, transverseVariance μ = (parabolaCovariance μ).det / normalVariance μ`，仅定义展开。 |

所以额外三个theorem恰为一个已逐行审查的私有AE原子引理与两个生成定义方程，均无隐藏数学假设；没有遗漏只审十二目标之外的声明。全部十八项及其传递依赖只含标准白名单。真实汇总为 `U7_FROZEN_THEOREMS 12`、`U7_ALL_THEOREMS 15`、`U7_ALL_DECLARATIONS 18`、`U7_AXIOM_GATE PASS`。

实际项目pin=`leanprover/lean4:v4.36.0-rc1`，manifest mathlib revision=`807d3836b165983210ee2ecf3cd28f239436949c`；实际版本探测为Lean `4.36.0-rc1`（commit `c9afcddf514a6772bd4d649f7cfc04eff0b9f15e`）、Lake `5.0.0-src+c9afcdd`。

STATUS: CORRECT

机械覆盖：LEAN_FULLY_CHECKED，仅指固定哈希U7三定义、十二目标、一个私有/两个生成theorem及其传递依赖的既有真实成功构建/公理审计。本轮完整独立源语义和数学证明审查在读取作者门之前形成，再独立核对真实机械绑定；不只是转述作者“等待审查”回执，也没有重复已成功目标。

JUSTIFICATION: 三定义与十二目标忠实匹配scope和R1，真实可积/L²排除方差总化，正原子AE提升、三点非退化、实际矩阵正二次型、det/S/τ²正性、32系数/精确1/30比较及共同finite/limit参数均有完整证明。十八声明实际TYPE、七份承重源、固定库定义、成功产物及传递公理门全部匹配，无关键缺口。此为完整独立CORRECT判定；没有commit/PR或根集成认证。全局唯一性、累积母函数微分、LLT、尾渐近、尖点、产品TV和对角未在此证明，根A/B/C/D保持OPEN。
