# U9b 完整独立声明、来源与证明审查

## 第一阶段：actual两定义五公开完整类型盲译

本节在读取本次实际证明、scope/R1、既有声明报告或作者receipt/Audit之前落盘。仅从实际SampleChangeOfMeasure.lean提取两定义和五个公开完整类型。实测源码SHA256=`d6259e330afca7b95e2e206c7021a44836e32cc0add596d14a6af8bdbda25134`，161行。前序声明审查上下文存在，本次仍从actual重新翻译；未读作者API/其他notes。

normalizedTailCoefficient是sqrt(2πn)·exp(n·saddleRate(ell,q,w))乘实际P(ell,w)^n在真实sourceTail(q,n)上的实质量；tiltedTailCoefficient是同一sqrt因子乘实际π_w^n下的sourceTail指标似然exp(−ell normalDeviation)积分。同一ell/q/w，两个真实测度方向不同。

1. 任意ell、非负HasSum w1及每个n，π_w^n上的exp(−ellΣY)真正Integrable，积分精确为单坐标inverseNormalizer的n次方。
2. 同样前提，真实P(ell,w)^n测度等于π_w^n按−ellΣY倾斜的测度，是完整测度等式。
3. 任意ell/q及上述真概率，对每个n和任意可测路径事件E，exp(n·saddleRate)P^n.real(E)=π^n下E指标乘exp(−ell normalDeviation)的积分；没有限定E=sourceTail。
4. 任意ell/q及每个n，两个真实尾系数精确相等。
5. ell≥0、q≤2、非负可和r、J、hM/hc及limit/finite四旧质量非负下，两个各自w对应的normalizedTailCoefficient差≤sqrt(2πn)·exp(11ell n)·n·C(ell)乘整个未来r尾；没有共同率或共同Z相等假设。

待核：真正单坐标/限制产品可积后才转实积分，Z正、率符号和分母消去、任意事件积分真可积、n=0、两law各自归一化、所有局部/生成TYPE及最后真实机械。当前尚无完整裁决；根A/B/C/D仍OPEN。

## 第二阶段：实际scope、statement与真实R1

盲译落盘后读取scope和既有声明报告；实测scope SHA256=`cac22df661588663b9fdcda118a1d71021df105867bc1545378f0c5dbf50a015`，statement SHA256=`8e77c997c83893418a23b6299d91fda8ac68b4426c0bb1e187236b93e054e011`。两actual定义体及五完整签名按空白规范化独立比较7/7相同，无量词、概率门或rate依赖变化。

真实R1 146–159与499–520已读，实测SHA256=`3473d34ff20bd0d334b9ef3ea3c3ee167fba4d5cc3a742849820ce54d639e662`。156行源率是ell q+log Z，501–507是π^n似然指标期望与原律归一化尾系数的(27)等式；509–520再接产品比较及尾量。本单元的前四项泛化为任意ell/q逆倾斜恒等式，源场景是其固定q/ell特例，不把这份代数恒等式升级为全局鞍点最优性。第五项接已审U11c直接误差，未声称(30)连续性。

## 第三阶段：全部161行证明与真实库API

本阶段尚未读取本单元作者receipt/build/Audit。完整实现没有显式private顶层辅助；所有证明局部hfun、hZ、hnorm、hdensity、hcoord、hprod、hZn、hprob、hrate、hpoint、hwl/hwj/hml/hmj均逐项审查。

| 实现行 | 独立逐步核对 |
| --- | --- |
| 19–26 | 两定义准确使用同一q/ell/w/n；normalized侧是真P_w产品的real事件质量及其自身rate，tilted侧是真π_w产品的同一指标似然积分。sqrt因子无遗漏或重复。 |
| 34–40 | 先由非负HasSum1建立π概率；hfun用实际有限和分配及exp_sum逐路径证明exp(−ellΣY)=Πexp(−ellY_i)。每坐标inverseExp_integrable真实成立后，Integrable.fintype_prod给联合真正Integrable。 |
| 41–43 | 在联合可积已建立的同一对象上，用实际积分有限产品公式与Fintype.card_fin得到Z^n。虽积分乘积库等式可有总化版本，本证明先给真Integrable，所以结论不靠不可积零分支。 |
| 51–60 | 建立π/P真实概率，hZ给Z>0，hnorm给联合可积和实际归一化积分。hdensity只用有限prod_div、prod_const及exp_sum，给H/Z^n=Π(h_i/Z)，不需限制事件积分为正。 |
| 61–68 | 实际Measure.pi_eq的方向是“产品律=候选测度”，要求候选在每个可测矩形上的质量等于各坐标质量乘积。源码将候选联合tilt在真实矩形上的质量先写为非负密度积分、替换hnorm实际Z^n，再以restrict_pi_pi转到每坐标限制测度的真实产品。 |
| 69–73 | hcoord把真实inverseExp_integrable限制到各s_i，再除以固定Z，得到每个限制坐标密度h/Z真正Integrable。限制测度仍有限/SigmaFinite，不需其概率质量1。hprod在这些真实门后给整个限制产品密度真正Integrable。 |
| 74–84 | 有hprod和各因子非负（由exp>0、Z>0）后，才用ofReal_integral_eq_lintegral_ofReal。随后实际有限产品积分给各限制积分乘积，integral_nonneg保证ENNReal.ofReal_prod可用。每因子恰为actual P.tilted_apply的质量，所以完成完整测度等式。没有把未证可积的lintegral转换成实数积分。 |
| 93–105 | 任意可测E下先立π/P概率、Z>0及hZn:Z^n>0、真实hnorm。通过完整产品测度等式及tilted_apply公式得到hprob，非负密度积分保证toReal(ofReal integral)=integral。真实可积门来自hnorm.1限制到E再div_const，不依赖概率real总化或tilted不可积零测度。 |
| 106–108 | actual saddleRate=ell*q+log Z，exp加法、exp_nat_mul与exp_log hZ给exp(nI)=exp(nellq)Z^n。正号和Z正性均真实，不把log总化值当log正数公式使用。 |
| 109–119 | hpoint逐路径使用hrate消去Z^n，再用exp_add合并指数，normalDeviation定义及ring给−ell(ΣY−nq)。field_simp所需真正非零前提Z^n≠0由此前hZn>0（亦由hZ>0的pow_pos）提供；不是仅有分母非负，也不假设n>0。 |
| 120–121 | 用hprob将exp(nI)移入E限制积分，再用可测E的integral_indicator将目标右侧同样写为限制积分；逐路径hpoint给AE相等。此处所有积分均真可积：H由hnorm.1，H/Z^n、其E限制与固定指数倍数皆可积；右侧由hpoint同样可积。 |
| 126–127 | 只展开两个定义，用同一sourceTail_measurable作E，乘相同sqrt因子得到精确系数恒等式，没有改变源事件。 |
| 140–151 | limit全部权重由hl/hr非负，finite由finiteMass_nonneg/hj/hr非负；hM/hc通过实际limit/finite约束HasSum的分量0给各自完整质量HasSum1。非奇异与约束在这里真实消费。 |
| 152–158 | 对limit/finite分别应用第四目标，二者各自rate/Z/P保持各自w；之后只是同一sqrt乘两个倾斜期望差，sqrt≥0让绝对值提出。用U11c最终似然尾界并结合实乘法得到确切所写误差，无两rate相等假设或TV偷换。 |

### 真实依赖语义及固定库

已审且本轮继续绑定的actual U4 InverseTilt定义Z=∫π exp(−ellY)、P=π.tilted(−ellY)，inverseExp_integrable和inverseNormalizer_pos对任意ell及非负HasSum1成立；actual U5a PositiveRate定义I=ell*q+log Z。U11c实际最终finite_limit_likelihood_tail_le包含同样hell/hq/hr/hs/hM/hc/hl/hj门并比较同一真实π产品，当前只在其已经完整独立CORRECT的版本上消费。其余实际有限质量/约束及sourceTail语义沿前置冻结源；全部15前置hash在最后阶段核实。

固定库Integral/Pi.lean（SHA256=`43c50a9d9a683b2050e145154410a7260c3dd84f3ec3010630cc6b90572afcd9`）33–71行实际有限产品可积门与79–122行积分公式、Measure/Tilted.lean（`355cce542b03dd9130d9511f80ae803cc11a12ba9e6a947e68402b124be2165f`）94–130行真实密度/实积分/概率门，在此前声明阶段已经只读逐项核过。本次为新证明方向与lintegral转换再只读服务器实际源确认：

| 固定库及SHA256 | 本次实读内容及消费 |
| --- | --- |
| Constructions/Pi.lean `bb89dee63d412cd1cc1f7f9fd7a81d64074139571960b2f0fcb66d8b763cd6ef` | 279–283行Measure.pi_eq明确在各坐标SigmaFinite下，以候选矩形质量=坐标质量乘积推出Measure.pi=候选；417–421行restrict_pi_pi给真实限制产品。当前π/P概率及限制有限性提供门，矩形证明方向准确。 |
| Integral/Bochner/Basic.lean `66837a733a5514a0fd824591ac10d43063c5a5cd94c9bdbbf80025686c16c670` | 737–742行ofReal_integral_eq_lintegral_ofReal明确要求Integrable f和AE非负；源码先给hprod及非负因子再调用，满足真实门。 |

这些均只读实际固定版本源，未运行Lean目标或更改cache。任何实际生成项将在TYPE阶段连同全部owned声明核对，最后再核真实内核成功记录；field_simp所需分母非零数学条件已由本证明中的hZn建立。

### 边界与非声明

n=0时Π密度=1、ΣY=0、Z^0=1；联合归一化积分为1，两个空产品都是唯一空路径Dirac，按0函数倾斜保持同一概率。矩形证明空坐标的hcoord真空、hprod为空产品常数1，可积与所有移项均合法。任意E的第三等式照常成立；真实sourceTail因energy>0门为空且sqrt因子0，第四/第五两端均0。没有遗漏0次方或错误消去零分母。

J=0时finite仅四旧点，其非负及真实质量1仍来自hj/hM/hc；尾为全部r。首四项任意ell/q仅是逆倾斜代数恒等式，不宣称任意q是均值、KL率正或全局Legendre极值。第五项同一固定q、ell、p及整条r适用于每个J/n，每个law有自身Z/I；不按n重选P或误将两law率等同。

在读取本单元实际generated TYPE及作者receipt/build/Audit之前，本阶段独立数学裁决：CORRECT。无(30)常数连续性、全局鞍点、LLT或根闭合升级，根A/B/C/D保持OPEN。

### 全部8个actual owned TYPE

上述数学结论落盘后仅从真实Audit.log提取DECL/TYPE，不先读取receipt、Audit源码或AXIOMS/PASS。实际8项逐个核对如下，统一省略Shao.OQ3前缀：

| # | 实际声明 | 实际TYPE核对 |
| --- | --- | --- |
| 1 | normalizedTailCoefficient_eq_tilted | ∀ell/q/w，hw≥0、HasSum w1→∀n，两个实际系数相等，任意ell/q门准确 |
| 2 | iid_event_change_of_measure | ∀ell/q/w、hw/hs、n及可测E，exp(nI_w)P_w^n.real(E)=π_w^n下E指标似然积分；方向及同一w正确 |
| 3 | normalizedTailCoefficient | ℝ→ℝ→(AtomicIndex→ℝ)→ℕ→ℝ，实际原律归一化系数定义 |
| 4 | normalizedTailCoefficient._proof_1 | `(1+1).AtLeastTwo`，sqrt系数内数值2所需类型类证明；唯一实际generated theorem，不是field_simp额外数学假设 |
| 5 | finite_limit_normalized_tail_error_le | hell/hq、hr/hs、hM/hc、hl/hj→∀n，两个各自w的实际normalized系数差≤sqrt(2πn)exp(11elln)n C T_J，与冻结签名一致 |
| 6 | iid_inverseNormalizer | ∀ell/w，hw/HasSum1→∀n，实际产品exp(−ellΣY)真Integrable且积分=Z_w^n，未弱化为仅总化积分等式 |
| 7 | tiltedTailCoefficient | ℝ→ℝ→(AtomicIndex→ℝ)→ℕ→ℝ，实际倾斜期望系数定义 |
| 8 | original_iid_eq_tilted | ∀ell/w，hw/HasSum1→∀n，真实P_w^n=真实π_w^n.tilted(−ellΣY)，完整测度等式 |

两定义、五public定理及一generated定理全部覆盖；没有模块private声明。8实际TYPE无关键缺口，下一阶段才核完整机械证据。

## 第四阶段：最后读取的真实机械证据

完成数学及TYPE判断后，才读取本地U9b-receipt.json/U9bAudit.lean与服务器真实run的完整receipt/build/Audit。共享server.py只读返回exit0、stderr为空，host key SHA256=`+IZMFu9Xx6FSAhvQhtvZ3MpV70v2d+XNWcequAbsp+c`。未重编、重跑Audit或下载raw logs。

实际worktree=`/root/rivermind-data/shao-lean-20261021/workspaces/lead-oq3`；branch=`feat/oq3-sample-tilt`，HEAD=`1a56e9cbfeaa12009030c3c4ad305608cb9d63b6`，git状态仅`?? Shao/OQ3/SampleChangeOfMeasure.lean`。真实源hash=`d6259e330afca7b95e2e206c7021a44836e32cc0add596d14a6af8bdbda25134`，与本次完整审查的本地161行冻结源一致。独立扫描无sorry/admit/axiom/unsafe/native_decide，无CR及尾空白。

真实run=`/root/rivermind-data/shao-lean-20261021/runs/oq3/u9b-20261021`；本地receipt/Audit与实际同名产物hash一致：

| 实际产物 | 字节数 | SHA256及事实 |
| --- | --- | --- |
| receipt.json | 4223 | `41841cf2df5d99ed85af1766815ec62f22b23791648b88aac069543928f4dae3`；记录build/Audit exit0 |
| build-02.log | 0 | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`；实读为空，无警告/错误文本 |
| Audit.lean | 1910 | `f1ad18e0bef46a41e920c8717a8294231f3ce1a03f2b23a80bea89227b3c67ec`；实际枚举源码已读 |
| Audit.log | 3564 | `2ab7c5accec805ea89e8c658ac76f7509eea0cdc50b2011caf502f608c5e5917`；全部DECL/TYPE/AXIOMS及末尾PASS已读 |

receipt绑定的既有成功命令为`lake env lean -o .lake/build/lib/lean/Shao/OQ3/SampleChangeOfMeasure.olean Shao/OQ3/SampleChangeOfMeasure.lean`及`lake env lean /root/rivermind-data/shao-lean-20261021/runs/oq3/u9b-20261021/Audit.lean`。本次核真实已有成功记录及其日志/冻结源绑定，没有虚称重新运行成功。

实读Audit要求五目标存在且为theorem，覆盖七公开源前缀及`_private.Shao.OQ3.SampleChangeOfMeasure`，拒绝项目axiom，对每个owned常量collectAxioms检查传递白名单。实际8声明/6定理/5冻结目标，与前表一致，AXIOM_GATE PASS。唯一数值生成定理仅含propext，其余七项仅含propext/Classical.choice/Quot.sound。没有未审模块私有项、额外公理或native证明入口。

实际服务器15份承重前置源逐份核hash，与receipt及已审冻结版本一致：

| 前置实际源 | SHA256 |
| --- | --- |
| U1 FiniteConstraints.lean | `800d9db8cb6749a31ecfe611409de92b10ea8bb2aef955bfd825ede7324f0ef0` |
| U2 SourceStarter.lean | `0e2a081619976f88149707c2ef9311dc909003e61d3d0f7c4e21e6c3dbbc5a6d` |
| U3a SummableAtoms.lean | `0ea4c64fe9ef9b45fbf44d24312771a1dbfbcc5de8448564e3e87bdf17c7178b` |
| U3b AtomicMeasure.lean | `59ddc48fb7b395f362939e58cbd9d7911685a6ed6e6574142e8a6d4ab3ee0c39` |
| U4 InverseTilt.lean | `c7e7d19e8b70481b663bec1fd12ea9301d73313faaf35997e85aa9ba99f21811` |
| U3c FiniteStageMeasure.lean | `1a32fb904e6ee9d2b0b48d92c4ebb3568452bb02500ce52a1a03eb01ae0256b1` |
| U6a AtomProjection.lean | `0d369052c7f87122765612efdeaca5d9ac71abca861e7785c86d1f9edcc74d22` |
| U6c ResonanceArithmetic.lean | `cd21a264d637bab30fed765bdc25ed09bb4ff56f6efb9c88ee09be4ca6e1648b` |
| U8 FiniteNormalSpan.lean | `0374da4860edf8af8bbbb9172e4e93bfe9b6c37ac57672b85a4f58392475b7de` |
| U9a SampleBoundary.lean | `7660e23b71ce28ab43a4ad1d8df1862cf8a507b6bb9b41255e961f0bee0b93e2` |
| U11b AtomicTailControl.lean | `ec528d9af8b475f1db8a78c93ab917d754365d280027a86be2823825b19c2f79` |
| U11c AtomicProductControl.lean | `6f886635f2201e04d1004a4f4b3b4058d406be3a283f716b70f1ce1cfaa5775f` |
| U5a PositiveRate.lean | `8e727078d3a4f1db2392384b84cc31235ff69efa13dd5e44b23eac818a788f7b` |
| shared FinitePath.lean | `898262898f9c088e2d10e6238e411b4397387b21b1b71a2b545c5edef936e1bb` |
| shared FiniteIID.lean | `d1b565489199d55af70a27c31a0f803a2b7433e78c9197a361b3c10c0598845b` |

真实lean-toolchain=`leanprover/lean4:v4.36.0-rc1`；实际Lean版本4.36.0-rc1、commit=`c9afcddf514a6772bd4d649f7cfc04eff0b9f15e`，Lake=`5.0.0-src+c9afcdd`；真实lake-manifest中mathlib rev=`807d3836b165983210ee2ecf3cd28f239436949c`。均为本次只读返回事实，未重跑旧成功门。

## 最终独立裁决

STATUS: CORRECT

JUSTIFICATION: 两实际定义、五公开类型与冻结scope/真实R1对应正确；全部161行证明、局部辅助、真实库API门及全部8实际owned TYPE无关键缺口。真实单坐标及限制产品可积先于积分转换，Z/Z^n严格正支持率和分母消去，事件任意可测且实际积分均真可积；n=0和两个原律各自I/Z处理准确。最后读取的真实服务器冻结源、15份依赖、pins、已有build/Audit成功记录及完整传递公理证据准确绑定本单元，支持本单元LEAN_FULLY_CHECKED。作者receipt的AWAITING_INDEPENDENT_PROOF_REVIEW仅为作者门时历史状态，完整独立裁决由本报告给出。

本单元完成源(27)对应的真实有限产品精确换测度及接U11c的直接尾误差，不声称TV等同、(30)连续性、全局鞍点唯一性、LLT或最终对角闭合。未重跑全项目构建或commit/PR/merge，未改实现/旧报告/公共文件。根A/B/C/D全部OPEN。
