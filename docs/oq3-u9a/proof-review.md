# U9a 最终独立声明、来源与证明审查

## 第一阶段：实际三定义与十二签名盲译

本节在本次读取最终证明、scope/R1、既有声明报告、receipt/Audit或作者notes前落盘。只读取实际 `SampleBoundary.lean` 的导入、三个定义和十二个公开签名。实测SHA256=`7660e23b71ce28ab43a4ad1d8df1862cf8a507b6bb9b41255e961f0bee0b93e2`，167行。前序声明审查上下文存在，本次从实际导出重新核对；未读u9a-api-notes、global-rate-frontier或其他作者笔记。

实际normalDeviation为ΣY(z_i)−nq，tangentDeviation为Σz_i−nq/4；sourceTail要求共享energy(z)>0及 `sqrt(q)/4·sqrt(n·energy(z))≤Σz_i`。它显式排除能量为0的路径。

十二目标独立翻译如下。

1. 任意q/n/z，normalDeviation=8Σz−energy−nq。
2. 任意q/n/z，样本恒等式 `(Σz)²−n(q/16)energy=(nq/16)normalDeviation+tangentDeviation²`。
3. 任意实q、自然数n，sourceTail是可测路径事件。
4. q>0、n>0时，尾事件等价于energy>0、Σz>0及第2项右侧≥0，保留严格正总和门。
5. 同样q/n门及normalDeviation=d时，尾事件等价于energy>0、Σz>0和 `−(nq/16)d≤tangentDeviation²`。
6. 任意q/n/J的逐坐标阶段支撑路径，存在整数k，使normalDeviation=meshJ·k−nq，包括空样本。
7. 每个完整fixedAtom的Y≥−9，不是|Y|≤9。
8. 任意w，atomicMeasure(w)下AE Y≥−9，不无条件承诺概率。
9. 任意ℓ/w，originalMeasure下AE Y≥−9，同样只断言支撑性质。
10. ℓ≥0、q≤2及路径各坐标Y≥−9下，对每个n有exp(−ℓnormalDeviation)≤exp(11ℓn)。
11. 同一概率μ下AE Y≥−9，则其真实n重Measure.pi乘积上AE有同一指数界。
12. q<103/100、非负真实HasSum w1下，对同一atomicMeasure(w)的n重乘积AE有sourceEll版本指数界。q/w均为n之外的固定输入。

本节尚未读证明。后续须核真实样本平方和、平方化符号、n=0/energy=0、整数聚合、实际Y下界、乘负ℓ的不等号、同一μ的真实乘积AE逐坐标提升，以及所有私有/生成声明；不把这些输入升级为换测度/TV/LLT或对角完成。

## 第二阶段：冻结、真实 R1 与共用实际定义

盲译落盘后才读取scope解释及真实R1 400–408、495–510。实测scope SHA256=`cd6883e78387d9fbeb50d42bddcab9fc0a81955458d7228c53f98eb23e4c35c9`，声明报告SHA256=`e463795881bc4a5f24df51e7d47000cfc76acc5540760358cbef5c4cfd9646f3`，真实R1 SHA256=`3473d34ff20bd0d334b9ef3ea3c3ee167fba4d5cc3a742849820ce54d639e662`。独立空白规范化比较三个实际定义体和十二完整签名，15/15相同，无前提或量词改变。

在作者机械证据之前，只读核对指定服务器真实共享源：FinitePath SHA256=`898262898f9c088e2d10e6238e411b4397387b21b1b71a2b545c5edef936e1bb`，18/31行实际Path(n)=Fin n→ℝ、energy(z)=Σz_i²，50–61行给能量非负及零能量当且仅当全坐标0；FiniteIID SHA256=`d1b565489199d55af70a27c31a0f803a2b7433e78c9197a361b3c10c0598845b`，32–43行把可测、独立、同分布实际样本路径的推前律等同真正Measure.pi。没有以方差或对角分布替换这些对象。

实际固定Mathlib `MeasureTheory/Constructions/Pi.lean` SHA256=`bb89dee63d412cd1cc1f7f9fd7a81d64074139571960b2f0fcb66d8b763cd6ef`，manifest revision=`807d3836b165983210ee2ecf3cd28f239436949c`。425–426行实际 `Measure.tendsto_eval_ae_ae` 把乘积AE沿坐标eval推到相应坐标μ-AE，其证明直接消费360–369行坐标零集原像在乘积中仍为零集的定理；这是本源151行实际使用的接口。354–358行还明确空指标乘积总质量为1。未运行Lean或读取本单元日志来代替这一步语义检查。

| R1锚点 | 实际源码覆盖与范围 |
| --- | --- |
| 400–402 | 第六目标给实际d=meshJ·整数−nq，与源θ分数部分约化后的同一平移网格一致；没有先输出相位返回。 |
| 404–408 | 样本S=ΣX、V²=energy，d=ΣY−nq、R=ΣX−nq/4，恒等式(18)系数nq/16及正尾S>0均保留。 |
| 499–503 | 实际同一μ的n重积上指数权重界，不用有限样本量后重新选律替代固定输入。 |
| 504–508 | 精确乘积换测度与C_n等式不在十二目标中，未因本单元权重界而升级。 |
| 509–510 | 实际Y≥−9与q≤2给exp(11ℓn)；产品TV是后续目标，不是本次完成项。 |

## 第三阶段：167 行全证明与所有局部辅助

完整读取固定哈希源1–167行及上述实际共享/库定义后，在本单元receipt/Audit/日志之前形成独立数学判断：CORRECT，无关键缺口。未读u9a-api-notes、global-rate-frontier或其他作者思路。

| 实现行 | 精确逐步检查 |
| --- | --- |
| 19–27 | d、R均是实际有限样本的居中和；尾事件使用真正样本energy并显式要求>0。sqrt阈值是sqrt(q)/4乘sqrt(n·energy)，没有误换成总体方差或缺少n。 |
| 31–39 | 有限和分配与Y=8x−x²给d=8S−E−nq，之后仅精确ring得到 `S²−n(q/16)E=(nq/16)d+R²`。对任意q/n成立，原子/概率/矩条件均未偷用。 |
| 43–51 | energy和S是有限坐标多项式，实际连续；全局连续sqrt组合给任意实q的阈值连续。两个实际可测不等式集合取交恰为sourceTail，未要求q正才能证明可测。 |
| 57–65 | hn精确转为正实n，energy_nonneg给E≥0；T≥0由实际平方根非负。计算T²时分别满足q≥0、nE≥0，得到T²=n(q/16)E，分母16正确。 |
| 68–75 | 前向消费E>0、q>0、n>0给T严格正，T≤S遂得S>0；在T≥0、S≥0门下sq_le_sq₀合法平方，结合真实恒等式得曲边界表达式≥0。没有只留平方而丢正尾符号。 |
| 76–79 | 逆向明确保留E>0和S>0；从曲表达式≥0、T²公式和恒等式得T²≤S²，再在T≥0、S≥0下用同一平方比较恢复T≤S。不会接纳负S支。 |
| 85–86 | 在完整尾事件等价式中代入同一hd，再把非负和式移项；两向都保留E>0及S>0，d可为任意实数，无额外层符号假设。 |
| 93–102 | 对每个坐标由hz取其真实阶段索引，U8给该坐标精确整数k_i；choose只选这些逐坐标证人，整数有限和k=Σk_i经Int.cast_sum与mul_sum给实际平移层。空Fin0上同样有空整数和0，未要求n>0。 |
| 106–115 | 全索引Sum两侧穷尽。旧侧实际Y向量[−9,7,6,12]逐分支核算，新侧Y=6+mesh(j+1)，mesh正给下界。不是从|X|界或错误|Y|≤9推断。 |
| 119–126 | π下用actual atomicMeasure_ae_range逐点继承真实Y下界；P下用其对同一π的倾斜绝对连续性继承。任意w/ℓ的目标仅为AE支撑性质，未误称总化零测度分支也是真概率。 |
| 131–139 | 逐坐标下界有限相加给ΣY≥−9n，q≤2乘非负实n给nq≤2n，故d≥−11n。这里q只需上界，不暗加q>0。 |
| 140–142 | 实际源码先以非负ℓ乘d下界，得−11ℓn≤ℓd；再转换符号得−ℓd≤11ℓn并用exp单调。等价于乘−ℓ时正确反向，没有把非正乘子当正。ell=0和n=0均为1≤1，ell<0不在该签名域。 |
| 149–155 | 对每个i以实际Measure.tendsto_eval_ae_ae把同一μ-AE界拉回同一真实n重积；ae_all_iff在有限Fin n上组合全部坐标AE后，才逐路径应用点态权重界。不是对所有路径无条件赋予支撑；mu未随坐标或n改换。 |
| 162–164 | hw≥0、HasSum w1明确给π_w真概率；sourceEll_pos.le、q<1.03<2和π实际Y下界准确满足通用乘积界。最后期望测度为倾斜律π的乘积，符合源C_n，不是把π/P交换。 |

全部局部辅助he、hs、ht、T、hnR、hE、hT、hTsq、hid、hTpos、hS、hsq、hi、k/hk、hmesh、hsum、hnq、hd、hm、hcoords、hall均覆盖。源无顶层私有数学引理；源外所有生成声明将在最后机械阶段实际TYPE逐项核对。

### 关键边界与非声明

n=0的唯一空路径有S=E=d=R=0，两条原始代数恒等式仍真、stage整数证人可取0；sourceTail因E>0门为空。energy=0也强迫所有坐标0，两个尾事件判据都保留严格能量门，所以没有把零能量路径接纳。几何平方化只在q>0/n>0声明，不对q=0零阈值场景错误要求S>0。

Y≥−9是单边真实支撑结论：baseAtom3（点x=2）的Y=12反驳|Y|≤9；x=−2满足粗绝对值界却Y=−20，说明仅有1≤|X|≤4+√10也不足以推出当前下界。源码按实际法向向量与新增公式处理，消除了这一源翻译风险。

乘积AE界包括空样本；概率μ给真正同一n重积，有限坐标拉回/AE全称组合没有引入一个随机变量重复n次的对角律。q/w/μ在n之外给定，可一次选定此前源族中的同一q与实际π/P后对全部n应用通用结果；源码没有∃q_n/μ_n或在n确定后重选P。P的AE下界和π的似然期望对象分开处理。

当前只完成样本几何、可测性、精确有限网格与指数支配；没有乘积换测度、产品TV、LLT/层支配求和、尾渐近、全局唯一率或对角闭合结论。根A/B/C/D保持OPEN。

本阶段独立数学裁决：CORRECT。此时尚未读取本单元作者receipt/Audit或机械产物。

## 第四阶段：最后读取的真实机械证据

上述数学判断落盘后，才读取本地U9a-receipt.json/U9aAudit.lean，并通过共享server.py只读核查实际服务器产物；未重新构建或执行Audit，未下载日志。本地与真实run同名文件哈希一致。真实服务器命令exit=0、stderr为空，host key SHA256=`+IZMFu9Xx6FSAhvQhtvZ3MpV70v2d+XNWcequAbsp+c`。

实际worktree为`/root/rivermind-data/shao-lean-20261021/workspaces/lead-oq3`，分支`feat/oq3-sample-boundary`，HEAD=`c812f19fc5068e3e24b2ee06637b56872b94ffab`；git状态仅`?? Shao/OQ3/SampleBoundary.lean`。真实源SHA256=`7660e23b71ce28ab43a4ad1d8df1862cf8a507b6bb9b41255e961f0bee0b93e2`，与本次完整审查的冻结本地源相同。独立源码扫描无sorry/admit/axiom/unsafe/native_decide、无CR及尾空白。

实际run为`/root/rivermind-data/shao-lean-20261021/runs/oq3/u9a-20261021`：

| 实际产物 | 字节数 | SHA256与事实 |
| --- | --- | --- |
| receipt.json | 3779 | `a8911132090616680b713f280b3813df11f9921cce467d5381d1fc8d8571b5d7`；记录build与audit均exit0 |
| build-02.log | 0 | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`；实际为空，无警告或错误文本 |
| Audit.lean | 2524 | `56036063873fbe31fe9961671338aa3a78881b68240932d5ba91aae195a51a29`；实读枚举逻辑 |
| Audit.log | 4660 | `3144601ede4e38011bb1f3910b7b54b95c6ceb3d5537e599f9a6b0b842fd9966`；实读全部DECL/TYPE/AXIOMS及末尾PASS |

receipt记录的成功命令分别是`lake env lean -o .lake/build/lib/lean/Shao/OQ3/SampleBoundary.olean Shao/OQ3/SampleBoundary.lean`与`lake env lean /root/rivermind-data/shao-lean-20261021/runs/oq3/u9a-20261021/Audit.lean`。本次从实际文件验证成功记录与日志绑定，未虚称重新运行成功。

实读Audit覆盖15个公开源声明前缀与`_private.Shao.OQ3.SampleBoundary`，检查12个冻结目标确为theorem，拒绝任何新项目axiom，对每个声明调用Lean.collectAxioms进行传递白名单检查。实际日志18声明/15定理/12冻结目标，均PASS。以下逐项列出实际TYPE核对结果；前三个额外声明并非由计数推测。

| 全部18项实际声明（省略统一Shao.OQ3前缀） | 实际TYPE核对 |
| --- | --- |
| normalDeviation | ℝ→{n:ℕ}→Path n→ℝ，与已盲译定义相同 |
| tangentDeviation | ℝ→{n:ℕ}→Path n→ℝ，与已盲译定义相同 |
| sourceTail | ℝ→(n:ℕ)→Set(Path n)，真实尾事件定义 |
| normalDeviation_eq_sum_energy | ∀q/n/z，d=8Σz−E−nq，无隐藏前提 |
| curved_sample_identity | ∀q/n/z，S²−n(q/16)E=(nq/16)d+R² |
| sourceTail_measurable | ∀q/n，真实sourceTail可测 |
| sourceTail_iff_curved | ∀q>0/n>0/z，尾事件↔E>0∧S>0∧0≤(nq/16)d+R² |
| sourceTail_on_normal_layer | 同q/n门，∀z/d，normalDeviation=d→尾事件↔E>0∧S>0∧−(nq/16)d≤R² |
| stage_sample_normal_layer | ∀q/n/J/z，真实逐坐标stageAtom范围门→∃k:ℤ，d=meshJ·k−nq |
| fixedAtom_normalValue_lower | ∀i:AtomicIndex，−9≤Y(fixedAtom i) |
| atomicMeasure_ae_normalValue_lower | ∀w，真实π_w-AE有−9≤Y |
| originalMeasure_ae_normalValue_lower | ∀ell/w，真实P-AE有−9≤Y |
| normal_likelihood_weight_bound | ell≥0、q≤2，∀n/z，全部坐标真实Y下界→exp(−ell d)≤exp(11ell n) |
| iid_normal_likelihood_ae_bound | ∀概率μ/ell/q，ell≥0、q≤2、μ-AE Y下界→∀n，真实Measure.pi(fun _=>μ)-AE指数界 |
| source_atomic_iid_likelihood_ae_bound | ∀q<103/100/w，∀i w_i≥0、HasSum w1→∀n，真实π_w重积-AE sourceEll指数界 |
| normalDeviation.eq_1 | ∀q/{n}/z，normalDeviation q z=ΣY(z_i)−nq；实际定义展开等式，不含新增数学前提 |
| normalDeviation_eq_sum_energy._simp_1_2 | 任意NonUnitalNonAssocSemiring R上的有限和分配：Σ_{i∈s}a·f_i=a·Σ_{i∈s}f_i；真实通用乘法分配辅助 |
| tangentDeviation._proof_1 | `(3+1).AtLeastTwo`；实数分母4所需数值类型类证明，不是未审数学引理 |

全部项的传递公理仅含propext/Classical.choice/Quot.sound的子集：有限和生成辅助只含propext/Quot.sound，AtLeastTwo生成辅助只含propext，其余项含上述三项。无额外私有声明、项目公理或隐藏强假设。

实际服务器11份承重导入源码逐份核SHA256如下，与已接受冻结版本及receipt一致；此处未重复旧目标构建。

| 实际源 | SHA256 |
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
| 共享FinitePath.lean | `898262898f9c088e2d10e6238e411b4397387b21b1b71a2b545c5edef936e1bb` |
| 共享FiniteIID.lean | `d1b565489199d55af70a27c31a0f803a2b7433e78c9197a361b3c10c0598845b` |

真实lean-toolchain=`leanprover/lean4:v4.36.0-rc1`；实际Lean版本4.36.0-rc1、commit=`c9afcddf514a6772bd4d649f7cfc04eff0b9f15e`，Lake=`5.0.0-src+c9afcdd`；实际lake-manifest的mathlib rev=`807d3836b165983210ee2ecf3cd28f239436949c`。这些均为本次真实只读返回值。无U7/U5a依赖。

## 最终独立裁决

STATUS: CORRECT

JUSTIFICATION: 冻结实际三定义/十二签名与scope及真实R1对应正确，完整167行证明及局部辅助、真实共享对象、乘积AE固定库语义和全部18个导出/生成声明均无关键缺口。平方化符号、零边界、真实Y≥−9、负指数方向与固定同一概率律n重积均已独立核实。最后读取的实际服务器源/依赖/pins/成功build记录/完整TYPE与传递公理证据准确绑定当前冻结单元，支持本单元LEAN_FULLY_CHECKED；这是独立声明、来源、数学与证明审查后的结论，不把作者门标签当作完整审查。作者receipt的AWAITING_INDEPENDENT_PROOF_REVIEW是此前作者门时状态，由本报告完成独立判断。

仅本单元通过，不宣称新运行全项目构建，不实施commit/PR/merge。乘积换测度、产品TV、LLT、尾渐近、全局鞍点唯一性及对角构造仍未由本单元证明。根A/B/C/D均OPEN。
