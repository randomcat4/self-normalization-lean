# U16f 独立声明、来源与静态接口审查

STATUS: CORRECT

唯一审查lease1，仅拥有本新报告及服务器statement-review.md；不改scope、源码、旧票、shared或cache，不spawn、Lean/probe/build或下载原始完整日志。并非独占代码库，保留他人编辑。下述第一阶段在只读取冻结Lean fence的两个完整公开类型（零新定义）后独立落盘；当时尚未读scope正文、作者路线或本次实际库。其初始落盘文件为2589字节，SHA256 fc5cce9239bb833447d01d337827ef5e97408e93d4a346403a9b44e8128ea1d6。后续阶段依次追加完成。

## 第一阶段：两个完整类型盲译

输入forty-second-unit-scope.md，SHA256 `fcbcce37d21640dec787be5b146d8b334520273d37e7b43f6d5d85cd1baad701`。

`jointCharacteristic_norm_le_of_measure_lower`：输入任意真实实数概率测度mu和nu、实数m≥0，假设实际ENNReal系数ofReal(m)缩放mu后作为测度≤nu。输出一方面m≤1；另一方面对全部实频率xi/eta，actual jointCharacteristic(nu,xi,eta)的复范数≤1−m(1−actual jointCharacteristic(mu,xi,eta)的复范数)。同一个m先于全部频率，未假设非格点、有界支持或m>0。m=0和m=1均含在完整类型内，不能除m或1−m。jointCharacteristic的actual积分与相位定义在盲译后核对，不能仅由名字假定其为概率特征函数。

`exists_compact_tilted_characteristic_bound`：给真实概率mu、实M≥0、同一mu-AE |x|≤M、实二元参数集K及IsCompact K、固定基准u0/v0；之后存在同一实m>0且m≤1，在全部p∈K和全部实频率xi/eta之前选择，使mu.tilted[p.1*x+p.2*x²]的actual jointCharacteristic范数≤1−m(1−固定基准mu.tilted[u0*x+v0*x²]的actual jointCharacteristic范数)。K可为空、M可0；无Nonempty K、m依赖p/频率或有限层n量词。两侧actualtilted必须真实由exp可积给概率，不能利用不可积时tilted退化零测度。

独立初判：第一目标可望从真实残差测度r=nu−ofRealm•mu和支配后的加法分解推得；所有相位在mu/nu/r上必须真可积，r的真实总质量为1−m，必须先保持有限ENNReal再转real。m≤1应由univ测度支配推出，m1时r零而不能归一化除1−m。第二目标若有同一正measure minorant m0，可先取min(m0,1)>0确保即使K空也有m≤1，再对每个真实概率tilt应用第一目标。actual measure subtraction/Bochner/API、真实tilt可积和系数转换仍待后查。

此为全频域标准范数转移，不是紧倾斜族C/sqrt n质量界、Chernoff或根闭合。零频率、m0/m1、空K和M0均需完整核验。本段先保存，之后scope/R1/actual已有接口与固定库；根A/B/C/D、紧族mass与概率Chernoff保持OPEN。

## 第二阶段：实际定义、来源与完整量词核对

盲译持久化后才读冻结scope正文及真实R1。输入本地scope与服务器run/scope.md均实际只读核得SHA256 `fcbcce37d21640dec787be5b146d8b334520273d37e7b43f6d5d85cd1baad701`。不存在本单元实现，未读未来作者实现或笔记。本次不是proof/Audit/receipt门。

真实R1是只读 `C:/game/shao/current/oq3/proofs/r1/report.md`，SHA256 `3473d34ff20bd0d334b9ef3ea3c3ee167fba4d5cc3a742849820ce54d639e662`，实际核348–366行，核心356–360行：倾斜Y律保留格距；任意紧倾斜参数集上的Fourier积分具有共同C/sqrt(n)上界，中央弧为Gaussian、补弧有共同模量缺口。本单元两个类型只给真实测度小化到实际联合特征模的统一转移，是上述解析步骤的一项标准充分前置，不是已经形式化该整段积分结论，更不是式(16)概率Chernoff界。

actual `Shao/OQ3/JointNonlattice.lean`20–27行的定义为 `jointPhase xi eta x = Complex.exp (((xi*x+eta*x^2:ℝ):ℂ)*Complex.I)`，`jointCharacteristic mu xi eta = ∫ x, jointPhase xi eta x ∂mu`，积分测度明确是mu；其全局相位范数恰为1，实际复指数正号与冻结目标一致。它不等于仅由名字假定的抽象特征函数，也不是root所有的其他quadraticChar定义。本单元不需要证明或复制二样本cosine恒等式。

第一类型的两个概率实例先于m与频率；hm允许0，不暗含严格正。m≤1是输出，不是隐含输入。hlower为实际Measure偏序，不能以积分下界、AE密度句子或形式RN替代。全部实xi/eta在同一m之后，没有小频率窗口、矩条件、有界支持或原子性条件。第二类型M/hb/K/hK/u0/v0之后才存在m，之后是所有p∈K和所有xi/eta；不存在逐p或逐频率选m。基准点不要求属于K。两侧tilted恰是同一原始mu的实际二次倾斜，而不是另选参考概率族。

## 第三阶段：独立数学审查

目标1：设a=ofReal(m)、lambda=a•mu、rho=nu−lambda。首先在univ应用hlower，两个真实概率的总质量都为1，故a≤1；实际 `ENNReal.ofReal_le_one` 给m≤1。a是有限ENNReal，不是∞；mu有限，因此lambda真有限。可用实际 `Measure.smul_finite mu ENNReal.ofReal_ne_top`，也可由lambda≤nu用有限支配，不能无依据让任意ENNReal缩放自动成为有限。

Measure.Sub是非负测度格上的减法，不是无条件逐集合带符号相减。lambda≤nu且lambda有限正好满足实际 `Measure.sub_add_cancel_of_le`，因此rho+lambda=nu。`Measure.isFiniteMeasure_sub`在nu有限时给rho真有限；也可用rho≤nu独立推出。对measurable univ用 `sub_apply` 可得rho(univ)=1−a。因为a≤1且1≠∞，实际 `ENNReal.toReal_sub_of_le` 和hm给rho.real(univ)=1−m。所有toReal转换都在有限门之后，没有top.toReal被当成真实质量。

另一个同样合法且不依赖减法实转换的校验：先由rho+lambda=nu，再对两个有限测度应用 `measureReal_add_apply`，得rho.real(univ)+lambda.real(univ)=1；`measureReal_ennreal_smul_apply`和 `toReal_ofReal hm` 给lambda.real(univ)=m。于是直接得到rho.real(univ)=1−m。这与前一路径完全相同，是独立的质量等式检查。

固定任意xi/eta。actual jointPhase为连续复值函数（实二次多项式、实到复嵌入、乘I、exp的复合），所以对mu、nu、lambda、rho均AEStronglyMeasurable；其全局norm=1，加上各测度有限，实际 `Integrable.of_bound` 先给四处真实Integrable。已有 `integrable_jointPhase` 公开类型只接概率测度；不得把rho误装为概率来调用它。对rho/lambda直接使用有限测度版同一标准可积论证即可，无需任何额外矩或支持条件。

在rho/lambda真可积后，`integral_add_measure` 和残差加法等式给χν=χrho+∫phase d(lambda)。`integral_smul_measure`给第二项a.toReal•χmu=m•χmu。hm使复实标量的范数是m*normχmu；不能在hm之前漏掉abs(m)。对rho，`norm_integral_le_of_norm_le_const`的常数1界给normχrho≤rho.real(univ)=1−m。故三角不等式得到normχν≤(1−m)+m*normχmu=1−m*(1−normχmu)。每次拆积分都具有真实可积门，未凭总化积分的默认0获得结论。

边界核对：m=0时实际lambda=0，结论为概率特征norm≤1；m=1时rho总质量0，残差为零测度，整个论证不除1−m，不归一化残差；xi=eta=0时两相位恒1，两边恰为1。任意退化概率、Dirac law与任意未有界的概率也允许，因全局单位相位的可积与概率总质量已经足够。

目标2：实际已接受 `exists_compact_quadratic_tilted_domination` 在mu概率、M≥0、同mu-AE有界和IsCompact K下，给同一实m0>0，在全部p∈K之前固定，并给 `ofReal(m0)•baselineTilt≤pTilt`。其第二个产品cosine积分结论不需要消费，本单元也不把m²产品界误当m线性特征界。其证明用连续参数差绝对值和的紧有界性，取max(C,0)，没有提取K的元素，空K有效。

公开m0接口没有m0≤1。独立取m=min(m0,1)，两个输入皆正故m>0，m≤1和m≤m0无须p存在。ofReal的单调性与非负ENNReal测度标量单调性，在每个集合上由非负乘法给 `ofReal(m)•baselineTilt≤ofReal(m0)•baselineTilt≤pTilt`。这一步没有从空K错误推出m0≤1，也没有要求基准(u0,v0)∈K。

实际 `quadratic_exp_integrable_of_ae_abs_le` 对任意实u/v给exp(u*x+v*x²)在同一个mu上真Integrable，其AE上界是exp(|u|M+|v|M²)。因此基准与每个p的指数均真可积；mu真实概率给NeZero，实际 `isProbabilityMeasure_tilted` 先给两端tilt真实概率。随后才对这些真实概率与同一m应用目标1。不能先infer不可积tilt概率，不能使用 `tilted_of_not_integrable` 的零测度分支掩盖缺门。

共同参数与边界：m只依赖已给mu/M/hb/K/u0/v0与已选m0，不依赖p、xi、eta。K空时min选择仍给正m≤1，其后全称命题为空，未加入Nonempty。M=0时hb是mu-AE x=0，所有二次指数在支持上为1，真实可积与概率仍成立；u0/v0或p任意实符号不影响AE绝对值控制。L=0、singleton K、频率0、基准不在K均无除零或遗漏分支。两目标不含n/J，不能凭此产生这些参数上的共同质量常数。

## 第四阶段：固定库实际接口与作用域核对

以下均只读指定服务器实际固定源码；没有Lean/#check/APIprobe或编译。实际API是否足以支持声明，与尚未存在的未来实现是否已通过内核明确分开。

`Mathlib.MeasureTheory.Measure.Sub`实际public import有限测度模块。`Measure.sub_apply`72–73行要求被减小测度有限、集合可测、实际下界；`sub_add_cancel_of_le`100–102行要求小测度有限及下界；`sub_le`48–49行给残差≤大测度；`isFiniteMeasure_sub`145–146行从大测度有限给残差有限。已核真实定理类型，未依赖文件说明注释中符号顺序错误的自然语言示例。

`Mathlib/MeasureTheory/Measure/Typeclasses/Finite.lean`307–310行实际 `Measure.smul_finite (mu) [IsFiniteMeasure mu] (hc:c≠∞)` 给c•mu有限；115–116行 `isFiniteMeasure_of_le` 是另一途径。`Mathlib/MeasureTheory/Integral/IntegrableOn.lean`171–172行实际 `Integrable.of_bound [IsFiniteMeasure mu] (hf:AEStronglyMeasurable f mu) (C:ℝ) (hfC:∀ᵐx,‖f x‖≤C)` 正好支持残差与缩放测度的真可积，不要求这些测度概率。

`Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`1002–1006行 `norm_integral_le_of_norm_le_const` 有有限测度门，右侧C*mu.real(univ)；1010–1015行 `integral_add_measure` 明确消费两项Integrable；1047–1048行 `integral_smul_measure` 的系数是ENNReal.toReal。后者作为总化等式对更广系数也成立，不意味着本题可省finite和真可积。所有复实标量范数步骤均在hm≥0后。

`Mathlib/MeasureTheory/Measure/Real.lean`71–73行 `measureReal_ennreal_smul_apply` 是真实缩放质量实公式；435–438行 `measureReal_add_apply` 要求两个集合质量均≠∞，本题由已建有限实例提供。`Mathlib/Basic/ENNReal/Basic.lean`253–254行 `toReal_ofReal` 的假设是m≥0；`Mathlib/Basic/ENNReal/Real.lean`41–44行 `toReal_add` 要求两个数都非top，229–230行 `ofReal_le_one` 正好从a≤1推m≤1；`Mathlib/Basic/ENNReal/Operations.lean`440–441行实际名为 `toReal_sub_of_le (hba:b≤a) (ha:a≠∞)`，不是scope路线文字的简写 `toReal_sub`。这是透明记录的实现API名称选择，不改变冻结完整类型，且所需b≤a/a≠∞已由univ比较与真实概率提供，不构成声明阻塞。

`Mathlib/MeasureTheory/Measure/Tilted.lean`42–43行actual tilted定义为mu.withDensity(ofReal(exp(f)/∫exp(f)))。46–48行不可积时tilted=0；126–136行 `isProbabilityMeasure_tilted [NeZero mu] hf` 真实消费指数Integrable，先由exp正性得正normalizer，再构造概率。`IsProbabilityMeasure.neZero` 在Probability.lean87–88行。不存在仅因定义叫tilted便能无条件infer概率的假设。

冻结三个imports为 `Shao.OQ3.FiniteFarArc`、`Shao.OQ3.CompactTiltDomination`、`Mathlib.MeasureTheory.Measure.Sub`。实际FiniteFarArc直接import JointNonlattice与FiniteNormalSpan；CompactTiltDomination→ProductMeasureDomination→TiltedMeasureDomination，Product还显式import Bochner.Basic；相关公共库import链可见Measure、tilted、Bochner积分、有限性/real质量、复指数与范数的实际接口。scope约定的namespace Shao.OQ3/open MeasureTheory/noncomputable section足以给两个类型所用名字；ENNReal.ofReal用完整限定名，无缺失额外NNReal记号作用域；没有隐式volume/default MeasureSpace使用或需要另加Lebesgue实例的目标。

服务器现有三个直接olean真实存在：FiniteFarArc 503008字节、CompactTiltDomination 129088字节、Measure.Sub 32216字节。静态import依赖解析未见缺失源码或所需API环境阻塞。没有运行Lean，因此这不是未来完整实现的elaboration或axiom audit成功声明。

固定库证据SHA：Measure.Sub `7255179e0ec6689998e84bb02b660d7499d67aeb71ee758a80914fc3142b5172`；Bochner.Basic `66837a733a5514a0fd824591ac10d43063c5a5cd94c9bdbbf80025686c16c670`；IntegrableOn `d1108ec5e836af0af6bc62c8ad5dd94a371dbc8df3e51698049d51221b3663c2`；Measure.Real `1b9d1490fa5acbffc570eac67f465d3d6ab0520aa3e54464f7520d60d6619b8d`；Typeclasses.Finite `a8ef0ba0a9b953a5aae9fb16188cd7ad93e0e8d5767c564d02e9f2e8c57eedf2`；规范Basic.ENNReal.Basic `f7fe64f0d1865209e4d2be2fd98e3bc5edf9af508dd665f0311e6396f8d513a2`；规范Basic.ENNReal.Real `da5573e6bb7b196bd109724302c3db8eda3a3efab72c8db958ce2ddbf643cecf`；规范Basic.ENNReal.Operations `9c5ae45fe78f42b7b3c6336c49cd4f837ebf083f64677b4cddd91f609bb3bf7e`；Tilted `355cce542b03dd9130d9511f80ae803cc11a12ba9e6a947e68402b124be2165f`。

## 第五阶段：真实项目前置与版本绑定

本次从实际import图只读枚举14项Shao前置，不把root公共quadraticChar或未来实现算入闭包。实际哈希如下：

|实际模块|SHA256|
|---|---|
|AtomProjection|0d369052c7f87122765612efdeaca5d9ac71abca861e7785c86d1f9edcc74d22|
|AtomicMeasure|59ddc48fb7b395f362939e58cbd9d7911685a6ed6e6574142e8a6d4ab3ee0c39|
|CompactTiltDomination|6f31ac2e3b2b9d9b2ef957ebe52cfe3664a86694bb396b09c1006b890cbd0623|
|FiniteConstraints|800d9db8cb6749a31ecfe611409de92b10ea8bb2aef955bfd825ede7324f0ef0|
|FiniteFarArc|3a0b05d0789e53320009a44499c9c40d0fb3d892427085052c65c04456b6cf71|
|FiniteNormalSpan|0374da4860edf8af8bbbb9172e4e93bfe9b6c37ac57672b85a4f58392475b7de|
|FiniteStageMeasure|1a32fb904e6ee9d2b0b48d92c4ebb3568452bb02500ce52a1a03eb01ae0256b1|
|InverseTilt|c7e7d19e8b70481b663bec1fd12ea9301d73313faaf35997e85aa9ba99f21811|
|JointNonlattice|51ce939232610353215fc3b7377e19b894451a9a108125e1828bf2fe8ec81559|
|ProductMeasureDomination|9f05af79e47b9f778cbce7a0d19c0addea6d457eab5f088a69bf372f660c5a3f|
|ResonanceArithmetic|cd21a264d637bab30fed765bdc25ed09bb4ff56f6efb9c88ee09be4ca6e1648b|
|SourceStarter|0e2a081619976f88149707c2ef9311dc909003e61d3d0f7c4e21e6c3dbbc5a6d|
|SummableAtoms|0ea4c64fe9ef9b45fbf44d24312771a1dbfbcc5de8448564e3e87bdf17c7178b|
|TiltedMeasureDomination|5445a68da1ac8302f174bfe2144eb8271a0af740fd6b91a87355abb41fed739b|

实际worktree为 `/root/rivermind-data/shao-lean-20261021/workspaces/lead-oq3`；固定toolchain文本 `leanprover/lean4:v4.36.0-rc1`，lean-toolchain SHA `d581a24b57a4ae9e0b2132ca8ac7cc3ac336a9fc2751fe6b29414e2d434d54c4`；lake-manifest SHA `40e8e3385f2b0c8ae56fa9de6947301472379cb62eeb83247944827c38b8af6e`；真实mathlib HEAD `807d3836b165983210ee2ecf3cd28f239436949c`。仅只读版本文件和现成缓存，没有更换环境或下载缓存。

## 最终独立裁决

STATUS: CORRECT

JUSTIFICATION: 冻结两个完整类型在其真实概率、非负小化系数、compact参数和AE有界假设下数学成立；实际jointPhase单位模保证所有所需有限测度上的真可积，真实残差分解先建立有限/质量转换再拆Bochner积分，得到正确线性m范数转移及输出m≤1。实际紧族接口给共同m0，取min(m0,1)保留空K与统一量词；两侧每个quadratic tilt由真实exp Integrable建立概率，未使用不可积tilt=0总化漏洞。静态固定库接口/public imports/现成缓存足够支撑声明，未发现需要修改公开假设、定义、量词或imports的阻塞。scope路线简写toReal_sub须实现时使用actual toReal_sub_of_le或有限real加法等式，属于API选择，已透明记录。

这是独立完整声明/source/API门的CORRECT，不是尚不存在的实现/proof/Audit/receipt通过。R1:356–360只绑定为共同Fourier常数所需的标准充分模量转移前置；不证明紧族C/sqrt(n)质量界、真实中央/远弧共同积分估计、概率Chernoff(16)/(17)、Legendre优化、root公共quadraticChar/cosine连接、WC、LLT/hW或根闭合，不作最优性/新颖性声称。根A/B/C/D、紧族mass和概率Chernoff仍OPEN。scope冻结时关于U16e排队的历史计划文字不改；本次派单已经说明U16e全proof终票被lead接受，未将历史计划文字用作当前状态证据。
