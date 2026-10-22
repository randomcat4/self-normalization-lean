# U16f 完整独立证明、来源与实际类型审查

STATUS: CORRECT

唯一reviewer lease1，仅拥有本新报告及远端run/proof-review.md。不独占代码库，保留他人编辑；不改作者源、scope、旧票、shared或cache，不spawn、Lean/probe/build、commit/PR或下载原始完整日志。承认此前已完成声明门的上下文存在；本次第一阶段仍先仅提取actual实现两个完整公开类型，独立盲译并持久化，当时尚未读取本次全proof、scope正文、TYPE或receipt机械证据。初次落盘2527字节，SHA256 01e92a8ed890361b5280f9595fb36d3ef2fde264c828bded751407d7373655a7。以下按阶段续写至最终裁决。

## 第一阶段：actual公开完整类型盲译，先落盘

actual本地输入 `C:/game/shao lean/drafts/oq3/CharacteristicMeasureDomination.lean`，仅公开类型提取及source hash，SHA256 `ec7032919bd8d825bb8746da15e84b29c5cb59ef97858367e4d73fdf52aa9bbb`。零公开定义、两个公开定理，不能把之前声明批准当作本次proof判断。

`jointCharacteristic_norm_le_of_measure_lower`：先给真实实数概率测度mu和nu，实m≥0，以及实际ENNReal.ofReal(m)缩放mu后作为测度≤nu。要求同时证明m≤1，及对全部实xi/eta，nu的actual jointCharacteristic复范数≤1−m*(1−mu的actual jointCharacteristic复范数)。m在全部频率前固定。未输入m>0/m≤1、有界支持、原子性或非格点条件；m0/m1和所有退化概率都须保留。真实有限残差、实际单位相位及真可积、复实标量范数/真实总质量不能只靠符号名称代替。

`exists_compact_tilted_characteristic_bound`：先给真实概率mu、实M≥0、同mu-AE |x|≤M、实二元参数集K与IsCompact K、任意固定基准u0/v0。存在同一实m>0且m≤1，在全部p∈K和全部实xi/eta之前选定，使p二次倾斜下的actual jointCharacteristic范数≤1−m*(1−基准二次倾斜下的actual jointCharacteristic范数)。倾斜恰是同一mu.tilted(fun x=>u*x+v*x²)；必须有真实exp可积并先建立各tilt概率。K可空、M可0、基准不必属于K，不能从选取p∈K推出m0≤1。没有n/J/LLT/Chernoff量词。

本次独立初判：如果实际证明建立lambda=ofReal(m)•mu和rho=nu−lambda真有限、真实加法分解及总质量等式、phase在两个有限measure上真Integrable，三角界可给首结论且无需除m或1−m。第二条应在全p/频率外选择min(m0,1)>0再消费真实概率门。实际proof/局部辅助/库API/actual TYPE和机械绑定尚待随后顺序核验。本阶段先保存，不把初判升级为CORRECT；根A/B/C/D、实际compact质量和概率Chernoff仍OPEN。

## 第二阶段：冻结类型、actual定义与来源

本次actual两个完整类型与冻结scope Lean fence按去白空格的全文比较相同；三imports逐项为FiniteFarArc、CompactTiltDomination、Mathlib.MeasureTheory.Measure.Sub，无新增公开定义或签名假设。scope SHA `fcbcce37d21640dec787be5b146d8b334520273d37e7b43f6d5d85cd1baad701`。声明门终票 `4b774df34c0c53f0627ab6c1925928165e5bbb6425f330fd4d49fa22b22c4280` 已被lead全文读过；本次独立proof判断不由该结论替代。

实际只读R1 `C:/game/shao/current/oq3/proofs/r1/report.md`，SHA `3473d34ff20bd0d334b9ef3ea3c3ee167fba4d5cc3a742849820ce54d639e662`，350–366行，特别356–360行：紧倾斜族Fourier积分的共同C/sqrt(n)界来自中央Gaussian和共同远弧模缺口。本单元是该处所需标准充分模量转移前置，不是整段积分估计或式(16)Chernoff证明。scope冻结时排队/U16e状态文字作为历史保留，未据此断言当前状态。

实际 `JointNonlattice.lean`20–27行：jointPhase为Complex.exp(((xi*x+eta*x²:ℝ):ℂ)*I)，jointCharacteristic为对传入mu的真实Bochner复积分，jointPhase_norm恰为1。真实定义与这两个目标的复范数一致，没有别名替换或修改root公共quadraticChar/cosine定义。现有U15a/U15c承重接口按实际源码核对，已接受报告可供继承，不重复构建或重审旧成功目标。

## 第三阶段：91行全部proof、私有辅助和局部数学门

11–15行唯一authored private theorem `jointPhase_integrable_finite`：输入任意实数有限测度和任意两实频率，输出actual phase真Integrable。13行展开真实phase后fun_prop消费多项式、实复嵌入、乘I和复exp的全局连续性；14–15行先AEStronglyMeasurable，再用有限测度版Integrable.of_bound及全局norm=1。没有把残差误装为概率，亦不需要有界支持/原子性/频率局部化。这一helper未放宽成totalized积分等式。

17–40行首目标质量部分：23行lambda=ofReal(m)•mu，24行用actual Measure.smul_finite mu ofReal_ne_top建立lambda有限；mu本身概率故有限。25行rho=nu−lambda是真实非负Measure subtraction，nu概率故有限，通过实际isFiniteMeasure_sub实例及局部let的定义展开得到rho有限。26行sub_add_cancel_of_le实际消费hlower与小measure有限，给rho+lambda=nu。这里不能无条件逐集合相减；实现没有这样做。

27–29行hscaled把lambda.real(univ)展开，mu(univ)=1、ofReal(m)有限且hm≥0，toReal_ofReal hm给实际m。30–35行hmassadd先用两个有限实例提供显式 `measure_ne_top rho _`、`measure_ne_top lambda _`，才反向应用measureReal_add_apply；再用真实加法分解和nu概率得rho.real(univ)+m=1。因此不存在top.toReal=0假充真实质量。36–38行用rho.real(univ)≥0推出m≤1，39行得rho.real(univ)=1−m；未预设m≤1或循环使用残差质量正性。

实现采用声明门已确认合法的“有限实质量加法”路径，不调用scope路线的sub.toReal简写。实际toReal_sub_of_le与sub_apply虽可用于另一证明，本实现没有消费，不能把未用API写成实际依赖。两条质量非top门都已在实际proof明确传入；rho有限来自库实例而非独立声明的第二个let，透明且充分。

41–50行积分分解：xi/eta在m固定后引入。42行helper给rho上的真Integrable；43–44行先用mu概率上的integrable_jointPhase，再用Integrable.smul_measure ofReal_ne_top给lambda上的真Integrable，允许m=0，不需m≠0。47–50行展开actual jointCharacteristic后，以hdecomp改写nu积分，`integral_add_measure hI_rho hI_scaled`真正消费两可积门；再以lambda定义和integral_smul_measure把第二项变为m•χmu。hm明确用于toReal_ofReal，未跳过指数可积或有限条件。

51–54行残差积分norm界：对有限rho调用norm_integral_le_of_norm_le_const，C=1和真实全局phase norm=1给≤rho.real(univ)，再hmass给1−m。该库界自身适用于总化积分并不自动保证真可积，但本proof已经在42行独立建立，所以没有总化漏洞。55–62行用真实hsplit、复三角、norm_smul与hm后的abs(m)=m、加法单调及纯环等式，得正确线性m缺口，不误用产品m²。

首目标边界：m0时lambda=0且smul_measure只要非top；m1时rho实际质量0，helper/分解仍有效，未除1−m或将rho归一化。零频率相位恒1得两侧1；任意Dirac/退化概率也合法。mu与nu只需真实概率，无隐含同支持、矩、原子或非格点假设。

64–82行紧族共同选择：71行actual U15c gives同一m0>0和forall p∈K的测度小化；只在87行消费其第一conjunct，未消费第二个产品cosine界。72–73行在全部p/xi/eta之前选择m=min(m0,1)>0；82行直接min_le_right给m≤1。因此即使K为空，也不从不存在的p推出m0≤1。74–76行基准mu0明确来自同一mu二次倾斜，先以actual U15a quadratic_exp_integrable_of_ae_abs_le对任意基准u0/v0建立真实exp Integrable，再actual isProbabilityMeasure_tilted给mu0真实概率；mu原概率提供NeZero。

77–81行hscaled按每个实际集合A展开测度缩放，ofReal单调与m≤m0、mu0(A)非负，ENNReal乘法单调给ofReal(m)•mu0≤ofReal(m0)•mu0。这里无需mu0(A)正、A可测或参数集非空；Measure偏序本来比较所有集合。83行之后才引入p/hp/xi/eta，84–86行逐p用同一M/hb建立目标tilt mu1的真实指数可积和概率；87行hscaled.trans(hfamily p hp).1给真实measure下界；88行对实际mu0/mu1和同一m应用首目标并取其全频conjunct。

因此m不依赖p或频率，基准不要求在K，K空、M0、singleton K、L0、任意有符号二次参数都保留。M0时hb使mu-AE x=0，指数在支持上1，可积/概率论证无除M。没有利用tilted不可积时零measure分支，没有从被缩放的lambda误取概率实例。

局部对象/假设已全覆盖：hf、lambda及有限instance、rho、hdecomp、hscaled、hmassadd、hnonneg、hm1、hmass、xi/eta、hI_rho、hI_scaled、hsplit、hh/hresnorm、m0/hm0/hfamily、m/hm、mu0/mu1及两个概率instance、A、p/hp、hdom；全部只是当前proof内部let/have/intro，不是新公开定义。91行namespace闭合，未发现尾部附加证明、私有递归或额外源码段。

## 第四阶段：实际固定库和继承语义核对

实际指定服务器只读核：Sub.lean100–102 sub_add_cancel_of_le要求小测度有限及小≤大；145–146 isFiniteMeasure_sub从大测度有限给残差有限。Finite.lean307–310 Measure.smul_finite要求缩放c≠∞。Measure.Real435–438 measureReal_add_apply要求两集合质量均非top；实际源码34行正好逐项传入。hmassadd在hm1之前，并未循环用m≤1构造lambda有限。

IntegrableOn.lean171–172 Integrable.of_bound要求AEStronglyMeasurable、有限measure和AE norm界。L1Space/Integrable.lean314–317 actual Integrable.smul_measure仅要求原函数真Integrable和c≠∞，不要求c>0，因此m0成立。Bochner.Basic1010–1015 integral_add_measure要求两个真Integrable；1047–1048 integral_smul_measure使用c.toReal；1002–1006 norm_integral_le_of_norm_le_const使用有限测度和AE norm界。源码逐门吻合；复实数标量norm_smul化成abs(m)后才按hm消绝对值。

实际Tilted.lean42–43定义是mu.withDensity(ofReal(exp(f)/∫exp(f)))；46–48不可积tilted为0。126–136 actual isProbabilityMeasure_tilted [NeZero mu] hf的hf是真exp Integrable，并通过integral_exp_pos hf建立正normalizer和有限非零门。U15a17–34的actual参数接口恰给本proof的两个hf，其上界exp(|u|M+|v|M²)对任意实系数有效。U15c30–56从紧参数盒和B=L(M+M²)给共同m0=exp(-2B)>0，空K证明不提取Nonempty；本实现只用其measure小化部分而未越界推root公共特征恒等式。

本阶段数学/actual API结论：两个public证明及唯一private helper逻辑正确，冻结签名/source fit相符。此结论先保存；尚未读本次Audit actual TYPE或receipt/构建/Audit绿灯，待下一阶段逐项核绑定。

## 第五阶段：逐项完整actual TYPE核对（在机械绿灯之前）

已仅从实际服务器Audit.log过滤DECL/TYPE块及全部续行，不输出AXIOMS/PASS/receipt；逐项实际读到如下三个owned类型，没有按作者计数推测helper类型。

1. `Shao.OQ3.jointCharacteristic_norm_le_of_measure_lower`，实际TYPE全文：

```text
∀ (mu nu : MeasureTheory.Measure ℝ) [MeasureTheory.IsProbabilityMeasure mu] [MeasureTheory.IsProbabilityMeasure nu]
  (m : ℝ),
  0 ≤ m →
    ENNReal.ofReal m • mu ≤ nu →
      m ≤ 1 ∧
        ∀ (xi eta : ℝ),
          ‖Shao.OQ3.jointCharacteristic nu xi eta‖ ≤ 1 - m * (1 - ‖Shao.OQ3.jointCharacteristic mu xi eta‖)
```

此TYPE保持两个概率实例、hm、真实measure下界及输出m≤1，xi/eta确在m之后；没有增加m正、额外概率/支持或频率窗口假设，未改实际jointCharacteristic常量。

2. `Shao.OQ3.exists_compact_tilted_characteristic_bound`，实际TYPE全文：

```text
∀ (mu : MeasureTheory.Measure ℝ) [MeasureTheory.IsProbabilityMeasure mu] (M : ℝ),
  0 ≤ M →
    (∀ᵐ (x : ℝ) ∂mu, |x| ≤ M) →
      ∀ (K : Set (ℝ × ℝ)),
        IsCompact K →
          ∀ (u0 v0 : ℝ),
            ∃ m,
              0 < m ∧
                m ≤ 1 ∧
                  ∀ p ∈ K,
                    ∀ (xi eta : ℝ),
                      ‖Shao.OQ3.jointCharacteristic (mu.tilted fun x => p.1 * x + p.2 * x ^ 2) xi eta‖ ≤
                        1 - m * (1 - ‖Shao.OQ3.jointCharacteristic (mu.tilted fun x => u0 * x + v0 * x ^ 2) xi eta‖)
```

已核所有长续行，特别同一个∃m先于∀p/∀xi/eta，未隐藏Nonempty K、基准属于K或额外可积假设；两侧都是真实mu.tilted及同一mu。真实exp可积/概率由proof内部建立而非偷偷加到导出类型。

3. `_private.Shao.OQ3.CharacteristicMeasureDomination.0.Shao.OQ3.jointPhase_integrable_finite`，实际TYPE全文：

```text
∀ (mu : MeasureTheory.Measure ℝ) [MeasureTheory.IsFiniteMeasure mu] (xi eta : ℝ),
  MeasureTheory.Integrable (Shao.OQ3.jointPhase xi eta) mu
```

它确为任意有限测度上的真Integrable，没有要求rho概率，也没有被生成成仅概率的helper或总化积分形式。三项实际TYPE与actual两个public+一个private源匹配。未发现额外generated TYPE；完整owned枚举覆盖性及传递公理白名单仍须下一机械阶段实际审计源/日志验证，而非在此假定。

本阶段已持久化，之后才读作者receipt/审计成功记录/构建与版本机械产物；数学与actual TYPE判断未以这些绿灯为前提。

## 第六阶段：最后读取的真实机械证据与绑定

在完整proof/API结论和全部三项actual TYPE已分别持久化后，才读取作者本地 `U16f-receipt.json`、真实run/receipt.json、Audit.lean、日志摘要、构建文件和依赖/pins。作者receipt的状态是AUTHOR_KERNEL_AND_AXIOM_CHECKED_AWAITING_INDEPENDENT_PROOF_REVIEW，表示author-check时独立终审pending；不是本报告的数学裁决。其nonclaims两条本单元U16f标签、当时未commit/PR状态与实际分支相符，没有把历史标签误当即时结论。

本地draft、服务器worktree `Shao/OQ3/CharacteristicMeasureDomination.lean`、run同名源码快照实际SHA256均为 `ec7032919bd8d825bb8746da15e84b29c5cb59ef97858367e4d73fdf52aa9bbb`，4783字节、91行、LF无CR、无尾空白；独立全文扫描sorry/admit/axiom/unsafe/partial关键词为空。两个公开完整签名与冻结scope按白空格规范比较PASS，三imports/namespace保持，零公开定义；不是根据receipt的PASS字段代替该比较。

|真实产物|字节或事实|SHA256|
|---|---|---|
|local U16f-receipt.json与run/receipt.json|两端一致，4965字节|049b36a16480623cb50ba8bcb4b5cb82514897f2748ceeee0f064af5765bb380|
|run/build-02.log|实际0字节|e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855|
|run/Audit.lean|实际1501字节，源码已全文检查|d87cbed5bea79940e12faf4ee57a14139ad3aa738c1b460fff1f7595c2b51419|
|run/Audit.log|实际1559字节，TYPE及AXIOMS/计数分阶段过滤读取|e6576b0018b44a99a9a7dba6bbde74b9d64c3dc88963ca61817043bef7f7d699|
|run/prerequisite-hashes.json|1464字节，与receipt依赖表完全相同|3ff770865cd16b00e87b8cb164d6535f7d6c212c3d656f64ce6239ef377b0411|
|run/scope.md与本地冻结scope|两端一致，5435字节|fcbcce37d21640dec787be5b146d8b334520273d37e7b43f6d5d85cd1baad701|
|run/statement-review.md与既有声明票|16957字节，冻结未改|4b774df34c0c53f0627ab6c1925928165e5bbb6425f330fd4d49fa22b22c4280|

existing receipt记录真实目标build-02命令exit0与Audit命令exit0；本次独立实际观察到相应build文件为空、Audit.log具备完整类型/公理/计数/PASS且所有hash匹配。未重跑这些命令，不把“只读核现有产物”描述成再次编译验证；未下载原始完整日志到本地。

实际Audit.lean先要求两个冻结目标存在且isTheorem；随后枚举两个公开目标stem全部后代及本模块整个_private前缀，对每项拒绝新axiom，并调用Lean.collectAxioms检查每项所有传递依赖。白名单只有propext/Classical.choice/Quot.sound。实际三个AXIOMS行均恰为这三项；实际摘要为 `U16F_FROZEN_THEOREMS 2`、`U16F_ALL_THEOREMS 3`、`U16F_ALL_DECLARATIONS 3`、`U16F_AXIOM_GATE PASS`。枚举与91行源及第五阶段逐项TYPE对应为2public theorem+1private theorem、0owned definition、0generated theorem，没有把作者计数当作唯一覆盖证据；不存在未读的第4项或长TYPE续行。

## 第七阶段：实际14项导入闭包与pins

从真实当前源码逐级解析Shao imports，独立得到14项，集合与receipt及prerequisite-hashes.json逐项完全相同；每一真实服务器文件SHA都重新计算MATCH，非仅相信清单。旧已接受目标没有重复编译。

|实际承重模块|服务器SHA256|
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

真实服务器worktree `/root/rivermind-data/shao-lean-20261021/workspaces/lead-oq3`，branch `feat/oq3-characteristic-measure-domination`，HEAD `c61d56f09da69781bf399eb12e0a35ce8dc150ab`；只读git status实际仅 `?? Shao/OQ3/CharacteristicMeasureDomination.lean`。未commit/PR或编辑其他文件。

实际lean-toolchain文本 `leanprover/lean4:v4.36.0-rc1`，文件SHA `d581a24b57a4ae9e0b2132ca8ac7cc3ac336a9fc2751fe6b29414e2d434d54c4`；lake-manifest.json SHA `40e8e3385f2b0c8ae56fa9de6947301472379cb62eeb83247944827c38b8af6e`；真实mathlib HEAD `807d3836b165983210ee2ecf3cd28f239436949c`。固定库实际源码含Sub、Finite、Real、Bochner.Basic、IntegrableOn、L1Space.Integrable与Tilted的已读数学门，与这些pins绑定；没有切换缓存或环境。

## 最终完整独立裁决

STATUS: CORRECT

JUSTIFICATION: 实际两公开类型与冻结scope严格相符；91行全部证明、唯一private有限测度phase helper、全部局部对象及实际固定库/继承语义已独立核。lambda/rho有限与真实加法分解先于real质量加法，两个非top门明确传入后推出m≤1与残差质量；phase真Integrable先于拆Bochner积分，得到正确线性m特征norm缺口，m0/m1不归一化残差。compact目标在全部p/频率外取min(m0,1)>0，保留空K/M0/基准不在K，两真实二次tilt均从真exp Integrable建立概率。三项actual TYPE全部长续行已逐项核，机械审计覆盖恰三owned theorem且传递公理仅白名单；本地/真实服务器/快照source、14真实闭包、scope与pins及现有build/Audit产物hash全部匹配。未发现数学、源对应、公开量词、类型或机械绑定缺口。

这一区分作者门与本完整独立判断：作者receipt提供历史kernel/axiom执行证据，本报告另独立检查数学/源码/全部actual TYPE后才核该证据。结论不升级R1:356–360尚未完成的共同积分估计。实际compact C/sqrt(n)质量、中央/远弧uniform积分、概率Chernoff(16)/(17)、方向符号、iid换测度、Legendre优化、完整layerdom/LLT/hW/KL、root公共quadraticChar连接及WC/根闭合均未由本单元证明；不作最优/新颖性声称。根A/B/C/D、实际compact质量与概率Chernoff保持OPEN。全部作者源、scope、旧票、共享文件和缓存均未修改。
