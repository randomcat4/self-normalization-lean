# U22s / U22t 独立完整最终证明审查

STATUS: CORRECT
S_HELPER: CORRECT
S_PRODUCER: CORRECT
T_ACTUAL: CORRECT
BATCH_INTERFACE: CORRECT
PRECISE_GAPS: NONE_IN_FROZEN_BATCH_SCOPE

日期：2026-10-23。本上下文是本批唯一 fresh 独立完整最终审查员，与实现作者分离，按任务指定使用 gpt-6.1-sol / xhigh，未切换模型。使用 math-theorem，不使用 math-ultra，未派生其他上下文。本上下文没有可读取的输入、缓存输入、输出及推理子集 token 计数，故不编造用量或订阅比例。

结论来自全部源码、全部实际所属类型、逐步数学推理、原源对应关系及精确服务器证据的共同核对。完整覆盖 S 的 75 行和 T 的 105 行、3/3 实际所属定理、0/0 定义值。没有仅凭 elaboration 通过判定语义正确，也没有重编或重跑公理审计。唯一写入工件为本报告。

## 1. 精确版本与证据边界

本地工件目录为 `C:/game/shao lean/drafts/oq3/`。服务器工作树为 `/root/rivermind-data/shao-lean-20261021/workspaces/lead-oq3`，实际当前 HEAD 与收据父提交均为 `3346440dea28ce226bad375c62b288163ea7479e`，收据分支为 `feat/oq3-boundary-laplace`。

| 单元 | 模块 / 源文件 | 完整源码 | SHA256 |
| --- | --- | --- | --- |
| S | Shao.OQ3.LocalBoundaryLowerBound / u22s-source.lean | 75 行，3690 B | 747aea48356569ac0e0d8cb0c292325a53a72f7cf8271763097472562a4e238d |
| T | Shao.OQ3.OpenDomainBoundaryLowerBound / u22t-source.lean | 105 行，5734 B | 426d3b0713595bea5fbb4205b550f2e20e6a7f9f4aea1c555bd847cdb060dcc4 |

两份完整源码均为 UTF-8、LF、CR=0；本地冻结源码、服务器对应当前源码、各 run 的 `source-01.lean` 逐字节同哈希。完整读取并核对冻结声明：`hundredth-unit-scope.md` 为 36 行、2364 B、SHA256 `567e83138b6d4ae97b4ad9b78fce3a83a2f14a0c2f494f0b2967738297471a88`；`hundred-first-unit-scope.md` 为 71 行、4360 B、SHA256 `13efbb648a10bdb5572cce26e3d20fc6e522b8eabaf63e9b5048b8611d46d443`。服务器各自 `scope.md` 同哈希。源码没有改变冻结前提、对象、量词或结论。

直接依赖 Q 源 SHA256 为 `0d566a0932a0c63bb9501abe6d0a25c17fc035046396186ef8b410cbdac89cf4`，R 源为 `b13cfa5a2a75b6375bf87fd530bf0921a5776dff613046a0573b769a9186ea8e`，本地与服务器当前源一致。完整读取已接受的 `u22qr-proof-review.md`（259 行、28267 B、SHA256 `19c18c4cfc7c3a236aa2ebcd8e2a2b78feeb666844cfc94d9d61fed485302a48`），并定向核对 Q 的完整 Taylor 接口及 R 的完整公开接口；复用其独立完整证明/来源/环境验收，不重新审查旧证明或重跑旧门。

## 2. 全部实际所属类型与定义值覆盖

| 实际所属定理 | 完整实际类型材料 | 覆盖 |
| --- | --- | --- |
| Shao.OQ3.exists_positive_boundary_lower_bound_of_taylor | u22s-actual-types.txt:10–25；源码 7–52 | 全部参数、四项严格正性、完整 Taylor 前提及结论、全证明 |
| Shao.OQ3.exists_positive_boundary_lower_bound_of_contDiffAt | u22s-actual-types.txt:1–9；源码 54–72 | 实际 C³、真实切向一/二阶导数与法向导数、全部量词及全证明 |
| Shao.OQ3.open_domain_quadratic_tilt_boundary_lower_bound | u22t-actual-types.txt:1–61；源码 9–102 | 全部真实概率律/参数、所有 let 值、图表/jet/全局率/余项/条件下界及全证明 |

两份实际类型文件的全部 25 行 / 1173 B 与 61 行 / 4229 B 已逐项完整读取；SHA256 分别为 `51d74a169993cb74e0101e3a51bfd0110da6d79188fe9505d8b5138f00e03e8b` 和 `3b6d30a8aedec5b12feaeaf625df8609bb9ac74683bdc6c90dcd63722b6d86d3`。本地与服务器 `actual-types.txt` 同哈希，服务器文件又逐字节等于完整 audit.log 中所有 DECL/TYPE/AXIOMS 段；未依靠截断打印或名称清单推断类型。

S 实际所属声明=2、实际定理=2、公开定理=2；T 相应为 1、1、1。两模块均无额外私有或生成声明，无公开、私有或生成定义。故定义值覆盖为 0/0；没有被遗漏的定义值。所有局部 let 仍逐个审查，不能用“零定义”跳过其内容。

S 第一定理对任意 `F,lambda,Lambda1,rho,C`，明确假定四常数严格正以及整个闭矩形上的完整余项界，结论是存在 `delta,c`，满足 `0<delta`、`delta≤rho`、`0<c`，且对所有 `r,z`，`|r|≤delta`、`0≤z≤delta` 时有 `c*(z+r²)≤F(r,z)-F(0,0)`。第二定理没有 Taylor 或所需下界前提：只输入实际中心 C³、实际切向一阶零、实际法向严格正、实际切向嵌套二阶严格正，产生相同局部下界而不对外暴露 rho。

T 的外部参数完整保留：实际概率测度 mu、theta 属于真实二元 MGF 域内部、同一实际倾斜律的抛物线协方差行列式非零、`level>0`、`a0>0`、`theta.2<0`、真实倾斜一二阶矩等于 `(a0,a0²/level²)`、`theta.1=-2*a0*theta.2/level²`。没有额外的目标 Taylor 界、目标下界、已有局部率表示或假定光滑性作为调用者前提。

T 全部 let 与实际导出类型一致：Omega 是真实 MGF 域内部；nu 是对原 mu 的实际二次指数倾斜；means 是其两个真实积分；K 是真实指数积分的对数；D 是 nu(theta) 的真实协方差。pr0/pr1 是两个坐标投影，row0=`D00*pr0+D01*pr1`，row1=`D01*pr0+D11*pr1`；B(u)=`(u.1,2*a0/level²*u.1-u.2)`。L 是该同一行映射的连续线性等价，e 的整个函数等于 means，保留 theta/source、means(theta)/target 及 source⊆Omega。J(z)=`e.symm(z)·z-K(e.symm(z))`；G(r,z)=`(a0+r,(a0+r)²/level²-z)`；F=J∘G；v=`(1,2*a0/level²)`；Lambda1=`2*theta.2/level²+(L.symm v).1+(2*a0/level²)*(L.symm v).2`。局部实现中的这些值与声明逐项相同。

T 对同一 L/e/J/G/F/v/Lambda1 完整输出：正法向系数 `0<-theta.2`；F 的中心 C∞；真实一阶导数 `(-theta.2)•pr1`；任意 u,v 的完整嵌套 Frechet Hessian；真实全域 EReal Legendre 率与 F 的完整零点邻域最终等式；固定正 rho/C 上的完整闭矩形 Taylor 界；以及 `0<Lambda1 → ∃delta,c>0, ∀r,z,...` 的下界。全部合取项及条件蕴含位置均与实际类型一致。

## 3. 全部源码逐段覆盖

以下互补区间覆盖全部 180 行，包括导入、空行、作用域与闭合命令。

| S 源码行 | 已审查内容 |
| --- | --- |
| 1–6 | 唯一导入、namespace/scoped/noncomputable section、空行；无检查设置或新逻辑假设。 |
| 7–16 | 第一定理全部实际条件、闭矩形、在 r/z 之前选择 delta/c 的量词。 |
| 17–25 | delta/c 精确常数、分母严格正、正半径及三个上界。 |
| 26–32 | 两项合法除法交叉乘法、系数预算、c 严格正及存在构造。 |
| 33–42 | 双侧 r 的三次项控制、非负 z 的混合/平方项、统一总余项预算。 |
| 43–50 | 两项吸收预算及 c 对 z/r² 的逐项支配；所有乘法保序所需非负性。 |
| 51–53 | 将新闭矩形嵌入原矩形、绝对值下侧界及最终不等式、空行。 |
| 54–61 | 第二定理完整实际导数条件及下界结论。 |
| 62–68 | 从 Q 真正生产余项，只用 htangent 消去一阶切向项。 |
| 69–72 | 用同一真实法向/切向二阶系数应用 helper，正确移除未公开的半径上界。 |
| 73–75 | 空行及 section/namespace 闭合，无额外声明。 |

| T 源码行 | 已审查内容 |
| --- | --- |
| 1–8 | 两项实际导入及全部作用域命令；无公理或绕过设置。 |
| 9–19 | 全部真实源输入、矩点及 saddle 身份。 |
| 20–34 | Omega/nu/means/K/D/投影/协方差行映射/B 的全部值。 |
| 35–47 | 同一 L/e、图表条件、J/G/F/v/Lambda1 的完整存在接口。 |
| 48–62 | 完整 jet、真正全局率最终身份、真实余项与正曲率条件下的下界。 |
| 63–78 | 证明中的全部别名，逐个与声明定义核对。 |
| 79–82 | 唯一一次 R 调用，原样传入所有输入，抽取同一组图表及余项见证。 |
| 83–93 | 同一 J/G/F/v/Lambda1 与 hbound 的定义相等性；没有重新选择见证。 |
| 94–102 | 完整携回 R 的结论，仅在明确 hcurvature 下调用 S helper，完成下界。 |
| 103–105 | 空行及闭合命令；无遗漏声明。 |

完整源码静态扫描没有 `sorry`、`admit`、新增 `axiom`、`unsafe`、`native_decide`、`implemented_by` 或 `set_option`。`noncomputable` 不绕过内核，不代替所需数学前提。

## 4. S 纯代数 helper 的独立数学核对

设 E=`F(r,z)-F(0,0)-lambda*z-(Lambda1/2)*r²`，原前提给 `|E|≤C*(|r|³+|r|z+z²)`。源码精确选择

`delta=min(rho,min(lambda/(4*C),Lambda1/(4*C)))`，`c=min(lambda/2,Lambda1/4)`。

由 rho、lambda、Lambda1、C 严格正，`4*C>0`，delta>0、c>0，且 delta≤rho。两个除法上界合法地给出 `4*C*delta≤lambda` 和 `4*C*delta≤Lambda1`；没有除以可能为零的 r、z、delta 或系数。

对任意 `|r|≤delta`、`0≤z≤delta`，`|r|³=|r|*r²≤delta*r²`，`|r|z≤delta*z`，`z²≤delta*z`。前两项的乘法保序分别使用 r²≥0、z≥0；第三项来自 `(delta-z)*z≥0`。乘以 C≥0 后，余项总预算是 `C*delta*r²+2*C*delta*z`，没有漏掉混合项或 z² 的系数。

两个预算又分别不超过 `(Lambda1/4)*r²` 与 `(lambda/2)*z`，因为 `4*C*delta≤Lambda1`、`4*C*delta≤lambda` 分别与 r²≥0、z≥0 相乘。使用绝对值界的下侧 `-R≤E`，得到

`F(r,z)-F(0,0) ≥ (lambda/2)*z+(Lambda1/4)*r² ≥ c*(z+r²)`。

最后一个不等式确切使用 c 的两个 min 上界及非负 z/r²。源码 51 行把 `|r|≤delta≤rho`、`z≤delta≤rho` 传给原 hbound，52 行的 nlinarith 只是在组合已列预算，没有承担未写出的分析结论。

量词与边界：同一 delta/c 在所有 r,z 之前固定，允许依赖 F 及输入常数，不依赖矩形点。r 可正、负或零，含 r=±delta；z 含 0 与 delta。原点两边均为零；边界只用 ≤，没有从开邻域偷换成未受控闭端点。严格正性只用于产生正半径、正 c 及合法分母。此 helper 明确输入已有余项，不能单独冒充原源余项生产者。S_HELPER: CORRECT。

## 5. S 实际 C³ 生产者消费者的独立核对

第二定理以真实 F 的 `ContDiffAt ℝ 3 F (0,0)` 调用已接受 Q 的 `exists_uniform_boundary_taylor_bound_at_zero`，取得严格正 rho/C 与完整固定闭矩形余项。Q 的系数是实际 `deriv (fun t=>F(t,0)) 0`、实际法向 `fderiv ℝ F (0,0) (0,1)`、实际嵌套 `deriv (deriv (fun t=>F(t,0))) 0`；不是另行指定的形式系数。

源码 63–68 行只用 htangent=0 将 Q 的切向线性项消去，常数项、法向项、二次项及右侧余项全部保留。随后向 helper 传入这两个实际正系数、Q 刚产生的 rho/C 及 hbound，得到所需结论。去掉内部 `delta≤rho` 仅是去掉未承诺的额外结论，没有弱化调用范围。

中心 C³ 确保所列导数具有实际解析意义，不靠不可微点处 deriv/fderiv 的总函数默认值。调用者没有给目标下界、目标 Taylor 界、现成 remainder、任意 Hessian 界或邻域 Lipschitz 界。正法向和正切向二阶仍是明确且必要的输入。范围是每个固定 F 的局部统一界，不是整个参数族统一常数。S_PRODUCER: CORRECT。

## 6. T 同一实际图表、源系数与批次接口

T 只在 79–82 行调用一次 R 的 `open_domain_quadratic_tilt_boundary_taylor`，完整原样传入所有源输入。L/e、图表条件、正法向、光滑性、一二阶 jet、hglobal、rho/C/hbound 全部来自该次调用。后续 J/G/F/v/Lambda1 由同一次 L/e 定义，没有第二次存在选择，也没有将一组图表的余项用于另一组率函数。

为核对保留的 Hessian，写 k=`2*a0/level²`。B(u)=`(u.1,k*u.1-u.2)`；实际全部方向公式为 `D²F(0)[u,v]=(L.symm(Bu)).1*(Bv).1+(L.symm(Bu)).2*(Bv).2+(2*theta.2/level²)*u.1*v.1`。代入 u=v=(1,0)，Bu=Bv=(1,k)，得到实际切向二阶 `2*theta.2/level²+(L.symm v).1+k*(L.symm v).2=Lambda1`，与 R 接口及原式 (10) 完全一致。修正项 `2*theta.2/level²` 的负号影响没有被丢弃；hdet 只提供协方差逆作用的可用性，不能由此推出 Lambda1>0。

T 的 hpositive 是 R 所给 `0<-theta.2`。91–93 行 hb 仅是同一 hbound 的定义展开，无新数学假设。94–95 行逐项原样携回所有 R 输出，尤其保留完整全方向 Hessian、完整邻域真实 EReal 率身份以及同一实际 F 的完整 Taylor 界。最后只在 96 行明确引入 `hcurvature:0<Lambda1` 后，向 S helper 传入 `F, -theta.2, Lambda1, rho, C` 和已生产的界，得到正 delta/c。所有 helper 前提均有真实来源；没有目标下界作为前提，没有循环依赖。

存在量词顺序正确：先选同一实际 L/e，定义其实际 Lambda1，再给出 `0<Lambda1 → ∃delta,c,...`。结论没有宣称已构造正曲率，也没有把这一条件移到另一个图表或另一个协方差上。T 使用 S 的纯代数 helper 而没有调用 S 的 C³ 消费者，是因为 R 已经生产了同一实际图表的余项；这不减少余项来源的要求。S → Q、T → R/S，接口无循环或未覆盖依赖。T_ACTUAL: CORRECT；BATCH_INTERFACE: CORRECT。

## 7. 原源语义与不可扩张的完成范围

只读原源 `C:/game/shao/current/oq3/proofs/r2/repair01.md` SHA256 为 `9d2e554838aa15b645aaf74a42468d423fed606aa91c1181d0dddf4e87c57cfd`。本次直接读取 1–45、112–187 行，完整覆盖式 (8)–(13) 的相关上下文，并读取同目录 `report.md`:36–79；已接受 Q/R 报告的来源说明一并核对。此处只认证本地分析依赖，不进行外部文献/新颖性复审。

level 对应原固定 x，theta 对应 `(hat s0,hat t0)`，G 是原边界坐标的准确逆变换，z 前的负号保留。F(0,0) 对应源 Lambda0 的中心率值；R 保留的真实全域 EReal Legendre 率身份说明 F 是实际率的 germ，而非任意替代光滑函数。`lambda=-theta.2>0` 对应式 (9)；实际 Lambda1 对应式 (10)。原源已明确假定其严格正性，T 如实保留这一条件，没有声称用 hdet 消去它。

Q/R 已闭合式 (11) 的真实固定小闭矩形余项；本批 S 证明从该余项和正法向/正切向二阶吸收得到式 (13)，T 将其用于同一真实图表。没有把仅有形式 Taylor 多项式、逐点余项或正 Hessian 直觉当作统一矩形界。

精确半径限制：T 的 hglobal 是完整 `𝓝(0,0)` 上的最终身份，不是全空间身份，也没有明说所展示的最终 delta 闭矩形每点均满足该身份。下界的字面结论是对同一 F 的全部该矩形；若后续需要在同一矩形逐点以真实 EReal 率代替 F，须把 delta 再与 hglobal 邻域的正半径共同缩小。现有结论直接允许这样的缩小，但本报告不把未显式给出的同半径性质写成已实现接口。这是范围说明，非冻结声明内缺口。

本批未闭合 Lambda1 正性本身、实际尾域与 z≥0 的坐标等价、a/q 正性、绝对 Jacobian=1、振幅及行列式控制、Laplace 积分、Edgeworth 到真实概率的误差或远场概率。全局率 germ 身份也不能代替远场概率界。原实际统一谱界、严格 `0<beta<2/5` 的弱 Cramér 条件、统一矩条件、正则/唯一全局 saddle、正曲率及修正后明确远场概率前提均保留。Song 的统一 Edgeworth 输入及其他外部结果归属原样保留。

局部 level>0 辅助接口没有替代原概率问题 x∈(0,1) 等全部约束，也不构造满足原根全部条件的 saddle。本批不改变原 B/C/D 的 OPEN 状态，尤其不宣布 B/D 根闭合；不对已接受 A 的既定范围作任何改动。本批是源局部正下界依赖的闭合，不构成新颖性或论文强度认证。

## 8. 服务器内核、完整所属公理及导入证据

既有作者成功门已直接核验并复用：S/T 均 attempt 1，完整目标 exit=0，耗时分别 9.131144843995571 s 与 5.8274858351796865 s；首个完整所属公理门 exit=0，分别 5.648829635232687 s 与 5.869706312194467 s。收据均记录 CPU14–17、native memory 8192 MiB、jobs4、autoImplicit=false、单 lane heavy 约束。实际工具链文件为 `leanprover/lean4:v4.36.0-rc1`，lakefile 的 mathlib pin 为 `807d3836b165983210ee2ecf3cd28f239436949c`，autoImplicit=false。

两份成功 build-01.log 及两份完整 audit.log 已直接读取。build 日志只有已知薄包视图的 mathlib local changes 警告，无 Lean 错误。此警告的固定依赖/API 来源已由精确接受的 Q/R 审查覆盖；本次不将其曲解为任意包清洁性证明或全项目重建声明。

完整审计源已读取：遍历 env.constants，通过 `getModuleIdxFor?` 判定实际模块所有权，覆盖公开、私有及生成常量，而非仅匹配 namespace/公开清单；逐个拒绝新增 owner axiom；逐个调用 `Lean.collectAxioms` 递归传递收集，只允许 propext、Classical.choice、Quot.sound；另验证全部冻结目标实际存在且是定理。三条实际所属定理的公理均精确为这三项，无 sorryAx。实际计数来自完整 owner 输出：S definitions=0、frozen theorems=2、all theorems=2、all declarations=2、PASS；T 为 0、1、1、1、PASS。因此没有漏审私有或生成定义值。

S run 为 `/root/rivermind-data/shao-lean-20261021/runs/oq3/u22s-20261023`；T 为同目录下 `u22t-20261023`。下表中 receipt、Audit 及三个 JSON 的本地对应工件与服务器文件均直接核对同哈希；两类日志的服务器实际哈希与已核对收据字段一致：

| 工件 | S SHA256 | T SHA256 |
| --- | --- | --- |
| receipt.json | 419941c1443474f8942157f8d0653e122aa9d841ef42697da4a996991be562d5 | daed0356bd560c2f76f64ab4ce45472496435c83bcff6c1c9317fb4964d771b6 |
| Audit.lean | 1c6b0de898e95fd658f51d76cba11ca2d0b25ddf661f60c8ce312d1ea0a186b4 | c3ccccad805dc886f793bba43a14beae29a413ae188d94c7aa88b4ce4aa8ffbd |
| build-history.json | c14ef85e6686753901a186dbc69e321aae8d126f46c7aa640d731cc833d2d6cb | 63ed970197518a7da2a69016afbbbb9d2875f797ceba55fa1bc6f1a7e4eb2326 |
| audit-record.json | c2ec88b8076c34c5c1718da5733bd5223084ddb9210d5f2e210aeab50bbb786d | 50698fba7583e47156505d73a60a880d1885bf3b3e0abf077f7aa96f80c70a01 |
| audit-environment.json | 9607f777af20381ba67054c19efe458c69496fe690ee27f85fd921cd75af2719 | 331cd1e39a902d25e91dc704304781dc8637dc063635219f4890212c1cb172c9 |
| build-01.log，均 133 B | fe9a6b741bba0630c9977614157f0259907b0b7ebce576a9400b542ee4518626 | fe9a6b741bba0630c9977614157f0259907b0b7ebce576a9400b542ee4518626 |
| audit.log，1420 B / 4476 B | 2e611b406ed1ada9922f138c2a2794593d125579b48a4c7c6b4a7c8529f3a2a5 | 223c2692c2b9d3e61adcb22eb022e50dc35a9e32227495417cb2a8903b080ccb |

实际类型、scope 与成功归档源的精确绑定见第 1–2 节。完整本地 build-history、audit-record、audit-environment 已读取并与收据相互核对。两单元各仅一次完整成功尝试，不隐去失败分母。环境清单复用已授权 accepted-source-view，仅添加 lane 自有新对象，没有复制二进制或写共享缓存。

定向只读观察 accepted-source-view 中实际 Q/R/S/T .olean 路径均解析到该 lane 工作树的同名自有对象。SHA256 分别是 Q `5e6a3ce2f66a9bbd3338c03d7c6d8a465e1cbe5003da85314b68bde62e5fac9e`，R `79dbfe6730c023911f392ebeba0a4d7296478acf5f03b9e4e6f57e725608b383`，S `5b3b1c07f823292b441f42c1c99538056651507e0a36e9a1e2ad4e70ae7049b9`，T `6be9582aee39433d33a46a52fef52cdeea79c7c0e6a63a271ff131d4e6cf1cea`。Q/R 与既有独立接受记录一致，当前源和归档精确一致；无接口或证据版本缺口。这是所用导入路径的定向核对，不是全缓存审计。

本审查只做文件读取、哈希、静态核对和数学审查；没有调用 Lean/Lake，没有本地 Lean、服务器第二次编译/公理审计、包更新、cache 修改、新 wrapper 或额外环境/许可仪式。旧成功证据与冻结字节原样保留。

## 9. 最终裁决与停止点

S_HELPER、S_PRODUCER、T_ACTUAL、BATCH_INTERFACE 全部 CORRECT。在冻结批次范围内，无关键数学缺口、未覆盖实际所有者/定义值、见证不一致、隐含结论性前提或精确证据缺口。180/180 行源码、3/3 实际所属完整类型、0/0 定义值及全部新推理覆盖完成，精确源码已有完整服务器内核/传递公理凭据。

本批闭合原式 (13) 所需的局部正下界依赖，正曲率仍按原源明确为条件，原 B/D 根仍 OPEN。报告最终字节数、行数及 SHA256 由最后一次外部完整性核对封存。本审查员在该核对后停止全部工具调用和写入，不启动下一单元。
