# U16e 完整独立证明、来源与实际类型审查

STATUS: CORRECT

唯一审查lease1，只拥有本新报告及服务器proof-review.md；不改实现/scope/旧票/shared/cache，不spawn、Lean/probe/build/复编或下载原始完整日志。并非独占代码库，保留他人编辑。承认已审声明上下文存在，本次仍先只提取actual两个公开定义完整体和两个完整类型，独立重新盲译并先落盘，尚未读实际proof/private/generated或机械证据。

## 第一阶段：actual两个full body与两个full type盲译

实际输入 NormalTrialCost.lean，SHA256 `8fb184ac4cf75e4f1c64e615b5c94c1a5f16c39109709a8f5dbc7fe2c5406895`，7121字节/145行。

`normalTrialTilt(mu,y,z)`：令实际S=normalVariance mu、实际T=transverseVariance mu、b=同mu Cov(normalValue,X)/S，返回实对(y/S−b*((z−by)/T),(z−by)/T)。定义对任意mu/y/z按实除法总化，无概率、非零或实际矩阵逆定理门；proof必须在真实S/T正后解释系数。

`normalTrialCost(mu,q,a,y,z)`：同一trial对的第一/第二分量分别乘y/z，相加后减同一mu和q/a中心下该trial参数处的真实centeredNormalLogMGF。它是显式单点试验值，不是Legendre上确界或最优值定义。

`exists_normalTrialCost_cubic_lower`：真实mu概率、hb AE有界、固定q/a和同mu真实E(Y)=q、EX=a、actual S>0以及actual parabolaCovariance.det>0之后，∃D>0和radius>0，先于全部实y/z。闭l1球|y|+|z|≤radius内，同时输出实际trial exp投影的真Integrable、真实积分严格正，以及actual profile(S,T,b,y,z)−D(|y|+|z|)³≤actual trialCost。未要求q>0、ell、阶段、原子性或b符号；S/T正与实际完成平方绑定必须后核。

`exists_normalTrialCost_weight_margin`：同一mu概率/hb，固定q/a/ell，q>0、ell≥0、两个真实均值门、actual S>0及actual parabolaDet>0，严格ell<q/(32*actual T)。之后∃同一delta/gamma/c均>0，先于全部自然n≥1、任意非负实k与signed实r；小比值k/n、|r|/n≤delta和nqk/16≤r²时，gamma*k+c*r²/n≤n*actual trialCost(mu,q,a,−k/n,r/n)−ell*k。n0排除，k不必整数，k/r不需非零，参数和中心不变。

必须核actualQ对偶式的1/2因子、共同L/D/radius先于全部y/z、真实试验exp/Z正、次目标将I真取actualcost后的全部hI门和统一n/k/r量词。不能用函数名、任意自由系数或作者绿灯替代。同一S/T逆所需正门不能省略；b/y/z零与ell0、n1等仍合法。完整定义的总化不等于定理的概率解释。

本盲译先保存。后续scope/R1→全145行/2private/alllocals/实际协方差与库→全部actual TYPE含生成eq_1→机械LAST。实际Legendre/概率Chernoff/紧族uniform、LLT/hW及根A/B/C/D均OPEN。

## 第二阶段：冻结文本、来源与实际承重接口

盲译先落盘后才读取完整scope、R1及全部actual实现。scope SHA256 `7fbbd6d73fb40cec315795bccf9af7655063576ffc722cf7ea5477f6abafb676`，已接受声明票SHA256 `5cce198f3be7e45865de731c8bf318a0b03c039b413d326a4eede02d4753a0e6`。本次独立提取两公开定义完整体和两目标完整类型，分别去空白与冻结fence核对，四项均相等；两条imports、namespace/open及noncomputable一致。

真实R1路径 `C:/game/shao/current/oq3/proofs/r1/report.md`，SHA256 `3473d34ff20bd0d334b9ef3ea3c3ee167fba4d5cc3a742849820ce54d639e662`，本次直接核350–383行。351行真实K_c、353–355行试验优化、370–371行inverse-covariance代价以及378–383行曲边局部余量，支持当前标准显式试验充分路线。actual normalTrialCost仍是一个具体试验值，不是已构造来源Legendre I；没有据此把(16)概率、全局唯一性或紧族质量常数记为完成。

实际已完整接受的CenteredLogMGF.lean SHA256 `1fb9f7b4ca976c02f5f100161da811738a443d75c47c72c2e274de54d9fb90f4`56–64行完整接口已再读：同一mu/hb/q/a及真实两均值给共同C/delta>0，在全实v/s闭l1球内同时输出真exp Integrable、真实Z>0和K_c≤actualQ/2+C*l1³。实际LocalRateMargin.lean SHA256 `5e0e4f9ebb0dc514e0b55b9ed3aa7e5a9e8b9c128fdda2edfd2257bc3ad70a77`49–60行完整接口给明确hI条件后的统一n/k/r余量，正是本代码后段消费的类型。两完整独立终票分别 `7dd7ce4fe20dc562fb4dfdc95683e067164f5ec1405479d838a9682c4859308e`、`a536247a23c01140ca82f79bcc72156081d92106ee2feea0dbf2234cf83f8169` 已接受；不重编旧目标。

实际RegularCovariance.lean SHA256 `0add3476cc949edc593e15dc195934a6df78a41a55f4a2281f66095733d4c853`29–30行T=parabolaCovariance.det/normalVariance，因此hD/hS直接给T>0，不需误用另需hbase的transverseVariance_pos。实际NormalTangentGaussian.lean SHA256 `d2c55bf4d7a371c9b43cd3c75eab8ece8b3c7caa21aa4827bf19c24b4c7cac39`67–75行在真实mu概率/hb/hS下给actual Q=S(v+b*s)²+T*s²，b正是同mu Cov(Y,X)/S，T正是det/S。该已接受接口通过真实normal_tangent_covariance_det绑定(Y,X)与parabola(X,X²)协方差，hb给实际矩/L²，不是任意det>0或variance总化。

## 第三阶段：全145行actual proof、两个private与所有locals

本独立数学判断先于Audit TYPE/receipt读取并先落盘。第1–18行两导入、两个公开定义完整体与冻结一致。normalTrialTilt使用同mu实际S/T/b，normalTrialCost使用同mu/q/a和实际log积分；全函数总化没有被当成概率门。

### private trial_parameter_bound（20–52行）

泛型S/T>0、b/y/z任意。23–26行u=(z−by)/T、R=|y|+|z|≥0，且|y|≤R。27–33行保留带符号b，三角不等式给|z−by|≤|z|+|b||y|；与(|b|+1)R的差正是|y|+|b||z|≥0，因此hznum正确。34–40行只在T>0后将绝对分母改T、保持除法不等式方向，得|u|≤((|b|+1)/T)R。

41–43行同样在S>0后给|y/S−b*u|≤|y|/S+|b||u|。44–50行相加并用正/非负系数控制两项；51行精确归并为[1/S+(|b|+1)²/T]R，52行仅加R≥0得到L=该系数+1的界。没有除b/y/z/u或假设b、y、z正，R0时依然有效。此为全局固定线性映射系数界，非逐点算子范数选择。

### private trial_quadratic_duality（54–60行）

完整类型保留generic S/T>0，用试验参数v=y/S−b((z−by)/T)、s=(z−by)/T的dot，减[S(v+bs)²+T*s²]/2，等于实际公开gaussianRateProfile(S,T,b,y,z)。58行展开真实profile，59行只凭S/T非零清分母、60行ring。独立代数验算：v+bs=y/S，dot=y²/S+(z−by)²/T，完成平方二次值也等于同一数，故减其一半恰为profile，1/2因子和两个参数坐标准确。没有在这个private泛型恒等式内部假装完成actual协方差绑定；main后面另行真正rewrites actualQ。

### 首目标真实正性与共同窗口（75–106行）

75–78行S/T/b全部取actual同mu值，hT通过actual T=det/S以div_pos hD hS得到，非新增hbase/原子假设。79–80行L=1/S+(|b|+1)²/T+1是真正数，b0和signed b都允许。81行在同mu/hb/真实q/a均值门下先取得U16d共同C/delta。82–86行先固定D=C*L³>0、radius=min1(delta/L)>0并返回这两个见证，87行以后才任取y/z，量词顺序合法。

88–93行v/s是真实normalTrialTilt分量，R=|y|+|z|；实际private全局界经明确展开actual S/T/b/L/R得到htilt。94–99行用radius≤delta/L和L>0先得radius*L≤delta，再将同一hyz乘L≥0，得到|v|+|s|≤delta。不是把各分量单独小误当l1球，也不逐y/z换delta。

100行消费U16d的完整三个真实分量hE/hZ/hupper，hE正是trial实指数的真可积，hZ正是同一实际积分Z>0；没有log0/不可积积分0。101–106行以非负参数范数和htilt作三次幂单调，再乘C≥0，真实得C(|v|+|s|)³≤D R³。C/D/L的正门和乘法方向保持，未对signed y/z清非零。

### actual二次型与下界方向（107–121行）

107–111行先真正以 `normalTangentQuadratic_complete_square mu hb hS v s` rewrite actualQ，再将actual同源S/T/b和trial分量展开，才调用泛型private duality。故hdual确为actual dot−Q/2=actualprofile，未仅靠改名自由系数跳过协方差语义。

112行返回actual hE/hZ；113–114行展开actual trialCost和R。116–120行由herr Cnorm³≤DR³，减较大误差给较小下界，sub_le_sub_left方向正确；121行再由真实K_c≤Q/2+Cnorm³，反向减去较大上界，得到profile−DR³≤dot−K_c=actualcost。两次减法均已独立核号，没有错将log上界当下界或遗漏dot/2。

### 次目标actualcost实例化（136–142行）

136行再次以actual hD/hS直接得T>0。137–138行首目标在同mu/q/a和真实中心给D/radius>0和全ball三分量。139–142行实际调用U16c的S/T/b是本mu真实值，q>0、ell≥0、S/T>0、D≥0由hDpos.le、正radius和actual hgap逐项匹配。I明确取normalTrialCost mu q a；hI是 `(hlower y z hyz).2.2`，正是首目标第三分量对所有合法点的下界，而非仅固定方向或部分点。该调用直接输出同一delta/gamma/c先于全部n≥1/k≥0/signed r的完整目标，未更换q/a、16/32因子或隐藏n0除法。

边界检查：y=z0时trial0、真实exp1/Z1/log0、cost/profile/误差全0；z=by、b0、任一坐标0都不触发被约掉分母。S/det严格正排除完整协方差退化，本单元不声称U16d的所有退化mu也满足逆型trial门。ell0、k/r0及n1由U16c完整已审门真实覆盖；r可负、k是实数非负，不误限为整数。若r0，正n/q与事件约束迫使k0，实际原点下界有效。

全部145行、两个private、所有locals与消分母/符号/量词步骤已审；数学阶段结论CORRECT。normalTrialTilt.eq_1及是否有其他generated留待实际枚举读取，不根据作者数量预猜。

## 第四阶段：实际固定库和继承语义

本次指定服务器只读再次核actual被消费接口；Mathlib Algebra.Order.Field.Basic SHA256 `fabd3062223bbdcd4efae38a4a586f88241f67da533e79ee06c56ba507c27b2d`673–674行abs_div，GroupWithZero.Basic SHA256 `28c0432242f3766a643689abd852cbf92fee391d314f76815e6977e64854103c`874–878行div_pos/div_nonneg、1128–1141行正分母比较以及1193–1195行div_le_div_of_nonneg_right的真实非负分母门，与private及radius计算吻合。真实field_simp只在S/T≠0处使用；标准abs_mul/三角、pow_le_pow_left₀、sub_le_sub_left均保留相应非负或反向减法门。

实际logMGF真可积、正Z及中心矩的继承语义由已完整接受U16d/NTMoments提供，actual Q完成平方由已完整接受U12b提供，真正generic hI曲边代价由已完整接受U16c提供；本代码各次调用完整同源参数如上。没有新增Fubini/DCT/总化Legendre上确界或概率率假设。以上先保存，再读全部actual TYPE，作者receipt/机械仍最后。

## 第五阶段：全部7个actual owned TYPE及真实生成方程

数学阶段先落盘后，从真实现有Audit.log只过滤DECL/TYPE与全部长续行，未先读AXIOMS/PASS/receipt。实际七项逐项核查：

1. `Shao.OQ3.exists_normalTrialCost_cubic_lower`，实际第2–30行所有续行完整读取。真实mu概率/hb/q/a/两个真实均值/actual S和det正之后，∃D/radius>0在全部y/z之前；同一真实trial参数exp的真Integrable、严格正真实积分和actual profile减三次项≤actualcost三分量齐全，实际S/T/b、中心及参数次序与冻结/actual一致，无隐藏q>0或额外正原子门。
2. `Shao.OQ3.normalTrialTilt`，第33行完整TYPE `Measure ℝ→ℝ→ℝ→ℝ×ℝ`，对应mu,y,z；无隐藏正性、概率或方向门，完整定义体已先独立审查。
3. `_private.Shao.OQ3.NormalTrialCost.0.Shao.OQ3.trial_parameter_bound`，实际第36–37行完整TYPE：S/T>0、b/y/z任意，trial两分量abs和≤[1/S+(|b|+1)²/T+1](|y|+|z|)。正分母门和完整系数L准确保留。
4. `_private.Shao.OQ3.NormalTrialCost.0.Shao.OQ3.trial_quadratic_duality`，实际第40–45行完整读取。泛型S/T正之后，dot减真实S(v+bs)²+T*s²的一半，等于profile；负号、两个坐标和1/2因子精确，未藏actual协方差或Legendre假设。
5. `Shao.OQ3.normalTrialTilt.eq_1`，实际第48–55行每一续行完整读取。对全部mu/y/z，无前提地展开let：第一分量为 y/normalVariance−[Cov(normalValue,X)/normalVariance]*[(z−[Cov(normalValue,X)/normalVariance]*y)/transverseVariance]；第二分量为同一个括号后的(z−b*y)/transverseVariance。两分量未交换、未错用b或T、无掉负号/乘y；这只是actual定义的let展开，在总化实除法下也成立，不是零S/T时的矩阵逆断言。main在真实正S/T后使用其数学解释。
6. `Shao.OQ3.normalTrialCost`，第58行完整TYPE `Measure ℝ→ℝ→ℝ→ℝ→ℝ→ℝ`，对应mu,q,a,y,z后输出real；定义体已审为同一actual trial的dot−actual logMGF，TYPE本身不推断Legendre性质。
7. `Shao.OQ3.exists_normalTrialCost_weight_margin`，实际第61–83行全部长续行完整读取。真实mu概率/hb、q/a/ell、q>0/ell≥0、同一两均值/S/det/hgap之后，∃三正见证再∀n≥1、实k/r、k≥0、小比值和16因子事件，结论是真实actualcost在(−k/n,r/n)处的权重余量。32/16、减ell*k、signed r与全n/k/r前的量词均匹配。

真实inventory为2公开def、2公开theorem、2 authored private theorem及1 generated等式，共7owned/5theorem；没有其他生成项。该结论来自实际枚举并完整读续行，不凭作者预计数量推测。类型阶段结论CORRECT；随后才读取实际Audit覆盖/公理和作者机械证据。

## 第六阶段：最后读取的真实机械证据与12源绑定

全145行数学及全部7个actual TYPE先完成并落盘，之后才读取本地/真实远端receipt、Audit源码/公理/PASS、现有build/olean和真实闭包/pins；作者机械门与本票独立数学裁决分离。本次未执行Lean/APIprobe/任何成功目标或Audit复编，未下载原始完整日志。

- actual本地、远端worktree `Shao/OQ3/NormalTrialCost.lean` 和run冻结快照均7121字节/145行，SHA256 `8fb184ac4cf75e4f1c64e615b5c94c1a5f16c39109709a8f5dbc7fe2c5406895`。真实源无CR、尾空白或sorry/admit/axiom/unsafe/implemented_by/extern。两完整定义体和两完整类型已由本审查独立去空白比较冻结fence而一致，不只采信receipt的PASS；两个import未变。
- 冻结scope两端SHA256 `7fbbd6d73fb40cec315795bccf9af7655063576ffc722cf7ea5477f6abafb676`，已接受声明票两端 `5cce198f3be7e45865de731c8bf318a0b03c039b413d326a4eede02d4753a0e6`。本地/真实远端receipt均4516字节，SHA256 `c7962583e0697d73ba422cbbe35bbae4372da8e237a22ac9944f3eba43505d07`；pending/No U16e commit PR是author-check当时历史状态，不误作本次完整裁决。
- 真实build-01.log为0字节，SHA256 `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`。作者保留回执记录命令 `lake env lean -o .lake/build/lib/lean/Shao/OQ3/NormalTrialCost.olean Shao/OQ3/NormalTrialCost.lean` exit0；空文件自身不独立证明退出码。目标实际olean存在，2258984字节，SHA256 `f84c34e18870a28e4c56e7045d7738cf3c8bf1f9b9aac25c9e2a1eb8979ebe61`，未复跑成功构建。
- 真实Audit.lean为1710字节/39行，SHA256 `94bf4339db6afbc92b6ffae6b6714cde8bd85374d9024e6bffc791db81fe08d4`，全文核读：核两个target的isTheorem、两定义的defnInfo，再遍历四个完整stem和整个 `_private.Shao.OQ3.NormalTrialCost` 前缀。拒绝每项isAxiom，用Lean.collectAxioms核全部传递依赖，仅白名单propext/Classical.choice/Quot.sound，覆盖含真实eq_1而非只查两公开目标。
- 真实Audit.log为4689字节/88行，SHA256 `1bf0914c5b2cd9a18a17ba73a13d3b6dc68894caaf92c843b9ad6fdf2173c0c5`。实际输出2 frozen、5 theorem、7 owned和 `U16E_AXIOM_GATE PASS`；7项每项实际AXIOMS均为[propext,Classical.choice,Quot.sound]。全部完整TYPE和eq_1长展开在此前阶段已逐项核查，不以该计数或PASS推断内容。
- 实际branch `feat/oq3-normal-trial-cost`，HEAD `f519386dfb8615853cb824ff747da4c2e51f0e00`，git status仅 `?? Shao/OQ3/NormalTrialCost.lean`。实际toolchain `leanprover/lean4:v4.36.0-rc1`，lean-toolchain SHA256 `d581a24b57a4ae9e0b2132ca8ac7cc3ac336a9fc2751fe6b29414e2d434d54c4`，lake-manifest.json SHA256 `40e8e3385f2b0c8ae56fa9de6947301472379cb62eeb83247944827c38b8af6e`，manifest pin与真实mathlib HEAD均 `807d3836b165983210ee2ecf3cd28f239436949c`。

从actual目标源码递归解析Shao imports，实际恰好12份传递前置；路径集合与receipt一致，每份实际SHA逐项MATCH，12份既有olean全部存在。真实prerequisite-hashes.json为1243字节/14行，SHA256 `79d0710518088524fdc46d2d4e65fa1f1cd577ac3bb37ee441bfb803a5c69470`，实际内容程序核对与receipt完全相同。实际各源值如下（共同Shao/OQ3前缀省略）：

| 实际前置源 | SHA256 |
| --- | --- |
| AtomicMeasure.lean | `59ddc48fb7b395f362939e58cbd9d7911685a6ed6e6574142e8a6d4ab3ee0c39` |
| CenteredLogMGF.lean | `1fb9f7b4ca976c02f5f100161da811738a443d75c47c72c2e274de54d9fb90f4` |
| FiniteConstraints.lean | `800d9db8cb6749a31ecfe611409de92b10ea8bb2aef955bfd825ede7324f0ef0` |
| FiniteStageMeasure.lean | `1a32fb904e6ee9d2b0b48d92c4ebb3568452bb02500ce52a1a03eb01ae0256b1` |
| InverseTilt.lean | `c7e7d19e8b70481b663bec1fd12ea9301d73313faaf35997e85aa9ba99f21811` |
| LocalRateMargin.lean | `5e0e4f9ebb0dc514e0b55b9ed3aa7e5a9e8b9c128fdda2edfd2257bc3ad70a77` |
| NormalTangentGaussian.lean | `d2c55bf4d7a371c9b43cd3c75eab8ece8b3c7caa21aa4827bf19c24b4c7cac39` |
| NormalTangentMoments.lean | `8cee48bc8f519f72b218a2ef80685d946a6debaea8b723af38a49c5bdca12cc1` |
| PositiveRate.lean | `8e727078d3a4f1db2392384b84cc31235ff69efa13dd5e44b23eac818a788f7b` |
| RegularCovariance.lean | `0add3476cc949edc593e15dc195934a6df78a41a55f4a2281f66095733d4c853` |
| SourceStarter.lean | `0e2a081619976f88149707c2ef9311dc909003e61d3d0f7c4e21e6c3dbbc5a6d` |
| SummableAtoms.lean | `0ea4c64fe9ef9b45fbf44d24312771a1dbfbcc5de8448564e3e87bdf17c7178b` |

## 最终完整独立裁决

STATUS: CORRECT

JUSTIFICATION: actual两完整定义体/两完整类型与冻结范围和真实来源的标准显式试验路线相符。全145行证明、两个private、全部locals及7个真实TYPE（含eq_1全部展开）均已核查。actual S/T正性、同mu Q完成平方、1/2对偶因子、共同L/D/radius先于全部y/z、真实trial exp可积和Z>0、误差减法方向均实际成立；次目标将I真取actualcost并提供所有hI门，得到先于全部n/k/signed r的统一曲边代价余量。零/signed边界和正分母合法，12份前置、版本及source/receipt/Audit/build绑定一致，全部owned传递公理在白名单。没有发现需修改的声明、数学、来源、类型或机械缺口。

本票接受actual同mu试验cost的局部三次下界及其确定性负层权重余量；不识别其为Legendre上确界，不证明实际Fenchel/逆Hessian、尾试验符号、真实iid换测度、概率Chernoff(16)/(17)、紧倾斜族统一质量界、全局唯一性/远区gap、完整(19)/LLT/hW/WC/KL/根闭合，不声称最优性或新颖性。实际Legendre、概率Chernoff、紧族uniform、LLT/hW及根A/B/C/D均保持OPEN。只写本新报告与授权副本，不改实现/scope/旧票/shared/cache，未spawn或复编。
