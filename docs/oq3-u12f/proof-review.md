# U12f CentralFourierIntegral 完整独立证明与来源审查

## 第一阶段：actual一定义与三个完整公开类型盲译（先落盘）

本节只从实际CentralFourierIntegral.lean提取公开定义体、三个完整类型及导入/作用域，在读取本次scope/R1、实现/局部辅助及receipt/Audit之前落盘。实测source SHA256=`4999d8148c1ee1ba50f61d6d19c40aed239cd001d76ee71f133d1a064c668a93`，144行。actual导入NormalTangentPowerLimit、NormalTangentDomination、Integral.DominatedConvergence；namespace Shao.OQ3，open MeasureTheory Filter。此前声明上下文存在，本次仍从actual独立重新翻译。

定义centralFourierIntegrand(mu,q,a,delta,s,d,n,v)：在闭增长窗口[−delta sqrt(n),delta sqrt(n)]上为exp(−i v d(n)/sqrt(n))乘同一actual中心characteristic_mu,q,a(v/sqrt(n),s/sqrt(n))的n次幂，窗口外0。所有随机积分属于mu，外层函数是实频率v到复数；允许delta任意及n0的总化值。

1. centralFourierIntegrand_integrable：任意实际概率mu、任意q/a/delta/s/d/n下，这个完整indicator零延拓函数在显式标准实volume下真Integrable。无hb、真实均值、delta正性或n正性门。
2. centralFourierIntegrand_tendsto：同一实际概率mu、真实AE有界支撑、q/a为actual EY/EX，给delta>0、固定s及全序列实有界d（∃M,∀n,|d(n)|≤M），则对每个固定实v，实际截断复函数沿自然n趋于Complex.exp((−Q(mu,v,s)/2:ℝ):ℂ)。d不需收敛，S/D/Q正性不要求。
3. exists_centralFourierIntegral_tendsto：同一mu/hb/真实q/a均值及actual S>0、D>0给一个共同delta>0，在全部s/d之前固定；随后任意固定s及全序列实有界d的真实显式Lebesgue积分趋于sqrt(2pi/S)*exp(−transverseVariance(mu)*s²/2)嵌入ℂ。需始终同一actual Q/S/D/τ²及中心，不能随n换律。

待核144行全部proof/局部/generated、真实连续主体紧窗口可积、n0/negative delta、d/sqrt趋0与cutoff最终包含v、delta与eventual支配量词、滤子版DCT四门/可数基、实复积分与真实Gaussian常数；随后才核全部actual TYPE及最后机械。当前无完整裁决，根A/B/C/D全部OPEN。

## 第二阶段：冻结定义/类型、真实R1及承重语义

盲译先落盘后读取scope SHA=`4059b088d8038323e630d4dc8c694b0138fa22cf4caf338e26b0e7bdebaf97b2`、statement SHA=`8889d6be125cb81c7c8ec9162fb6599db44872d954ea8cbfeed6879555886a72`及真实R1 309–345，实测R1 SHA=`3473d34ff20bd0d334b9ef3ea3c3ee167fba4d5cc3a742849820ce54d639e662`。actual定义体和三个完整类型与冻结接口一致。源315/318/335–343要求同一mu的EY=q、EX=a和sqrt尺度中心characteristic；324的有界层位移对应这里负Fourier相位。这里只证明已缩放中心积分的极限，未引入格距或反演的外部归一化。

承重前置已读取实际定义/类型/证明：FiniteFarArc 50–65在任意实际概率mu下用真实可积常数1及phase norm1取得联合频率连续性，未要求随机矩；NormalTangentPowerLimit 137–192给同一mu/中心、每个固定v/s的真实点态n次幂极限，内含合法eventual n>0处理；NormalTangentDomination 262–308给∃delta/c>0先于s、随后eventually n、全部v增长窗口内的Gaussian界。两者完整独立票SHA分别`96b2dfc6293e571e91a969aa7f2f07dc758989ea2fb22238f3b7cfa99f978841`、`3f20da936f2d35e0cd9558ccb0d46768dcb28e9434e0b6604031f6cc1cc479b9`已完成，不以这些票代替本次实际消费条件的审查。

NormalTangentGaussian的Q为actual Var(Y)v²+2Cov(Y,X)vs+Var(X)s²；normalVariance=S=Var(Y)，transverseVariance=actual D/S=τ²。其101–121在同一mu/hb/S>0下已证明实Gaussian真可积及真实全积分常数。actual project import图已独立递归得到17项目前置并读取本地hash，最后再与真实服务器及receipt核对；没有以其他源族或随n变化mu替换这些对象。

## 第三阶段：144行全部proof/局部辅助及实际库的独立数学审查

本阶段先于任何Audit TYPE、receipt/build绿灯。源码144行已全部读，无authored private；各局部have/let均审查。生成常量真实TYPE留待下一阶段单列。

1. **实际定义19–25**：是闭Icc窗口indicator的真实零延拓；内部层位移相位与actual centered characteristic幂都按同一mu/q/a计算。外层v是Lebesgue频率变量，内部随机积分仍是mu，两个measure没有混同。
2. **可积27–48**：hchar用实际joint频率连续性与固定n的线性频率映射复合；hbody是连续复相位乘连续char的自然幂。47用hbody.integrableOn_Icc在真实紧Icc上给真IntegrableOn，48再以measurableSet_Icc给indicator全空间真Integrable。没有声称indicator在边界连续，也没有把norm≤1当成无限volume上的全局可积。实volume在紧集有限，实际库所需IsFiniteMeasureOnCompacts满足。

   delta<0且n>0时窗口为空；delta=0为单点支持；n0对任意delta都是{0}且主体为1，Lebesgue积分0。连续性/IntegrableOn/indicator证明统一覆盖这些情况。固定n的除以sqrt(n)只是乘一个总化实常数，0分母时也连续；本证明没有作sqrt非零消去。
3. **点态50–96：真实norm squeeze**：57取明确全序列界M。58–61从sqrt(n)→∞得到倒数趋0，允许合法总化初值。62–67对每个n用abs_div、abs_mul、sqrt_nonneg及逆非负得到真实范数界≤(|v|M)/sqrt(n)，包括n0。给定hM n本身已足以支持乘法不等式；不假设d(n)收敛，亦不需要M另显式严格正。68–71该真实上界趋0，通过norm squeeze得到v d(n)/sqrt(n)→0。所有新局部恒等式在0分母也成立，无field_simp、inv_mul_cancel或非法sqrt除法。

   72–78由实到复及指数连续性给负层相位趋1。79–85调用同一mu/hb/q/a/hq/ha和同一固定v/s的U12d幂极限，乘法极限得连续主体的Gaussian极限；S/D正性无须加入。86–93用delta>0和sqrt趋∞，将固定v最终放进真实Icc；这里只除以正delta。94–96以eventual equality去掉cutoff，正确允许该点态阈值随v变化。hd始终是实际全序列界，没有把未形式化的O(1)初项补界暗中消费。
4. **共同积分98–134：量词与filter DCT**：109–112从同一mu/hb/真实中心/actual S/D正性选delta/c，refine delta先于intro s/d/hd，故半径不依赖后来的s/d。113–116将每项真Integrable转成all n的AEStronglyMeasurable，再提升为eventual门。117–128先从hlocal s取得一个在全部v外的eventual n门；对该n再ae_of_all v。窗口内，norm_mul和实际phase norm1后，准确使用hn v及由真实Icc成员推出的|v|≤delta sqrt(n)；窗口外indicator0≤exp(−c v²)。阈值不是逐v选取，也未冒称全n共同支配。

   129–132将目标2的每个v点态极限提升为AE v极限。133–134用的是实际tendsto_integral_filter_of_dominated_convergence，四个门依次为hmeas、hbound、以c>0给出的真实Lebesgue Integrable Gaussian、hlim。atTop:Filter ℕ的IsCountablyGenerated实例由Countable ℕ提供，基可取各Ici N。故库eventual版适用；没有误用要求∀n支配的序列版。
5. **实际常数135–141**：实指数嵌入的复指数通过Complex.ofReal_exp逐点成为真实实Gaussian的嵌入，再用integral_complex_ofReal和actual integral_normalTangentGaussian得到所列常数。源内未另写一个real-Gaussian Integrable have，但这不造成总化漏洞：当前同一mu/hb/hS满足已独立核实的U12b normalTangentGaussian_integrable（101–109），且上一步真实共同Integrable bound和AE点态极限也控制该复极限。实Gaussian和复嵌入均真实可积；hvalue的转换不是对一个不知可积的形式函数凭数值猜积分。

   actual S=Var(Y)>0，D=det Cov(X,X²)>0，τ²=D/S。U12b完整平方、真实正S/2 Gaussian和平移不变Lebesgue积分已给sqrt(2pi/S)*exp(−τ²s²/2)，是τ²而非τ。所有矩、中心、Gauss及volume始终同一对象，未替换任意形式矩阵或错误测度。

**边界与范围**：n0的单点零体积不影响atTop极限，且本单元本地从未要求消去sqrt0；U12d/U12e只在其真实最终正n门后使用相关消去。第二目标可退化Q=0，第三目标以S/D正性取得可积支配。d无需格点可达或自身收敛，只有显式hd被消费；没有隐藏有限初项补界证明。这里的delta对全部s/d共同，pointwise阈值可随v，domination阈值必须在v外，actual代码严格区分。

**固定库只读核验**（指定服务器，无Lean/API探针/新构建）：

|API|实际条件及SHA256|
|---|---|
|Integral.DominatedConvergence 68–75|countably generated filter；eventual AEStronglyMeasurable、eventual AE共同bound、真Integrable bound、AE点态Tendsto。`56394aacfe591230d26a1d93641f2a1d3e3a3eae4fcfe772775533a1da295833`|
|Function.LocallyIntegrable 568–597|真实紧集可测/有限measure下连续函数IntegrableOn，595–597给Continuous.integrableOn_Icc；实际volume满足紧集有限。`a100190a7214f8976974c9c2856c7f411ba8e3bb46ef8bf7965fbcf1c00e649c`|
|Integral.IntegrableOn 340–350|可测Icc下真实IntegrableOn→indicator真Integrable。`d1108ec5e836af0af6bc62c8ad5dd94a371dbc8df3e51698049d51221b3663c2`|
|GaussianIntegral 115–117；Bochner.ContinuousLinearMap 158–163|c>0给exp(−c v²)真可积；实际实到复积分转换。SHA分别`4378f161cf5d482be77941cc9aea0195d2e83fe54eeb51b2ab33db1a318ccb9c`、`272fbf423443f1cd4aa032396f85a19c2f4f80b9fe9df655de16b0df655a22c3`|
|Lebesgue.Basic 87/124|volume Icc=ofReal长度，单点volume0。`4955d3400a03ba9d525206fcf1cff8592497dfff06674ca13d68d3bdcabb964d`|
|Topology.Algebra.Order.Field 75–79|inv在atTop趋0，可与真实sqrt→∞复合，无逐n非零假设。`35482bce0fa30cac4daa22bc80dad118f4bc912a9604086f349c2ff41b4c0e32`|
|Order.Filter.AtTopBot.CountablyGenerated 32–35|真实instance [Preorder α] [Countable α]→(atTop:Filter α).IsCountablyGenerated，实例化ℕ。`3c1d68629ce12667363796008d575e8289344ffface525bafae8e9db5e57b909`|

独立数学阶段判断：全部144行实际实现及局部辅助未发现需要修订的数学、来源或量词缺口。本判断在任何Audit TYPE、receipt或机械绿灯前落盘；实际generated TYPE与最终绑定仍待后两阶段。根全部OPEN。

## 第四阶段：全部8个actual owned TYPE逐项核对

数学阶段判断落盘后，仅从真实服务器Audit.log读取DECL/TYPE和全部续行，没有读取receipt/Audit源码/公理结果/build。按actual枚举顺序：

|序号|实际常量|完整TYPE核对|
|---|---|---|
|1|centralFourierIntegrand_tendsto|同一mu概率/hb/真实EY=q与EX=a，delta>0，固定s及全序列有界d后，对每个固定v的真实截断函数趋于exp(−actual Q/2)。完整续行和量词均一致，无S/D或d收敛门。|
|2|exists_centralFourierIntegral_tendsto._simp_1_3|∀x:ℝ，Complex.exp(↑x)=↑(Real.exp x)，真实实到复指数兼容，对全部实x正确。|
|3|exists_centralFourierIntegral_tendsto._simp_1_2|任意Preorder，(x∈Icc a b)=(a≤x∧x≤b)，与实际支配证明的窗口成员转换相符，无假定a≤b。|
|4|exists_centralFourierIntegral_tendsto|完整TYPE保留mu概率/hb/两均值/actual S>0/D>0；∃delta>0在∀s/d及hd之前，真实volume积分趋于同一S/τ²常数的复嵌入。所有长续行已读，无格距/反演系数或另外mu。|
|5|centralFourierIntegrand.eq_1|生成定义等式，∀mu/q/a/delta/s/d/n/v，将实际函数严格展开为Icc(−delta sqrt n,delta sqrt n)的indicator，主体为负层位移相位乘同一实际characteristic(v/sqrt n,s/sqrt n)^n；与actual定义体逐项完全一致，无额外概率/正性假设。|
|6|centralFourierIntegrand|Measure ℝ→四个实q/a/delta/s→实序列d→自然n→实v→ℂ，参数数目、顺序和返回类型与定义一致。|
|7|centralFourierIntegrand_tendsto._simp_1_1|同样任意Preorder的Icc成员等式，供点态窗口证明；正确且不添加端点顺序门。|
|8|centralFourierIntegrand_integrable|任意实际概率mu、任意q/a/delta/s/d/n→该实际函数对实volume真正Integrable；无delta/hb/n正性等隐藏改变。|

实际1定义、3公开定理、4生成定理（一定义等式、两个Icc成员simp及一个实复exp simp），共8 owned/7 theorem，零authored private。不是预猜生成项分类；全部TYPE包括生成定义等式的完整主体均已核。下一阶段才读取作者机械凭据。

## 第五阶段：最后读取的作者凭据与真实机械绑定

前述独立数学及全部actual TYPE判断落盘后，才读取本地U12f-receipt.json和真实服务器receipt/Audit源码、公理/计数结果、build元数据。作者receipt的状态为AUTHOR_KERNEL_AND_AXIOM_CHECKED_AWAITING_INDEPENDENT_PROOF_REVIEW；作者门与本报告的完整独立判定严格区分。

实际worktree=`/root/rivermind-data/shao-lean-20261021/workspaces/lead-oq3`；run=`/root/rivermind-data/shao-lean-20261021/runs/oq3/u12f-20261021`。实测branch=`feat/oq3-central-fourier-integral`，HEAD=`e82928fdeba6b627f86a9644b1d1cf278cacf61e`，git status仅`?? Shao/OQ3/CentralFourierIntegral.lean`。共享broker只读连接的原SSH host key SHA256=`+IZMFu9Xx6FSAhvQhtvZ3MpV70v2d+XNWcequAbsp+c`。

|产物|实际SHA256/事实|
|---|---|
|本地源码、worktree源码、run源码快照|均`4999d8148c1ee1ba50f61d6d19c40aed239cd001d76ee71f133d1a064c668a93`，7939 bytes、144行|
|本地与run scope.md|均`4059b088d8038323e630d4dc8c694b0138fa22cf4caf338e26b0e7bdebaf97b2`|
|本地与run statement-review.md|均`8889d6be125cb81c7c8ec9162fb6599db44872d954ea8cbfeed6879555886a72`|
|本地及run receipt.json|均`c7712d3de5889ed584a6efbd94f7cc229b264be37c671e6f31af4df709c7254f`，4585 bytes|
|真实Audit.lean|`f0e321a7a307e55e6b7415ef7e30c43bd4a842ae53c9bf33a746b5addf7bd952`，1589 bytes|
|真实Audit.log|`62c55cac485b0373ea575926e3621cd928e7655fbed2e4483465d0df8ea41c75`，3345 bytes|
|真实build-03.log|0 bytes，`e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`|
|实际已有CentralFourierIntegral.olean|存在，185848 bytes，`d12d4899732517fa0f360cd9029720256752fb0e5b27cedc1b11bc5a6fab725f`|

Audit源码完整读取：逐项核三冻结目标存在且isTheorem；枚举四公开stem完整前缀和整个`_private.Shao.OQ3.CentralFourierIntegral`前缀，拒绝新axiom，并为每项collectAxioms检查完整传递依赖。与全部源声明/生成TYPE对照，覆盖完整。实际日志为FROZEN_THEOREMS=3、ALL_THEOREMS=7、ALL_DECLARATIONS=8、AXIOM_GATE PASS；8项AXIOMS逐项核，序3/7仅[propext]，其余6项均[propext, Classical.choice, Quot.sound]，无白名单外公理。

receipt记录已有build与Audit命令退出码均0；本次核真实空build日志、实际Audit结果、源码/olean和pins，没有重新执行成功target或Audit，也没有下载完整原始日志。一定义体和三个完整公开类型经独立去空白文本比较与冻结scope逐项匹配；源码LF无CR、无尾空白，sorry/admit/axiom/unsafe/native_decide/implemented_by扫描为空。

数学阶段已独立读取实际17项import图；最后与receipt对照时，本地与真实服务器各源重新hash均一致，真实服务器的import递归闭包也恰好同一17项：

|项目前置|两端共同实测SHA256|
|---|---|
|AtomProjection|`0d369052c7f87122765612efdeaca5d9ac71abca861e7785c86d1f9edcc74d22`|
|AtomicMeasure|`59ddc48fb7b395f362939e58cbd9d7911685a6ed6e6574142e8a6d4ab3ee0c39`|
|FiniteConstraints|`800d9db8cb6749a31ecfe611409de92b10ea8bb2aef955bfd825ede7324f0ef0`|
|FiniteFarArc|`3a0b05d0789e53320009a44499c9c40d0fb3d892427085052c65c04456b6cf71`|
|FiniteNormalSpan|`0374da4860edf8af8bbbb9172e4e93bfe9b6c37ac57672b85a4f58392475b7de`|
|FiniteStageMeasure|`1a32fb904e6ee9d2b0b48d92c4ebb3568452bb02500ce52a1a03eb01ae0256b1`|
|InverseTilt|`c7e7d19e8b70481b663bec1fd12ea9301d73313faaf35997e85aa9ba99f21811`|
|JointNonlattice|`51ce939232610353215fc3b7377e19b894451a9a108125e1828bf2fe8ec81559`|
|NormalTangentDomination|`b65b9f5a9d67e42e611a3841563ac07004e796415c3e5b74f177a8ca80e48e90`|
|NormalTangentGaussian|`d2c55bf4d7a371c9b43cd3c75eab8ece8b3c7caa21aa4827bf19c24b4c7cac39`|
|NormalTangentMoments|`8cee48bc8f519f72b218a2ef80685d946a6debaea8b723af38a49c5bdca12cc1`|
|NormalTangentPowerLimit|`819bd0e801eb0b9adce0fbdbcd6ced6441b04787eb0501b811721933db0e9457`|
|PositiveRate|`8e727078d3a4f1db2392384b84cc31235ff69efa13dd5e44b23eac818a788f7b`|
|RegularCovariance|`0add3476cc949edc593e15dc195934a6df78a41a55f4a2281f66095733d4c853`|
|ResonanceArithmetic|`cd21a264d637bab30fed765bdc25ed09bb4ff56f6efb9c88ee09be4ca6e1648b`|
|SourceStarter|`0e2a081619976f88149707c2ef9311dc909003e61d3d0f7c4e21e6c3dbbc5a6d`|
|SummableAtoms|`0ea4c64fe9ef9b45fbf44d24312771a1dbfbcc5de8448564e3e87bdf17c7178b`|

实际lean-toolchain=`leanprover/lean4:v4.36.0-rc1`；只读version结果Lean 4.36.0-rc1、commit `c9afcddf514a6772bd4d649f7cfc04eff0b9f15e`，Lake `5.0.0-src+c9afcdd`。mathlib实际HEAD及manifest rev/inputRev均=`807d3836b165983210ee2ecf3cd28f239436949c`。实际库条件/hash见第三阶段。

STATUS: CORRECT

JUSTIFICATION: actual定义与三个完整公开类型先盲译落盘，再与冻结scope/真实R1、144行全部proof/局部辅助、所有4个generated及全部8 actual TYPE独立核对通过。真实可积性由连续主体的紧Icc可积及可测indicator得到；有界层位移通过真实norm squeeze除sqrt趋0，固定v窗口最终包含，n0未被非法消去。delta/c先于全部s/d、U12e的eventual支配阈值在全v外，实际filter DCT四门及atTop Nat可数基正确；同一mu的actual Gaussian实复转换和S/τ²常数正确。最后真实服务器源码、17项传递闭包、pins、既有build/Audit和全部传递公理白名单均匹配本次审查对象，未发现需要修订的声明、证明或来源缺口。

本票确认带有界层相位的已缩放中心Fourier积分极限，不把它当作格点反演、格距归一化、条件Lévy、完整混合LLT、实际hW或对角闭合。本次不改实现/旧票/共享文件/缓存、不spawn、不重编成功target/Audit、不commit/PR；根A/B/C/D全部OPEN。
