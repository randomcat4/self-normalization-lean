# 单元184独立完整源码—陈述—证明审阅

STATUS: CORRECT

阶段状态：SOURCE_REVIEW_COMPLETE_MACHINE_PENDING。本结论针对精确源码 `a58b2eecf616fed7c4fcb58ca9019294034d52db2d8260cea34a5a8ca7b5d519`（19001字节、379个LF、UTF-8无BOM、CR为0）。独立阅读没有发现数学关键缺口或冻结陈述漂移。本上下文没有执行Lean、服务器、网络、Git、上传、缓存变更或子代理；本单元的内核、实际所属常量、完整展开类型/非定理值、逐名递归公理仍待父级服务器回执，不能据此报告机械通过或最终QUALIFIED。

审阅者为 `/root/oq56_ghost184_final_review01`，不是本单元作者，也不是Root协调员。规定配置是新上下文gpt-6.1-sol/xhigh；实际模型、努力与细分用量在本工具界面不可见，另存为null。唯一写范围为本目录。作者RELEASE0的SHA256为 `904d42cc43d7e9b0bc0691f83198b5c83986f01fb4a3dd77f2dbd04b56b92f36`，其写者、执行、工具、子代理及锁均为0；未改作者源码或其他所有者工件。

## 精确输入与完整覆盖

已经完整阅读379行实际源码，包括两个私有定理P01/P02、一个公开定理T01的全部声明与证明，以及其显式输入、全部源级局部类型/数据值、分支、嵌入表达式与控制绑定。不是仅审公开头。完整读过作者的source-to-statement-proof、primary-api-conditions、source-declaration-manifest、frozen-scope-read，并用actual-full-scope-read-view对actual-typed-scopes无损重构后逐项对真实源码核对。

已完整阅读冻结declarations-values、Stage1的problem、assumptions、derivation、frozen-theorem-proposal、declarations、declaration-proposal、api-needs、provenance；原typed-scopes的110记录和25嵌入条目，逐项读取完整type/value/rawBinder，以全部135有序context向量和完整前缀重构原rawFullLexicalScope，再与原文件逐字比较。Stage1提案与最终冻结的三个声明对象、prefix/suffix及29公开数据值精确相等。不是将作者自称“found”的数目视为审阅证据。

实际源码的三个完整声明头与冻结头字面相同。作者manifest的完整prefix、三个header/separator/proofBody、suffix重组后与全部实际源码字节相同；每个proofBody的独立SHA也相同。29公开let值逐项对其实际证明局部副本核对，类型和值均相同。没有新增实质数据函数或假设。所有源哈希、依赖资格、主库材料及阅读绑定见input-bindings.json；独立比较见independent-static-check.json。

主API材料完整读取了pair-integral-measurable-primary-source-packet的8文件选定完整声明/范围与其全部顶层结构作用域、294行SpecialFunctions.Basic原源、实幂复用包内全部所用完整声明及其Real命名空间/变量作用域、integral-nonnegative补包与冻结导入路径。locator只作定位，不作完整签名证明。主库绑定为mathlib `807d3836b165983210ee2ecf3cd28f239436949c`。旧导入路径快照中的183初版哈希 `ef6c5a…` 是历史路径证据；本次实际消费的是下述已经qualified的 `9ffdbe…` 版本，未将旧路径快照当作当前183证明资格。

已经完整读取只读p44、p51、p54正文，分别实际核得SHA256：

- p44：`3d6a674252a81b7ca051fd54aa0a621511ebce94af2f0bdf9b4eca8715bc5239`。
- p51：`96920f428b8fc09788a6388103cefe398e3ec739129a5922b984babd09e99359`。
- p54：`e03649e1324def02de3ff234bcc94c9e1cb643e074a324e1817ef940f5e01c43`。

## 作用域元数据的独立补全

作者的两份actual作用域文件彼此确能重构143份rawscope，且源码sourceRaw范围均精确对应实际文本；但“重构成功”没有证明其中每份fullType完整。实际发现：

1. `T01.h182Threshold`（源码206–230）与 `T01.hN0Spec`（274–298）的fullType/rawBinder在内部 `let C : Set Ω := …` 处提前截断。真正的类型包含后续d、ν、条件律事实及全部lam/H/κ/G/σ2/σ/K/Kstd包络链。实际Lean源码没有截断。
2. `T01.instProbν`的元数据rawBinder写成普通let；源码319行实际是letI，必须保留其局部实例语义。

已在本独占目录的independent-complete-source-scope-coverage.json内从完整sourceRaw提取最后一个have赋值分隔符前的真实完整类型，并逐项与冻结完整类型比较；保留真实letI；以补全后的唯一绑定重建全部有序作用域，其中62份后续scope引用了受影响绑定。原作者文件和Lean源均不修改。这些是证据呈现补全，不改变定理、数据值或证明。没有据作者错误的截短类型宣称审阅完成。

另以embedded-and-control-coverage.json保留三个完整头、全部完整围合表达式、源位置、真实外层有序scope、嵌入/控制绑定及两个完整嵌套模板。尤其审了h183Uniform/hC0Spec里局部Ω/μ/Y/n/q的遮蔽，以及h182Threshold/hN0Spec里N0、R、C/d/ν、lam和七个实际残差数据的连续作用域。每个积分/AE/lambda有自己的fresh局部变量；G的内层积分y处于外层o的范围内。RHS使用引入该have之前的上下文，不能把待证明事实放入自己的证明范围。P01两分支不泄露，`clear huv`后只保留huvNot；P02过滤后的z/hfirst/hsecond在hED证明内结束；T01的n/q支结束后lam支不含n、νn、Yn、S或q。

143是这份作者源级命名记录的条数，114是其正则定位的语法命中条数，135是冻结原提案的记录加嵌入条目数；三者都不是Lean实际所属常量总数，也不是全部实际binder总数。本审阅不把这些描述数相互代换。实际模块全部owner数、生成/私有常量和展开TYPE/FULLVALUE数量保持UNKNOWN，等待服务器实际module-index全环境扫描。

## P01：所有正α的点态指数支配

审阅范围是源码15–57，全部实数α,τ>0及u,v≥0。先由add_nonneg得u+v≥0。Real.rpow_two将自然平方换成实二次幂，Real.rpow_mul的前提只有底数非负，所以适用于u+v=0；2·(α/2)=α由实环等式支付。得到 `((u+v)^2)^(α/2)=(u+v)^α`，没有假设u+v严格正，没有在零点错用对数公式。

在u≤v支，u+v≤2v，Real.rpow_le_rpow的三个条件依次为hsum、该底数比较和hα.le。Real.mul_rpow使用底数2≥0和v≥0，指数仍为任意正α。v^α≤u^α+v^α只用u^α≥0。在否定支，由¬u≤v取得v≤u，完全对称地使用2u。没有把凸性估计误用于α<1，也没有加入α≥1或α≤2。u=v=0、单边为0及0<α<1都在同一证明中。

Real.rpow_pos_of_pos给2^α>0。乘以τ/2^α为非负保序，field_simp仅用这个非零分母，实环代数给τu^α+τv^α。Real.exp_add的反向重写只将右侧指数乘积合成exp和；Real.exp_le_exp.mpr再用已证指数比较。故P01确实给冻结的乘积支配。该较松的2^α因子合法，无α≥1偷加。

## P02：真实ν.prodν、先L¹后积分比较

审阅范围是59–102。真实输入ν为任意可测Ω上的概率，v可测且ν-a.e.非负，F=exp(τv^α)真正可积。三个局部函数完整值分别是F、D(z)=F(z.1)F(z.2)、E(z)=exp((τ/2^α)((v(z.1)+v(z.2))²)^(α/2))。

`MeasureTheory.Integrable.mul_prod`的完整签名在NormedRing目标L上要求两个边缘Integrable；紧邻的omit [SFinite ν]仅用于该定理，确实移除了外层SFinite条件。此处L=ℝ、两侧边缘都为输入ν、两次hFint，首先给真实乘积D的L¹（78行）。没有从总化积分数值反推可积。

E的可测性（79–82）按v∘fst、v∘snd、和、自然平方、实α/2幂、常数乘法和exp逐步复合。Measurable.pow_const需要的自然幂实例与Real.hasMeasurablePow的全实数幂实例均在完整主源中核对；值域ℝ给Borel/可分度量与AE强可测性。即使v在零测异常集为负，E仍是全域定义的可测实值函数。Real.exp_nonneg给E每点非负。

坐标AE拉回的真实全名为 `MeasureTheory.Measure.quasiMeasurePreserving_fst/snd` 与 `MeasureTheory.QuasiMeasurePreserving.ae`；输入p(o)=0≤v(o)，两次hvnonneg，实际源/目标测度分别为ν.prodν与ν。两个坐标定理各自omit hν，无额外空间结构假设；不使用记忆中的不存在ae_fst等名字。交集上P01给E≤D。此后Integrable.mono_nonneg以hDint、E的AE强可测、AE非负、AE支配给hEint（92–93）。

`MeasureTheory.integral_mono_ae`真实需要两侧Integrable，98行显式提供hEint/hDint及hED。`MeasureTheory.integral_prod_mul`则是RCLike目标的真实乘积积分恒等式，原文件此处需要SFinite μ与SFinite ν；此处两侧均是已给概率ν，通过概率→有限→SFinite支付。它没有L¹前提这一点未被拿来省略本证明自己的L¹支付。最后平方只是同一真实边缘积分乘自身。没有自由因子分解合同、配对可积性假设或配对矩上界假设，也没有标准Borel、无原子、可数生成或Nonempty Ω加强。

## T01：来源、固定常数与实际条件鬼样本

审阅范围是104–374。公开输入完整保留182的原核h、真实投影、原L²、对称、中心化、投影二阶矩1、可测w及μ-a.e.w≥1、原exp(τw^α)可积、真实残差乘积包络、2<p≤3及原投影有限p矩。唯一新增公开前提hαtwo:α≤2早已冻结，并由p44 §3的原适用范围支持。

对182精确源 `c24bb3330f4fb6c384941596f434ef8839af04e9fdb91ce5780081e8dd7168bf` /21227字节，已核父qualified-evidence SHA `48fb70c715211b92ea0b9143835736fd8344164024b43a16dce2c5f8efe16962` 及其独立资格绑定。读取其实际完整公共TYPE（type-006的515行）并与完整源头14–71核对，只复用旧独立完整审阅、内核及逐owner递归公理证据；未重审旧模块证明或重跑检查。

184的g、r、M、W2、Cenv、aenv、wstd、tauStd、Mexp与182返回的值完全相同。198–230行原样传递所有原始实参、提取结论，hαtwo没有被误传为182假设。阈值含同一个原C={w≤R}、d=μ.real C、ν=(μ C)⁻¹•μ.restrict C，未换成{wstd≤R}或抽象条件律。182支付aenv≥1、aenv²=Cenv、tauStd>0、Mexp≥1、wstd可测/L²，以及其统一N0后的全部条件律、边缘指数积分和真实Kstd包络。

从0<α≤2得到β=α/2∈(0,1]；τpair=tauStd/2^α>0；Mpair=(2Mexp)²≥1。Mpair平方比较使用Mexp≥1，未需要额外积分假设。183精确源 `9ffdbe105b2cbdc5552acdc11d8942dd08372e8d55574bd65dcad8c186344470` /67573字节，父资格SHA `a1d033ddcc9da864d965d77e7e2555f9c74d6f12c64b24fad90f43130e265427`，独立资格SHA `e81c3d47330b8fd69661c43170dffe1e00c26c377a0f477eb81c1fc0f583f8e3` 均核对精确字节。只读取消费的T03完整实际TYPE及三def完整实际TYPE/FULLVALUE、当前源接口；旧证明与旧检查按哈希复用。

183的定义实际为scalarMomentScale(β,t,M)=M(tβ)^(−1/β)，sumMomentScale=2·2^(1/β)·scalarMomentScale，coordinateSum(Y,x)=Σi Y i (x i)。239–271的h183Uniform/hC0Spec与T03的全部量词和前提一致：见证常数先于Ω、n、坐标测度、Y和实q。C0=Classical.choose h183Uniform及其相等式只用于把正见证改写成预先固定的Cmom，不引入可随R/lam/n/q变化的常数。N0也仅选择182已有阈值；它位于所有R之前。

固定任意R≥N0后，pairLaw真正定义为ν.prodν；W=wstd∘fst+wstd∘snd，Y=W²。182给ν-a.e.1≤wstd，故得到AE非负，且已有wstd可测及Fstd在ν下的真实L¹。319行letI把hνprob放入真实局部概率实例，产品概率由两个ν概率导出。W、Y可测，平方每点非负。

327–331调用P02，所有实参是ν、wstd及已支付的可测、AE非负、α>0、tauStd>0、Fstd可积，返回的函数和测度与Y/β/tauPair/pairLaw定义相同。332–339从exp每点非负得到边缘实际积分I≥0；与182的I≤2Mexp及Mexp≥1，在非负区间比较平方得到I²≤(2Mexp)²。340–342串接P02给配对指数实际积分≤Mpair。常数来自边缘实际积分，不是截断高度aenv R的指数粗界，因此统一于R。

346–365对所有n:ℕ构造νn(i)=pairLaw、Yn(i)=Y、S=coordinateSum Yn。坐标概率、可测、AE非负、指数L¹和积分≤Mpair五项均直接由已经证明的事实给出，再将Ω×Ω、n、νn、hνn、Yn、全部前提、q和hq显式交给T03。最终simpa只展开Cmom/S、用C0等式与Real.rpow_eq_pow，不改变被积函数或法则。

这保留全部n含0，全部实q≥1含q=1，以及β=1/α=2端点。n=0由同一已qualified接口覆盖，空坐标函数无需选取Ω默认元素；没有n≥1前提。q≥1与β>0保证展示中的1/q和1/β无零分母。原子、鬼样本相等与重复样本均允许。未声称常数统一于趋近0的α。

366–374的lam∈[0,1]分支保留H、κ、G、σ2、σ、K、Kstd七个实际值，精确复用同R下182返回的hKstd两个AE包络。没有用λr/σ替代真实条件典范核，没有把n/q支的绑定泄露给lam支，也没有让lam进入pairLaw、Y或Cmom。

## 来源忠实性、未支付义务与机器待办

本单元支付p44 §1鬼样本权重平方到§2(6)非负和矩引擎的条件输入适配，即§3中Y=(wstd+wstd′)²具有β=α/2的统一伸展指数矩及其独立坐标和的全实q矩。P01/P02为本模块适配，实幂/指数/乘积积分/可积理论归mathlib，真实条件核输入归182，组合矩与实阶提升归183。

p51 S6的“条件标准化p矩变化有任意多项式速率”被p54 F3固定法则反例否定；本源码没有采用该速率作为输入、阈值选择或输出。没有声称支付p54的严格余量、真实upper大分子/分母坏事件、编码极限、闭尾原子、零分母或compact概率费用。Shao–Zhou随机区间定理、原类Lemma6.1及其外部工具保留外部归属。

本结果尚不包括Hilbert双重对称化、Khintchine、二阶符号混沌、实际F/行能量矩尾、DC或相对概率引擎，也不证明任何原根完成。C2/C12/OQ56仍OPEN；OQ3仍PAUSED_BY_USER。本轮不作新颖性、优先权或原创根定理声明。

静态禁词检查未发现sorry/admit/新增axiom/unsafe/native_decide。该静态结果不代替内核。下一步由父级对同一源版本串行取得native内核与实际module-index全owner清单（不按namespace/public过滤，含private/generated）、每name完整TYPE、每个非thm完整FULLVALUE、逐名递归AX，并只接受propext/Classical.choice/Quot.sound白名单。数量必须来自实际清单，不能预填3。后续在同一独立上下文审元数据与回执时可复用本次完整source审阅；若仅证据呈现变化无需重审未变Lean证明，若源码数学变化则仅重审受影响范围。
