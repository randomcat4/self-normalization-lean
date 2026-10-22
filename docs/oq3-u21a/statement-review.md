# U21a CompactTiltWeakCramer 独立声明／来源／API审查

STATUS: IN_PROGRESS

## 不可改写盲译前缀：精确imports及完整TYPE

先仅读冻结scope73唯一Lean fence的两个imports与完整公开TYPE，尚未读其解释／路线、作者candidate／scanner或新机械证据。此前前置上下文存在，不把它们直接当本新族估计的证明。0publicDEF／1publicTHM。

```lean
import Shao.OQ3.CharacteristicMeasureDomination
import Mathlib.Analysis.SpecialFunctions.Pow.Real
```

独立全部量词／let／常数与边界翻译：

1. 任取实线上真实概率mu，并给实M≥0及同mu的AE |x|≤M。
2. 任取实二维参数集K且IsCompact K，不要求Nonempty K。
3. 任取实u0/v0作为基准二次倾斜参数，不要求(u0,v0)∈K。
4. beta、c、R都是实数，其中唯一显式数值正性输入为c>0。
5. hWC只控制同mu基准倾斜mu.tilted(u0*x+v0*x²)的jointCharacteristic。
6. hWC对全部实xi/eta成立，条件为R<sqrt(xi²+eta²)。
7. 半径是实际欧氏sqrt(xi²+eta²)，不是L1频率范数或复参数替代。
8. 幂因子为Real.rpow(该半径)(−beta)，必须按实幂总定义及非负底数核。
9. hWC右侧是1−c*rpow，不能暗中换成对平方模的假设。
10. mu0在结论内let精确等于这个同mu的基准倾斜，不可另择law。
11. 结论只存在同一个实m，它必须同时满足0<m、m≤1及0<m²*c/2。
12. m在所有p∈K与所有xi/eta之前固定，不允许分门各选m。
13. 对每个p∈K，第一项要求真正ENNReal.ofReal m • mu0≤同mu的p二次倾斜测度。
14. 这是实际measure domination，不是仅对某类函数、仅a.e.密度或自由概率law的比较。
15. 同p第二项要求全频率m²*(1−norm(basechar)²)≤1−norm(pchar)²。
16. 这个全频谱平方gap比较使用同一个m，不只在hWC外区成立。
17. 同p第三项要求同beta/R欧氏外区上的真正范数弱Cramér界。
18. 新系数精确为m²*c/2，并且在m存在合取中已经交付严格正。
19. 新目标没有caller给全族WC、tilt概率、指数可积、operator比较或平方gap恒等式假设。
20. 所有倾斜必须由原mu AE有界真实证明exp可积并建立概率，不能使用不可积时tilted=0总化分支。
21. 紧集空时不能抽取一个p来证明m≤1；须使选择仍真正满足全部外层数值结论。
22. 基点不在K不应阻塞比较，基准参数u0/v0仍是固定有限实数。
23. M0和实beta/R任意的边界需要独立核；源应用beta>0/R>0并非TYPE已有假设。
24. beta/R可使半径0进入hWC条件，rpow在零底数的总定义不能被非法log化或除半径。
25. 从实际范数比较推出平方gap时要先有两个特征模≤1及m≤1，再核精确m²系数。
26. 从基点normWC到族normWC需要平方gap与1+b≤2等准确不等式，不能把平方gap直接冒作normgap。
27. 需要全族共同测度下界来自既有公开compact quadratic tilt API，不能把familybound当输入。
28. 不能偷用root未接受公共char恒等式／canonical rate，也不能跨模块privatehelper。
29. 无新公开定义，不声称谱比较以外的root C或A/B/C/D闭合。

当前仅为完整TYPE的独立盲译和待核门清单；后续只追加，保留这些字节不改写。

## 同一盲审阶段追加：第二fence完整公开TYPE

scope73实际分开两个Lean fence；上一检查点原样保存了imports与基于初始全部fence输出的独立翻译，但仅第一个fence被嵌入。现仍未读取scope说明／来源／API／机械，先把第二fence完整TYPE追加持久化，保留前46行3280B历史字节，不倒改该检查点。以下与上面的量词翻译共同组成完整不可改写盲前缀。

```lean
theorem exists_compact_tilted_weakCramer_bound (mu : Measure ℝ)
    [IsProbabilityMeasure mu] (M : ℝ) (hM : 0 ≤ M)
    (hb : ∀ᵐ x ∂mu, |x| ≤ M) (K : Set (ℝ × ℝ)) (hK : IsCompact K)
    (u0 v0 beta c R : ℝ) (hc : 0 < c)
    (hWC : ∀ xi eta : ℝ, R < Real.sqrt (xi ^ 2 + eta ^ 2) →
      ‖jointCharacteristic (mu.tilted (fun x => u0 * x + v0 * x ^ 2)) xi eta‖ ≤
        1 - c * Real.rpow (Real.sqrt (xi ^ 2 + eta ^ 2)) (-beta)) :
    let mu0 : Measure ℝ := mu.tilted (fun x => u0 * x + v0 * x ^ 2)
    ∃ m : ℝ, 0 < m ∧ m ≤ 1 ∧ 0 < m ^ 2 * c / 2 ∧
      ∀ p ∈ K,
        (ENNReal.ofReal m • mu0 ≤
          mu.tilted (fun x => p.1 * x + p.2 * x ^ 2)) ∧
        (∀ xi eta : ℝ,
          m ^ 2 * (1 - ‖jointCharacteristic mu0 xi eta‖ ^ 2) ≤
            1 - ‖jointCharacteristic
              (mu.tilted (fun x => p.1 * x + p.2 * x ^ 2)) xi eta‖ ^ 2) ∧
        ∀ xi eta : ℝ, R < Real.sqrt (xi ^ 2 + eta ^ 2) →
          ‖jointCharacteristic
            (mu.tilted (fun x => p.1 * x + p.2 * x ^ 2)) xi eta‖ ≤
              1 - (m ^ 2 * c / 2) *
                Real.rpow (Real.sqrt (xi ^ 2 + eta ^ 2)) (-beta)
```

完整公开TYPE已在来源／数学／API阅读前落盘。后续仅追加，不改写此前内容。

## 一、冻结版本、审查顺序与原来源

以上76行5031B构成完整不可改写盲审前缀，SHA256=c938d902b7327e5a95a86973ad1ccc0c856ac7e225284f3e2f1f1af7ec0a079f。初始46行3280B检查点SHA256=da1a60ceac51827fed80270334642abbf43d5ab984c423b9c51de205eead8fcd也保留；它仅嵌入首个imports fence，故在同盲审阶段、读取任何scope解释／来源／API之前，已透明追加第二fence完整TYPE。两个fence现均与scope逐字相同，没有倒改历史。
页首IN_PROGRESS为先行检查点状态，末节为本次声明门最终裁决。所有数学／API分析在完整TYPE落盘之后，静态图／hash／Git绑定在数学门之后。
本轮不读作者future／candidate／scanner笔记或JSON作证明；scope路线只作待核说明，不以其自认证。尚无本单元source／Audit／proof可验收。

R2真实343–352行要求原有界mu的二次倾斜族对基点倾斜有同一个参数无关m>0测度下界(20)。
355–363行给双样本cos表示及实际平方模缺口(22)；366–369行从基点norm弱Cramér条件推出同beta／R的统一常数m²c/2。
新TYPE精确要求真实测度下界、全频率实际平方gap及同欧氏半径Real.rpow的范数WC界，全部输出共用同一个m，不把族WC预先当输入。
R2原件SHA256=572e74aa9c12e2771f5543a5709a2807666eeea0a4076e7a3263e5c7bcf87f55。
(21)可作为已存在共享库的证明路线，但此exact2imports不消费它；本门独立用更强公开norm比较导出(22)。不依赖该identity不等于断言共享库缺失或identity未被证明。
本TYPE没有canonical rate、矩阵标准化或root最终组装结论；它仅生产原C的真实有界倾斜稳定性这一直接承重项。

## 二、所有倾斜的真可积／正配分／概率门

mu是真概率，M≥0，且同mu AE |x|≤M；任意实u/v的exp(u*x+v*x²)都是可测连续函数。
实际TiltedMeasureDomination.lean17–34的公开quadratic_exp_integrable_of_ae_abs_le完整消费mu概率、M/hM/hb及任意u/v，给该指数真Integrable。
其证明用真实有限常数exp(|u|M+|v|M²)主控：先由AE |x|≤M得x²≤M²，再控制指数；即使M=0或u/v=0，也不把非可积时积分默认0当作有限性。
因此基准(u0,v0)和每个p∈K的指数均在同原mu上真可积；基准不必属于K。
MeasureTheory.integral_exp_pos在概率所给NeZero后给每个配分Z>0；Measure/Tilted.lean126–136的isProbabilityMeasure_tilted明确消费真exp Integrable、正归一化及有限积分门，给真实倾斜概率。
这两个概率实例须在调用jointCharacteristic_norm_le_one或测度分解比较前实际建立；不能仅靠一般tilted是零或概率的总化类型类。
本TYPE虽不额外输出每个倾斜的IsProbabilityMeasure，它们是从当前输入可实际生产的证明前置，不是隐藏caller前提。
不需要把倾斜mu0的均值／协方差固定为原mu，也没有source q或n参数；这里只比较同原mu的实际二次倾斜。

## 三、同一个m的真实生产与空紧集

实际CompactTiltDomination.lean30–42的公开exists_compact_quadratic_tilted_domination消费同mu/M/hb、紧K、任意固定u0/v0。
它一次生产m0>0，以及∀p∈K的ENNReal.ofReal m0 • mu0≤mu_p；还附带一个cosine-pair积分比较，但本路径无需消费该附加结论。
其上游15–28的exists_compact_parameter_box以连续函数|p1−u0|+|p2−v0|在K上有界，选择L=max C0≥0，再43–49由公开quadratic_tilted_measure_domination给m0=exp(−2L(M+M²))。
空K时连续像界仍可给某C，再max C0，整个选择不需要提取p∈K；u0/v0在K外也只是有限固定参考，紧性仍控制相对坐标差。
为保证目标外层m≤1而不从一个不存在的p抽取，选择同m=min m0 1；m>0、m≤1、m≤m0均真实成立。
对每个测度集合A，用ENNReal.ofReal单调和μ0(A)≥0得(ofReal m)*μ0(A)≤(ofReal m0)*μ0(A)，所以ofReal m•mu0≤ofReal m0•mu0≤mu_p。
这正是原CharacteristicMeasureDomination.lean77–81中公开实现使用的点集缩放比较形式；不需要任意Radon–Nikodym输入或忽略ofReal有限性。
m为有限实数，ENNReal.ofReal m≠∞，并先于全部p和频率固定；同一个缩小m用于measure、平方gap及最终WC，不能分别调用两个∃m定理后混用其见证。
特别不能只调用exists_compact_tilted_characteristic_bound再另取measure-domination m，因为前者公开输出没有保留同m的measure比较。应按上述一次m0／同min m路线保留关系。
由m>0及c>0，真实sq_pos／mul_pos／div_pos给0<m²c/2，分母2严格正，无额外频率条件。

## 四、从真实范数压缩到精确平方模缺口

对任意p∈K，先给mu0及mu_p建立上节真实概率实例，再将同m、m≥0与同hdom输入CharacteristicMeasureDomination.lean17–22的公开jointCharacteristic_norm_le_of_measure_lower。
它给全xi/eta真实b≤1−m(1−a)，其中a=‖jointCharacteristic mu0 xi eta‖，b=‖jointCharacteristic mu_p xi eta‖。
该公开proof23–62用有限lambda=ofReal m•mu0及真实残差rho=mu_p−lambda，先sub_add_cancel和有限measureReal加法得残差质量1−m，再真phase Integrable后拆积分、三角不等式。
所以这里不是从未证明的cosine identity或假设族char界出发；有限／正质量／积分线性门都由已完整验收的实际公开定理承担。
JointNonlattice.lean37–43的jointCharacteristic_norm_le_one在真概率下给0≤a,b≤1；a,b下界来自norm_nonneg。
设u=1−m(1−a)。因0≤m≤1及0≤a≤1，0≤u≤1，且0≤b≤u，故b²≤u²。
独立核算的精确恒等式为
1−u²−m²(1−a²)=2*m*(1−m)*(1−a)≥0。
所有右侧因子已真实非负，因此m²(1−a²)≤1−u²≤1−b²，正是新TYPE第二项所需的全频谱平方模缺口。
它使用同一个measure-lower m，而不是重新选择平方界常数；频率没有R外区限制，亦不需要beta/c假设。
该环节只是实有序环不等式及ring展开，可由当前已导入公开代数／norm API实现；不新增root公共char identity import或private helper依赖。

## 五、从基点norm WC到族norm WC的精确系数

固定任意xi/eta且R<r，r=sqrt(xi²+eta²)；r永远非负。记t=Real.rpow r (−beta)，delta=c*t。
实际Pow/Real.lean163–165的Real.rpow_nonneg完整前提是0≤底数、指数任意实数，故t≥0及delta≥0；无需先假设r>0或beta>0。
hWC在同mu0给a≤1−delta，即delta≤1−a。由0≤a≤1，a(1−a)≥0，故1−a≤1−a²。
乘非负m²并应用上一节全频平方界，得到m²delta≤m²(1−a²)≤1−b²。
再用真实实恒等式2(1−b)−(1−b²)=(1−b)²≥0，得m²delta≤2(1−b)。
除正2并整理实乘法，精确得到b≤1−(m²*c/2)*Real.rpow r(−beta)，没有少一个交叉因子或把平方gap直接当normgap。
新常数m²c/2已独立证明严格正，保持同beta及同R；m不依p或频率，故是真正统一族WC界。
不需要误用更强假设“基点1−a²≥c*t”；这里确实从原hWC的1−a≥c*t生产所需平方界下界。
此论证从头到尾不除r、不写log r，也不把Real.rpow任意底数的行为粗暴替换成exp(logr*exponent)。

## 六、边界／量词／原用途

K=∅时，∀p∈K三项本来真空，但外层0<m≤1和0<m²c/2仍由同min选择真正生产；没有Nonempty偷渡。
theta0=(u0,v0)不在K时，compact parameter box控制相对固定参考差，仍生产同exp界，不需调用基点属于K。
M=0时真实bounded-exp／probability／measure比较仍合法；若某组hWC与退化law本来矛盾，那只是该条件实例无模型，不影响全称条件命题，proof不靠该矛盾取巧。
beta/R任意实是当前代数传递更一般的接口，不意味着原source WC定义已取消beta>0／R>0；原应用必须另保留这两个正性条件。
R<0可让r=0进入条件；Pow/Real.lean30–45／128–160明确0^0=1，0^y=0(y≠0)，因此rpow_nonneg仍覆盖零底数。证明从未非法用正底数公式或除以零半径。
若hWC在这些边界本身不可满足，定理只是正常条件式；不声称任意beta/R/有界mu都自动存在正c满足WC。
所有M/K/u0/v0/beta/c/R先固定，存在一个m再∀p／∀频率；没有n参数或随n变化的常数，更没有把全族目标界放进hWC。
mu0的let与hWC中显式同基准倾斜定义相等，未更换参考measure或暗设它是原mu。

## 七、数学后作的一次独立图及冻结绑定

本轮独立扫描exact2imports CharacteristicMeasureDomination／Mathlib.Analysis.SpecialFunctions.Pow.Real：剥除注释／字符串，识别ordinary/public/private/meta，传统非module普通imports按公开处理。
physical遍历全部内部边，public只遍历公开边；仅展开Shao／Mathlib，外部Lean/Batteries等停止并另计，不冒称其内部闭包已展开。
独立physical=15Shao＋2418Mathlib＋211外部停止=2644节点；public=2402内部＋189外部停止=2591；全部内部source及对应olean存在，缺0。
canonical15相对源路径键sorted compact SHA256=2b038a74d11a67ef91fcaceaf4dd5c3fa88de4757967e5e2d9d555851cf02bb5。
实际公开可达CharacteristicMeasureDomination／CompactTiltDomination／TiltedMeasureDomination／JointNonlattice／Pow.Real／Measure.Tilted。
LowFrequencyDamping不在这个exact图；这只表示本目标不依赖它，不表示共享库缺少其quadraticChar_gap_identity。行政补充提到的共享现有(21)未被当作本门假设或要求新增import。
Pow.Real本身9行public meta import Nat.NthRoot.Defs亦被扫描纳入，未忽略meta modifier或把external停止节点口径混入内部总数。

关键本地／server实际源SHA匹配：CharacteristicMeasureDomination91行4783B ec7032919bd8d825bb8746da15e84b29c5cb59ef97858367e4d73fdf52aa9bbb；CompactTiltDomination59行2459B 6f31ac2e3b2b9d9b2ef957ebe52cfe3664a86694bb396b09c1006b890cbd0623。
TiltedMeasureDomination105行4754B 5445a68da1ac8302f174bfe2144eb8271a0af740fd6b91a87355abb41fed739b；JointNonlattice118行4920B 51ce939232610353215fc3b7377e19b894451a9a108125e1828bf2fe8ec81559。
local／remote scope73同48行4770B，SHA256=b539efde780e8033134f2503dcfd8070a811fbae8db759814bc75d3c1829ea77；两个Lean fence与本报告逐字一致。
真实R2原件SHA256=572e74aa9c12e2771f5543a5709a2807666eeea0a4076e7a3263e5c7bcf87f55。
固定Mathlib807d3836b165983210ee2ecf3cd28f239436949c／lean4:v4.36.0-rc1及既有pins沿用，不重复旧pins／成功smoke／稳定缓存检查；本轮新图只扫描一次，没有Lean／probe／build／Audit／cachewrite。
实际worktree branch仍feat/oq3-source-remainder-not-bigo，HEAD9170a40f3e9a6d519a987c2a0ceaade85136cd36，status为空；U21a CompactTiltWeakCramer.lean／Audit.lean／receipt.json实际不存在，无新branch或proof验收可预报。
本target15旧已接受source可用不等于依赖153／152／151／148等叶PR；精确imports没有这些模块，也不消费root新canonical定义。
所有server项目读取taskset -c 14-17；未碰外部CPU0–9／80GiB、ulimit-v、shared cache／pins或他人编辑，未改冻结scope或旧票。

## 八、最终声明裁决与优先级暂存

STATUS: CORRECT

JUSTIFICATION: 完整TYPE与R2(20)/(22)及m²c/2实际范数WC传递一致。当前公开生产者从真bounded mu给每个quadratic tilt真exp Integrable／正配分／概率，紧性给基点可在K外的共同测度下界；一次m0再同min m0 1保留measure比较并处理空K。该同m的真实norm压缩界经明确非负因子恒等式给全频m²平方gap，继而从基点norm hWC与非负实幂准确推出统一m²c/2，所有半径0／任意beta/R边界均无需非法除法或额外假设。实际公开API／静态source和olean无缺项，未发现声明或环境阻塞。本票是声明CORRECT，不是尚不存在实现的proof验收。

原target→消除义务：原C有界倾斜稳定性中，单基点WC到同compact族的真实测度下界／actual平方模缺口及精确统一范数常数传递。
直接consumer→root实际倾斜族WC及原C组装；协方差标准化的频率／统一矩阵范数比较、Edgeworth／格胞／远区概率链等仍为后续独立义务。
仍OPEN→root canonical rate适配／全局rate及原A/B/C/D最终组装不由此声明关闭；所有原根A/B/C/D仍OPEN。
优先级行政事实：root新v38 canonical accepted checkpoint交接后，当前指令仅要求完成此声明最终报告，再由lead全文读后将U21a记为DEFERRED_UNIMPLEMENTED并优先下一canonical same-law adapter。声明数学合法与优先级暂存相互独立；暂存不代表INCORRECT，也绝非proof通过。本轮没有实施／Lean／探针，不改scope字节或153冻结树，不提前读取下一scope。
