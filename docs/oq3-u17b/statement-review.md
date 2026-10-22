# U17b SourceEnergyGeometry 独立声明/source/API审查

STATUS: CORRECT

本票仅冻结声明门，源尚未实现。唯一reviewer lease1；只拥有本新报告和授权run/statement-review.md，不spawn/Lean/probe/build/rebuild/写cache或其他文件。第一阶段仅取冻结scope Lean fence，先独立翻译并落盘，再读正文/来源/实际前置/作者路线；旧样本几何审查上下文存在，不作为自动批准理由。

冻结scope SHA256=`7d1b62f0a8f93e99fb86398b7af6313dce03ecc69acae17abcb8626976b159e0`。

## 1. 冻结的两个完整定义体与三个完整类型

```lean
def sourceEnergyRatio (q : ℝ) (n : ℕ) (z : Shao.Path n) : ℝ :=
  Real.sqrt (Shao.energy z / ((n : ℝ) * q))

def sourceFarEnergySet (q H delta : ℝ) : Set ℝ :=
  {R | 0 ≤ R ∧ 1 ≤ q * R ^ 2 ∧ q * R ^ 2 ≤ 1 + H ∧
    delta ≤ q * (R - 1) ^ 2}

theorem sourceFarEnergySet_isCompact (q H delta : ℝ) (hq : 0 < q) (hH : 0 < H) :
    IsCompact (sourceFarEnergySet q H delta)

theorem sourceTail_normalDeviation_energy_lower (q : ℝ) (hq : 0 < q)
    (n : ℕ) (hn : 0 < n) (z : Shao.Path n) (htail : z ∈ sourceTail q n) :
    -((n : ℝ) * q * (sourceEnergyRatio q n z - 1) ^ 2) ≤ normalDeviation q z

theorem sourceTail_far_energy_mem (q H delta : ℝ) (hq : 0 < q)
    (hH : 0 < H) (hdelta : 0 < delta) (n : ℕ) (hn : 0 < n)
    (z : Shao.Path n) (henergy : ∀ i : Fin n, 1 ≤ (z i) ^ 2 ∧ (z i) ^ 2 ≤ 1 + H)
    (htail : z ∈ sourceTail q n) (hfar : normalDeviation q z ≤ -delta * (n : ℝ)) :
    sourceEnergyRatio q n z ∈ sourceFarEnergySet q H delta ∧
      0 < sourceEnergyRatio q n z ∧ sourceEnergyRatio q n z ≠ 1
```

## 2. 独立盲译（先持久化）

第一定义 sourceEnergyRatio 对任意实q、自然n和真实路径z:Fin n→ℝ，取真实能量Σ_i z_i²除以(n:ℝ)*q后的标准实平方根。定义自身不排除q0、负q或n0，依实除法/实sqrt标准总化而为实函数；后续目标另给正q/n，不可把定义总化当合法归一化证明。

第二定义 sourceFarEnergySet(q,H,delta) 是实R的集合，要求同时R≥0、1≤qR²≤1+H，以及delta≤q(R−1)²。参数本身无正性条件，也没有显式排除R1或要求集合非空；后续须由真实目标的参数门判断。

第一定理给任意实q/H/delta，只假设q>0、H>0，断言上述完整集合是实拓扑紧集。delta可负/0/正，空集也须覆盖；不能为紧致性擅加delta>0、非空或q接近1的隐含条件。

第二定理固定任意q>0、自然n>0和任意真实路径，只要求该路径属于实际sourceTail q n；结论真实normalDeviation q z≥−n*q*(sourceEnergyRatio q n z−1)²。它没有坐标energy上下界/AE/概率/有限原子/真实均值假设，故推导只能使用实际样本几何与正分母/开根门；不能偷用能量约束或统计中心替换q。

第三定理给q,H,delta均正、自然n>0、真实路径z，假设每个坐标真实平方在[1,1+H]、z属于真实sourceTail、且normalDeviation q z≤−delta*n。结论同一个实际R=sourceEnergyRatio属于完整sourceFarEnergySet，并严格R>0且R≠1。坐标条件是逐点全Fin n，不是仅AE；该目标没有概率分布输入或iid假设。n0被显式排除；R严格性和非1必须真实推出，不能从集合定义无条件读出。

本阶段未判断数学/source/API。没有一般KL、Bernoulli指数试验、远区概率界或紧覆盖结论；各根及full17/19/LLT/hW/globalfar仍OPEN。

## 3. 来源与actual前置（盲译之后）

盲译阶段已先持久化：报告SHA256 `21d4090d17d0b389a956e4e270a64d65fd5e138633210ffa0e43a45406e3c5da`，3490 bytes/46行。之后才读取scope正文、真实R1及既有SampleBoundary/FinitePath源码。没有读未来SourceEnergyGeometry实现、作者energy/rotation备忘或下一scope。

R1原件 `C:/game/shao/current/oq3/proofs/r1/report.md` 实际SHA256=`3473d34ff20bd0d334b9ef3ea3c3ee167fba4d5cc3a742849820ce54d639e662`。164–172的源能量支持1≤X²≤1+H与边界能量比 EρX²=qR²是本定义的来源；386–391说明远区需另有compactness/global rate gap，400–408是真曲边恒等式/正尾符号。本单元只给真实路径能量比与其远区参数的确定性紧性，不能将该紧集本身称作远区概率指数界或有限覆盖完成。

actual `Shao.Basic.FinitePath`：Path n=Fin n→ℝ（18），energy z=Σ_i(z_i)²（31），energy_nonneg（50–51）来自真实平方和，没有代换成variance/矩期望。actual `SampleBoundary.lean:19–27` 定义M_q=Σ_i normalValue(z_i)−Nq、tangentDeviation q=Σ_i z_i−Nq/4和sourceTail={energy>0且sqrtq/4*sqrt(N energy)≤Σ_i z_i}。其公开29–32 `normalDeviation_eq_sum_energy` 精确给M_q=8Σz−energy−Nq；34–39的曲边平方恒等式和53–86的正尾等价也真实存在。本票第二目标不需要概率/均值，只消费正尾定义与这个8系数代数式。

三个拟目标的所有q/H/delta都是同一次调用的相同实参数。这里没有p、eps、P、r、J或μ输入，故不会在此产生或改变一个概率族；未来概率专化仍须以同一实际source参数消费。本票不把R1中切向R_n与本新energy ratio混为一物，也不将a=q/4默认为任意坐标中心。数学独立于J和U17a的指数测试，不消费它们的未完成实现或未来far规划。

## 4. 三个完整类型的独立数学可行性

### 4.1 sourceFarEnergySet_isCompact：所有实delta与空集

令F={R | 0≤R ∧ 1≤qR² ∧ qR²≤1+H ∧ delta≤q(R−1)²}。q/H/delta固定，四个左右函数都是连续实多项式或常数，由实际isClosed_le及有限交知F闭。没有严格不等式被误当闭集，也没有要求F非空。

q>0,H>0给U=(1+H)/q>0，B=sqrtU≥0。对任意R∈F，已有R≥0，且除正q得R²≤U。由于B²=U且R/B底数均非负，可用平方序等价推出R≤B，所以F⊆Icc0 B。actual实数闭有界区间Icc0 B紧；闭子集F也紧。delta在这两个论证中可负、0、正，无额外delta>0或“离1正距离”隐含假设。若delta太大/其他条件使F空，闭子集定理仍正确，不能先提取一个R或非空见证。R=1在delta≤0且能量可行时可在F内，第一目标不排除它；R=0因1≤qR²不可能，但不需要额外删点才紧。

### 4.2 sourceTail_normalDeviation_energy_lower：真实正尾与平方根门

固定q>0、自然n>0、真实路径z及htail。记N=(n:ℝ)>0、E=energy z≥0、S=Σ_i z_i、R=sqrt(E/(Nq))≥0。Nq>0先给分母非零，E/(Nq)≥0后才用Real.sq_sqrt得到R²=E/(Nq)，再合法取消正Nq得NqR²=E。这里没有用总化sqrt在负数上的值推平方恒等式，也没有在n0/q0清分母。

定义T=(sqrtq/4)*sqrt(NE)和U=NqR/4。T≥0、U≥0，且在q≥0、NE≥0下真实平方根平方公式给
T²=(q/16)*(NE)，而U²=(N²q²/16)*R²=NqE/16，故T²=U²。在两个底数非负门后sq_eq_sq₀推出**T=U**，没有从平方相等忽略±号。htail的原正尾分支给S≥T=U，所以8S≥2NqR。用actual M_q=8S−E−Nq与E=NqR²，得到
`M_q ≥ 2NqR−NqR²−Nq = −Nq(R−1)²`，精确匹配目标。

sourceTail还给E>0，事实上使T/S正，但本下界只需已建立的非负和原始尾阈值；不会把负S的平方事件也加入。该推导不使用任何坐标energy upper/lower、样本均值、概率、finite stage、原子正质量或Bernoulli界，故完整类型的较弱假设足够。q可任意正实，n只需>0；不暗加q近1或n趋无穷。

### 4.3 sourceTail_far_energy_mem：真有限和、严格R和非1

在第三目标原假设下，逐坐标全Fin n的1≤z_i²≤1+H可直接有限求和得N≤E≤N(1+H)，使用真实Fin n元素数n及real cast，不是把AE坐标门未经提升当作全样本门。N>0允许除N，于是1≤E/N≤1+H。由前一比率恒等式qR²=E/N，得到F的两能量不等式；R≥0由sqrt定义。因N≤E且N>0，所以E/(Nq)>0，真实sqrt_pos_of_pos给R>0（亦可从1≤qR²与R≥0排除0）。

对同一q/n/z，第二目标给−Nq(R−1)²≤M_q；hfar给M_q≤−delta*N。合并后先整理N*delta≤N*q(R−1)²，再只取消**正N**，得到delta≤q(R−1)²。于是R属于原完整F，方向与定义一致；hdelta>0使R=1将推出delta≤0矛盾，所以R≠1。没有除R−1、没有在还未证明R正前消sqrt或取消R，没有从非严格far边界丢掉等号。

若energy上下端点处取等号或hfar等号，上述弱不等式仍成立；delta严格正仅用于最终非1。第一目标没有借第三目标的hdelta正性；第二目标没有借第三目标的逐坐标bounds。n0/q0只在两个定义中总化，两个带路径目标均在明确hn/hq之后取消分母。这些分层前提没有交叉偷用。

## 5. actual固定库API/作用域的静态检查

只读指定服务器实际库源，无Lean/#check/API probe：

- `Mathlib/Topology/Order/Compact.lean` 不是弃用wrapper；6–10为module/public imports，51–56定义CompactIccSpace并公开导出isCompact_Icc，77–79给ConditionallyCompleteLinearOrder+OrderTopology到该实例。真实ℝ满足这些实例；使用的是紧区间，不是全ℝ CompactSpace。
- `Mathlib/Topology/Compactness/Compact.lean:104–107` 的实际 `IsCompact.of_isClosed_subset (hs:IsCompact s) (ht:IsClosed t) (h:t⊆s)` 给IsCompact t，正好消费上面的Icc紧性/闭F/包含关系。它不要求t非空，因此没有空集门缺失。
- `Mathlib/Topology/Order/OrderClosed.lean:443–446` 的实际 `isClosed_le` 消费Continuous f/g给{b|f b≤g b}闭。实多项式qR²/q(R−1)²和常数连续，可用IsClosed.inter把四个弱不等式集合组合；无需对sqrt函数的负半轴做闭集逆像推断。
- `Mathlib/Analysis/Real/Sqrt.lean:143–145,177,227–229,285–288` 给真实Real.sqrt_nonneg、需0≤x的sq_sqrt、包含右侧非负门的sqrt_le_iff、真实Real.sqrt_pos/sqrt_pos_of_pos。注意较早同文件96行是NNReal命名空间，不把它当作ℝ的另一个签名；本票用的是实数版本。
- `Mathlib/Algebra/Order/GroupWithZero/Basic.lean:748–749,758–759` 的sq_eq_sq₀/sq_le_sq₀均明确两个底数非负。用于T/U正根比较和R/B有界性时这些门已先给出。标准正除法单调/取消、有限和单调、sum_const/card_univ/Fintype.card_fin和ring代数均在SampleBoundary已实际消费的环境中可见。
- SampleBoundary公开normalDeviation_eq_sum_energy和真实sourceTail完整定义已直接读取；FinitePath给energy有限平方和和nonneg。这三个目标不需要新Integrable/AE/Fubini/概率/normalizer API，也不以没有这些对象为借口偷用概率结论。

拟imports仅SampleBoundary与Topology.Order.Compact；namespace Shao.OQ3、open MeasureTheory、open scoped BigOperators、noncomputable section可承载完整两个body/三个类型。未发现完整类型中的未绑定变量、全局非空/可测/MeasureSpace.volume/Matrix scope或新cache需求。静态API/数学阶段判断支持CORRECT，最终冻结hash/真实import闭包/现成olean/pins仍留到下一阶段核。

## 6. 最后冻结/实际导入闭包/缓存/pins核对

数学/source/API阶段报告已先持久化：SHA256 `e7ea4573002731a5f15ed86f9b3ce2ebd635f4ff1170429ffcf6c384d9c385df`，11061 bytes/95行。随后才只读核实际两端scope、SampleBoundary及递归闭包、库源与现成olean/pins。当前新源 `Shao/OQ3/SourceEnergyGeometry.lean` 远端确未创建；无本单元实现、target build/Audit/receipt可声称已通过，未以任何未来绿灯代替本声明审查。

本地 `C:/game/shao lean/drafts/oq3/forty-eighth-unit-scope.md` 与remote `runs/oq3/u17b-20261021/scope.md` 实际SHA256均=`7d1b62f0a8f93e99fb86398b7af6313dce03ecc69acae17abcb8626976b159e0`，3995 bytes/38行。actual SampleBoundary本地draft/远端工作树均SHA256=`7660e23b71ce28ab43a4ad1d8df1862cf8a507b6bb9b41255e961f0bee0b93e2`，7131bytes/167行。

拟imports的实际递归项目闭包是以下12项；集合由实际source imports重新枚举，每项hash同此前完整接受的J闭包冻结pin，所有12个既有olean均实际存在。无J/U17a模块依赖，未重跑任何成功旧目标：

| 实际项目源路径 | 实际SHA256 |
|---|---|
| Shao/Basic/FinitePath.lean | `898262898f9c088e2d10e6238e411b4397387b21b1b71a2b545c5edef936e1bb` |
| Shao/OQ3/AtomProjection.lean | `0d369052c7f87122765612efdeaca5d9ac71abca861e7785c86d1f9edcc74d22` |
| Shao/OQ3/AtomicMeasure.lean | `59ddc48fb7b395f362939e58cbd9d7911685a6ed6e6574142e8a6d4ab3ee0c39` |
| Shao/OQ3/FiniteConstraints.lean | `800d9db8cb6749a31ecfe611409de92b10ea8bb2aef955bfd825ede7324f0ef0` |
| Shao/OQ3/FiniteNormalSpan.lean | `0374da4860edf8af8bbbb9172e4e93bfe9b6c37ac57672b85a4f58392475b7de` |
| Shao/OQ3/FiniteStageMeasure.lean | `1a32fb904e6ee9d2b0b48d92c4ebb3568452bb02500ce52a1a03eb01ae0256b1` |
| Shao/OQ3/InverseTilt.lean | `c7e7d19e8b70481b663bec1fd12ea9301d73313faaf35997e85aa9ba99f21811` |
| Shao/OQ3/ResonanceArithmetic.lean | `cd21a264d637bab30fed765bdc25ed09bb4ff56f6efb9c88ee09be4ca6e1648b` |
| Shao/OQ3/SampleBoundary.lean | `7660e23b71ce28ab43a4ad1d8df1862cf8a507b6bb9b41255e961f0bee0b93e2` |
| Shao/OQ3/SourceStarter.lean | `0e2a081619976f88149707c2ef9311dc909003e61d3d0f7c4e21e6c3dbbc5a6d` |
| Shao/OQ3/SummableAtoms.lean | `0ea4c64fe9ef9b45fbf44d24312771a1dbfbcc5de8448564e3e87bdf17c7178b` |
| Shao/Probability/FiniteIID.lean | `d1b565489199d55af70a27c31a0f803a2b7433e78c9197a361b3c10c0598845b` |

规范path→hash JSON字典（sort_keys=True,separators=(',',':')，UTF-8）整体SHA256=`b7fa606fd07656d7eb65409e9e402ea4bd1bc59c72d99bd762130cbe6eaaaafc`。闭包中虽有既有概率/有限阶段基础模块，三个新目标本身仍只是确定性样本几何，不由“import了概率”凭空得到概率尾结论。

下列实际库API模块均从拟import源码图可达、其现成olean实际存在，且实际源码字节逐项同真实Mathlib HEAD git对象一致：

| 实际库模块（Mathlib前缀省略） | 实际SHA256 |
|---|---|
| Topology.Order.Compact | `e3d3e63921f09661fc6178857a0a72f28c27d41f7810f66607f24ac5919c7001` |
| Topology.Compactness.Compact | `cdc05494e34ec5d4163211223acf44d4c980629cac5542a52ca6d7360d80754e` |
| Topology.Order.OrderClosed | `011a07d8a57515c2a6bf066bf4ef24ff22eeffcc4d6115afd9ff22f5d45ded9e` |
| Analysis.Real.Sqrt | `1f19e1d6722b2f51c2cd676d0b28ede856c7915ac815b597cef4b3919040c204` |
| Algebra.Order.GroupWithZero.Basic | `28c0432242f3766a643689abd852cbf92fee391d314f76815e6977e64854103c` |

实际toolchain=`leanprover/lean4:v4.36.0-rc1`，lean-toolchain SHA256=`d581a24b57a4ae9e0b2132ca8ac7cc3ac336a9fc2751fe6b29414e2d434d54c4`（29bytes）；lake-manifest.json SHA256=`40e8e3385f2b0c8ae56fa9de6947301472379cb62eeb83247944827c38b8af6e`（3541bytes/117行）；真实Mathlib HEAD=`807d3836b165983210ee2ecf3cd28f239436949c`。共享broker只读成功，host key SHA256=`+IZMFu9Xx6FSAhvQhtvZ3MpV70v2d+XNWcequAbsp+c`，没有改连接/读凭据。本票绑定冻结scope与实际前置源/pins，不把正在发布J的工作树分支/旧HEAD当作必须保持不变的本门前提。

这些是静态声明环境/现成cache的事实，**不是**SourceEnergyGeometry新目标已经elaboration或内核验证的声明。后续实现仍须按actual fullbody/types→source/proof/private/generated/API→所有actualTYPE→最后机械证据做新的完整独立审查。本轮未运行Lean/API probe来确认这些API。

## 7. 最终独立裁决

JUSTIFICATION: **CORRECT。** 两个完整定义体与三个完整类型的参数/量词/实际能量语义匹配真实来源。远区集合在全部实delta、含空集时都是闭多项式约束的有界闭集；正q/H给真实紧Icc上界，无非空隐含门。样本下界从actual sourceTail的正尾阈值、q/n正域、真实平方根与8ΣX−E−nq恒等式推出，未偷用第三目标坐标界或概率/均值。第三目标先真有限平方和得能量平均可行区，再由同一几何下界和far门取消正n给delta分离，严格R>0/R≠1门完整。n0/q0只在定义总化，实际证明取消均在显式正前提后；所有弱不等式/energy端点及非正delta紧性都保留。实际公开库API/导入、12项旧源闭包、现成olean与pins未发现声明/环境阻塞。

本结论仅批准 **U17b声明/source/API门**，没有证明尚不存在的实现。输出是一般确定性几何/远区参数紧性，不是有限覆盖已经构造、Bernoulli指数试验、真实iid概率far界、KL/RN/Legendre优化、source3唯一全局鞍点、完整17/19/LLT、hW/WC或任何根闭合，也无最弱/最优/新颖性主张。根 **A/B/C/D、source3/generalKL/globalfar/full17/19/LLT/hW保持OPEN**。

本轮仅写拥有的新报告及授权run/statement-review.md；未改source/scope/receipt/旧票/shared/cache，未spawn/Lean/probe/build/rebuild/commit或下载raw完整日志，未读作者future notes/实施备忘。报告上传后另核两端SHA，交lead全文读取；声明批准前不实现。
