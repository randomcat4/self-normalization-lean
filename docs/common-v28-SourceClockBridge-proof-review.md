# SourceClockBridge 独立完整证明审查

STATUS: CORRECT

FORMAL COVERAGE: LEAN_FULLY_CHECKED（仅本冻结三条source-clock桥及其真实导入依赖）。

SCOPE: 冻结三条公开定理、唯一手写私有辅助及完整 source→statement→proof 忠实性。独立 reviewer，从未编写本单元实现。只写本报告；未改数学源、冻结scope、旧票、缓存或其它文件，未运行本机/服务器Lean，无子实例。复用此前独立声明审查及已验收依赖，先完整检查实际360行证明，再读取作者最终机械回执，并通过获授权broker独立只读核对现有服务器工件，不重复成功目标。

## 冻结、格式与独立签名绑定

| 对象 | SHA256 |
|---|---|
| 最终LF SourceClockBridge.lean，360行/18678字节 | `ced48edd68d62919d066dd1bd964374a166bd5ccb47c309849ccbe6009f1fe65` |
| 原已读取CRLF源码，360行/19038字节，历史保留 | `9f00b17703aa2580d826eb281dee48dff053f2a937acc36dfb97514d7f44594f` |
| 冻结 SourceClockBridge-next-scope.md | `673ad95d64459843af58dd563696a600f3820c662cd038bf5baff7b419b6877c` |
| 独立 SourceClockBridge-declaration-review.md | `9ffbaf9313a71907db6dcad6411b4d986b289ef6489aa2543aab614db04fdcad` |
| 已验收 SourceTruncationBridge 实现 | `05321c22d1b2ea178fbc116178af345f4186bfce51011c8242b4ccfd2e0dd7d1` |

先完整读取9f00版本；作者随后仅为格式门转换新模块为LF。本 reviewer实际读取最终ced48版本，CR字节数0、360个LF、单末尾LF，独立计算 `final.replace(b'\n', b'\r\n')` 的SHA256恰为原9f00全值，证明当前与先读历史源的差异严格只有每行CR删除。三份完整公共签名再次独立提取，与scope Lean块空白归一化比较3/3相同、名字集相同、零新增定义。直接扫描最终完整原文，sorry/admit/axiom/unsafe/native_decide无token匹配。

实际原source与依赖仍为此前精确绑定的main.tex `beb00f718487e36de433175c97f1d500cb48e7a92ce5bd5ad5d62bb132122d06`、supplement.tex `b99f2ac4d2f39dd39772d98a5702b7a923c2f10f8730a08fc1b4cd6bba4742bd`。其main:423–455/491–499/546–556，supplement:836–858/3078–3150/3894–3907分别给实际固定N_x、真实条件iid/raw Q、两个坏事件及小x方差分支。相关段落已在本reviewer's独立声明票中实际完整核对；当前实现没有改其事件、law或quantifier。

承重公开接口复用已接受实际源码：ConditionalIID `855c2eb0e560ac9372505f8b41551a9895b9eb753be3ce2b3f3752be845af787`、ClockControl `c7782d17c1b6dec827cde84d1d44f9b6cb7a7d8dd166bee2183cac4d2dd5cdba`、FiniteIID `d1b565489199d55af70a27c31a0f803a2b7433e78c9197a361b3c10c0598845b`、FinitePath `898262898f9c088e2d10e6238e411b4397387b21b1b71a2b545c5edef936e1bb`、GaussianTail `f166fab0061199e25d0391bbde5c977905e368513a6e0e18b492877c65160922`。没有用未验收的目标概率作为依赖。

## 实际声明与第一条证明，18–109

三条声明完整保留原μ/ν概率、原X可测/独立/IdentDistrib、原平方可积和源预算。第一条仅要求x≥0、0<ε≤1、R≤ε³/8；第二/三条另保留真实nEνz²=1、原Eνz=0、ε≤1/8。第二条严格保留y≥2与|y−x|≤1/[2(1+x)]。各自A=⋂i X_i⁻¹{|z|≤ε/(1+x)}、μx=cond μ A、ρ=cond ν B是实际已有对象；固定x后不因y改变law。零新增数学定义。

41–68行先证B闭、A与严格尾可测。原IdentDistrib给真实单坐标map=ν，所以每个尾质量相同；Aᶜ逐点精确等于有限并 `{h<|X_i|}`，不会丢失cutoff处原子。真实有限并real概率界与已验收原尾预算给μ.real Aᶜ≤R/ε³。

69–83行在ε³>0后由小预算得补集≤1/8，再用概率补集恒等给μ.real A≥7/8。非零μ(A)在安装μx概率和调用generic conditional-vector theorem之前独立证明，未循环使用条件iid。

84–109行的关键边界处理正确：hBpos被写为**收到实际i:Fin n后**才证明ν(B)≠0，使用A⊆X_i⁻¹B和原边缘。hjoint通过已验收 `indep_cond_joint_map_eq_pi` 在同一个A上给实际联合map=ρⁿ；hcoord内部才按该i局部安装ρ概率并映射eval得到真实边缘。之后用真实联合map判据恢复独立，最后构造IdentDistrib，measurable项由原hX与id直接给出。

因此虽然没有显式case n=0分支，空Fin依然正确：A=univ、联合law为空产品，hBpos/hcoord/边缘的索引均无实例，未在空样本全局宣布ρ概率。第一条未增加n>0、normalization、原均值零或ν(B)>0前提。hjoint不是一个假设的条件iid结论。

## 第二条：精确坏时钟双事件与R支付，111–193

实际bad是同一μx下 `prefixSquares (samplePath X) (n/2)<1/16` 与 `energy(samplePath X)∉Icc(1/4,2)` 两概率之和，samplePath不改变原X，clock始终为raw平方和。n/2是自然数floor，半事件严格<，最终好区间闭，端点与原子保全。

158–174行先把更小源邻域1/(2a)合法放宽至1/a，a>0。第一条产生真实μx概率、条件iid及共同边缘；已验收scalar law_data给ρ真概率与支持。variance_bounds的前两conjunct确是raw nm2上下界，并未把centered variance替代m2。clock_inputs给三项真实numeric门，其签名不要求conditional mean0；所有门从原始h2/N/M/ε/R证明，而非被另加为premise。

175–178行以参数 `(μx,ρ,X,h,y)` 精确调用已验收 `iid_bounded_clock_bad_probability_le`；h≥0、y≥2、真实支持、raw二矩两界、三numeric门均实际传入，故第一目标的2048√(2π)及raw cube支付完全匹配。

179–192行从同一固定x的nearby_payment取 `(1+y)³nm3≤16R`，使用tail非负乘界给32768√(2π)R·Tail(y)。再以真实高斯local comparison上侧、R≥0乘界，得到32768√(2π)exp(2)R·Tail(x)。未把R丢成粗H≤1，也没有用未证样本高斯近似或在y变化时换截断law。

## 唯一私有 helper：真实平方和方差与切比雪夫，195–263

`sc_final_clock_chebyshev`的所有泛型门被保留：μ/ν真概率、原族独立、各真实共同law、ν下真实四矩、raw nm2∈[3/4,4/3]。helper没有假设目标概率界或conditional mean0，也不需要原X额外pointwise可测，因为IdentDistrib已给所需AE可测性。

213–229行实际定义Y_i=X_i²、Q=energy(samplePath X)，以真实IdentDistrib的可测平方复合，把ν的z⁴可积提升为z²∈L2再传给每个Y_i；有限和在L2中，故Q是真L2。积分有限和使用每个Y_i真实L1，得到EQ=nm2，非总化不可积积分。

230–249行平方复合保留独立；`IndepFun.variance_sum`明确消费每个Y_i L2与互不相同坐标的IndepFun。真实边缘variance相等给Var Q=nVarρ(z²)。`variance_eq_sub`在z² L2下给Varρ(z²)=m4−m2²≤m4，乘n≥0得Var Q≤nm4。没有假设Q与坐标独立、误把Q当∑(X_i−EρX_i)²，或将原ν全局四矩塞进条件源。

250–256行把最终坏区间之补集严格分成Q<1/4或Q>2；EQ在[3/4,4/3]确保对应偏差至少1/2，包含方向是bad⊆{|Q−EQ|≥1/2}。257–263行在Q真L2与δ=1/2>0上调用Chebyshev；ENNReal界转real时使用有限ofReal上界及非负方差/平方分母，不把∞的toReal=0当概率事实。得到bad≤4Var Q≤4nm4。所有helper局部辅助均在完整证明内核对。

## 第三条：保留四矩与R、所有x的常数，265–358

302–318行重新从原始输入和第一/scalar桥得到真实μx、ρ、第四矩可积与raw二矩两界。将它们传入唯一helper获得首项bad≤4nm4，未在小x分支调用y≥2的clock指数界。

319–334行从paid_moments的**正确conjunct**分别取得nm4≤h·nm3与nm3≤2R/a³，先用h≥0，再以a>0的真代数给nm4≤2εR/a⁴和bad≤8εR/a⁴。由8ε≤1、a⁴≥1、R≥0给统一粗界bad≤R；过程中没有除R、m3或n，x=0亦合法。

335–357行先取实际Tail(2)>0及Tail(x)≥0。若x≥2，调用第二条y=x，其邻域为0并满足hy；丢掉非负半时钟概率，取得32768√(2π)R·Tail(x)，无需exp(2)。若x<2，实际tail反单调给Tail(x)/Tail(2)≥1，故bad≤R≤R·Tail(x)/Tail(2)。两branch最后仅加一个非负常数项，得到冻结的 `[32768√(2π)+1/Tail(2)]R·Tail(x)`。x=2进入大支，x=0进入小支，所有x≥0已覆盖。

## 数学裁决与未覆盖部分

完整数学/源码裁决为 **CORRECT，GAPS: None**。实际三签名、原source、360行全部证明和唯一私有helper无关键缺口。所有概率/条件iid门由原始输入产生，原条件均值可非零，三个目标与精确事件/常数一致。源γ约束未被设为0或偷作概率前提；y≥2的generic clock范围与单独small-x方差分支保持分离。

这里只关闭实际N_x条件sample和clock概率支付。晚块signed identity、噪声、平滑/解平滑、Fourier域、原bad-large、完整夹逼与C1/C2根仍为独立依赖。不能将b_x支付等同于整个source sandwich或原根完成。

## 数学判断后的最终LF机械工件独立核验

完整数学判断形成后，读取实际作者 `SourceClockBridge-author-receipt.md`，本地SHA256 `14e6257bd8baffe279eec2325f0fc7af9df847e029cdffc8366e67b4f6b79f1a`，与作者/协调者提供值一致。随后按root要求，用现有 `tools/server.py` broker作两次只读文件/哈希/Git核验，远端均exit0、stderr为空。没有运行Lean、重做target/Audit或写cache。

实际worktree为 `workspaces/takeover-source-clock-bridge`、branch `author/takeover-source-clock-bridge`、HEAD `bf6ba73b36aacc572a8d26cbf8af87ee3d680442`，目标source的Git状态为空。真实目标SHA为最终ced48全值，与本地360行/18678字节相同；没有拿历史9f00 target回执替代本次绑定。三直接项目依赖的真实字节和14个完整project依赖closure的哈希逐一与本地已验收源锚一致，未发现source不匹配。closure总计15源（目标+14既有依赖）；SourceTruncationBridge仍为05321全值，没有随新模块格式修复而被改变。

本 reviewer实际完整读取服务器 `.author-source-clock/OwnedAudit.lean`（2438字节），其SHA256为 `d0a0442f1474210d94dfa268f46db21424272e4958ba753fdbb8deba9f48e6fe`。它通过env.getModuleIdxFor?/真实moduleNames选出全部导入Shao-owned常量，逐项Lean.collectAxioms并throw任何非标准公理；target单元以exact module `Shao.Probability.SourceClockBridge`识别，不按声明名prefix漏掉private/generated。它分别检查三个公共目标存在、theorem种类和精确模块归属，打印实际elaborated types并单独#print axioms。

真实 `audit-02.log`为52469字节，SHA256 `3174771a735419c7fa66125b6f18c1c44c583e8f635f6684070849c1e3aa018f`。本 reviewer对完整实际日志独立解析：321条DEPENDENCY_DECL名字各异、21条TARGET_DECL名字各异，target全为theorem，所有axiom列表均仅在{propext,Classical.choice,Quot.sound}内，零违反项。21=3公开+1手写私有+17生成证明；**321是全部导入Shao常量，包含这21个，并非额外321个依赖**。实际全部target名字和owner已读；私有helper及其生成_simp项均被覆盖。

三个实际PUBLIC_TARGET/TYPE已完整读取，逐项保留n=0可用的首条签名、7/8正事件质量、真实cond/product/iid/边缘，后两条原normalization/mean/ε门、y≥2/小邻域、严格半事件/闭好区间外、raw cube/fourth及全部常数。与本地已独立匹配冻结文本一致，无源外新增前提。实际汇总确为3 frozen、21 target constants/theorems、321 full-import constants、whitelist-only；三个单独#print axioms也只有标准白名单。

真实 `check-06.log`与 `diff-check.log`均0字节、SHA256 `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`。真实新目标olean为1043488字节，SHA256 `7a7eceb94c1293f94beb6739a7a9ef01d0741007696f9a1ec17f00693d3f0aeb`，与最终作者回执一致。原target/object和audit的实际exit0由作者回执记录；本次独立读取确认其绑定产物、完整成功审计记录和源字节，未声称又执行一次内核检查。

真实 `lean-toolchain`为leanprover/lean4:v4.36.0-rc1，SHA256 `d581a24b57a4ae9e0b2132ca8ac7cc3ac336a9fc2751fe6b29414e2d434d54c4`；真实manifest SHA256 `40e8e3385f2b0c8ae56fa9de6947301472379cb62eeb83247944827c38b8af6e`，实际只读Mathlib checkout HEAD为 `807d3836b165983210ee2ecf3cd28f239436949c`。作者记录实际Lean commit c9afcddf514a6772bd4d649f7cfc04eff0b9f15e、Lake5.0.0-src+c9afcdd，本reviewer没有再执行版本或Lean命令。

最终裁决：**CORRECT / LEAN_FULLY_CHECKED，GAPS: None**，接受最终LF源码ced48edd…的三条完整目标与21owned/321full-import公理覆盖。根协调者仍需将此源、作者回执与独立报告接入最终公共import/manifest及集成树gate。只有source clock概率桥闭合；未把本结果提升为完整Fourier/平滑/解平滑或C1/C2根完成。
