# SourceWeightedRecordStrip source01 独立完整源审查

STATUS: CORRECT（数学源与原始题意层；形式合格仍未授予）

审查对象为 `drafts/c2-weighted-record-strip/source01/SourceWeightedRecordStrip.lean`，SHA256 `646229c67baef64e212d61fca0d832e64c1dd108cf5ba3885f2bc949b40ad1e0`，63293 字节、1185 LF、0 CR。冻结为 `coordination/weighted-record-strip-root-freeze-v1.json`，SHA256 `d624c19f64ef6da930f4263737b02f5c840ffa339a47426f2820dc53d98bca60`。我完整阅读了 1–1185 行的全部声明、证明和局部数据，未发现数学关键缺口。三个完整声明与前缀逐字匹配冻结，12 个 statement let 分别为 2/4/6 个；源层新增全局 def/abbrev/instance/opaque 为 0。

`formalQualified=false`。本阶段没有该新源成功 elaboration/kernel 的凭据、原始成功对象、完整实际归属 TYPE、全部非定理 FULLVALUE 或递归 AX 凭据。因此本报告不声称 Lean 接受，更不把源阶段候选等同于形式证明。原始对象和实际归属凭据到达后，还须据其覆盖实际生成常量、私名、完整类型与任何非定理值；若修复新源，只刷新其受影响完整证明/类型及相应证据。

审查者为 `/root/weighted_record_strip_final_review`，与作者独立的新鲜上下文；配置指定 gpt-6.1-sol/xhigh。实际后台模型和 input/cached-input/output/reasoning-subset telemetry 均不可观测，记为 null。使用 math-theorem，不启用 math-ultra。本阶段仅本地只读数学来源及依赖，写入本审查目录；Lean/AX/构建/服务器访问/上传/Git/API/再委派均为 0。

## 原始数学来源与命题语义

精确原始输入取既有 proposal inputs manifest 约定的 `C:/game/shao/current/c12/main.tex`（SHA256 `beb00f718487e36de433175c97f1d500cb48e7a92ce5bd5ad5d62bb132122d06`）及 `supplement.tex`（SHA256 `b99f2ac4d2f39dd39772d98a5702b7a923c2f10f8730a08fc1b4cd6bba4742bd`）。完整阅读 main149–260、1151–1565、supplement5196–5588。任务初始描述的 `C:/game/shao source/history` 当前不存在；Root 已澄清上述 current 路径就是既有只读原始来源。未创建、迁移或改动来源目录。

main149–167 定义真实和、真实平方和、弱 crossing 和零能量约定；main1210–1216 的居中有界辅助法在各项中保持同一 iid 法。main1365–1380 明确第二墙 overshoot 的真实记录差和圆弧 witness，并将循环平均与加权 ballot 作为其承重依赖；该后续完整 overshoot 预算不在此新模块结论内。

supplement5198–5217 的 D_N 是 `(S_N-max_{0≤r<N}S_r)_+`，圆弧 witness 包含空弧、全弧，按 N 个带标签旋转计重。新私有声明正好覆盖该全体实路径恒等式与圆弧旋转不变性，不加入一般位置、无原子或正总和假设。

supplement5305–5310 的记录矩为真实 `(D_N²+βD_N)exp(θL_N)`，精确 .506 二次系数、β/√N、多项式 `1+Nθ²`，小参数 θB≤.01、θ√N≥1。新公共声明固定方差 1、居中、a.e. 有界 rho，并额外显式提供可测性及可积性；β 就是该 rho 的第三绝对矩。常数的存在量词在 rho、B、N、θ 前，未引入结果预算假设。

supplement5353–5429 的真实 floored strip 及 5535–5544 的加权 smallballot 使用 `S_j-x√max(Q_j+U,n/2)`，固定完整真实后缀后 U≥0。新公共声明将 U 写成任意 q≥0，覆盖 j≥12、j≤n、x≥1、B≤√n/(200x)、θB≤.01、θ√(j/4)≥1；统一常数在 law/n/参数之前。其 β/j 与 `(1+θ√j)^5` 是原 late-rank smallballot 的通用长度形式；在 j≥γ₀n、θ=2x/√n 时产生原文 β/n 与 C_{γ₀}(1+x)^5。没有宣称 θ=0 的普通 strip 界、端点尾界、低全能量付款、后缀 W 积分、完整 separated overshoot、原始分布返回或 C2/C12 闭合。

## 第一证明：完整循环恒等式（14–150）

局部 `D` 与冻结值相同。局部 rotate 用 `Fin N` 加法，与冻结的显式模 N 索引定义相同；`NeZero N` 来自 hN。31–34 用带标签加法置换保持全和，不把重复数值路径合并。

令 N=n+1，`M(j)` 是第 j 个旋转的前 n 步最大值，含零。45–63 从 maxWithZero 的完整前缀刻画得到完整最大值 `max(M(j),S_N)`。64–78 验证去掉旋转首项的尾块恰为下一旋转的前 n 项，包含 n=0 的空 Fin 分支。79–88 消费已接受的 Lindley 私有递推，得到 `max(M(j),S_N)=max(0,a_j+M(j+1))`。

当 S_N>0 时，该最大值严格正，故右侧未截断量非负。90–111 分别处理 M(j)≤S_N 与其反面，均得到 `D(rot_j a)=a_j+M(j+1)-M(j)`；等号/ties 在前一分支内。112–116 对全部带标签 j 求和，M 的循环置换和相消，剩 S_N。当 S_N≤0 时，M(j)≥0 直接使每个 D 为零，117–124 包含总和等于零。无正漂移延拓或未定义无限最大值。

127–150 对每一圆弧、每一长度 k∈Fin(N+1) 显式重标起点 i→i+j，并用其满射给出集合的两个包含方向；总和也不变，因此 sSup 的整个值集合相同。k=0 与 k=N 均保留。没有先将所有旋转当成不同数值路径、再除以轨道大小的错误。

## 第二证明：真实加权记录矩（152–722）

176–188 从已接受 weighted survival 和 witness moment 的全局存在式取得 CW、CM，再定义统一 `C=10+8CW+10000CM`；选择发生在所有法和参数前。199–218 由 a.e. 有界支持建立各绝对幂可积、β≥1 和 B≥1。θ√N≥1 联同 θB≤.01 排除 N=1；θ>0 也由大参数下界推出。原文提及 N=1，但本声明的 θ 条件在 B≥1 时不可能同时成立，该分支合法而非漏掉实质情形。

231–293 从已接受 extrema geometry 的完整 let 值与结论取得 `0≤L≤Σ|a_i|`、`|S_N|≤L`，并直接用有限支持盒对 `D^r exp(θL)` 作常数支配。D 的 measurable 由 head 坐标、prefixSum、maxWithZero 和 max 组成。294–303 正式构造 D、L 可测性和目标可积性；不存在把非可积积分按默认值处理后使用不等式的问题。

308–425 处理 βD。每个确定旋转在真实 product rho 法下 measure-preserving，故相关积分全相等；324–343 使用第一证明和实际旋转不变 mark 得到 `N E[Dexp(θL)]=E[S_N^+exp(θL)]`。无条件重抽样或期望恒等式冒充逐点恒等式。取 λ=1.001θ，θB≤.01 确保 λB≤.1。`S_N^+≤L` 与 `u≤exp(u)` 给出逐点吸收 `S_N^+exp(θL)≤(1000/θ)exp(λL)`；θ√N≥1 给 `1/(Nθ)≤1/√N`。`1+Nλ²≤2(1+Nθ²)`，且 `.5010005·1.001²<.506`，三次系数 `1.001³CM≤C`，线性新增项非负。最终 4000CM 系数有充足松弛。

426–711 处理 D²。`N=m+1`，m>0。实际映射 `J(b,v)=snoc(reverse(v),b)` 由真实 iid 末坐标分裂与前块确定逆序构成 measure-preserving map，目标仍是原 P。433–441 用前块终和在最大值以内得到 D≤b_+。若 D>0，原前块每一前缀严格低于真实终和；521–548 通过完整逆序前缀恒等式推出反向块在每个 k=0,…,m 满足 `S_k≥-b_+`。严格记录仅用来推出包含在闭 survival 中；D=0 分支直接为零，不丢失边界。

549–579 从已接受 witness concatenation/reversal 得到 `L_{m+1}(J(b,v))≤b_++L_m(v)`；正记录也确实推出 b>0，因此单步 witness 用 |b|=b 合法。580–587 得到可测非负 majorant G。510–520 已对真实乘积法以支持盒常数证明 G 可积。592–636 对固定 b 应用精确闭 survival at -b_+，并以 b_+≤B 将 `θb_++CWθ(B+b_+)` 放大至 `(2CW+1)θB`。

637–656 的标记付款为 `E[b_+²(b_++β)]≤E|b|³+βE b²=2β`，逐点正/负分支和可积性均给出。657–671 合法使用实际 map integral/Fubini/积分单调性。m≥1 保证 `√(m+1)≤2√m`，二次项从 m 放大到 N、三次/线性常数由 C 吸收；8CW 是宽松付款。712–722 将两个真正可积项相加，`8CW+4000CM≤C`，精确得冻结目标。

## 第三证明：真实闭记录条带（724–1183）

754–795 先取得全局 CE、CR，定义 `C=10+16CE·CR+4CE+4CR`。796–823 令 k=⌊j/2⌋、l=j−k，j≥12 保证正长度、k+l=j，且两者≥j/4；θ√(j/4)≥1 因此给出 k、l 的记录矩 guard 和 θ>0。没有遗漏奇数 j。

824–842 中 Pk、Pl 是同一 rho 的真实 iid 块法；H、T 为实际首块和末块。dl 是实际末块最后记录差，wk、wl 是同一 circularWitness。Phi 只在二次坐标使用 `clip z=max(-B,min(z,B))`，仍保留未截断的线性 prefixSum、真实末块能量 `energy v`、任意 q，以及 floor n/2。I(v) 是闭区间 `[-S_l(v),dl(v)-S_l(v)]`。无 oracle 值、替代 joint law、替代方差能量或去掉低全能量分支。

843–948：末块记录矩与 prefix/energy/max 的可测接口给出 F、E、Phi、varying-section indicator 和 G 可测；E 正是两个弱不等式的交。目标 integrand 和 G 各自都用真实支持盒常数支配，故可积；并未以目标积分上界反过来假设可积。

952–970：完整 accepted tes_head_tail_measurePreserving 将原 P 推送至 Pk×Pl，tes_head_tail_sum 对 g(z)=z 和 z² 给出真实总和、真实能量拆分。用反向前缀及反向末块前缀完整恒等式推导 `S_{k+r}=S_k+S_r(T)`，索引 r=0,…,l 均覆盖。

971–989：实际 j−1 前缀最大值 Mj 覆盖每个 k+r，其中 r≤l−1；因此 `Ml≤Mj-S_k(H)`，含末块零前缀对应原 k 时刻。这给出真正逐路径 `D_j≤dl(T)`，无外加正记录或全能量条件。994–1003 精确拼接实际 H/T 并处理 Fin 长度 cast，得到 `L_j≤L_k(H)+L_l(T)`。

1004–1014：在真实 a.e. 支持盒中 clip(H_i)=H_i，所以 `F(a)=Phi(Ta)(Ha)+S_l(Ta)`，利用真实 energy 拆分且保持 max(...,n/2)。这直接涵盖低于 floor 与高于 floor 两支，不需要借用 accepted hClipped 的“高于 floor 才等于未 floored wall”子结论。1015–1033：0≤F≤D_j 配合 D_j≤dl 产生 Ha∈I(Ta)，闭端点保持；witness subadditivity给出原 integrand≤G(H,T) 的 a.e. 点态界，E 外由 G≥0 完成。

1034–1073：B≤√n/(200x)、x≥1 给 `4xB≤√n`；Q=energy(v)+q≥0、T=0。accepted clipped statistic 的完整 global slope 范围 [1/2,3/2] 与 Phi 精确相符（仅加法结合和 +0 化简），故其固定 v 可测且有合法全空间坐标增量。accepted coordinate concentration 的 a 参数为 -S_l，宽度为 dl≥0，所获区间仍是 I(v)；其常数对 v 与 q 统一。乘以 `dl exp(θwl)` 后恰得到 `(dl²+βdl)exp(θwl)`，不是独立性假设下凭空拆开的随机标记。

1074–1092：先用 P 的 a.e. 点态支配，再通过实际 measure-preserving split 与已证 G 可积进行 Fubini，最后使用末块真实记录矩。全 joint law 自始至终是同一 rho-product；q 只是固定且任意的真实后缀能量参数，外部消费者仍需对自己的真实完整后缀进行合法条件化/积分。

1094–1183：令 t=θ√j。由 θ√k≥1 得 `θ+1/(θk)≤2θ`；l≥j/4 得 `1/√l≤2/√j`；`1+kθ²`、`1+lθ²` 各≤(1+t)²，故组合≤`4/j·t(1+t)^4≤4/j·(1+t)^5`。二次系数 `.503k+.506l≤.506j`，三次项由 CE,CR≤C 和 k+l=j 吸收，线性 CRθB≤CθB；4CECR≤C 支付最终系数。数值和方向正确，精确 .506 未被替换成 .51 或无定量的大常数。

## 消费依赖、私名和局部数据覆盖

九个 direct dependency 的当前物理 SHA256 已逐一与作者 DIRECT-DEPENDENCIES-v1 及 accepted v102 `source_files_sha256` 比较，全部相同；v102 PASS，Lean `v4.36.0-rc1`、mathlib `807d3836b165983210ee2ecf3cd28f239436949c`。复用其既有合格完整证明/对象/递归公理证据，不重复审查旧证明。实际接口阅读覆盖：

- FinitePath：Path、prefixSum、energy、maxWithZero 及其 finite-set 上下文/全值；prefixSum_zero/length、energy_nonneg、maxWithZero_le_iff/nonneg 的完整声明。head/ tail 的全值和 head_prefixSum 的完整声明从 SpitzerFinite 读取；不存在使用 Spitzer 的 generic subset-mean 假设。
- MeasurablePath：`{n : ℕ}` 上下文，measurable_prefixSum、measurable_energy、measurable_maxWithZero 的完整类型与定义语义。
- AuxiliaryEnergyCentered：absolute third moment ≥1 的完整量词、二阶和三阶 integrability 前提及方差归一化；本源从有界支持给齐这些前提。
- ActualOneWallRecordEnvelope：circularWitness 的完整 sSup 值、全弧/空弧/零长度分支及 namespace；其余 record envelope 定理均未消费。
- SourceCircularWitnessMoment：cwm_path_extrema_geometry 的 L/A/R 三个完整 let 值、所有 measurable/非负/上界/精确公式/反射项，以及 public small_parameter_moment 的全部 law/let/θ guards、完整指数。实际 owner-index 中 geometry 私名和 public moment 归属与源调用一致。
- SourceWeightedPrefixWall：concatenation 的 L/joined 完整 let、reversal 的 L/rev 完整 let、clipped statistic 的 clip/F 完整 let 及 Q/T/R/斜率/同一支持全部前提；weighted_closed_lower_survival 和 weighted_coordinate_concentration 的完整 law/β/P/L/闭事件/θ/区间/指数声明。其五个私名均已与 accepted actual-owner-index 精确对照。
- Lindley：`namespace Shao; variable {n : ℕ}` 下 private `maxWithZero_cons (a : Path(n+1))` 的完整类型；实际文件模块是 `Shao.Basic.Lindley`，声明命名空间是 `Shao`，源的 mkPrivateNameCore 两段恰据此构成，不误写成 Basic namespace。
- SourceTrueEnergyStrip：`namespace Shao.Probability`，四个 tes 私有声明完整类型及实际 accepted `all-owned-types.txt` 的四个 complete TYPE/AX 块：head_tail_measurePreserving、head_tail_sum、reverse_prefixSum、reverse_tail_prefixSum。隐式 n、显式 k/j、n−k 尾长度、原法/乘积法及反向总和均精确；私名属于 `Shao.Probability.SourceTrueEnergyStrip` 模块下的 `Shao.Probability.tes_*`。

源中每个 run_tac 仅以 literal module/name 通过 `Lean.mkPrivateNameCore` 找既有 accepted 常量，然后 eval 一个 `have hLocal := thatConstant`。没有 addDecl、动态新假设、修改环境或跳过 kernel 的逻辑；局部类型由旧常量完整类型推断。该机制仍需新源真实 kernel/actual-owner receipt 验证成功解析和归属，不能单靠此源阅读宣布成功。

已完整读到并审查的 proof-local 数据包括：第一证明 D/rotate/M/NeZero；第二证明 d/w/law、概率实例、A/rot/lam、R/J/Alive/G/K；第三证明 k/l/Pk/Pl/H/T/dl/wk/wl/clip/Phi/I/G/Mj/Ml/K/t。各初始值都在源内明确，局部参数不穿越统一常数的量词，不产生新的 oracle 接口。源码语法层没有新全局定义/实例；实际 compiler 生成 owner 数及非定理值数尚未收到，绝不以 3 个 source heads 推断实际 owner 总数。

## 尚待形式证据与范围限制

源扫描没有 sorry/admit/new axiom/unsafe/native_decide；这只是源扫描。允许的最终传递公理只有 propext、Classical.choice、Quot.sound。已有依赖的精确合格证据可以复用；新模块仍须同一最终 SHA 的成功 native/kernel、原对象绑定、env actual-owned 全 TYPE（含 private/generated）、全部 non-theorem FULLVALUE 和递归 AX。需检查私名引用实际命中本报告所读接口，所有新增归属与旧 accepted names 无重叠或覆盖；若新源变化，只重读变化影响的完整证明/类型。

本轮未发现数学反例、隐藏预算假设、law 替换、能量替换、闭端点丢失或常数不等式错误。结论只认证这三个冻结源陈述的数学推导与原题相符。C1 immutablev85 的已完成状态不变；C2/C12/OQ56 仍 OPEN，OQ3 仍 PAUSED_BY_USER。源阶段完成后本审查者实际 0 in-flight 写入/执行，下一依赖为 Root 提供精确新源的服务器证据或受影响源修复；不占 heavy slot。
