# PR331 原 C1 增长相对比较：独立完整最终审查

STATUS: CORRECT

审查对象仅为 `Shao.Probability.SourceOriginalGrowingRelative`，PR331 头 `bb0afc1532827c5f13370fb05c258b0e948b1c80`。完整生产源为 544 行、30869 字节，SHA256 `44882c03a4f3820730a772b6299125d976b79ff2fa25dbaf4dceafc7f74d50a4`。本审查确认该精确版本的原 AE iid 两符号、正前缀、x≥1 单侧相对比较，以及实际零能量的 Rₙ(x)Ψ(x) 代价；不存在尚未支付的目标概率接口或本模块数学证明缺口。此结论不构成完整 C1/C12 根关闭，也不是合并授权。

## 独立性与实际覆盖

审查者为全新非作者 `/root/original_growing_relative_final_review`，配置 gpt-6.1-sol/xhigh；实际模型、努力等级和 input/cachedInput/output/reasoningSubset 遥测分别不可获得，均记 null。作者为 `/root/true_energy_strip_author`，其源、执行与生产元数据权已在 SHA256 `36e1d98fb100733459b4751602787cc6741619108ab7c3815cfd5b3a5a8116d2` 的 RELEASE 中释放。本审查仅拥有自己的审查目录，无 production、冻结、coordination、缓存、执行或合并写权。

已完整阅读新源全部 544 行，包括唯一公开头、所有 proof-local 定义/实例/证明、全部归一化和 AE 回迁。已逐字完整阅读原成功对象导出的全部 11 个实际完整 TYPE，未压缩或省略重复类型字节；已读原审计驱动、完整 owner/AX 清单和零非定理值库存。没有读取巨型机器 theorem proof value；源级证明全部阅读，机器证明信用来自原成功内核。本次没有 Lean、审计、旧 proof 或成功检查重跑，没有新代理、侧栏、Goal、调度或外部评论。

原文完整读取范围为 main.tex 150–207、288–860，以及 supplement.tex 72–178、2045–2079、3851–3909。原文摘录包已从实际只读 TeX 按编号逐字重建，完全相等。两份原 TeX 的哈希与 `source-inputs.json` 相符。该原文限定了真实原始平方和、弱乘法 crossing（包含全零样本）、严格 survival 补集、时间 1,…,n 的两符号最大值、原 p∈(2,3] 矩、Lₙ、Rₙ 和同一 enlarged Iₙ。

## 冻结与接口绑定

最终完整公开头和其上下文与冻结文件 SHA256 `2a11145099e5b021e7716ae63aac54c06e0ba9e85d5e2ae8c00edab2ff62ae5d` 逐字一致。一个公开定理、12 个 literal head lets、零 head letI、零源级全局 def/instance/private helper。候选到冻结仅明确增加 async=false/maxHeartbeats=5000000，数学头未变。数值常数 C 先于 ρ⋆、p、原律、n、符号和 x；最终域仍使用给定 0<ρ⋆≤1/16。保存的 activation 时间为 19:25:51Z，早于第一个保存的 source01 快照 19:32:26Z；最终 source05、producer05、audit05 的物理时间顺序也一致。时间证据仅是保存记录和当前文件元数据，不声称证明不存在未记录的更早草稿。

已完整读候选提供的 consumed interfaces、probability、analytic/normalization、full-y、definition values 与 namespace contexts。39 个带行号的旧头片段均按声明行与实际已接受源逐字匹配；FullY 两个完整头及补件两个完整旧头均是对应源中的精确连续文本。旧 consumed-boundary 包确实将两个头截于 let 赋值前；本审查不使用该截断内容作为完整头，消费 SHA256 `81046e06dbd08ca087b1186fa0e32057894b3083b1c9a048f2d5ebda68214c72` 补件中的完整 law_data/variance_bounds。

31 个选定旧源的实际本地字节同时匹配不可变 v82/v83 source maps；9 份精确旧资格的哈希、对应源/对象对、完整独审 MD 与 coverage 哈希均匹配，按已接受资格复用旧完整证明/TYPE/VALUE/AX。FullY 为 f17b6443…；当前 bounded fixed-cutoff 为 d7128716…，使用 integration-v67 的 `common-fixed-cutoff-exports-root-qualification.json` 中准确 SourceBoundedYReflection 行，而非旧 eca369… 资格。本次未重读这些旧证明或重跑它们的成功检查。所有实际使用的接口已单独核对条件与当前调用值。

## 完整证明核对

1. **统一常数（63–127）。** L、L2、alpha、epsilon0、t0、eta0、epsilon 均为已接受 FullY 的同一 literal 值；兼容头给 epsilon=1/81977600 及正性和两个上界。eta 的四项正，支付 cube、eta0、邻域 budget 与近零尺度；K−1、Gaussian 两处分母及全部除数严格正。coarse、pullback、full-y、endpoint、near-zero 的数值常数在任意律之前取得。Ccan、Cq 和最终 1+Ccan+Cq 因而统一于所需全部参数。

2. **实际 canonical 域与有限上确界（128–199）。** hCanonical 只接真实概率律、有限二阶矩、均值零、nE a²=1 与原 p 矩。Ibar 使用固定 1/16 仅作内部吸收域。权重 w=RΨ 的紧性、连续性、严格正下界由实际 accepted 接口提供；F0、G∈[0,1] 给 |E|≤1，因此 sSup 有限，不需 CDF 连续或无原子。moment 分支逐项给 x⁶≤n 与 nEF(xa)≤1；small-budget 分支以 sample-size lower 和 F 幅值单调性给相同 coarse guards。没有将“部分有限恒等式”用作原根证明。

3. **三个分支与真实邻点（200–295）。** 大预算由 coarse 支付 (Cc+2)Ψ≤C1RΨ。近零分支由 R(0)≤R(x)<eta 和 A0eta≤1/4，得到 x≤1/2；实际 near-zero CDF 界连同 Ψ(1/2) 下界支付 C2w。余下 D3 同一固定截断 x、epsilon、条件律、N、pN、noise 始终不变。正邻点由 R(u)≤8R(x)<8eta≤1/16 自身 small-budget 分支进入 Ibar，再给 |E(u)|≤LMw(x)；不要求 moment 区间或原给定 ρ⋆ 域对邻点封闭。非正邻点的严格正能量事件为空，E(u)=0。

4. **去平滑四接口与闭合（272–308）。** pullback 实际给 |F−G−E/pN|≤Bpull w；同一 epsilon 的 endpoint 给 |Fend−G|≤Ce w；FullY 的完整结论对实际 gamma≤y 和所需邻域给同一条件 P、同一 full noise 上的 Jmax/Jend 与 Fubini 后 bound；第四输入是上一步实际邻点界。源中逐个代入 weighted_desmoothing，所有 epsilon/eta0/geometry/cube/eta/D3 guards 均支付，取得 Cd+M/4。条件均值未被设为零，真实平方和未被方差替换。全域 ratio 界 B0+M/4 与有限 M 给 M≤4B0/3，从而 canonical 弱 crossing 的真实 R(x)Ψ(x) 比较闭合。不存在 hImage/hRegular/hSmall、可积性、任意 HasLaw 或目标误差 oracle。

5. **真实 Gaussian 尺度 Q0（309–365）。** 大预算使用全零路径属于弱正前缀 crossing，再除以固定 eta。小预算证明 Q=0 蕴含每坐标零并属于 N；可测 N 上的 `cond_mul_eq_inter` 与精确 cond(P0,N)=P 给 P0(Q=0)=pN P(Q=0)≤P(Q=0)。实际 conditional endpoint zero-energy 头给 exp(−(1+x)⁶/(16R²)) 和 sqrt(2π)RΨ 的界。最终 Cq 支付原 Q0；没有使用 16R(0)、紧窗 CR(0) 或 PR327 信用。

6. **原尺度与 AE iid 实际产品律（366–408）。** accepted raw normalization 提供原 sigma>0、scale=sigma√n>0、真实归一化矩及 beta=Ln。`iIndepFun.map_fun_eq_pi_map hX` 直接使用各 Xi 的 AE 可测性与实际 IdentDistrib 边际，构造 map population μ=ρⁿ 和 HasLaw；没有添加处处可测性或可测空间完备性。normalize 为可测实际除尺度映射，energy(normalize a)=energy(a)/scale²，零能量集合 preimage 精确相同；原 rawEnergy 就是原样本有限平方和。

7. **符号与原域回迁（409–491）。** s=±1 的实际标量 pushforward 保持二阶矩、均值、p 矩；|s|=1、s²=1 和 truncationF 的偶性逐项给相同 Ln/Rn。Measure.pi_map_pi 给真实 signed 路径 law，零能量保持，正尺度 crossing 由 accepted 精确头回迁。x∈原 I 的两个分支分别直接给 moment 条件，或经 ρ⋆≤1/16 限制到内部 Ibar；最终声明没有更换域。upperMax 保持时间 1,…,n 和原自然顺序。n=1、闭 moment 端点、原子、墙等号和 Q0 均未排除。

8. **可积性、严格补集与真正正尾除法（492–543）。** 原 crossing/survival 是 canonical Borel 事件的 AE preimage，其指标真实 AE 可测且绝对值≤1，于概率 μ 上可积。crossing 为 NullMeasurable，survival=crossingᶜ 逐点成立，因此 μ.real survival=1−μ.real crossing；无需原 Ω 完备。两绝对误差相同。标准 Gaussian 尾对每个有限实 x 严格正，最后除法合法并给公开相对比值结论。

## 全实际所有者、值库存与公理

原驱动遍历完整 env.constants，以 `env.getModuleIdxFor?` 等于实际模块选择全部 owner，未用名称前缀筛选。实际 module-local index 为 5136。11 个 owner 均为 theorem：1 public+10 generated _simp；零 non-theorem、definition、opaque、global private、instance。原日志无 VALUE 块，导出零值库存与实际 all-owner 清单一致；proof-local let/letI 的数学值已在源中全部阅读，不冒充全局 definition 库存。

公开实际类型保留全部量词、原 AE 假设、12 个 literal lets、原 I、两符号 x≥1、两个指标可积性、Q0、弱/严绝对误差和相对比值结论。10 个生成类型分别为集合补集成员、非零整数幂、2/3/4≠0、全序 not_le、preimage 成员、特征零 n+1≠0、非零乘积与非零自然幂的等式化简。每个完整类型、逐名类型 SHA256、AX 和源级唯一 proof 的关系均记录于 full-review.json；它们没有引入额外概率假设或新全局定义。全部读的是原 pp.all/deepTerms/proofs 完整文本，原导出三类省略符计数均零。

原 collectAxioms 对每个实际 owner 递归执行，驱动逐个拒绝 whitelist 外公理。公开定理与 _simp_7 使用 [propext, Classical.choice, Quot.sound]，其余仅 [propext]。这是实际递归结果，不是仅审公开头。原完整审计 payload 的 11 段从 audit05.log 重建后与 all-owned-types.txt 逐字相等，整体 SHA256 `1e5f9a410b6f91bdb40a6ffccbd0af88c3d8b5d30733914b5aaa71b1a919e8b4`，所有逐类型哈希均独立复算匹配。

## 原机械证据与物理核验界限

唯一成功信用是 check05：完整 source05 与最终源相同，kernel_rc=0；同次保存调用的原 producer05.olean SHA256 `af7315d52b15def266c76b3492399979981faaf0050f0df190d4bdc5461e3ebc`，audit_rc=0。当前导入位置的对象与该原对象字节相等。原内核日志 SHA256 `667f80d046bd58a1000545cb5f915face664fd8706119144b7cf41fc09604349`，0 error、0 sorry warning；31 个 warning 行不影响原 rc0。原审计日志 SHA256 `abdc0bd109c371415d1725afc73228ce17d0bbcf21ea490f78fdd6372e9acf3d`。原审计驱动、owner index、零值文件、check05、失败保存清单和原源/对象均物理哈希匹配。

通过 transport_client 的一次有界只读物理核验，66 个指定服务器文件（包括31旧源、9资格对象、原成功源/对象/驱动/日志/导出及四次失败源/日志/回执）全部匹配。服务器工作树 clean，HEAD 与 PR 头相同，commit 中源 SHA256 相同且只增目标一文件。固定 Lean 为 leanprover/lean4:v4.36.0-rc1，mathlib 为 807d3836b165983210ee2ecf3cd28f239436949c，packages 指向只读 shared-v34。GitHub connector 独立确认 PR open/unmerged、一个提交和目标一文件。19:50:25Z 实际观察无该模块 Lean 进程；审查自己的远端请求均已返回，无在途操作。

check01–04 均 rc1，源/日志/回执保留且哈希匹配，没有对象或 AX 成功信用。尤其 check01–02 保存回执的通用 scope 字符串写 WHOLE…，但实际是未完成末尾公开目标的失败诊断；本报告明确覆盖该标签，不将其称为完整 pass 或完整成功检查。check03–04 是完整源失败。没有删除失败记录或重跑成功源。

物理核验是本次读取时的指定文件哈希、现存 Git 对象与日志 payload 绑定；未重执行内核，未独立复现原 CPU/内存/锁持有时序，未把当前 mtime 当成不可篡改执行证据，未重新物理遍历全部742旧对象。原 pinned kernel/all-owner recursive AX 的资格来自现存 source-bound 成功收据及匹配原对象/日志，结合本独立完整语义审查。此处不存在需要追加 Lean/AX 重跑才能覆盖的源变化或证据缺口。

## 范围与交接

本模块正确地闭合原单侧 x≥1 增长相对比较这一个精确单元；PR327 紧窗是独立已 Rootqualified 的旧源，本模块没有借其证明信用。C2 residual/原律回迁、双墙、联合 endpoint、完整 C1 根装配及 C12 全根均不由本审查宣称关闭。C12/OQ56 OPEN，OQ3 PAUSED_BY_USER，OQ4 仅其单独原有限范围已验收。原文 Jing–Shao–Wang2003、Pinelis2011、Shao–Zhou2016、Liu–Shao–Wang2013 与 Lindley1952 的来源归属保留；本审查是正确性与源忠实性判定，不是新颖性或外部标量/Fourier 引擎的新增认证。

可供 Root 一次全文读取的最终结论为 CORRECT。Root 可按精确哈希复用本完整独审与唯一原成功检查；本审查不修改源、不给作者补证建议、不自行合并。审查 RELEASE 仅释放自己的 review 写权，实际零在途；作者旧模块权不因本审查释放而恢复。
