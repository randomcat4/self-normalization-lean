# unit196 repair-01：两个完整证明的独立续审

STATUS: CORRECT

此裁决是**源码与数学续审通过**，不表示 native02 或公理审计已经成功。精确新源为 `bc64d3e11a64f62ad654305ce579c1779546d4df37b5593090105af910502edc`，33066 字节、742 LF；当前 `qualified=false`、`actualOwned=UNKNOWN`，本轮未收到成功原始对象。

上一轮源 `843626299442d229a46db6c462474a046b02b90ed9a522be1848917b66cca002` 的 SOURCE-REVIEW（`ae120ad245d5ff39e7f0c1a2af81214270643736b23d97285f2aed0c2c9a6246`）仍保留 CRITICAL_GAPS，其首次 native 的 RC1/3 errors/22 warnings/no object 也完整保留。本报告仅对新的、事前冻结的限定修复作续审，不改写旧失败。

## 角色、复用与精确读取

同一独立实例 `/root/oq56_studentizer196_final_review` 按父 OQ56 lead 授权仅写 `final-review-01/repair-01/`。先独立复核原8份 payload、原 manifest `3ab33316371a2d3b18a26f7efd78b716ec05510fb6e8ef213a76813dd448c7df`、原 DONE 与 SOURCE-RELEASE0 均未改变，全部零状态保持，再实际写入本轮 RUNTIME-ACK。没有修改作者、原审查、冻结或共享文件。

实际完整读取新 D16 L208—250 与新 D22 L486—738 的声明和完整证明，不只读取差异片段；同时读取 affected-proofs 的全文本绑定。其余 D12、D13、D14、D15、D17、D18、D19、D20、D21 的九个完整证明仅按实际未变字节及上一轮完整独立审查复用，没有再次进行完整数学阅读。22头、11RHS和全模块数据/作用域契约以独立字节核对确认不变。

新增主要声明包 `pinned-abs-add-le-primary-source.json`（`09ed47b06dcc15617be3d8187431ff84a3f402953bf3d6b593a35e0232cd5119`，19865字节）已完整读取，包含固定原文件全文、L121—127完整声明及L1—122完整词法前缀；其 fullFile 的独立摘要等于实际来源 SHA `574421adeb1391adcc9008c7e4a7981b2b444416f5d63ecf3ec48a4454851463`、13056字节。该包是主要源码证据，不冒充新的 Lean 反射 TYPE。

请求模型/强度 gpt-6.1-sol/xhigh；实际自省 UNKNOWN，input/cached-input/output/reasoning-subset 均 null。本轮执行、heavy、inflight、外部待处理、子实例均0；未运行 Lean/AX、服务器、网络、Git/API、上传或缓存操作。

## 精确修复的独立重建

父 delta02 `b2cb61d78de2424d952a3da2ff7412f433c18aedcb1ebfbe9eab34bda078ef4f` 在修复实施前冻结三种替换。独立从旧8436源逐次计数并替换，实际次数为 **[1,3,1]**，重建结果与新bc64源每个字节相同。另用独立的统一补丁解析，对 exact-source.patch 的三个 hunk 逐行核验旧上下文、旧/新起点及行数，在内存应用后再次精确得到同一新源。没有运行作者的修复脚本。

全部五处文本编辑正好为：D16的一处规则拆分/β规约、D22三处三角接口名修正、D22最后一处归一化与有序相加。没有其他源编辑、警告清理、声明/假设或承重数据更动。

独立本地静态结果是 **859/859 PASS**、**64 个唯一精确本地绑定**、**285 个新源字节段**。这些计数来自本实例自己的检查，不复制父946项或旧690项。它们只核对字节、文本来源与契约，不代表内核证明成功。

## D16：完整实际居中行公式

新的完整 D16 仍全称量化原 n、Ω、g、r、x、索引 i，并仅要求 r 逐点对称与 n≥4。其数学链完整且正确：

1. N≥4支付 N、N−1、N−2 的非零性；旧 offDiagonal 接口对实际样本 r 矩阵给 Σψ_i=2F。
2. 同一个 u_i=ψ_i/(N−2) 给 Σu_i=2F/(N−2)。hrow 的完整有限和展开为 (N−2)g_i+S+ψ_i，未用核函数 r(a,a)=0 或观测互异。
3. 将同一个 actual rowMean 和已审 D15 的 actual U 代入，再展开 center/mean，目标准确是原公式

\[
q_i-U=\frac{N-2}{N-1}\left(g_i+u_i-\frac{\sum_j(g_j+u_j)}N\right).
\]

4. 新L247先只重写有限和与hU，L248 `dsimp only` 规约现有 `(fun j => g(x j)+residualU ... j) i`；L249再用原 frozen residualU_eq_erased_row。这里没有更换 u 或引入新函数，只暴露同一个函数应用的定义相等项。最后仍以原三个非零分母进行 field_simp/ring。

因此旧L247缺口对应的源级原因已准确处理，整个证明的原样本、对称性与系数没有改变。新完整证明体 SHA 为 `0927227d6d5cc886c6920b6bb03fcfcdff856a62a729d5c80840f3f79c86b043`，1651字节；真实 tactic 是否被内核接受仍待native02。

## D22：完整界与两处修复

已重新完整阅读新 D22 的全部证明。原 hsym、n≥4、K/q≥0、y≥1、实际 F/行范数界和同一样本 G_y 均保留；没有补入 s>0、S1、d小、q整数或额外概率资格。

L503—645的完整计算仍正确：N²≤4(N−2)²给 J≤4Kq；N/(N−1)≤2 与1/V≤2给 |D|/V≤4Kq/√N；非负平方比较给 √J/√N≤2√K√(q/N)。S1四项分别以2y/√N、162y/√N、16√K√(q/N)、16Kq/N上界。J项的 N≤4(N−1)V²直接使用 G_y 的 V²≥1/2，而不是从较弱的V≥1/2误推。所有除法均有原正分母；K=0/q=0/J=0不会被平方比较排除。

**三角不等式接口。** 新L660、664、669使用全局 `abs_add_le`。固定主要原源码在 `section Lattice` 下有 `[Lattice α]`；先前 `section Group` 已在L115关闭，因此其 `[Group α]`、`[MulRightMono α]` 不会成为当前声明的幽灵捕获。当前 `section CommGroup` 明确是 `[CommGroup α] [MulLeftMono α]`。L122的 `@[to_additive]` 将完整 `mabs_mul_le (a b : α) : |a*b|ₘ≤|a|ₘ*|b|ₘ` 及其 sup_le 两支证明生成加性接口

\[
\{\alpha\}\to[Lattice\ \alpha]\to[AddCommGroup\ \alpha]\to[AddLeftMono\ \alpha]
\to(a\ b:\alpha)\to |a+b|\le|a|+|b|.
\]

实际特化α=ℝ只消耗已有实例，返回普通Prop事实，无新实例/数据/选择器。三个调用依次控制 |(V²−W²)+2C|、|(V²−W²+2C)+B|、|V²+(−W²)|；B≥0和两个平方非负、|2C|=2|C|随后准确给 |V²−W²+2C+B|≤V²+W²+2|C|+B。新调用没有改变捕获或三角界强度。

**末项组合。** 新L732—737先用环恒等式把 `(164*y)/√N`、`(16*K*q)/N` 精确写成 `164*(y/√N)`、`16*K*(q/N)`；中间 √K√(q/N) 项原样保留。这是总实数除法下也成立的代数重排，没有新增非零或正性要求。随后 `add_le_add (add_le_add ht1 ht2) ht3` 与目标左右结合顺序一致，准确相加三个系数比较。末尾原ring继续把同一个 C(K) 提出。因此最后界仍是

\[
|d|\le164y/\sqrt N+16\sqrt K\sqrt{q/N}+16Kq/N
\le200(1+K+\sqrt K)\{y/\sqrt N+\sqrt{q/N}+q/N\}.
\]

完整新D22证明体 SHA为 `9b4f72ba3a0f5ce33baa1a5adcf81de9057c7545480be7b24b90876e5ed5a8da`，12924字节。其四个返回合取仍依次为 J、D/V、显式d、C(K)d。没有新的数学缺口或未冻结数据风险；没有把源码推导正确写成native成功。

## 保全、复用与接纳边界

九个未变完整证明由实际源抽取、摘要和原审查覆盖共同复用；完整11个证明覆盖仍成立。22头/11RHS/16匿名形状/64承重数值/2显式ite、全局初值/捕获、分支与实例环境均保持。新源只在普通Prop证明的上述五处变化；没有新命名数据、局部数据函数、实例或选择器。既有144条普通/泛型表头记录的缩进/尾空格惯例不变。

diagnostic-dispositions的25条原完整message与旧诊断逐项匹配，22条warning对应的旧/新源行字节逐项相同。该事实仅证明没有清理警告，不预报native02会报告多少警告；三条旧error的完整消息与已终止失败仍保留。原mathlib环境stderr警告也保留，未据此改动依赖。

原审查的源忠实性、V=0仅总化而非全局S1、n=0/1/2总定义、s=0/K=0/q=0、重复观测/索引对角和非严格阈值分析均仍适用。196不导入195，不支付197窗口/概率和或并集，不宣称p54严格1/8已完成；p54统一p矩修正与Shao–Zhou外部输入归属保留。C1 immutablev85完成；C2/C12/OQ56 OPEN；OQ3用户暂停；124非前置。

本回合以 allzero SOURCE 状态封存；原SOURCE报告保持原样。下一步仍由父执行新精确源native02，并在成功时提供同一首次成功原O的全部实际所属索引、全部TYPE、所有非定理FULLVALUE、完整名字组件/层级/body和递归AX白名单证据。本审查者收到并实际完整核对后才可升级资格。当前没有成功原O或新AX，`qualified=false`、`actualOwned=UNKNOWN`。
