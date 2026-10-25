# SourceWeightedRecordStrip source06 最终独立完整资格审查

结论：本单元数学审查为 **CORRECT**，同一最终源的形式资格为 **formalQualified=true**。没有发现未覆盖的数学、实际类型、非定理值或递归公理缺口。本结论仅授予本报告列明的三个源定理及其实际模块归属生成常量；C2/C12/OQ56 根结论仍为 OPEN，OQ3 仍为 PAUSED_BY_USER，原 C1 immutablev85 的既有完成状态不变。

唯一最终源是 `drafts/c2-weighted-record-strip/source06/SourceWeightedRecordStrip.lean`，SHA256 `cc6a0fbb25536cf375509ed1bf6db3f791ffbb45e1023d7a8e74d07a7ef3b76b`，66661 字节、1241 LF、0 CR。原 native006 成功对象为服务器 `producer006.olean`，SHA256 `c10591c156a6f52c0ae4de32016bac3e4deeaf9f3baea357d957cdf66615fde1`，4341768 字节。对象身份由精确源 native receipt、原对象安装与规范别名 receipt、同对象审计 receipt 共同绑定；本审查者未下载或复制二进制，也未执行 Lean 或服务器操作。

审查者为 `/root/weighted_record_strip_final_review`，与作者独立；指定配置 gpt-6.1-sol/xhigh，实际后台模型、实际 effort 和 input/cached-input/output/reasoning-subset 数值均不可观测，记为 null。使用 math-theorem，未使用 math-ultra，未再委派。权限仅为本独立审查目录的新工件；作者源、原始数学来源、旧审查、library、注册表、共享实现均未修改。

## 完整数学审查的精确继承

冻结文件 SHA256 为 `d624c19f64ef6da930f4263737b02f5c840ffa339a47426f2820dc53d98bca60`。三个完整声明、导入前缀、12 个 statement let（2/4/6）、假设、常数与依赖在修复过程中未变。source01 已完整阅读全部 1185 行与指定原始数学来源；source02 已完整阅读三个受影响证明；source03/04 已完整阅读两个受影响证明；source05/06 已各完整阅读受影响的记录矩证明。每次修复均完整比较 delta 并只刷新受影响证据，失败源、失败凭据和当时 formalfalse 结论均保存。

本次不重放旧证明或原始来源阅读。当前源的完整证明覆盖由既有连续审查链给出：循环证明 14–154，块 SHA `6964d4b2b87dca0d7c9b06d959b21c6a791ef5ce4d0d36b8e6ab5d3ca8c2064d`；记录矩 156–756，块 SHA `f050f189a31ad126325bd3f5a57710d9ef6330b32323e944ea2c61ab01f60af2`；条带 758–1239，块 SHA `fce63cb18895df1d146ea132fb3de97d0cbc8c0fc53d3442aa804aa260f071b9`。块范围及结尾空白字节约定沿用 source06 修复映射。最新源阶段报告 SHA `5293f83a07c145a8fc305438e36655e6a5a2728af188aef4c9d1c70302210fca`，结构记录 SHA `2d6305e977893bbede32bab1e2d985ab4ac7e129a24fa0e1ba42b2ae5c4e1a40`；两者当时的 formalfalse 未被改写。本次新增成功机器证据使最终资格闭合。

原始来源为作者精确 inputs manifest 指定的只读 `C:/game/shao/current/c12/main.tex`，SHA `beb00f718487e36de433175c97f1d500cb48e7a92ce5bd5ad5d62bb132122d06`，已完整阅读 149–260、1151–1565；以及同目录 `supplement.tex`，SHA `b99f2ac4d2f39dd39772d98a5702b7a923c2f10f8730a08fc1b4cd6bba4742bd`，已完整阅读 5196–5588。最初的 source/history 描述已由 Root 澄清，本审查没有创建或迁移来源。本次重新核对两份原始输入 SHA，字节仍精确相同。source01 报告 SHA `6e7c8b99dd0f4e8a46667ca8aa5e6cd80cb3b582bccf6f8ef35e5ec15f3d9f11` 的完整 source-to-original 审查精确继承；全部前序报告/结构记录/有关 seal 的当前哈希见 INPUT-SEALED-MANIFEST.json。

## 原始命题、实际类型与证明逻辑

**循环记录恒等式。** 任意实路径及 N>0，D 为 `(S_N-max_{0≤r<N}S_r)_+`。N 个带标签的循环旋转之 D 总和等于 `max(S_N,0)`，且 circularWitness 在这些旋转下不变。实际完整机器类型 993–1024 行逐项保留 N>0、路径、D 与 rotate 的两个完整 let、所有 Fin N 标签的和以及 witness 等式；没有一般位置、无原子、严格总和为正或去重旋转假设。

原证明在正总和支路通过 Lindley 的 max 递推，把每个旋转记录差识别为相邻循环最大值增量并作有限望远镜求和；非正总和时每个 D 均为零。圆弧的模 N 重排给出 witness 不变性，包括空弧、全弧、重复数值路径和 ties。N=1 及非正总和均在原证明覆盖内。当前实际私名为 `_private.Shao.Probability.SourceWeightedRecordStrip.0.Shao.Probability.SourceWeightedRecordStrip.wrs_cyclic_record_identity`，不能从公开 namespace 名称猜测其归属。

**真实加权记录矩。** 实际完整机器类型 1–191 行为先存在统一 C≥1，再量化概率律 rho、Bcap、长度 N 和 theta。rho 居中、二阶矩为 1、a.e. 绝对值不超过正 Bcap；beta 完整 let 就是该 rho 的第三绝对矩，P 完整 let 为同一 rho 的有限 iid 乘积律。D 仍为真实记录差，L 仍为真实 circularWitness。theta≥0、theta Bcap≤1/100、theta sqrt N≥1 后，结论给出 D/L 可测、真实 `(D²+beta D)exp(theta L)` 可积及其积分上界

`C beta/sqrt N * (1+N theta²) * exp((253/500)N theta² + C N theta³ beta + C theta Bcap)`。

这里 253/500 精确等于 .506，且是类型中的有理数，不是打印近似。不存在额外输入预算、拟合常数、oracle 矩界或替换 joint law。

原证明先由有界支持取得所需幂次与指数积分、beta≥1/Bcap≥1、D/L 的真实可测性和支配界。beta D 部分使用循环平均恒等式与实际乘积律在坐标旋转下的不变性，将积分转为正总和加权积分；稍放大 theta 后使用既有圆弧矩界，`0.5010005*(1.001)^2<0.506` 留出所需二次余量。D² 部分将最后一步 b 与反向前缀 v 组合，映射 `J(b,v)=snoc(reverse(v),b)` 的实际推前律等于同一 P；D>0 强制 b>0，闭存活事件、D≤b_+ 和 L≤b_++L_prefix 使已接受加权一墙包络可用。对真实乘积律作 Fubini，再用 `E[b_+²(b_++beta)]≤2 beta`、平方根比较和统一吸收常数获得所示界。最后一次修复只显式填写这个实际 integral_map 的 integrand、theta 参数函数类型与 hMap 等式；数学映射没有变化。所有 integrable 使用已证明的真实支配条件，未利用 Bochner 非可积积分的零约定冒充上界。

**真实能量闭条带。** 实际完整机器类型 278–551 行同样先存在统一 C≥1，再量化 rho 与全部 n/x/j/q/theta。明确保留 n>0、x≥1、Bcap≤sqrt n/(200x)、12≤j≤n、q≥0、theta≥0、theta Bcap≤1/100、theta sqrt(j/4)≥1。六个完整 statement let 为 beta、实际乘积律 P、真实 D、真实 L、`F=S_j-x sqrt(max(energy_j+q,n/2))` 和 `E={0≤F ∧ F≤D}`。结论给出 F 可测、E 可测、真实指标加权积分可积及

`E[D exp(theta L); E] ≤ C beta/j * (1+theta sqrt j)^5 * exp((253/500)j theta² + C j theta³ beta + C theta Bcap)`。

E 两端均为弱不等式，q 加在真实 energy 内，n/2 的截断下界保留，P 没有被替换。

原证明取 k=floor(j/2)、l=j-k，12≤j 确保两块正且均至少 j/4；实际头尾可测等价分解同一乘积律，并保留和、平方和恒等式。真实 D_j≤D_l(tail)，witness 次可加。为应用坐标浓缩而延伸的 Phi 仅在头部平方项中使用裁剪坐标，头部线性和保持真实坐标，后缀能量加 q 与 n/2 截断均保留；在实际支持盒上精确回到 F。固定真实后缀后闭事件变成头部的闭区间，长度为 D_l，合法斜率界由 Bcap 限制与真实截断提供。头部闭区间浓缩及尾部记录矩支付 D_l²+beta D_l，所有乘积可积与指标积分转移均有证明。系数比较给出 beta/j 与五次多项式，`0.503 k+0.506 l≤0.506 j`，三次项和 theta Bcap 项由统一 C 吸收。常数在 law/n/参数前固定，不以当前 law 或后缀值选择。

这正覆盖原 supplement 的循环记录、加权矩与 late-rank true-energy smallballot 承重单元。它没有包含 theta=0 的普通 strip 结论、后缀 W 积分、低全能量付款、完整 separated overshoot、原始分布返回或 C2 根定理。原始 main 的完整 overshoot 后续消费仍须 Root 单独完成。

## 依赖、私名与四 API 闭合

实际消费的九个项目依赖为 FinitePath、Basic.Lindley、MeasurablePath、SpitzerFinite、AuxiliaryEnergyCentered、SourceTrueEnergyStrip、SourceCircularWitnessMoment、SourceWeightedPrefixWall 和 C2.ActualOneWallRecordEnvelope。它们的已接受完整声明、statement let、非定理定义值及必要上下文在前序数学审查中已完整阅读，已接受旧证明不重审。本次逐文件重新核对当前 library 字节与 DIRECT-DEPENDENCIES-v1.json 的 accepted v101 源 SHA，九件完全相同；当前接受基线为 v102，精确证据可复用。

特别检查 Basic.Lindley 的模块归属与私名 `Shao.maxWithZero_cons`，以及 SourceTrueEnergyStrip 模块的私名 `Shao.Probability.tes_head_tail_measurePreserving`、`tes_head_tail_sum`、`tes_reverse_prefixSum`、`tes_reverse_tail_prefixSum`。作者用 Lean.mkPrivateNameCore 和 run_tac 取得的都是此前已接受常量的精确局部 have 引用；完整声明/let 已核过。它们不创建全局声明、不提供新公理、不替换数学定义，也不绕过 Lean 对局部项的类型检查。SourceWeightedPrefixWall 的五个私有拼接/反转/裁剪/闭区间浓缩接口和圆弧矩依赖的实际所属类型也已在前序完整覆盖。

本次完整阅读同一成功对象审计输出的四 API 全部 243 行；所有行区间和块 SHA 见 36TYPE-4API-0VALUE-coverage.json：

| API | 完整打印范围 | 独立核对结果 |
| --- | --- | --- |
| MeasurableEquiv.piFinSuccAbove_symm_apply | 1–131 | 完整机器 TYPE 是逆可测等价底层函数与 Fin.insertNthEquiv 底层函数的函数等式；保留全部依赖族、可测空间和插入位置参数。此前只有生成规则及定义源码的缺口现由真实 TYPE 补齐。 |
| Fin.insertNthEquiv_apply | 132–185 | 完整 TYPE 将 insertNthEquiv 的实际应用识别为插入位置上的 fst 与其余坐标 snd；依赖索引无弱化。 |
| Fin.insertNth_last' | 186–209 | 完整 TYPE 为任意 Sort 值在最后位置 insertNth 等于 snoc，方向与实际使用吻合。 |
| Fin.lastCases | 210–243 | TYPE 211–223 的 motive/last/cast/i 全部保留；FULLVALUE 225–243 是以 last 和 cast 支路作 Fin.reverseInduction，完整读过。 |

这些机器类型和值与前序已完整阅读的 pinned mathlib/core 源上下文吻合，包括 MeasurableEquiv.piFinSuccAbove 的双向可测性及 Measure.pi 相应 measure-preserving 环境。概率律给出的有限/SigmaFinite 实例满足所用测度定理前提。没有把 piFinSuccAbove_symm_apply 当成源码里的字面 theorem head；现明确以真实生成机器 TYPE 作为最终覆盖。

## 实际归属完整性与公理审计

完整阅读 OwnedAudit002.lean。程序从 env.constants 全集枚举，以 `env.getModuleIdxFor? name` 对照 `env.header.moduleNames` 筛选实际模块 owner，不以 namespace 字符串筛选；因此长私名及生成常量也被覆盖。对每个实际归属常量调用 Lean.collectAxioms，逐项拒绝白名单外公理，再打印 pp.all 下的完整 info.type。对 definition/opaque 打印完整 value；对其余任何非 theorem 种类抛错，不能静默遗漏非定理值。两个指定公开源 head 必须存在且实际为 theorem。程序没有只审三个人写 head 或只计公开 namespace。

实际枚举 36 个 owner 均为 `Shao.Probability.SourceWeightedRecordStrip`，全部 theorem，包含三个源定理与 33 个生成辅助定理：循环 1+7、记录矩 1+3 个 _proof +8 个 _simp、条带 1+15 个 _proof。指定公开源 head 为两个；这里 public_count 是对这两个明确期望名字的核验，不被解释为把生成名称当作其他数学公开接口。

我连续完整阅读 1104 行全部 actual TYPE、每项 AX 列表、量词、let、实例与结论，没有只扫 header。两个公开源 head 与私有循环 head 均逐项对照冻结完整声明及原始语义。其余 33 个实际类型分别是 Fin/Nat 索引、分块长度、减法重排、非零数与幂、交集成员等证明产生的命题，完整前提使所有 False 结论都是反证支路；没有新增预算、law、事件或隐藏结论假设。每项精确名字、范围、块 SHA、公理及语义角色列在覆盖清单。

独立本地确定性核验逐项确认：36 个 TYPE 块覆盖行 1–1104 连续无遗漏；每块 SHA 与 Root index 相同；打印名、kind、owner、AX 与实际 owner report 完全一致；所有 36 项递归 AX 都属于 `propext, Classical.choice, Quot.sound`。实际 owned non-theorem 为 0，故本模块全部 non-theorem FULLVALUE 清单为空；这不是省略审核。外部依赖 Fin.lastCases 的唯一此次定义 FULLVALUE 单列且已读。没有 pretty-printer 省略号，也没有未打印生成 API 留项。

## 成功凭据与失败事实保全

native006 receipt 明确自然 RC0、0 error、32 warning，精确绑定当前源及原成功 O。原对象安装 receipt 确认规范别名的 SHA 与原对象完全相同并解析到该原路径，oldProducerRecompiles=0、priorSourceEdits=0。audit002 receipt 明确自然 audit RC0、0 error、同源与同原 O；审计日志 SHA `ad276c984a01dfb1992791561d22ac680e5a3c278a13aa3d5f11d61bfbce4fea`。七件 ready payload 的当前字节数与 SHA、所有 block hashes 和九依赖哈希均由本 reviewer 本地独立核验，通过结果保存在 independent-binding-verification.json。

审计001的程序输出、36 owner report 与最终标记已经存在且没有 Lean error，但其后 Root 的回执 Python 转义错误造成外层 RC1。其 Lean 自然返回码未观测，绝不推断为 RC0。effects inspection 记录同源/同原对象、完整日志与 owner report、root lock 空闲后，Root 只重新执行这个尚未 accepted 的新目标审计002以取得明确自然 RC0；001、002 日志 SHA 完全相同。原 metadata 失败分类和 effects response 均纳入输入封印。这个回执错误不是数学源失败。native001–005 的真实失败与所有旧报告也不被当前成功改写。

INPUT-SEALED-MANIFEST.json 对 50 件本地输入及两份只读原始来源逐件绑定；sha 为 `00e91170e11331cf8915b910a12b525b679f6a3faaa29168679a1b2f7a4f3788`。OUTPUT-SEALED-MANIFEST.json 绑定本次新生成报告、结构资格记录、完整覆盖清单、核验结果、ACK、CHECKPOINT 与 RELEASE0，seal 本身明确自排除。本次不复制完整日志、环境或缓存。

本 reviewer 的 Lean/AX/服务器/上传/Git/API/作者源编辑/他人文件编辑/再委派均为 0。完成本次源单元资格后实际 review inflight=0、heavy=0，无持锁、写者或后台任务。下一精确动作由 Root 使用本同源合格证据完成单元接纳及其后续 source-bound 消费；本报告不要求 Root 普通回合停止，也不声称根结论完成。
