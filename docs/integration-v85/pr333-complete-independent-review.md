# SourceNonresidualBrownian 独立完整终审

**STATUS: CORRECT.** 本裁决只覆盖精确新源 `Shao.Probability.SourceNonresidualBrownian` 的两个公开定理、一个事先冻结的私有定理及其全部实际生成声明。没有发现关键证明缺口、隐藏前提或源范围误报。可供 Root 对这一精确源复用；不表示已合并或原 C1/C2 根结论已闭合。

审查者 `/root/nonresidual_brownian_final_review` 为新鲜、非作者的独立上下文；未修改任何作者源码、冻结文件、其他 lane 或 Root 文件，未调用子代理。按任务明确配置 `gpt-6.1-sol / xhigh`；工具未提供可核实的实际模型/努力级别及用量遥测，结构化报告全部记为 null，不推算订阅百分比。已先保存 runtime-ack，再执行实质审查。遵循 math-theorem、当前 AGENTS.md、SERVER.md 和 streamlined-acceptance-current.md。

## 精确对象及覆盖

- 新源码 1058 行、56057 字节，UTF-8 无 BOM、LF；SHA256 `e6de66f3b78a8607842ad71608e0bbce53751f2b69b3e6b973c7f125d8361b23`。已完整逐行阅读 1–1058 行，包括全部证明。
- 完整实际 TYPE/AX 记录 181545 字节，SHA256 `0d3a0f68000e03ea084f4afab59b044667de5878fd9e7021d7aa40a28ffd64a9`。按 16 个无损、相邻字节区间完整显示和阅读，覆盖 [0,181545)，遗漏 0 字节，未使用截断、摘要或仅源码替代实际类型。
- 59 个实际所属声明全部是定理：2 个公开、1 个显式私有、56 个生成定理；0 个非定理，故非定理 VALUE 完整清单为空。每项实际类型字节范围、SHA256、完整读取标记、递归 AX 和语义分类均逐行写入 full-review.json。没有只按文本 theorem 计数。
- `Shao.C2.doubleCrossing.congr_simp` 虽位于别的命名空间，实际所属模块是本模块，已纳入第 20 项审查；其类型是参数相等引起的事件集合相等。生成算术和 simp 定理也全部覆盖，包括展开很长的 Nat.find/停止时间局部类型。
- 已完整阅读冻结公开头、私有头及其全部上下文、完整消费接口/定义值记录，并直接阅读原 main.tex 150–196、1153–1172、1211–1270、1426–1438 和 supplement.tex 4681–4699。

原 main.tex SHA256 `beb00f718487e36de433175c97f1d500cb48e7a92ce5bd5ad5d62bb132122d06`；supplement.tex SHA256 `b99f2ac4d2f39dd39772d98a5702b7a923c2f10f8730a08fc1b4cd6bba4742bd`。仅只读访问 C:/game/shao/current；没有写入原文或历史。

## 冻结及先后顺序

审查脚本独立提取三个完整声明头，逐字节比较，结果与作者 frozen-comparison 一致：公开头的 SHA256 分别为 `2fb2101335b92b60992a410a96102d8cb502b9b0701f8d4c939210bce6191527`、`3e588ee2c9ec5da54201a3b432c04590f0e383cec50bc0fef7bc149c8034ce43`；私有头为 `48cad1f35f971c7b10ac8248341c9d295274810fbfcc9edfd2ec9a7bf71b0157`。完整共同上下文相同；公开 literal let 为 5+9=14，私有为 2。没有新全局定义、实例、opaque、结构或公理。autoImplicit=false、Elab.async=false、maxHeartbeats=5000000 与批准上下文一致；后两项是实现前已批准的上下文选项。

Root 的 PR328 资格时间为 2026-10-24 19:29:53 UTC，正式生产 activation 为 19:31:41 UTC；私有头 amendment01 为 19:35:00 UTC，首个保留的私有源 kernel 尝试为 19:38:56 UTC。私有头请求明确在证明体开始前提交，amendment 明确事先完整冻结并禁止更早写体；对应请求头与冻结头一致，作者记录确认 first write 在该冻结之后。没有发现相反的写入或签名变动证据。公开冻结 SHA256 `54f39aecff8f6873dad54405d2031540cbee5918c72f11ca8bc458c2411e5976`，私有冻结 `60a5bcac9371175c794fb63bc793745266084b7554e4755c627faa34cf9807e8`，activation `dfbb23ef40863311a4ce4c178c9ae085ff7b771236ab53382ec9e177f68e1d99`，amendment01 `5b52caa5613863748f4c6dab4db3a67ae112400247146ed13cd5a0c449773295` 均物理核对。

源码首部“candidate only / PR328 pending / no private helper”是保留的冻结历史注释，不是当前授权或范围；后续 activation、先行 PR328 资格及 amendment 已明确更新对应状态。它没有改变 Lean 陈述或证据适用范围。

## 私有高斯网格证明：19–482 行

真实对象是 N>0、a>0 下独立 `Gaussian(0,1/N)` 的 N 个增量及正前缀最大值；墙为固定 a，没有随机自归一化墙前提。令 λ=3a、q=λ²/(2N)，所以 Nq=λ²/2。

40–68 行直接调用 pinned Mathlib 的真实高斯矩母函数及 `integrable_exp_mul_gaussianReal`，同时处理 ±1 两种符号。指数绝对值由两个真正可积的指数函数之和支配。因此没有利用 Lean 对不可积 Bochner 积分取零的约定获得伪等式。

69–151 行的因子分解有实际独立性依据：`clip i.val` 只保留坐标 j<i，F 可由这些过去坐标重建；有限坐标集合与 {i} 不交，产品律坐标独立性给出 F 与当前坐标函数独立，进而同时得到乘积可积性和积分乘积公式。逐步建立 exp(λΣ|w_i|) 的可积性。

152–243 行对每个顺序 η=±1 定义可预测符号 ε_i：若此前某个前缀已经到 η 方向的上墙，则取 −η，否则取 η。判断只使用前缀长度 j≤i；prefixSum j 只含坐标 <j，故没有读取当前增量 w_i。Measurable、clip 不变性均显式证明。Y_k 为带符号部分和，Z_k=exp(λY_k−kq)；|Y_k|≤Σ|w_i|，q≥0，故所有 Z_k 真正可积。

244–317 行把尚存活状态按 ε_i=±1 分拆为非负、过去可测的 Hplus/Hminus。因子分解适用于两个分量，真实 ±λ 高斯 MGF 均等于 exp(q)，所以每项停止差分 delta_k 可积且 E delta_k≤0。这里没有假定翻转后的全部增量仍 iid，也没有假定某个新的条件矩母函数结论。

318–385 行用有限和直接证明停止后的 W=1+Σdelta 等于首次 Y≥3a 时的 Z_j，若未命中则等于 Z_N。j 是样本逐点的最小整数，限于 0,…,N；W≥0，命中时 W≥exp(3λa−Nq)。此处使用有限望远镜恒等式和 q≥0，不引用未支付的强 Markov、随机墙停止或无界可选停止定理。

386–420 行核查两墙事件的确定性包含：η 方向先到 a，之后到 −a。若 τ 是第一次上墙，则切换后的 Y_k=2ηS_τ−ηS_k≥3a；上墙 overshoot 不破坏不等式，等号也被保留。421–460 行证明事件可测并对其指标积分，得到概率≤exp(−3λa+Nq)。461–482 行将两种先后顺序并起来，代入 λ=3a，得到精确 `2 exp(−9a²/2)`。N 正性、端点 k=N 和两种顺序都已覆盖。

## 第一个公开定理：484–874 行

对象是任意原可测概率空间上的真实 `IsBrownianReal B PB`，x>0；BridgeTime 是完整闭区间 [0,1]，不是有限网格或布朗桥。U/L 为两侧弱命中，DB=U∩L，H 为绝对值弱命中概率，d 为实际 PB.real DB。

504–541 行正确只声称 NullMeasurableSet。连续路径空间 C([0,1],ℝ) 内的全时间 strict upper survival 由紧性给出开放集，其补集为弱 upper hit。消费 accepted `aemeasurable_brownianUnitPath` 及在同一个 AE 集上对所有实时间同时成立的路径等式，将其拉回原概率空间。负侧使用实际 hB.neg。因此没有把逐时间 AE 等式对不可数时间取交，也没有给任意不完备 ΩB 添加全局可测路径前提。

542–621 行只消费已接受的 `BrownianUpperJointReflection.brownian_upper_joint_reflection`。取 r_j=x−1/(j+1)<x，strict survival 与终点≤r_j 的事件递增到 strict survival 本身；因为 t=1 在区间内，后者确实要求终点<x。有限概率测度的递增连续性及标准高斯尾连续性给 strict survival 概率 1−2Ψ(x)。它是弱 upper hit 的精确补集，故 P(U)=2Ψ(x)；对 −B 同理得 P(L)=2Ψ(x)。没有新增反射、路径律、强 Markov 或条件布朗桥假设。

622–644 行逐点识别绝对值弱墙事件=U∪L，零测可测集合的容斥给 d=4Ψ−H；非负性来自实际测度，DB⊆U 给 d≤2Ψ。弱等号与 strict complement 的方向一致。

646–854 行处理真正全实时间上界。N=2^m 始终正；网格是 1/N,…,1，嵌入下一层的下标为 2i+1，因而两侧命中事件 F_m 递增。ceil/max(1,·) 构造证明网格在整个 [0,1] 稠密，包含靠近 0 的逼近及端点 1。固定 a∈(0,x)，accepted Brownian finite-dimensional law 在等长 duration=1/N 上恰是累计 Gaussian(0,1/N) 增量律；累加映射、正前缀上下最大值与网格事件的等价逐项证明。真实 HasLaw 和可测 G 支付 measureReal 映射等式。

在共同 AE 连续路径上，真实 ±x 弱命中给 ±a 严格命中；开邻域与稠密网格使两次命中进入某个共同细网格。因此 DB 在 AE 意义下包含于 ⋃F_m 的反向比较所需方向为 `DB ⊆ᵐ ⋃F_m`。有限测度保证所有 ENNReal.toReal 转换合法；这给 d≤2exp(−9a²/2)。855–873 行取 a_j=x(1−2^{−(j+1)})∈(0,x)，a_j→x，再用右侧连续性得目标弱墙界。没有把弱墙直接等同于恰好命中 x 的离散网格事件，故未丢失等号。

## 第二个公开定理：876–1056 行

先给 cstar>0，再固定 K=√(2π)、C=2K+2e+2、Crel=K(2+4e/cstar)+4K/cstar；二者正性先于任意 B、PB、nu、n、x 量化。实际输入只有 Brownian 条件，以及概率律 nu 的 AE 有界支持、零均值、n∫z²=1、n>0、x≥1。二、三矩可积性、beta>0、n≥16x²、D 可测及真实 truncationBudget=u 都是结论。

917–925 行精确消费已获 Root 资格的 PR328 公共头，其相同 nu/n/x/支持/均值/方差输入供给真实 `P=nu^n` 和 `D=Shao.C2.doubleCrossing hn x` 的概率估计及上述全部附带结论。其 source `13d3917b95fec82a10505f44b18832d20601ebd55e4713675a83061d15ec59cc`、原 producer004 对象 `07c8756921fdd7b557cb0663d4c7f7cb29fedf5ca909e8f2f84de69790b7c1b4` 和资格文件 `53be6eac27b26d7e5e7d1f7b289cf07b62d8fb0b0681e91e58bd04898ca9fb6d` 均核对。原独立审查、收据和释放等六个引用文件只做精确字节资格复用，没有重读旧完整证明或重跑旧检查。

D 使用每条样本自身的同一个最终平方和 Q_n，两墙均为弱乘法事件；正前缀是 1,…,n。Q_n=0 时两弱墙都成立，并未删掉这一事件。私有高斯网格引理中的固定正墙不承担自归一化 Q=0 的工作；此处 Q=0 由 PR328 的实际低能量支付保留。nu 可以有原子、非对称及重复坐标。无额外目标概率、integrability、耦合或 path-law premise。

926–1019 行把先前的真实概率上界转为所需尺度。由第一个定理 d≤2exp(−9x²/2)≤2exp(−4x²)。若 0<u≤1/20000，u=beta(1+x)^3 给

`1/(5832 beta²) ≥ x²+1/u`, `exp(−1/u)≤u`, `24 beta x³≤1`。

故 PR328 的两个指数项分别≤u exp(−x²)、2e exp(−4x²)。beta 的正性使所有除法合法；x≥1 使这里用到的幂比较合法。下 Mills 界及 `(1+x)exp(−x²/2)≤2` 给 `exp(−x²)≤2KΨ(x)`。于是 `P(D)≤2K u Ψ(x)+2e exp(−4x²)`。

1020–1034 行由 P(D),d≥0 得 `|P(D)−d|≤P(D)+d`，从而≤`2K u Ψ(x)+(2e+2)exp(−4x²)`，再放宽为冻结常数 C。这里不需要在两个原概率空间之间构造耦合。

1035–1056 行只在明确的非剩余条件 `cstar exp(−3x²)≤u` 下，将 `exp(−4x²)` 支付为 `(u/cstar)exp(−x²)`；得到 `d≤(4K/cstar)uΨ(x)`。与 PR328 的实际相对 P(D) 界相加，恰为冻结 Crel。u=1/20000、u=cstar exp(−3x²)、x=1 的等号均保留。第一头 x>0、第二头 x≥1；没有声称 x=0 由这些估计覆盖。

原 main.tex 的有界中心辅助律经 A=X/√n 标准化后，beta 对应 δ、u 对应 δ(1+x)^3，真实 R=u；这支付 d:nonres 的有界中心范围。一般原律截断、中心化及回迁仍需独立接口，不能把此辅助律说明当作完成原律回迁。

## 原始服务器证据及公理

本轮 0 个 Lean 命令、0 个 AX 重跑、0 个旧 producer 重编、0 个 cache 写入。已实际只读检查服务器物理文件，并复用作者唯一整模块成功对象：

| 项目 | SHA256 |
|---|---|
| producer006.olean | `1c43222adcc43fb0503a38b5b797d1124332c47d8199952a2b6b04fe19d26a0c` |
| attempt006.log | `f5e396cdea2ffe89561bc2526fe18cdce63e15fc965fa0d9db9f34d659f734dc` |
| OwnedAudit.lean | `bb18be3d8eb7641e9e94302046a75804ac46691c31c1d846b2c7981b70890c59` |
| owned-audit001.log | `0c79523b2518fe63bd576c892099ed4c5d472d275e84fac40850b6912e7578c9` |
| owned-audit.json | `52010ce44d310a6c190df110f8525d99c89c022fac0efd741dd9df38ecda5e1c` |
| author receipt.json | `3b65e822194bb3e9837257c8560cc7051eefb7e67a8e524f8d235aaf59f792ef` |
| author RELEASE.json | `a57ad226f2571f3b6abd79aafa6e4d0f3cb9447d5bd375dd28bb614257f908a5` |

producer006 位于 outputs/common-nonresidual-brownian-v84，3809736 字节。实际导入路径 `.lake/build/lib/lean/Shao/Probability/SourceNonresidualBrownian.olean` 解析到这个同一原对象且哈希相同。原 attempt006 的源码快照、新 worktree 源及 Git blob 内容 SHA256 全相同；kernel exit0、53.774261713 秒。audit command001 exit0、6.512491465 秒，记录绑定同一源和对象。驱动按 env.getModuleIdxFor? 选取全部精确所属常量，不按命名空间筛选，调用递归 Lean.collectAxioms，并拒绝白名单外公理。其全部源码已阅读。

原审计日志逐字节包含完整 181545 字节类型记录，含 59 个 TARGET_DECL/ACTUAL_TYPE、0 个 VALUE、0 个省略号标记；最终 footer 为 59 owned /2 public /59 theorem /0 definition。逐项 transcript AX 与 owned-audit.json 一致，所有依赖均属于 `{propext, Classical.choice, Quot.sound}`。源码无 sorry/admit/新增 axiom/unsafe/native_decide；没有公理漏洞。

全部 37 个直接服务器源/对象/驱动/日志/类型/失败快照/原 metadata 物理哈希匹配；本地 32 个作者 compact 文件形成独立哈希清单，receipt 内部引用均匹配。742 个旧 Shao 源与 accepted v83 源映射一致，742 个原对象引用全部仍是指向同一 accepted 原对象的符号链接。另加资格已确认的 PR328 producer004；没有复用私有引理 partial 对象冒充 whole 对象。钉死工具链为 leanprover/lean4:v4.36.0-rc1、Mathlib `807d3836b165983210ee2ecf3cd28f239436949c`，真实 package path 是 shared-v34/packages/mathlib。

首次只读哈希查询包含已从干净 worktree 移除的临时 OwnedAudit.lean，报文件不存在；保存此查询失败，改为原 outputs/OwnedAudit.lean 后全部绑定通过。首次宽泛旧源映射还含 11 个配置/审计文件；最终 742 计数来自 `Shao/*.lean` 实际源/对象映射，另存 physical-old-reuse.json。两者均不是 Lean 尝试或证明失败，也没有触发重核。保留的原 outputs 驱动和原日志足以核实实际审计内容，未发现证据缺口。

历史尝试分母保持：001 私有局部失败；002 仅私有引理通过（对象 SHA `6470c72d187d7db1ed24086e0cc6879b4c71dfcbc10f3ffedea1026b384406d4`），不能算两个公开结论通过；003 整体失败；004 锁忙 exit75、0 Lean；005 整体失败；006 精确整源成功。合计 5 次实际 kernel、3 次失败、1 次 partial 成功、1 次 whole 成功，另 1 次实际全所属 AX 审计。所有失败快照、日志、原 metadata 的物理哈希已对照，未被覆盖为成功。各源快照均 UTF-8 无 BOM/LF、未含禁用证明占位符。资源命令绑定 root-heavy.lock、CPU10–13、-M8192/-j4。

PR333 的保存 API 记录与当前 native Git 相符：head `6db2a7e20787b56dbae1a1d2f5d2d799eb63aa89`，tree `3b766bcdc8e196b1e6ea1112bfe41142881be10d`，blob `853b4a983550751fcd74a07cb4350297e7ceb9e5`。只新增这一源文件，1058 行，worktree clean；没有合并。

## 保留的未付范围

本单元不证明更尖的 `d≤4Ψ(3x)`，但已证明的 `2exp(−9x²/2)` 足够支付本 nonresidual 结论。`u<cstar exp(−3x²)` 的相对误差、原未有界律及非零均值保留律的条件截断/中心化/回迁、返回原 R_n(x)、full 原 p-moment I_n、C2 根和 C1 全增长装配均未由本单元闭合。没有把有限恒等式或小 Brownian d 单独当成原根定理。

C12/OQ56 仍 OPEN；OQ3 保持 PAUSED_BY_USER；OQ4 只有另行验收的限定原范围 COMPLETE。未唤醒 OQ3、未新建 sidebar/Goal/自动化，未向其他 chat 发送消息。Root 后续只需按精确哈希和实际接口/交互范围验收；本报告没有提出重复审查旧证明或重跑旧成功 kernel/AX 的要求。

本审查已完成；最终 RELEASE.json 释放本目录审查写权，0 inflight。其后 Root 资格、合并及新的 source-bound 任务仍归协调者。
