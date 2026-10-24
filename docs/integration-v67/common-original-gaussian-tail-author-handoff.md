# OriginalGaussianTail 作者交接

本单元实现与作者检查完成；独立完整复核待根协调者安排。作者写权已释放，无在途操作，最终只读进程观察未发现本单元 Lean 或审计进程。没有推送、创建 PR 或合并。所有原始根问题仍为 OPEN。

- 分支：`feat/common-original-gaussian-tail`
- 父提交：`d32ac06685132eeae5534cf3603ac5bcc6bc73a5`
- 提交：`335ec95d164d1e1841716bade84c7e8547521764`
- 树：`fe234520ecb52ccf6526c63b0b1a72c2659c012e`
- 唯一提交文件：`Shao/Probability/OriginalGaussianTail.lean`
- 最终源 SHA256：`f6b3df97e75be79ffcad5d0cb0cd9479e919dabad096796a16d3e54e1576a583`
- 同次最终对象 SHA256：`ddf6815a43d250a2d4f8cd6ebd9afcf40ce5faf40977504086a279ab87c2a337`

最终源是 UTF-8 无 BOM、LF，640 行。两个公开完整头与原冻结逐字空白归一化匹配；七个私有辅助定理的完整头均在证明前记录，并与冻结匹配。源码有 40 个证明局部 let/letI。实际模块所有权审计得到 33 个自有常量，全部是定理：两个公开源码定理、七个私有源码定理、24 个生成定理。新增全局、私有及生成定义均为零，定义值为零；全部传递公理只含 `propext`、`Classical.choice`、`Quot.sound`，33 个实际完整类型均无真正省略。

两个公开定理为 `original_coarse_gaussian_upper` 和 `original_marked_crossing_gaussian_upper`。只使用原律有限二阶矩、原均值零、`n * rawsecond = 1`、`t > 0`、`t^6 <= n` 和字面截断预算。常数在全部 nu/n/t/h/s 之前选择。真实条件乘积律、坏点数有限指数权重、有序删点、标记坐标与余下有序坐标的独立性，以及真实 signed scalar pushforward 的尺度恢复均已实现；零能量和原子保留。没有原律全局第三矩、指数矩、对称、条件均值零或正能量假设。

第一版两个完整头的内核检查在 `check007` 成功，但随后实际所有权审计发现集合覆盖证明中的模式 lambda 生成了 `original_coarse_gaussian_upper.match_3` 定义，因而不符合原冻结的零定义要求。007 的源、对象、完整类型/生成定义值、日志和退出码全部保留。唯一修复是把该 lambda 换成 `constructor/rintro` 的直接逻辑消去，未改公开头或数学假设。最终零定义版本在 `check008` 首次同次 `-o` 整源通过，随后 `audit002` 对该精确版本首次完整所有权/公理审计通过。没有重跑 007，也没有重跑任何依赖生产者；最终精确源通过后零生产重跑。

冻结候选中不存在的 `Shao.Probability.TruncationBudget` 路径经根协调者同意，使用实际已验收的 `Shao.Basic.TruncationBudget` 导入闭包；候选原字节保留。最终审计使用 21 个原对象只读链接形成完整 Shao 导入闭包，其中 20 个旧依赖源与对象哈希均保持不变。没有复制对象或写共享缓存。原有三个不相关未跟踪源未加入提交。

根复核入口是本目录 `handoff.json`、完整 `OriginalGaussianTail.lean`、`actual-owned-types.json`、`original-gaussian-tail-owned-audit.json`、`author-source-scan.json` 和 `source-declaration-index.json`。内核收据为 `check008-exit.json`，审计收据为 `audit-exit.json`；修复差异为 `zero-definition-proof-repair.diff`。需要新的独立上下文完整复核本源全部证明、两公开头、七个私有头、33 个实际类型及全部 40 个局部值；作者检查不能替代独立接受。

全部原始检查日志、失败源、007 与 008 对象留在服务器 `/root/rivermind-data/shao-lean-20261021/outputs/common-original-gaussian-tail/`。旧版失败审计完整结构文件为 `audit001-failed.json`。所有 Lean/审计均为固定版本、CPU10–13、root-heavy.lock、`-M8192 -j4 -DautoImplicit=false`，未安装本地 Lean、更新版本或构建 mathlib。

直接消费者是原始 fixed-x conditioning/CDF pullback。原始端点相对误差及 Shao–Zhou2016 外部归属、CDF pullback 本身、同 cutoff bounded/growing public witness、D2、加权收缩及 C1/C2 根组仍未闭合。模型为 gpt-6.1-sol/xhigh；平台未暴露分代理输入、缓存输入、输出及推理子集计数，交接以明确的不可见字符串记录，没有空值或订阅额度估计。
