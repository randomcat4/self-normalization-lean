# 固定截断公开伴随：作者交接

状态：七个新源版本的完整内核检查及七次完整所属声明审计全部 PASS；等待新的独立完整审查。作者没有自行验收。

仅源码提交 `4c426f20019e9a9cf9ed7cbd1d54aee6932f2027`，树 `f6643187ccfed1e7c2cc2680771fd5d48d367d0c`，父提交 `32618ea59e6fde25d96fac17a638cd3327805d5c`。分支 `feat/common-fixed-cutoff-exports`；服务器工作树 `/root/rivermind-data/shao-lean-20261021/workspaces/common-fixed-cutoff-exports-v65`。提交仅追加七个授权 Probability 源文件，共 2061 行；工作树干净。未 push、建 PR 或 merge。

采用 math-theorem，配置 gpt-6.1-sol / xhigh、fresh context，未使用 math-ultra 或子代理。写权和执行权均已释放，无源写入或 Lean 命令在途。

## 冻结和精确字节

公开冻结文件 SHA256 `d344822aa1926e6bfbf04de4ffd41c5ca889bd14ced5d0cd77084a892c186c64`；完整 14 头文件 SHA256 `f5b027c8312cb470de8b3f82e857d6a8f290e76cd12b6afe917930b3a6d03334`。8 个 public、6 个 private 的完整声明头与冻结逐字一致，新增定义 0。

每个新块均在原 namespace 最终 end 前，以 BEGIN/END FIXED CUTOFF PUBLIC COMPANIONS 标记。删除整块恢复每份完整旧源字节，旧 imports/options/types/proofs/defs/注释/空白均未改。`author-source-scan.json` 和 `source-bindings.json` 给出全部七份新旧 SHA256、精确恢复、UTF-8/LF 与禁止构造扫描。

| 模块 | 新源 SHA256 | 首次完整成功 | 全部所属：旧→新 | 旧定义值 |
| --- | --- | --- | --- | --- |
| SourceKernelMarkedOutside | `1e10a319b5c2b3c874cacf843f3585c02af9b1be2c6e26f5a99f8e76a39388ac` | check001 | 101→102 | 16 |
| SourceLongKernelBounds | `be8fe1284646a3c0a12c974f222576cb6faf9890860eb3ffc89d234956614e88` | check002 | 63→74 | 6 |
| QuadraticFullNoiseMarkedLowRegions | `7ef3a0c16a59b4a0d73dbe9ea5cb36c8e17c477c1235dbc9522fafcd253a8d74` | check001 | 67→69 | 0 |
| QuadraticFullNoiseMarkedOutside | `2532534a1f6d6f260a768b436dbf856b5a17d9d429fed985e6922a3dcc5cebf6` | check001 | 28→31 | 0 |
| SourceShortTimeKernelBounds | `13e76b7cb955436f76647790eda5518c490097b72912b0605f0f1c608dd0fea4` | check002 | 34→43 | 6 |
| SourceShortTimeKernelTaylor | `cb01cea27110980c3be3083b72c32c0b96b88cf9f1dabfbbf55c80c12f5b8e1b` | check001 | 4→5 | 0 |
| SourceBoundedYReflection | `d71287167c38577758ace4f3e2de4d86832ed67b70a8815e259d2dca62fa2861` | check002 | 56→64 | 0 |

## 内核、所属与旧证据复用

所有实际检查均在服务器，先 activate 再 cd，使用同一 `root-heavy.lock`、CPU10–13、`-M8192 -j4 -DautoImplicit=false`，原 Lean/mathlib/shared-v34 pins 不变。七份完整目标的原生 Lean 退出码均为 0；成功对象来自同一条 `-o` 调用，源快照和对象以只读文件保留。首次成功后重编次数为 0，未运行旧依赖 producer。

服务器证据根为 `/root/rivermind-data/shao-lean-20261021/outputs/common-fixed-cutoff-exports/`。各模块子目录的 `first-success.json` 绑定源、不可变源快照、原成功对象、原生 rc、完整日志及命令。私有执行视图的七条目标链接仅指向各自成功对象；69 个原依赖对象 SHA256 全部未变，其中 62 个未受影响依赖的只读链接和源未变。未写包缓存、未复制缓存、未 lake update。

各模块的 `audit-exit.json`、`owned-audit.json`、`actual-owned-types-values.json` 已完整下载为结构化证据，原始完整日志留服务器。审计按实际 `getModuleIdxFor?` 取 owner，覆盖 private/generated/foreign-namespace 所属常量，对每个常量执行递归 `Lean.collectAxioms`，仅观察到标准三公理。完整类型与全部 definition 值导出无省略号。

总计 388 个实际所属常量＝360 个 theorem＋28 个旧 definition。本批增加 35 个 theorem，其中 14 个冻结源声明、21 个生成项；新增 definition 0。`ownership-delta.json` 与 `new-owned-types.json` 给出实际新增名、完整类型、公理与模块归属。这里的零只指新增定义。

`old-type-retention.json` 将全部 353 个旧所属完整类型与其既有合格导出逐项比较，仅规范打印空白，零差异；名字、kind 和公理集合也全部保留。`old-definition-value-retention.json` 对全部 28 个旧定义完整值作同样比较，零差异。没有重跑旧内核或旧公理检查来取得这些比较。

## 保留的失败与实现修复

三个模块的 check001 原生退出码为 1：SourceLongKernelBounds、SourceShortTimeKernelBounds、SourceBoundedYReflection。各失败的原始完整源快照、日志、rc 与收据都保存在服务器原路径；对应 `check001-exit.json` 已下载。修复仅发生在新块：

- 长时证明的 hsmallA/hsmallC 显式展开固定 δ，使用冻结的具体 epsilon 上界支付数值界。
- 短时证明的 hsmall2/hsmall5 同样显式展开固定 δ 并使用具体 epsilon 上界。
- 反射证明的 he0 用 `le_min` 与数值传递显式取得两项上界，避免 simp 把目标先改写为合取。

完整差异保存在三个 `*-candidate-proof-diff.txt`；其他四个候选证明体未变。所有声明、假设、law、预算、时钟常数和结论均未改。

## 独审接续与范围

下一依赖是由 root 安排一个新的合格独立上下文，完整审查本提交全部新增 companion/helper 的源到陈述、证明、完整实际类型、局部值和 21 个 generated obligations。作者已完整实施候选，没有自行接收结论；既有旧证明证据只用于字节恢复和旧类型/值绑定后的未改范围。

固定参数为 δ=1/16、长时及有界反射 epsilon≤1/16384、短时 epsilon≤1/8192、L2=16384。一般原律仍仅二阶可积、均值零及 raw-second 归一；真实条件均值一般非零，实际 full noise、strict/weak 区域和 Q=0 保留。原 p54 修复及外部结果归属随旧源字节原样保留。未改 growing epsilon/rho/noise/预算。PB、END、same-law full-y、加权收缩及全部原根仍 OPEN。

`handoff.json` 提供提交、14 冻结头、七个对象、七次实际审计、失败账、35 个新增所属名及证据 SHA256 的机器可读绑定。下一审查不需要重跑已成功的源版本。
