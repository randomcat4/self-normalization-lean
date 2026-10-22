# OQ4 立方根精细率：单次 canonical 交付

状态：CANONICAL_COPY1_SOLE_EMIT1_PASS_STOP。已执行恰好 1 次排他 Source 字节复制和 1 次唯一对象生成，Lean 退出码 0，实际编译耗时 5.887082051485777 秒。重型 lease 已报告回收；成功后没有修改、修复、重放或更多 emit。

| 交付 | 字节 | SHA256 |
|---|---:|---|
| canonical Source | 9422 | 6f51957e561b4b693bcff304f797e284d905fc7a5ea3b5457819c3fe5e851247 |
| 唯一 canonical olean | 1145648 | 077c3bf16faa70254cb9f1bfac16ef9add577da6ecf0f762c0198ef421fb5cf8 |

Source 位于 `/root/rivermind-data/shao-lean-20261021/workspaces/lead-oq4/Shao/OQ4/RademacherCubeRootRates.lean`；唯一对象位于 `/root/rivermind-data/shao-lean-20261021/workspaces/lead-oq4/.lake/build/lib/lean/Shao/OQ4/RademacherCubeRootRates.olean`。2 个公共定义、4 个公共类型及 2 个显式 private 引理保持原成功 Source 身份。

| 持久守卫阶段 | PASS | 全 W 前缀数 | Source 集合数 | build 集合数 |
|---|---|---:|---:|---:|
| beforecopy | 是 | 2 | 273 | 109 |
| aftercopy | 是 | 3 | 274 | 109 |
| beforeemit | 是 | 3 | 274 | 109 |
| afteremit | 是 | 4 | 274 | 110 |

四阶段各自的旧映射 52/224/276/109 全部零差异；两份初始私有 Source 的 path/kind/resolved/SHA/bytes 均完整保留。新增 Source 和对象均为非符号链接普通文件，父目录直接解析在 W 内；没有 ilean、ir、trace 或额外对象。CP 唯一绑定、唯一只读 alias、固定 binary、packages 指向、HEAD/branch 和六个冻结引用均通过守卫。

以上是本次 emit 的不可变持久历史。父随后为 Unit/Full53 imports 增加的只读目标对象 alias 属于后续阶段；本报告没有重新扫描当前 W，也没有用稍后前缀数回填本次四阶段快照。

实际唯一 Lean 命令：

```text
taskset -c 18-21 /root/rivermind-data/shao-lean-20261021/toolchains/elan/toolchains/leanprover--lean4---v4.36.0-rc1/bin/lean -M8192 -j4 -DautoImplicit=false -R /root/rivermind-data/shao-lean-20261021/workspaces/lead-oq4 -o /root/rivermind-data/shao-lean-20261021/workspaces/lead-oq4/.lake/build/lib/lean/Shao/OQ4/RademacherCubeRootRates.olean /root/rivermind-data/shao-lean-20261021/workspaces/lead-oq4/Shao/OQ4/RademacherCubeRootRates.lean
```

编译工作目录为 `/root/rivermind-data/shao-lean-20261021/workspaces/lead-oq4`；计时直接包围 sole subprocess.run。未使用 RLIMIT_AS/ulimit-v、lake/cache 命令、旧对象重建或对象复制。父接受文件只经 hash-only 门核对：3800B，SHA256 d89da0f5d9e87f5bf3b643f2b8855da3134fefe7a65b3f358d5b89cca6c8b574；没有读取其内容或审查推理，也没有下载 runtime-env 内容。

标准输出 1768B，仅含原有 7 条 tactic/linter 警告；标准错误 0B，运行 exception 为 null。全部警告保存在 canonical-receipt.json，未关闭 linter，也未为消除警告改动成功 Source。

持久结果 SHA256：3199e5582528f712688ab8a0f2d37e8f87504ee6e9fb65a72c0ea3ac5ecb909c。四守卫、全部前缀清单、精确命令、状态历史、输入账和读取边界见 canonical-receipt.json；大型 raw guard 与环境均留在服务器。

父将另行导入唯一对象执行 Unit/Full53；本作者未运行这些检查，没有 Git、发布或更多 emit 授权。rawleaf 增量 0，不扩大原研究根闭合。已 STOP。
