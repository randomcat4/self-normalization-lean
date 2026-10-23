# 独立阶段 B：单次实际执行失败后停止

STATUS: FAILED_STOP_AUDIT_SUFFIX_API_ERROR

唯一一次独立 actualNative 已用完，Native 退出码 1，实际耗时 5.9064249489456415 秒，原始 stdout/stderr 完整捕获；没有 timeout、wrapper exception 或清理异常。失败位于审计后缀的 Options API，未发现原 Source 范围的错误诊断。没有重试、修改 Source 或修改审计工具。原阶段 A 的数学/源码语义结论 CORRECT 保持原件冻结；本报告没有机械 PASS 或完整实际环境审计结论。

## 精确错误与范围

原始 stdout 共 106 行、11026 bytes，唯一错误头及完整必要类型上下文在其 104–106 行：

    /root/rivermind-data/shao-lean-20261021/workspaces/lead-oq4/repro_outputs/oq4-rademacher-strict-cube-implementation-v1/independent-v1/private/Shao/OQ4/RademacherStrictCube.lean:897:42: error(lean.invalidField): Invalid field `setNat`: The environment does not contain `Lean.Options.setNat`, so it is not possible to project the field `setNat` from an expression
      o.setBool "pp.all".toName true
    of type `Options`

最终原 Source 为 835 行；其末尾有换行。runner 按唯一许可方式拼接原字节、一个换行、审计后缀，组合文件 51566 bytes、SHA256 362b475ab2cdb039c2e1129c883725cfc4ca313a6dc42cc6fdd666e431dcc645。组合文件第 836 行是额外分隔空行，后缀第 1 行对应组合第 837 行。因此组合 897:42 精确对应 audit-suffix-v1.lean 第 61 行：

          ((o.setBool ("pp.all".toName) true).setNat ("pp.maxDepth".toName) 1000000).setNat ("pp.maxSteps".toName) 100000000) (Meta.ppExpr e)

这一行尝试从 Lean.Options 投影 setNat，当前钉死环境没有 Lean.Options.setNat，run_cmd 在执行前的 elaboration 阶段失败。完整错误属于 suffix 范围，不属于原 Source 的 1–835 行。静态准备未识别此 API 不兼容；实际运行给出了上述具体错误。本审查者没有自行修补或尝试替代 API。

原 Source 范围还出现 unused/unreachable tactic 警告，它们不是本次退出的错误头。完整原始诊断留在服务器，本地只保留 curated 错误块。

## 执行、保护检查和重型租约

执行授权文件 SHA256 f10b71e42f7a8fa19d94e6b921ac1531cdadb2ae9550aa313626779f417ca8b0。首先只读确认独立 OWN、round001、private Source、永久 once 锁、PASS 标记及共享重型锁均不存在；所有已存在父目录真实且无 symlink；canonical Source/olean 均不存在。整个 W 的目标前缀仅有原 author Source，其 SHA256 为 5802fb4b5403ec27ed2df3ed1a53160e10885cc29056e65aa3e453591f9d4ef5。随后仅新建 OWN，原字节上传所审 runner、suffix、最终 Source、冻结公共接口和授权文件，逐文件 byte/hash 校验通过。

按授权先激活固定环境再进入 W，执行已审 runner。其唯一 Native 命令固定 CPU18–21、-M8192、-j4、autoImplicit=false、debug.skipKernelTC=false，private -R，无 -o；命令完整记录于 execution-metadata.json 和服务器 command.json。

三个 guard 全部 PASS：

- before-assembly：未组装，原输入、所有路径与保护映射匹配。
- pre-native：组合字节精确匹配原 Source+换行+suffix，所有保护检查匹配。
- post：所有保护检查继续匹配。53 个旧 OQ4 源、229 个受保护源码配置、282 个完整源码配置条目及 110 个旧 build 工件的 hash 与集合不变；7 个冻结 ref、二进制、packages symlink 不变；33 组选定源码/olean 和 33 条别名链接全部匹配，canonical pair 仍不存在。

目标前缀由执行前的唯一原 author Source，增加且只增加本次 independent private 组合 Source。原 author Source 的 SHA256 保持 5802fb4b5403ec27ed2df3ed1a53160e10885cc29056e65aa3e453591f9d4ef5；新 private 组合 Source 的 SHA256 为 362b475ab2cdb039c2e1129c883725cfc4ca313a6dc42cc6fdd666e431dcc645。

共享锁释放记录为 SAME_TOKEN_SHARED_LOCK_RELEASED_AFTER_DURABLE_RESULT、released=true，实际共享锁已经不存在。永久 native-attempt-once.lock 保留，133 bytes，SHA256 201599aab0af647ed60f63551f169f109f7200702090160b11b7f8eb3421b0b3。本次 heavy 已结束并归还父，不会启动新重型命令。共享锁文件已按相同 token 规则删除，故不虚构删除后不存在文件的 SHA；其 token/device/inode 仍保存在本次服务器 result.json。没有接触外部 CPU0–9/80GiB 工作负载。

## 本次实际审计未完成的范围

audit-native.json、raw-expressions.json、owned-interface.txt 都没有产生。run_cmd 没有执行，因此下列数量保持未知，而不是使用冻结声明数或旧结果推测：实际全部 owned 数、actual generated 数、递归 closure 数、实际 findOLean import 数。也没有生成可供全文审读的 actual owned interface，故不能交付或伪造其 curated 完整版。

前后 guard 已实际核验 33 个冻结源/对象与别名文件，但 suffix 内的实际环境 33 import/findOLean、unfiltered owned=envdiff=stage2、全类型/定义值导出、递归 opaque 闭包及公理门未得到本次结果。命令设置虽固定，后缀内 trustLevel=1025 等实际断言同样未执行，不将其记为已通过。

## 所有本次服务器 round 文件

目录：/root/rivermind-data/shao-lean-20261021/workspaces/lead-oq4/repro_outputs/oq4-rademacher-strict-cube-implementation-v1/independent-v1/round001/

| 文件 | bytes | SHA256 |
|---|---:|---|
| before-assembly-guard.json | 181290 | b780a45739d9a05a0176f30f6dd7d898d1e2a924353667a6b85ca3bec7482c9b |
| command.json | 1235 | 9fbf97c22d16ffd969a0e93ac3488b5b3a80d4641817377bce1c31054c3c5f30 |
| execution-release.json | 1768 | a4b24105dc16b16e5508b6e5079247fc113c4354ffd89b1cb1e3fd9282e927c8 |
| post-guard.json | 181718 | df86158ba580d8fbc834e9e348ffd1332326e4afbb49d9d0e12fc90c862a60aa |
| pre-native-guard.json | 181718 | a03237a542439ed76ccf972f70f17c735cfaf93b8552613cb849b7e396fd85d0 |
| result.json | 1647 | 1b7ba26ac54fa4610bb14f8b4f57738a51ddf22766b56dfdafa1ed1165d4398e |
| shared-lock-release.json | 91 | bec3bb73bb753f514844c9862e19f8a3da4640de5dee544e8e7c168d31c59678 |
| stderr.txt | 0 | e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855 |
| stdout.txt | 11026 | 4d4e358994f517ae8bbe9b0cdc2e175f910e7a5a5d84b817229e3141c4b6680f |

输入文件 hash、实际命令、组合文件身份、各 guard 的完整 curated 摘要、目标前缀变化、永久锁和释放记录都在本目录 execution-metadata.json。原始日志、完整 guard、原始环境及任何本体均留服务器；没有下载其他作者结果/收据、旧 review 或 raw 环境值。

STOP。等待父依据这个具体工具错误决定后续；不自行重试或改动。原 OQ4 总根 OPEN，rawleaf 增量 0。
