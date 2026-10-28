# Unit249 有限定理执行选项的独立审查

STATUS: CORRECT

sourceAcceptedForNative=true；qualified=false，kernelChecked=false，axiomAudited=false。此裁决覆盖执行选项、精确字节变化和坐标映射，并通过联合覆盖复用已完成的完整数学源码审查。它不声称新源已经执行 Lean、产生对象或通过公理检查。

精确新源 SHA256 为 `19c3e659b538c19d7e73a55bcaec1dc6727b435665e215890cc6c219c88704a0`，240965B、3825LF。freeze03 SHA256 为 `392ce9b9e9fba5ac31c77999f823fa32b624faac7002e48165798d574c702a99`，3292B。

本同一独立角色已实际阅读 freeze03 全文、作者 DELTA.md、STATIC-CHECKS.json，以及 MANIFEST 和 FINALWRITE release 的来源、接口、映射、执行限制及释放字段，并独立重算其所有 input/payload 绑定。作者说明不替代本次核对。本角色仍从未成为证明作者；旧两个审查目录和阶段释放文件保持只读。

## 变化、作用域和语义

唯一变化是在旧第 15 行定理命令前加入：

```lean
set_option maxHeartbeats 800000 in
```

实际新第 15 行为该选项，新第 16 行为唯一 theorem；完整定理及证明终止于新第 3821 行 `exact hRelativeBounds`，随后只有 section/namespace 结尾。`in` 把有限值 800000 限定到随后这一个 theorem command，没有全局或无界心跳选项，也没有新增其他选项。

独立按 UTF-8 字节确认插入恰为 35B、1LF。移除这一行精确恢复上一版 `8202e1075c016ea5180a40774a6e01d456399bf4d82742327cad176fcf1f899b` 的全部 240930B。原前导、公开数学声明、所有假设、定义、实例、选择、完整证明文本与结尾不变。尤其前一版第 3768 行的已审加法修复，在新源第 3769 行原样保持；无需重新审查旧证明。

该选项只允许 elaborator/tactic 使用更高的有限步数预算，不改数学命题或推理规则，不增加假设、公理、selector、helper 或实例。原 native02 的 RC1/noO、默认 200000 心跳失败及所有 warnings 继续保留，绝不转记通过。冻结规定的 -M8192、-j4、CPU52–55 和外部 300 秒约束没有在本次源差异中改变；本审稿人未访问服务器，不另作当前服务器运行状态声明。

## 映射和联合覆盖

28 个事实的完整冻结类型和片段 SHA256 全部相同，h248 仍是唯一获准推断 Prop。730 个 ordinary let、8 个 letI 的完整类型/RHS 均重新按精确冻结引用匹配；public155、optional159、两项数据选择的结构保持。全部 159 项 optional 源码映射的类型和 RHS 哈希独立重算相同。

独立遍历并按实际新源字节重定位 FACT137、DECLARATION1674、OPTIONAL318，共 2129 个坐标对象，错误 0。另对这 2129 个对象逐项比较新旧字典：全部 byte+35、line+1，column 和 UTF-8 byte-column 不变，错误 0。没有照抄描述性计数。

作者 manifest 的全部 29 个 input/payload 绑定独立复算相同。前导加该唯一选项后与原 head 精确连接，closing 精确相同，完整旧248 head 仍可按既有契约逐字节恢复。UTF-8 无 BOM、仅 LF，禁用 token 为零。

本次实际新阅读为新 1–33 行的选项与完整 scope 开头、新 3820–3825 行的终止位置以及以上全部差异和映射。新 1–14 行对应旧 1–14，新增第15行由本次直接覆盖，新16–3825逐字节对应旧15–3824。旧完整 SOURCE 报告及第一次修复的联合覆盖按精确哈希复用，覆盖全部数学声明和证明；p51/p54 来源、p54 修正、外部 Shao–Zhou 归属、同一次 witness、固定 rho、全部加权费用和真实物理统计量保持。没有重读或重审旧完整证明，也没有重放旧248/236 proof/TYPE/AX。

## 当前资格边界

受影响 SOURCE/执行选项裁决为 CORRECT，新源可进入指定服务器 native03。当前尚无本版成功 FIRSTO、完整 actual TYPE、必需 VALUE 或递归 AX 审查；qualified=false。本同一独立上下文保留，等待 lead 提供这些材料后完成最终资格，不能把执行选项通过等同于内核通过。

requestedModel=gpt-6.1-sol，requestedEffort=xhigh；实际 backend/model/effort 和 input/cachedInput/output/reasoningSubset 不可见，均为 null。本角色 Lean/lake/PP/AX/server/network/upload/Git/publication/children/Goal/schedule/sidebar 操作均为零。
