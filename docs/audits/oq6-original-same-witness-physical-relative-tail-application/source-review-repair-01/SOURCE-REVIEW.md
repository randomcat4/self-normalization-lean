# Unit249 同一独立角色的单行修复审查

STATUS: CORRECT

这是受影响源码审查结论。`qualified=false`，`kernelChecked=false`，`axiomAudited=false`；新源的实际成功对象、完整 actual TYPE、必需 VALUE 和递归 AX 尚未提供。本报告没有把数学上正确的调用当作 Lean 已执行通过。

精确新源为 `author-repair-01/OriginalSameWitnessPhysicalRelativeTailApplication.lean`，SHA256 `8202e1075c016ea5180a40774a6e01d456399bf4d82742327cad176fcf1f899b`，240930B、3824LF。继承的完整接口冻结 SHA256 为 `1c02c82ad8077a51d1f445c0a5b0d9b9b92c3b1a512832f4dfee5d6626772e20`；本次精确修复冻结 SHA256 为 `cbc16090a06cbe6dcb9f43aece8d224b03fe6fc1969eba9ac07026d35d257787`。

本审稿人就是旧源码 `a81c0e0e50a16e3ee9ae06ef3d1ce8b82f4a0c6a97766320a1a529a2bfb245f5` 的独立完整审稿人，从未作为该证明的作者。旧 `source-review-01/` 的全部封存字节保持不写。旧完整报告、全部 3824 行覆盖和精确失败证据原样保留；本次只审实际变化、完整受影响上下文和更新的映射，没有重新阅读或重新审查旧证明。

## 精确变化与局部证明

独立按字节确认，唯一变化为第 3768 行：

```lean
-- before
      apply add_le_add_left
-- after
      apply add_le_add le_rfl
```

只增加 2 个 UTF-8 字节，LF 数和全部行号不变；前缀和后缀逐字节相同。公开 head、前导、结尾、所有冻结声明、类型、let、实例、选择和其他证明执行文本不变。已知首次失败的旧字节没有覆盖。

实际重新阅读的受影响完整局部块为 3753–3784 行，含两个 payment 的完整 RHS、费用倍数等式、`hPaymentLeOne` 的完整类型及证明、236 吸收、下损失和上损失。所需继承上下文为 N00–N06，特别是固定 n、t0、cg，以及 `hz : 1≤z`。局部全文与旧完整审查覆盖联合，不留新的未读独特作用域。

展开 payment 后，目标为 `A+B≤A+C`，其中

`A=3*exp(-boundedPolylogMomentOrder t0 n)+exp(-cg*n)`，
`B=4*exp(-(z*sqrt(n))/2)`，
`C=4*exp(-sqrt(n)/2)`。

`add_le_add le_rfl` 用自反的 `A≤A` 作为第一项，并把第二项保留为 `B≤C`。这不要求 A 为正或使用任何新前提。余下未改的证明去掉非负系数 4，使用指数单调性，再由 `z≥1`、`sqrt(n)≥0` 得 `-(z*sqrt(n))/2≤-sqrt(n)/2`。因此此次调用消除了旧报告精确指出的共同前缀方向错误；`hPaymentLeOne : payment≤payment1` 的冻结类型完全不变。原倍数恒等式、同 cg、原 t0 的费用吸收和最终损失传递均不受影响。

这是一项完整的局部源码判断。尚未用新源实际 native 和成功 FIRSTO 的证据确认该调用的 elaboration、整条证明或公理闭包；旧 RC1/noO 从未转记为通过。

## 坐标与完整覆盖的联合

独立复算新源及其 author manifest 的 37 个 input、7 个 payload，共 44 个文件绑定，全部相同；另将作者 manifest 自身纳入本报告输入绑定。新前导/head/closing 与完整旧 head 恢复均逐字节成立，UTF-8 无 BOM、仅 LF，禁用 token 为零。

直接重新核对 28 个事实的完整冻结类型与实际源码提取；27 个显式类型不变，h248 仍为唯一获准推断的 Prop。事实片段 SHA256 中只有 hPaymentLeOne 改变。730 个 ordinary let、8 个 letI 继续按全部完整类型和 RHS 匹配原冻结引用。全部 159 行 OPTIONAL-MAPPING 的源码坐标、类型 SHA256 和 RHS SHA256 均相同；public 155、optional 159、数据选择 2 的结构保持。

不采用描述性计数，独立遍历三份新映射中所有具备 byte/line/column 的坐标对象，按实际 UTF-8 源字节重新定位：FACT 137、DECLARATION 1674、OPTIONAL 318，总计 2129，错误 0。前后字节偏移的实际变化由真实源确定，未将旧描述计数照抄成新结论。

UNION-COVERAGE.json 绑定旧完整报告及覆盖清单，声明旧源除第 3768 行之外的精确字节覆盖在新源复用，同时为 3753–3784 行提供新的直接局部阅读。旧 source-review-01 的 CRITICAL_GAPS 保持历史状态；本报告只在新精确源上解决那一个已知源码缺口，不改写旧裁决。未重放 248/236 的旧 producer、证明、TYPE 或 AX。

## 资格边界与下一步

新源 affected-SOURCE verdict 为 CORRECT，sourceAcceptedForNative=true。全体数学来源、真实统计量、p54 修正、外部 Shao–Zhou 归属、全加权与删除费用、固定 rho 和同一次选模范围精确复用原独立审查，不新增数学假设或根结论。

本同一独立上下文等待 lead 提供新源首次成功原对象的来源绑定，以及全部实际所属完整 TYPE、必需非定理 VALUE、transitive AX、native 和 same-object audit 材料。只有读完并核对这些材料，才会给最终资格；当前 qualified=false。

requestedModel=gpt-6.1-sol，requestedEffort=xhigh。实际 backend/model/effort 及 input/cachedInput/output/reasoningSubset 均不可见，记录 null。本审稿人 Lean/lake/PP/AX/server/network/upload/Git/publication/children/Goal/schedule/sidebar 操作均为零。
