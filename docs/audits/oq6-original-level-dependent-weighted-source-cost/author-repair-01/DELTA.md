# Unit250 冻结的三个形式证明修复

状态：完整修复候选已按精确冻结字节封存；新源未运行 Lean、PP 或 AX，未获得独立 affected-delta/final-machine 接受，sourceAccepted=false、qualified=false。

旧源 SHA256 `17ab15bf0299531a33ba9710cbb8e43c61d59de6d306aeb5e900378b2a799c2a`，19166B、363LF。
新源 SHA256 `9eab174ed67833ed40df18ea889fb60a98e0c49401d4955872560e15bc4ebe6f`，19238B、365LF，UTF-8、无 BOM、0CR。

1. 新238–240行：只为原 `hr.comp` 的坐标对映射加显式 `Measurable (fun ζ : Fin n → Ω => (ζ j, ζ k'))` 类型标注，固定映射定义域。没有引入新 fact、实例或可测性前提。hEdgeM 的完整类型保持。
2. 新327行：在 hFullDom 中用 `add_le_add le_rfl` 配对共同左前缀 `z * |D1 ζ|` 与 `z^2 * B ζ ≤ z^2 * BA ζ`；原非负乘子证明不变。hFullDom 的完整类型保持。
3. 新333行：在 hDeleteDom 中以同样 API 保持共同左前缀 `||D1 ζ|-|Ddeleted ζ i||`，右分量继续用 z 非负乘真实预算删除差支配；原 cap 与指数的非负乘法步骤不变。hDeleteDom 的完整类型保持。

STATIC-CHECK.json 给出三个 before/after 全块、旧新字节/行坐标、四段不变字节区间及 SHA256；逆替换精确重建旧源。除此之外所有字节精确相同，冻结 preamble/head/closing 与全部 let/have 完整类型不变。原模型及全部量词、full/deleted 权重、原 n 与 (n-2)^2 删除归一化、真实绝对删除差、预算当前层级 z、原 cap `min |z*ξ0_i| 1`、同一正积分 I=m^n 与最终常数全部保留。没有涉及 unit249 的 fixed clipping1。

从新365LF实际重新导出：118 个命名绑定，50 let（结果 telescope 16，proof 34）和 68 have；131 个定义明确的源 binder-marker 站点（旧源重导 130），17 组公共参数。新增站点仅为类型标注中的 lambda；不是新假设或 machine owner。SOURCE-INTERFACE-INVENTORY.json 包含逐个完整 signature/RHS/source block、实际新行列、局部 binder 类型和 hDeleteM 内嵌 hAbsD/hAbsB 的作用域。

既有独立审稿的363LF全文及 p51/p54覆盖仅在三个delta之外按精确旧hash复用；原REPORT、COVERAGE、MANIFEST、GAP及native01失败资料均未改写。原native01自然RC1/3errors/noO保持，不是新源的pass；这里不重复旧production、proof、TYPE或AX检查。同一独立审稿角色仍需核对真实三个delta与首次成功原始O的全部actual TYPE、required VALUE及逐owner递归AX。source-level inventory不替代这些机器材料。

此角色只在 author-repair-01 写文件，无 Lean/lake/PP/AX、服务器、网络、上传、Git/API、发布、子智能体、Goal、schedule 或sidebar操作。请求 gpt-6.1-sol/xhigh；实际模型、强度及input/cachedInput/output/reasoningSubset用量均不可见，记null。
