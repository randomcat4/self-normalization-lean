# GI272 — 实际独立和的闭扩张与内缩夹逼

本单元是 OQ3 高斯去平滑链的通用集合接口。原稿 report.md 165–215 的 B_Q 是 Q∩D_x 的仿射像，可有曲边与裁剪边；不得替换为轴平行矩形。

冻结两个完整声明及两个完整 rho let，先于证明实现。任意两个平面概率 nu、eta 与任意可测集合 s，实际平滑律始终是同一个 `(nu.prod eta).map (fun q => q.1+q.2)`。

外扩集为 `Metric.cthickening eps s`；内缩集为 `(Metric.cthickening eps sᶜ)ᶜ`。距离与噪声范数均为 Lean `ℝ×ℝ` 的默认 max 范数。闭扩张对任意集合闭，内缩可测。eps 允许任意实数；负 eps 时好噪声事件为空，坏事件是全集，结论仍成立。eps=0 可能得到 closure/interior，未假设 s 闭或开。

第一条复用精确已合格 GF269 的两条实际独立和概率比较，逐点证明好噪声下的扩张/内缩包含，返回 ENNReal 不等式。第二条用实际概率测度的有限质量转成实数夹逼；只在实数上相减，不对 ENNReal 无穷作减法。

唯一项目承重是 Shao.OQ3.IndependentSumSmoothingBounds（GF269）。复用其完整合格独立报告、所有实际 TYPE、两个完整 rho let 和同首对象回执。新增固定库接口只读 Thickening/Measure.Real 的精确原文与编译导入存在性；不重跑旧生产者或旧 AX。

此处不量化高斯坏噪声、不估计原始曲边小胞的管状邻域面积或加权振荡，也不证明典范密度一致误差或去平滑极限。GH271 的 eps=n^-3 log n 比原稿 h=n^-3/log n 大 log²；其新边界误差义务由 u22gh-source-repair-clarification.json 保持开放，不继承原稿同 h 的式(9)。

保留严格 0<beta<2/5、p54 修复 `v_corr=-hat_t0*sqrt(detDelta)*sqrt(Lambda1)`、Song uniform-in-law 外部输入归属以及联合非格点反例。原始外区、B–D 与 OQ3 正面根仍 OPEN。

所有 Lean/全拥有递归公理门只在指定服务器执行，CPU36–39/44–47、既有 c12-heavy.lock、-M8192 -j4，当前 phase40。固定工具链和 shared-v34 只读；独立审查者不参与作者证明。无 sorry/admit/新增公理/unsafe/native_decide，公理白名单 propext、Classical.choice、Quot.sound。
