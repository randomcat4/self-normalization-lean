# unit280 来源到完整实现忠实性表

状态：8声明/6完整proof已著作，独立SOURCE/Lean/AX均未运行，sourceAccepted/kernelChecked/qualified=false。

| 接口/边界 | 精确实现 | 来源与证据 | 限制/状态 |
|---|---|---|---|
| D01共同E | 固定n/r/w后一个样本集合；全部坐标非负，全部i≠j样本原残差包络 | freeze D01 HEAD/RHS逐字切片 | 定义本身不声称可测；保留原对角与重复观测 |
| D02有限包 | x后∀有限v∀B；absFA半系数、行差、中心化范数系数1 | freeze D02与278实际T12/T13/T19 | 原n−2；n4仅后两项，cardB3仅范数项 |
| T01 pair MP | Pi恒等坐标iIndepFun→hij两独立→joint map→两个eval边缘 | 原7组Mathlib完整HEAD/context复用；源码43–59 | Ω任意可测，μ概率；i≠j≠观测值互异；不消费旧private hPair |
| T02共同AE | 单坐标和pair QMP.ae；有限Eventually.all；同x合取 | 源61–86；hw/hr原AE | 无r/w可测隐藏条件，不对v作不可数AE交 |
| T03真实可测 | 权重/残差复合坐标可测；Set.ofPred_forall有限/命题iInter | 源88–107；显式hmr/hmw；本地同版API语法例绑定 | 不用StandardBorel/非原子/可测单点或对角可测 |
| T04两种概率1 | T03+T02→mem_ae_iff_prob_eq_one→Measure.real/toReal1 | 源109–123；附加完整MathlibProbability HEAD/context | AE不自动蕴含E在原σ域可测；两可测前提明确 |
| T05实际有限代入 | 先x∈E解包hxW/hxR，再取v/B，逐项精确调用278 | 源125–147；12完整TYPE/9VALUE覆盖/原O复用 | 无新增对称、均值0、方差1、g可测或矩条件 |
| T06量词 | 同一AE E内点态加T05，得到x∈E∧∀v∀B | 源149–158 | S(x)可点态代入，不宣称S/统计量/选后事件可测或尾概率 |
| 空/小n | E及半系数项全部n；空指标/空B量化合法 | D01/D02/T02与278原边界 | cardB≥3不是279物理m=3推广；279未qualified不消费 |
| 零能量/分母 | 无除Qb或sB；零sB/Qb允许 | 原278范数平方根表达式 | n≥4保证实际n−2范围，不改为cardB−2 |
| 缩放/对称 | backgroundRow/sB沿原((cardB−2)/(n−2))残差核 | p41(4)-(5)/278固定VALUE | 不添加T10分子恒等式；三界不要求对称 |
| 冻结字节 | 8HEAD/2RHS/PRE/CLOSE逐字；defHEAD带outer:=接裸RHS | DECLARATION-BYTE-MAP source653589d6…7371B/162LF | 无额外声明、helper、前提或重复separator |
| 供应复用 | qualified278源码/原O/独审/native/AX复用 | SUPPLIER-COVERAGE和未省略TYPE/VALUE副本 | 0旧proof重审/0旧producer或AX重跑；wrapper false/warnings保留 |
| 认证状态 | 本地纯文本guard/字节重建 | STATIC-TEXT-GUARD | 不是独立SOURCE或Lean核验；新actual-owner/AX结果未产生 |
| 原范围OPEN | 条件投影/均值方差/交互/rareblock/PE-R/PE-L/NR/DC/root | p41/p51原域；αp=2(p−2)/(2p−1) | 不从276任意α条件窗偷换无条件范围 |
| 历史/权限 | 原proposal/partial追加/freeze/library整树只读 | 新实施ACT与原incident provenance | 旧postLAST追加不被追认；仅新author scope封存/释放 |

作者自查并非独立审查。author-01内的uniqueLAST只释放本次active+dormant权限；没有后台任务、排队或活跃等待。
