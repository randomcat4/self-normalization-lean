# A 独立完整终审

STATUS: CORRECT

审稿者 context220，独立 fresh gpt-6.1-sol/xhigh；未参与本批数学稿、冻结或证明体写作。判定仅绑定 `Shao.OQ4.RademacherStrictCriticalPhase` 的 attempt004 精确源码。所有原根组仍 OPEN；这里不作一般 OQ4 闭合或新颖性声明。

## 精确版本与审稿范围

- Source：`drafts/oq4/rademacher-strict-critical-phase-v1/attempt004/Source.lean`，SHA256 `be88fb766730153fa175116695cc591f563ba6c11441d55388fad8b2fadd71af`，23394 bytes、425 LF、UTF-8 无 BOM、无 CR。
- Combined：`e5c7a070a5def8c7271efb40d993395a6d7aa4096bdbb13a16563dcbfabfd37f`；独立验证其等于精确 Source 加原 audit suffix，也等于服务器真正编译的 private 源文件。
- 冻结接口：`607578234f37274d3ced12535266970c82906bf60a4d4add5deefe16c9fb3573`；lead freeze：`db9a2732dcb4b637dfba9e9e7e4c118616d18d0be7dde97b4c96e091f8f75f70`。
- 完整数学稿：`e3475ea9facf26aa784c24d6df33c0188f68249bbbf490872d3dbe5ea0845228`。已完整阅读；只使用冻结的直接 upIndex+1 路线，替代对角路线没有成为隐藏前提。
- 实际来源 `C:/game/shao/current/oq4/c01/spectrum01.md` 全文已读并核 SHA256 `b65f9e0c2f9b40a28d092491b479bd20d0b8ee8a9ac940c3c4760cfff7d2670b`。§3 的固定 Rademacher 临界子列结论与 §4 的严格边界修正均被保留。

已逐步完整阅读全部 425 行新源码，全部 35 个实际所属声明的完整展开类型，以及五个非定理声明的完整展开值。35 的分解由实际所属表独立重算为 11 public（五定义、六定理）+1 explicit private theorem+23 generated theorem，不仅审六个公共结果。所有生成辅助命题均在完整类型覆盖和逐 owner 公理遍历中；本批没有生成非定理值或 opaque 值遗漏。字节级反向剥离七段证明体后完全等于冻结文本，故前导、十二个声明头、五个透明定义值没有变化。

还完整阅读同次机器导出的 48 个实际直接消费项目声明的完整类型和全部可用非定理值；其余成熟证明资格复用，不重新审旧证明。对 S5 的 `PositiveTime`、N 的自然数实数转换链、BrownianSup 的 U/pathSup/fullStrip 语义和固定 Rademacher 两个半权原子作了必要定义展开阅读。`Cluster z` 的实际定义是存在 StrictMono 的自然数映射且沿之趋于给定实数，不是另一个滤子极限点概念。

## 完整证明检查

1. **五定义（14–35 行）**：delta 是真实高度的 Nat.ceil 减高度；exponent 为固定 q 乘 delta，factor 为其指数。Q 的分子是同一实际严格路径概率，分母是实际 BrownianSup 概率在字面 `c * n^(-1/6)` 的值。phaseIndex 的三个分支分别为 downIndex、upIndex+1、nearestIndex(c,1-d)，与冻结精确相同。
2. **私有 above_height_error（39–76 行）**：k≥1 提供正 k²；非负高度及正 c³使立方单调比较合法。ceil 舍入加一后的实误差严格正且小于 2。立方差分解的二次因子至少 k²，由此得到严格正的高度差及 `<2c³/k²`。没有把旧 upIndex 可能恰落整数的非严格下界当作严格上端点。
3. **canonical_probability（79–101 行）**：n=0 单独用两个正指标事件的全空间概率一处理。n≥1 时，只在路径积测度的几乎处处真实支持上用 V=√n，接 S5 的字面 x√n=height 恒等式，再用事件的 AE 等价传递概率。未把能量恒等式提升成任意路径的逐点断言，也未加入 r=0 约束。
4. **phase_bounds（104–132 行）**：全 n 高度非负保证 Nat.ceil 是所需上取整；得到 0≤delta<1。q>0 后指数和倍率界方向正确；整数高度时先证明整数非负，再用 toNat 与整数上取整得到 delta=0。零时间没有被用于正时间除消。
5. **phase_realization（137–256 行）**：局部 finish 把已接受的严格单调截尾再平移 2，保持 StrictMono、cutoff 和趋于无穷。d=0 和内点只在已证明的严格开胞元内把旧弱相位与新严格相位精确对齐。d=1 重新证明正高度误差趋零，最终 k<h<k+1，ceil(h)=k+1，从而严格相位趋 1；整数 target 也被加一排除。由旧 up 子列的 StrictMono 加一，及 cutoff 下界的传递，得到真正子列。任意固定 c>0、d∈[0,1] 都覆盖，K 可依赖 c、d，没有统一门槛暗假设。
6. **critical_main（260–320 行）**：对恒等时间列完整满足 GeneralStrictS4 的高度无穷、二尺度无穷与三尺度尾部上界；第三尺度以 n≥1 的 n/h³=1/c³实现，未错误声称 n=0 也成立。S5 正时间接口真正对齐 h/√n 与字面 x；修正项等于 q*delta。尾部三项正性、整列 log 误差趋零及比值趋一都来自同一个已合格严格 S4。差趋零使用精确恒等式 Q−F=F(Q/F−1) 及固定上界 F≤exp(q)，没有假设 F 收敛。
7. **cluster_sets（323–387 行）**：三个相位量的外包含由逐项界和极限保序得到；内包含分别由任意 d、L/q、log(L)/q 的实际 StrictMono 实现得到。log 使用 L≥1>0；q>0 支持除法，端点均覆盖。Q 和 F 的 cluster 双向包含沿同一 StrictMono 映射，用整列 Q−F→0 转移，没有丢失实际子列语义。
8. **not_convergent（390–421 行）**：每个对象的两个端点都属于已证明的实际 cluster；q>0 保证 exp(q)>1。若整列有极限，则两条 StrictMono 子列也趋同一极限，与实数极限唯一性矛盾。四项均覆盖，无额外随机空间条件。

## 服务器证据与公理

复用首次成功 Lean PID874706 的真实 exit0/reaped 收据，耗时 22.63010542280972 秒；Lean v4.36.0-rc1、固定 mathlib `807d3836b165983210ee2ecf3cd28f239436949c`，-M8192/-j4，CPU18–21，autoImplicit=false、skipKernelTC=false、trustLevel1025。执行收据 SHA256 `22db0141717e418ac9ffba2ea5efd5775853d86ba2941b20e710ea99f13a0eec`。

独立只读服务器检查从原成功 `audit-native.json` 重算 type AND value 递归闭包，未调用 Lean 或重新生成 native walk：61388 个节点全部可达且无悬空边，765 个项目依赖声明、31 个项目模块、101 个实际导入项目模块。逐一从全部 35 个实际 owner 重新遍历，所得公理集合分别与同次 collectAxioms 和逐 owner 导出完全一致；总集合仅为 `propext`、`Classical.choice`、`Quot.sound`。无 unsafe、partial、新 axiom、不可用 opaque body；实际完整类型和值没有省略标记。whole environment difference、module ownership、stage2 精确一致。

原 saved audit SHA256 `4c4eed5a8c52cda8f8ac4cdad400d01ca2dd9e029ae378bf64a3325a0c3c2a1f`；全部 17 份 compact manifest 工件在本地及服务器分别核对，投影与原成功 JSON 一致。

首次成功对象采用作者首次内容哈希 `c3530da84db53b2f3c703c0edf913e05c5b7b83faf94878098c6a12f6d5fafe2`，本审稿只做 stat：device64947、inode5111955、size982960、mtime_ns1792827373786978196，均与首次收据一致。所有 ns 均由 Python 整数处理。实际解析的 GeneralStrictS4 对象也与其已合格首次对象的四项 stat 完全一致；本模块没有导入 OriginalStrictS4。旧对象只 stat，不读取或重新哈希二进制，不重编旧 producer。

一次低效的纯 JSON 校验实现已中断并保留中断记录；只修正集合遍历方式后，针对同一 saved JSON 的确定性校验于 07:46:20 UTC 完成 PASS。这不是新的 Lean/audit 运行，也没有修改任何作者输入。

## 裁决与边界

没有发现关键数学、形式陈述、来源忠实性或精确证据绑定缺口。本结果证明固定 Rademacher 严格自归一化事件在字面临界尺度的整列修正、完整闭区间实际子列极限点集合和不收敛；不外推到一般分布或原研究根闭合。B 原空间搬运尚未作为本 A 裁决的一部分；A 报告与收据固化后不为 B 重审或改字节。

输入、缓存输入、输出、推理子集 token 计数工具未提供，均为 null。审稿者无 Lean/nativewalk、Git、缓存或共享源码修改，未派生子 agent；唯一写入目录为本终审目录。
