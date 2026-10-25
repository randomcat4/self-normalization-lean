# SourceWeightedRecordStrip source06 独立完整修复审查

STATUS: CORRECT（数学源；formalQualified=false）

精确源 `drafts/c2-weighted-record-strip/source06/SourceWeightedRecordStrip.lean`，SHA256 `cc6a0fbb25536cf375509ed1bf6db3f791ffbb45e1023d7a8e74d07a7ef3b76b`，66661 字节、1241 LF、0 CR。同一独立 reviewer `/root/weighted_record_strip_final_review` 比较全部 source05→source06 diff，并完整阅读唯一受影响记录矩的完整声明/证明 156–756。其完整 proof-block SHA `f050f189a31ad126325bd3f5a57710d9ef6330b32323e944ea2c61ab01f60af2` 与 REPAIR-MAP 精确相符。

唯一变动是原 source05 的 688–689 两行替换为 source06 的 688–695 八行：给 hMap 完整等式类型，显式 integral_map 的 f 和 θ 常函数的 measurable domain。替换块前后所有源字符/换行相同。hMap 的完整命题是

\[
\int D(v)^2e^{\theta L(v)}\,d[(\rho\times R)\circ J^{-1}]
=\int D(Jp)^2e^{\theta L(Jp)}\,d(\rho\times R)(p).
\]

这里 J 仍是把原末步 b 放在真实逆序前块后的同一 snoc 映射，R 仍是该 rho 的 m 坐标 product law；D、L、θ 均为原冻结对象/参数。没有更换 joint law、积分函数、record event 或 majorant。

source04 已读取 pinned Bochner Basic.lean1076–1078 的 integral_map 完整类型及 ambient group/measurable 环境，本轮精确复用：hJMP.aemeasurable 给实际映射的 a.e. 可测性；全局 measurable D 的二次幂、显式实数常 θ 与 measurable L 的乘法/exp 给该 f 在 mapped measure 下的 a.e. 强可测性。原 hJMP.map_eq 再把 mapped measure 改回 P，得到原第一步积分等式。方向正确，不要求 D 或 L 在 J 下不变；没有偷偷增加 target integrability，且 hI2 与 hJI 仍独立提供实际可积性，以供之后积分单调性使用。显式类型处理的是真实失败的未推断函数，未添加数学前提。

完整重读的其余记录矩证明保持：常数 C 在法和参数前统一选定；有界支持给所有幂可积、β≥1/B≥1、θ guards/小样本排除；D/L 可测与支持盒可积；真实 product rho 的带标签 cyclic marked average；λ=1.001θ 吸收与 .506 slack；真实末步/逆序前块分解；正记录⇒所有闭 lower survival、D≤b_+、witness concatenate/reversal、D=0 分支；`E[b_+²(b_++β)]≤2β`；实际 map/Fubini、m=N−1 根号比、4000CM/8CW 和统一 C 吸收。未发现数学关键缺口，β/√N、多项式 `1+Nθ²`、精确 .506 和三次/线性参数保持。

循环完整证明 14–154（SHA `6964d4b2b87dca0d7c9b06d959b21c6a791ef5ce4d0d36b8e6ab5d3ca8c2064d`）和真实条带完整证明 758–1239（SHA `fce63cb18895df1d146ea132fb3de97d0cbc8c0fc53d3442aa804aa260f071b9`）与 source05 byte-exact，复用 source04/source05 审查，本轮未重读。三个完整 heads、12 statement let、prefix、假设、guards、统一常数、局部数据初始化、项目依赖、API 均未改动。原始 source-to-original 语义与全部原始数学范围沿既有 source01–05 精确报告复用；没有重审未变 accepted producer 证明。

复用 source05 report SHA `541d1f355bd3c15652d61c4cddb0507e791bf64e0e0292f3e407b1a2e8bc1184`、review SHA `7a7fd73a85a516a50d917d6240a33dd06fe7ea9356fea8e72f044c7df95a5fa7`、seal SHA `83e46f8ad8b66ffc959bbb4cd8f417d8b0ef15a355d3ab32b6e2e604dda5eccb`；这些文件保持不变。source05 实际 native005 RC1/7 errors/18 warnings/no O、错误块 SHA `abd6bf7eb9999ede48632f822c9bcc540088cf26f7752d28ae8c4e63b4c7acaf` 保留，源层数学正确不改写编译失败事实。

source06 的实际 native006 成功凭据/原 O、全部 actual-owned TYPE、全部非定理 FULLVALUE 和递归 AX 尚未交付本 reviewer，故 formalQualified=false、actual counts=null。source04 已读四 API pinned 源环境/字面类型或全定义值，但生成 `MeasurableEquiv.piFinSuccAbove_symm_apply` 实际 TYPE 仍未打印；Root 计划在首次成功对象的必须 owned-audit 合并四 API print，无额外 smoke。本报告不假称有打印凭据。最终公理白名单仍为 propext、Classical.choice、Quot.sound。

本轮仅写 reviewer 目录 source06 新文件，未改作者源或旧证据。Lean/AX/build/server/upload/Git/API/delegation 均 0；配置 gpt-6.1-sol/xhigh，实际 backend/input/cached-input/output/reasoning-subset telemetry 均 null。源数学阶段完成后实际 0 in-flight/0 heavy；下一依赖是同最终源成功对象与审计凭据，或仅实际受影响的后续完整证明修复。Root 继续普通回合。此单元不完成 full separated overshoot；C1 immutablev85 保持既有完成，C2/C12/OQ56 OPEN，OQ3 PAUSED_BY_USER。
