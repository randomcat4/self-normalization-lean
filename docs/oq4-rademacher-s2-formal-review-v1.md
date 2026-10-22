# S2 独立有界数学与声明审查

STATUS: CORRECT（数学证明与当前源码的冻结陈述忠实性）
NATIVE_STATUS: PASS（2026-10-22T14:38:56Z 实际有界独立检查）
ROOT_STATUS: OPEN；新增原始叶与认证增量均为 0。

本审查是新上下文 86 的独立判断。只读取冻结发布允许的完整原文、两份冻结陈述、匿名数学证明、当前 Source，以及必要的已接受实际依赖定义/公开接口；未读取其他 S2 审查、作者报告、checkpoint、失败修复推理或通用 capsule 报告。参考 math-theorem 的独立验证协议；不搜索出处、不作新颖性裁决、不增加假设。

## 输入及冻结一致性

发布为 s2-bounded-independent-certification-release-v1.json：5074 字节，SHA256 3dff90dbc05564b124d2b3588f2b2b3769e633b7b0af7a07d62a4e7fd1be9508。完整 8 项输入的字节数/哈希均匹配，见 input-binding.json。

原文 spectrum01.md 完整 4306 字节；匿名证明完整 18504 字节（386 行）；当前 Source 完整 17020 字节（426 行，SHA256 1229ec6631165367e1b3fcef50fbe15c3dd8d73b0688de348c5659693c93e3c9）。透明定义 H、N、t、a、rho、eps、q、R、B、p、K、D、C_U 共 13 个，与形式冻结代码逐字一致。definition_bridges、F0、F0_zero_time、F0_small_cells、T0、F1、Q1 共 7 个完整定理头也逐字一致。

## 原文到实际陈述

原文第 1 节对 h≥1 的弱事件取 m=floor(h)、H=m+1；形式域 m:ℕ、1≤m、m≤h<m+1 恰表达相同胞元，含整数下端、排除上端，不把 H 改成 h。p 的定义是实际 Fin n→ℝ 产品测度对 Shao.closedStrip 的实值测度；law 是两项 1/2 加权 Dirac(±1)，closedStrip 监测 0 到 n 的所有前缀绝对值≤h。此时 h≥1，监测零前缀与原文 M_n 弱事件相同，空路径概率为 1。K 是实际 killed kernel 的自然幂在起点 0 上的常数 1 积分。它们均未按谱和重新定义。

原文 S2 的主项 a_H rho_H^n、负主模态 (-1)^(n+m) tan²(π/(4H))、统一 O(exp(-π²n/H²))，分别由 a/rho/B、eps/q、固定实际 Pair.remainder 与实际 Tail.absoluteC 表达。原文统一余项的有效阈值 n/H²≥1 恰为 F1 的 H²≤N；未提高阈值、删小胞元或改余项。原文 O(H^-2) 的正切平方校正被 T0 的明确非最优常数 π²/4 加强，该常数在结论侧内部证明。

Q1 对任意自然索引序列只假设逐点胞元条件及 H→∞、N/H²→∞；无需单调性、奇偶匹配、n/h³ 条件或 Brownian 输入。它把原文渐近式表为实际 p/B→1，并导出 K/B、最终正性和相对对数；这些是透明派生输出，不增加原始叶，也不声称 S3–S5、一般分布或 OQ4 根已完成。

## 完整数学证明审查

1. 定义桥（匿名证明 59–147；Source 41–56）：alpha(m,0)=u、beta(m,0)=z 由自然数 2·0+1=1 直接展开；cotangent=cos/sin 给 a=Scalar.a，rho=Scalar.rho。没有把两个同名对象的相等偷作前提。Scalar.SCA0 在 m≥1 上给 H≥2、角度合法、a>0、0<rho<1，因此所有 n:ℕ 的 B>0。定义桥本身没有 m≥1 假设，H=m+1 的透明相等对 m=0 也成立。

2. 全有限域 F0（证明 149–179；Source 58–114）：实际 Pair 的概率桥与归一化接口均量化全部自然时间，前提恰为原胞元条件；由 B≠0 才除去主项。p=K 与 D=K/B 没有过程替换。n=0 时单独输出 p=K=1；zeroMode(m,0) 对偶 m 是 (-1)^(m/2)/H，因为 0^0=1。m=1 的删首下半谱和与中心项均为零，故 R(1,n)=0；m=2 的尾和为空而中心项为 -(1/3)0^n，故正时间余项为零，但 R(2,0)=-1/(3a(2))≠0。源码明确保留这个例外。无奇偶限制。

3. T0（证明 181–219；Source 116–171）：在 x∈[0,u]、u≤π/8 上，cos x>0 且 cos(2x)≥0，故 cos²x≥1/2。tan 连续且内部导数 1/cos²x≤2；中值定理/凸区间导数界给 tan u≤2u。tan u≥0 后才平方，得到 q≤4u²=π²/(4H²)。|(-1)^(n+m)|=1 对所有 n，包括 0。未调用 Scalar 的私有便利估计或任意 C_tan。

4. F1（证明 221–250；Source 173–209）：C_U 在所有 m/h/n 与序列之前由固定实际 U1 取定；当前源码直接绑定 Tail.absoluteC。实际 remainder_uniform 只有 m≥1 和 H²≤N，无隐含胞元、奇偶或更大时间条件；它比需要的胞元接口更强。D-1-eps·q=R 是 F0 的精确代数恒等式；三角不等式及 T0 得总误差界。三条界使用同一个常数与同一个 R。H≥2、H²≤N 自动排除 n=0；没有以新正时间假设缩小 F0。

5. Q1（证明 252–366；Source 211–422）：全 k 的 F0 与空路径身份先保留。t→∞ 在阈值 1 上给固定 K_time，此后 H²≤N 且自然数 n≥1，故 F1 在同一时间尾段同时给三条界。H→∞ 给 H^-1→0，从而 π²/(4H²)→0；t→∞ 和 -π²<0 给指数项趋零。匿名证明也给逐容差阈值及两个实际误差趋零的独立实分析推导，未把收敛放在前提侧。夹逼得到 |D-1|→0，再得 D→1 与全点相等的 K/B→1。

6. 正性与对数（证明 321–366；Source 354–415）：从 D→1 得固定 K_pos 上 D>0，由全点 B>0 与 p=BD 得 p>0，再由 p=K 得 K>0。两条精确对数等式都在这个同一正性尾段成立。a、rho、rho^n、B 在全点为正；log B=log a+N log rho 的指数是实际自然数 n 的实数强制转换。Real.log 的总函数性未替代正性证明。log 在 1 连续给 log D→0；概率/K 的相对对数与它最终相等，因此同趋 0。Source 中 K_pos 不必大于 K_time：对数恒等式仅消费全时间 F0 与已证正性，完全不需要额外时间域；若后继需要统一尾段，取 max 即可，不是新增假设。

## 承重依赖与限制

数学判断相对于固定已接受的实际 Pair、Scalar.SCA0、Tail.U1 接口。匿名证明中 U1 形式状态 PENDING 是写作时的历史元数据；当前 native 检查必须绑定实际已接受 Tail 源码与 artifact，不能把该句当新的输入假设或通过凭据。本审查核对其实际定义与完整接口条件，不重新证明上游已认证模块。

当前 Source 没有 sorry、admit、axiom、unsafe、partial、native_decide 词项。静态审查不能替代内核和全 owned 传递公理门；实际状态与全部失败记录由最终 check-receipt.json、owned-axioms.json、actual-interface.json 给出。历史工具域或来源缺口不追溯宣布通过。任何根仍 OPEN。


## 实际服务器内核与全 owned 公理结果

最终门 PASS：2026-10-22T14:38:47.938246Z 至 14:38:56.228585Z，exit 0，无超时；实际 Lean 调用 2 次（首次仅审计显示选项失败，后缀修复后通过）。最终用时 8.044932 秒；子进程最大 RSS 3,783,272 KiB，约 3.61 GiB。这是最大单子进程 RSS，不是合计内存峰值。仅占 CPU18–21 单重槽；已释放。所有 Lean 均在服务器执行。

实际主模块为 Shao.OQ4.RademacherS2Assembly；真实 -R 根为服务器本任务 actual-R-attempt3。完整原 Source 从第 13 字节偏移连续嵌入，前置仅 import Lean 加空行（13 字节，SHA256 a13d0e5aed18fede2f97a7dd73b97c2a95513fb67c6c2a3ea37325b09619a541）。后缀为本人的 4699 字节局部审计，SHA256 3ecd6a400286876d29ebe9eb936b41ad25cc2601a79e19dd7ca836d02c471a23；合并文件 21732 字节，SHA256 5e36002764ea7adc2b5000c117053bdf904b3651fb9e48490f392185767ad391。无 self-import，无 -o；canonical 源码、canonical olean、fresh target olean 在检查前后均不存在。

固定工作树 HEAD c340b9f27c497ce0959e54aa49bc41ef055ae959；Lean 4.36.0-rc1 / commit c9afcddf514a6772bd4d649f7cfc04eff0b9f15e；Lake 5.0.0-src+c9afcdd；mathlib 807d3836b165983210ee2ecf3cd28f239436949c。精确版本文件、可执行文件、libleanshared、owner/axiom API 源码哈希在 check-receipt.json。

精确 argv（cwd 为服务器 workspaces/lead-oq4）：

```text
taskset -c 18-21 lake env lean -M8192 -j4 -DautoImplicit=false -R /root/rivermind-data/shao-lean-20261021/workspaces/lead-oq4/repro_outputs/oq4-rademacher-s2-independent-bounded-v1/actual-R-attempt3 /root/rivermind-data/shao-lean-20261021/workspaces/lead-oq4/repro_outputs/oq4-rademacher-s2-independent-bounded-v1/actual-R-attempt3/Shao/OQ4/RademacherS2Assembly.lean
```

按 pinned Lean Environment.getModuleIdxFor? 的实际语义，some idx 是导入声明，none 是当前模块；当前 mainModule 已断言精确身份，且未作为导入出现。枚举 kernel 中全部 none 声明，并与 getLocalConstantInfos(skipTheoremSubDecls=false) 的完整未过滤清单比较相等，两个计数均为 44。未按命名空间、private 或 generated 过滤。44 项为 13 defn + 31 thm（7 个冻结公开定理和 24 个生成定理）；其中 5 项位于目标 namespace 外，完整保留：

- Shao.OQ4.RademacherScalarBounds.H.eq_1
- Shao.OQ4.RademacherScalarBounds.a.eq_1
- Shao.OQ4.RademacherScalarBounds.u.eq_1
- Shao.OQ4.RademacherScalarBounds.z.eq_1
- Shao.OQ4.RademacherSpectralPairing.amplitude.eq_1

逐项 Lean.collectAxioms 传递检查覆盖类型与证明/值；全部公理集合均属于精确白名单 propext、Classical.choice、Quot.sound。unsafe=0、partial=0、新 axiom=0，无 sorryAx/admit/native_decide 等违规传递公理。每项完整名称、kind、module owner、universe 参数、flags 与精确公理数组见 owned-axioms.json（16490 字节/SHA256 f8fa14ca8c661eac9d1ec1b5c620e602d9d3caf02819d5ecc2d5e731712e5fdf）。

已完整读取实际 20 项公开类型/透明值输出，并与冻结声明和定义逐项核对，PASS；文件 actual-interface.json（14961 字节/SHA256 00be6d511b480f5d079dd4b389e26f82a51eeaec53ae86022711e4004e7f5152）。没有隐藏新增前提，保留全部自然时间、实际概率、实际唯一 R、同一个 C_U、两种尺度与同一正性/对数尾段。

实际环境导入 5513 模块。仅对其中 21 个实际 Shao 项目依赖闭包的源码与旧工件及固定输入执行有界前后哈希核对，无漏项目、无额外项目，全部不变；完整项目字段/哈希见 project-dependencies.json（SHA256 0203a63d1a02e2ac047eade6582f0ca6f375d6a1232e9bbbe4eea8698e586b6a）。三指定上游源码与冻结完全匹配，工件 hash 为：Tail 5191d3b546c3aea887442a0290892319af37affc1167759589adbf0809c8169c；Scalar eca40068036732752546d5280ce828ded6e42eeeb3c347c2d84a964617ad5380；Pair b90ac1f16d32e4ebca0b616e6bada7da37d9e07f4648f8a7bf80c1f812be4df1。非项目共享缓存使用固定版本/pins 与 root 的 cachequiet 凭据，不声称完成其全缓存前后哈希或历史来源重认证。最初一次预检曾绑定较宽传递文件闭包；父提醒收窄后不再重哈希，它保留服务器且不参与最终门。

## 尝试分母与保留限度

预检 1 因 Lake 源码另位于 src/lean/lake 而停止，Lean 调用 0；预检 2 因服务器没有 /usr/bin/time，Popen 在创建子进程前失败，Lean 调用仍为 0。均仅修复自己的路径/runner。

实际 Lean 第 1 次（attempt2）运行 7.934248 秒、exit 1；Source 没有报错，44 项 owned/20 接口和公理门已经产出；失败恰为本审计后缀 pp.width、pp.maxDepth 两个 Unknown option（合并文件 432–433 行）。只删除这两行本人的显示设置；Source 从未修改。该次完整 stdout/stderr、源文件、后缀、runner、依赖快照与公理输出原样保留服务器；check-receipt.json.attempt2 是外带的简明失败收据。

实际 Lean 第 2 次（attempt3）完整原 Source + 修复后审计通过，未再重复编译。无源码 blocker。原 8 项本地输入在最终读取时仍逐项哈希匹配。完整 raw/full logs、二进制及完整环境原始输出均留服务器；只外带本报告、简明 metadata/attempt receipts、全部 owned 名称公理和实际公开接口。未写 canonical、shared cache/build/install、pins、Git 或其他工作者文件；未干预外部 CPU0–9/80GiB 工作。

本结果为冻结 S2 范围内 LEAN_FULLY_CHECKED_WITHIN_FROZEN_S2_SCOPE。它不回溯认证旧工具域或旧来源缺口，不增加新数学假设；所有根继续 OPEN，新增认证原始叶为 0。
