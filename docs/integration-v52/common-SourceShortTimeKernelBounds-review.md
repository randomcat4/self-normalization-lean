# 实际短时间核求和的独立完整最终审查

STATUS: **CORRECT**

审查者 `/root/common_short_kernel_review`，fresh `gpt-6.1-sol` / `xhigh`；作者 `/root/common_short_kernel_author`。审查者从未编写或修改本单元的数学陈述、假设、定义或证明。本轮仅写本报告及同名 JSON；未运行 Lean，未改旧生产者、冻结物、原日志或旧收据。使用 `math-theorem`，未使用 `math-ultra`。

结论绑定提交 `9c258ccccfae5fe3e34110dde0822325401f8174` 的 `Shao/Probability/SourceShortTimeKernelBounds.lean`，完整读取其全部 655 行源与证明，并完整读取服务器实际所属的全部 34 个声明类型、全部 6 个定义值及每个声明的递归公理集合。唯一公开手写定理是 `sourceTruncation_futureNoise_short_kernel_sums`。同名 JSON 给出逐 owner 的完整名称、实际类型/值哈希、字节数、公理与审查结论；计数来自真实模块所属映射，不来自源文件关键词。

## 精确版本与冻结

| 绑定物 | SHA256 |
| --- | --- |
| 源文件、当地 `drafts/c12-short-kernel/work.lean`、冻结提交 blob | `842e13b2b1a59fa4673b6f938d3a58ba986116fdb0ba3fd72745cef1614da06d` |
| 实际 `.olean` | `77a708f2f094ccb6ceecc4dcfb110789720f0db298e710205c28969f0c3118f9` |
| 实际 `.ilean` | `5825478f6c99bedd98e95a2128991a3ea56fc1a74d65cfc5f9d2ceef155543c4` |
| `drafts/c12-short-kernel/author-receipt.json` | `aad81af2d3a21d6e1ac385b958090d755a8f34a9eb9f98da925591f856811ab4` |
| 根完整冻结 `coordination/public-short-kernel-declaration-freeze.md` | `7d0cdce4c26ea98fb09442650dceb80aa4bac468479bdef26d87cdaf281e80b8` |
| 完整候选声明 `drafts/c12-short-kernel/candidate-declarations.md` | `e45e8bd4964377fbb5ec07aee971be7f51747fcdc5bfbc7570b40dcefffb41b1` |
| 完整源合同 `drafts/c12-short-kernel/source-contract.md` | `ee0c497e27cc5118ca21b090bd119d17eb52a9e7a83a6ae56ca582295f9d83bb` |
| 已批准路线补充 `coordination/public-short-kernel-proof-route-addendum.md` | `33905b1eab113a71ffe5c2b6e78191c6c889d6945153b2f6cdf43bf4aadbf9f3` |

当前服务器工作树 `workspaces/common-short-kernel-v51` 的 HEAD 正是上述提交，状态干净；源字节等于提交 blob，源/对象/日志/审计文件现物哈希逐项符合最终收据。源为严格 UTF-8、无 BOM、LF、零 CR；无 `sorry`、`admit`、新 `axiom`、`unsafe` 或 `native_decide`。公开声明与冻结完整字面声明在仅规范空白后相等，数学假设和量词无变更。

原始只读来源 `C:/game/shao/current/c12/supplement.tex` 的 SHA256 为 `b99f2ac4d2f39dd39772d98a5702b7a923c2f10f8730a08fc1b4cd6bba4742bd`。已完整读取 LF571–650 的上下文及 realkernel(iii)、LF2342–2366 的真实核/奇偶反演定义、LF2554–2698 的短时间分区、区域界和时间网格路线。本单元忠实证明该来源 realkernel(iii) 的实际核版本。

## 从来源到实际陈述

源 LF476–510 与实际展开类型保留了：在所有原始概率律之前选绝对 `C,epsilon0,L2`；原律有限二阶矩、`n*∫a²=1`、原律均值零、`x≥0`、`epsilon>0`、足够小的 `epsilon` 和实际截断预算；真实条件律 `cond ν0 {|a|≤epsilon/(1+x)}` 及其 `mu,m2,m3,variance,gamma`。没有把条件律假定为中心或对称，也没有输入区域界、时间和式或核界。

实际 `sourceFutureNoiseKernel` 是已接受的未来增量产品律与真实全噪声卷积核；本轮读取其完整定义以核对坐标、平移方向和测度，未重审旧证明。`f i q w` 的第一坐标恰为 `w`、第二坐标为 `q`；奇偶部分取第一坐标的正负反射。第一导数与嵌套第二导数均为通常的实 `deriv`，并额外给出所需三项实际可微性。

`J` 恰为 `range(n+1)` 中满足 `n/2<i` 和 `L2*gamma²≤T_i<max(L2*gamma²,y²)` 的指标，`T_i=(n-i)m2`。自然数的 `n/2<i` 与整数指标的实数严格半程条件一致；它不引入 `i=0`。LF555–563 在下界已成立时严格证明 max 上界等价于 `T_i<y²`，从未假设 `J` 非空。若 `y²≤L2*gamma²`，`J` 自动为空、可微性断言真空成立且两个有限和为零。`gamma>0,m2>0` 和正下界保证 `i=n` 不属于 `J`，没有删除定义中的零步端点或额外假定 `m>0`。

最关键的量词没有弱化：LF632–652 对任意 `q,w : ℕ→ℝ` 逐指标使用 `hpoint i hi (w i) (q i)`，仅约束所选指标的 `|w i|≤y/16`。每项可选不同空间点，`q` 全实空间不受限制。因此保留来源的有限和逐项一致上界强度；没有只证明一个共同 `q,w` 的和，也没有借总化上确界引入完备性假设。

## 完整证明核对

1. **真实律与小量支付，LF232–318、534–554。** 内部选 `h=epsilon/(1+x)`，由 `x≥0`、`epsilon>0` 得 `h>0,h≤epsilon≤1/2`，且真实条件律几乎处处 `|a|≤h`。接受的 `sourceTruncation_law_data`、`sourceTruncation_variance_bounds` 与 `sourceTruncation_gamma_bounds` 在完全相同的原前提下给出概率律、三阶矩可积、`V=m2-mu²>0`、`m2>0`、`gamma>0`、`gamma≤2h≤1`、`gamma≤2*n*m3`。原 `3/4≤n*m2≤4/3` 等支付由精确已接受生产者内部使用，不变成新假设。

   `kappa=1/128,L2=16384`，确有 `L2≥20`、`kappa*sqrt L2=1`。`epsilon0=min(1/2,delta2/8,delta3/512,delta5/8)>0` 在律之前选取。由 `y≤2` 得 `(4h)y≤8epsilon≤delta2,delta5`，以及 `(gamma/kappa)y=128gamma*y≤512epsilon≤delta3`；全部三个真实外区小量条件均已支付。

2. **第四区统一包络，LF43–73、105–190。** 实际使用的参数是 `b=gamma/kappa=128gamma`，原下界正好给出 `b²≤T`。所以 `b^10≤T^5`，且 `b^9 sqrt b=b^(19/2)=(b²)^(19/4)≤T^(19/4)`；正 `T` 下的实幂合并严格得到偶轮廓 `≤R=1+sqrt(y)T^(-1/4)`、奇轮廓 `≤bR`。再由 `gamma≤2B`（`B=n*m3`）得到 `bR≤256(A+B)R`。这条路线完全符合已批准补充，无须另证 `a=-5` 积分。

   其余四区用 `R≥1`、`T<y²≤4`、`sqrt T≤2`、`h,gamma≤1` 支付：区域1/2系数取4；区域3偶界的 `384+81920=82304` 和奇界都足够；区域5用 `gamma^30≤gamma` 保留奇界的 `n*m3` 因子，偶界用 `b≤128`。固定 `M=10*4^31*128^30` 为绝对数。没有把与律有关的小量塞进绝对常数。

3. **真正五区全平面积分，LF75–103、319–434。** 明确使用可测 `U={|u|≤kappa/gamma}`、低集 `L⊆U` 与含 `u≠0` 的锥 `C`；五集分别为 `L∩C,L\C,U\L,Uᶜ∩C,Uᶜ\C`。LF366–388 完整证明它们等于每个真实生产者的集合。原点属于区域2；`u=0,v≠0` 属于区域3；低阈值等号保留在低区，锥边界使用闭不等式。

   接受的第四区界在高阈值闭集 `R4bar` 上成立；LF389–410 先以非负范数的集合积分单调性限制到严格 `R4⊆R4bar`，再作全平面加法，边界没有双算。`short_five_integral` 先从五个真实区域可积性推出全平面可积，再用相交/差集及补集的积分分裂得到精确和，不把有限重叠覆盖直接当成等式。

   所有区域的被积函数已经包含 `1/y²`，LF413–434 只合并现有因子，最终 `K=4C1+4C2+82304C3+256C4+M*C5` 同时控制两个真实二维范数积分。

4. **真正标记对积分和相位，LF436–474、582–629。** 完整消费已接受两条标记分部积分反演接口；它们各自同时提供真正 `Gplus,Gminus` 的二维绝对可积性和反演恒等式。没有从固定 `v` 界乘无界 `v` 积分，没有推出三重绝对可积性。`shortB` 完整定义正是幅度 `chi(r)/(sqrt r+sigma*w/y)^2` 配合 `sin(u*(y*sqrt r+sigma*w))` 和 `exp(-ivr)`，两符号分别被实例化，未丢反射、半因子或相位。

   奇系数为 `-I/((2*pi)^2*y²)`，偶系数为 `((2*pi)^2*y²)^(-1)`，与原来源反演和两次分部积分一致。由 `1≤(2*pi)^2` 得系数范数 `≤1/y²`。`exp(ivq)` 的范数严格为1；`short_marked_norm_integral` 把该一次 `y^-2` 等同于已含该因子的区域范数积分，因而没有重复乘 `y^-2`。两符号相加得到 `2K/y²` 点态包络，实际可微性从同一真实核接口直接取得。

5. **实际时间网格与最终任意逐项选取，LF511–514、555–567、630–653。** 读取并核对已经独审 `CORRECT` 的 `SourceShortTimeGrid` 完整消费接口；精确 `m2/y² * sum R(T_i)≤Cg` 作用于上述真实条件律、真实 `T_i` 和相同 `J`。对每个指标的空间点单独应用统一包络后，有限和单调性给出奇界 `2K*Cg*(n|mu|+n*m3)` 和偶界 `2K*Cg`。`C=2K*Cg>0` 在所有数据之前选定。空和无需特殊非空前提；证明没有以任意权重替换真实 `m2` 网格。

## 旧证据与实际接口复用

以下精确源/对象哈希均在本次服务器只读检查中匹配其合格独审记录；完整读取本消费者使用的声明或定义，不重审或重跑旧证明。

| 模块 | 源 SHA256 | 对象 SHA256 | 复用审查 |
| --- | --- | --- | --- |
| `SourceOddEvenMarkedIBP` | `37cbf000078f4b60e383a0b736df9c718810a55b983f7c2d7288fba3bb15a414` | `814d8a4a7fec3af1e42a586daf9fa31de6a4757f9307cd17bcf53148bc51e452` | `common-marked-pair-ibp-review.json` |
| `QuadraticFullNoiseMarkedLowRegions` | `366e8729e1a11cdf13c23108214ad1266d6799641668c68a909ea1a3f8379461` | `d7e2ec9093379ae0ac8929758847f1ef299faaf439ff2e7b8b12ec8e07326951` | `common-marked-low-regions-review.json` |
| `QuadraticFullNoiseMarkedOutside` | `1a876e82b81195320278d8e8274374bbd9de293da7e1e6e58fb345e1e8f9ec48` | `b1102c4dbbd7d04d9a22c48770c2fa73c9636fbb0fd50c66f5cf82863c727a95` | `common-region35-review.json` |
| `QuadraticFullNoiseMarkedRegionFour` | `b921940ad68c9b35125b29a81d543e6c1d999a0d06b10b9f90ca6e68f538d58f` | `1ef36c40d6b61aea8460c2a8a121c172ea3141c05c7bdaff78189a9d4ad923a8` | `common-region4-marked-review.json` |
| `SourceShortTimeGrid` | `39484ec8a491ed78070731e94e9ad01a1b5018df46058b693b3d801dfa67fb69` | `a3d3b6e102fb70964f61c340d125c57f205661166004644a589b0e3fa6a761ef` | `common-short-time-grid-review.json` |
| `SourceFourierScale` | `5f31eb92eff8ded33b91f55a59a16de4e58cdd7a9e0514d082a2c4932f5feff0` | `181f3e96c2cde028a900a0d7c167ca7e521e1a19b28ac97427b9530e6433ab8b` | 已接受精确生产者映射 |
| `SourceTruncationBridge` | `05321c22d1b2ea178fbc116178af345f4186bfce51011c8242b4ccfd2e0dd7d1` | `3a23c563b69b9316b50d14f3b008ad26575d4c547602f4abd13e9c1718295c7a` | 已接受精确生产者映射 |

网格旧收据原组合 shell 未单列 Lean 退出码的边界已由其独审及 `coordination/integration-v51/short-grid-original-execution-supplement.json` 明示；本轮复用其完整现物充分性结论，没有重新开启该旧检查。

## 服务器内核与全部所属公理证据

固定工具链 `leanprover/lean4:v4.36.0-rc1`、mathlib `807d3836b165983210ee2ecf3cd28f239436949c` 在实际工作树中只读核对一致。原作者两个命令均在 CPU10–13、公共 `root-heavy.lock` 下，使用 `-M8192 -j4 -DautoImplicit=false`。本轮只读现物，不增加重型进程。

`drafts/c12-short-kernel/check-07-request.json` 的原命令对目标源编译并生成上述对象。关键是其内层 shell 在 Lean 命令之后立即执行 `short_rc=$?`，随后输出完整日志，最后 `exit $short_rc`；对应原始 `check-07-result.json` 退出码0准确传播 Lean 的直接退出码。原始 stdout 去掉首行源哈希后的5906字节，SHA256 正是当前完整 `check-07.log` 的 `0b89484e1c45cf34ffe343964976bcbc7a11f757d3fad762c6681212968dff00`。完整日志仅有样式、弃用和旧 mathlib 本地变更警告，无错误。不是仅凭组合 shell 的末条输出成功推测内核成功。

`owned-audit-request.json` 同样在 Lean 后立即保存 `$?`，再输出日志末四行，最后传播保存值；原始结果0因而同样为实际审计 Lean 的直接退出状态。执行过的 `outputs/common-short-kernel-v51/OwnedAudit.lean` 哈希为 `1be63ad58a6e13583557c4e4115bf5208d12ad607b1ccfef14d3748470b79782`，与当地审计源一致。脚本按 `env.getModuleIdxFor?` 的实际模块索引选取每个所属常量，对每个分别执行 `Lean.collectAxioms` 并拒绝非白名单公理；不是按名字前缀筛选，也不只检查公开定理。

当前完整导出 `actual-owned-types-values-axioms.log` 为205968字节/2466行，SHA256 `62f3ef57f84b0cb3950360c2292259257914729e17c2364cbe5263b9d1909609`；实际 `owned-audit.json` 的 SHA256 为 `9ee16c440f06899b80f3437c1920bcc6e98da9542162541217447a3d132e6869`。审查者逐记录完整读取 34 个 `ACTUAL_TYPE` 和6个 `DEFINITION_VALUE`，其中包括长公开展开类型、长私有范数界类型、全部生成的集合/结合律/有限和包装及定义方程；导出无省略号。实际映射恰为28个 theorem、6个 definition，无 other；一项公开手写定理、零公开定义。

所有34项的递归公理集合均在 `propext,Classical.choice,Quot.sound` 内；集合恒等式生成项仅需 `propext`，纯结合律项无公理，求和分配项和数值生成项的实际集合也逐项记录在 JSON 中。没有把私有或生成项排除在审查外。原失败历史保持原样；本轮未重跑任何已通过检查。

首次共享连接的两个快速复合只读命令输出不完整，未被用作证据；随后单一 Python 只读命令完整返回所需现物哈希和原导出分段。一次原生 SSH 只读备用尝试无有效输出，未用于判断；最终只读检查确认该尝试无在途进程。这不影响原作者直接退出码的独立保存与完整原日志绑定。

CRITICAL GAPS: **无**。REQUIRED FIXES: **无**。

接受范围仅为上述精确版本、真实条件律和来源范围内的 realkernel(iii) 短时间奇一阶/偶嵌套二阶导数求和。regulator 概率期望、局部 Taylor 消费、early/long、large-y、desmoothing、原概率定理、C1/C2 及其他根组仍按现有台账 OPEN；本审查不评定或声称新颖性。审查完成，作者源保持冻结，本审查名额释放，不自行启动下一任务。
