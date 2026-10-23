# 实际短时间核局部位移的独立完整最终审查

STATUS: **CORRECT**

审查者 `/root/common_local_shift_review`，fresh `gpt-6.1-sol` / `xhigh`；作者 `/root/common_local_shift_author`。审查者从未编写或修改本单元的数学陈述、假设、定义或证明。本轮仅写本报告及同名 JSON；使用 `math-theorem`，未使用 `math-ultra`，未运行 Lean，未修改生产者、冻结源、旧报告、缓存、原日志或收据。

结论精确绑定提交 `2da0aba7f23b43b901f7d229b714c8a14adf1e56` 的新单文件 `Shao/Probability/SourceShortTimeKernelTaylor.lean`。完整读取全部 273 行源及证明、服务器实际所属的全部 4 个声明的完整展开类型与每项递归公理集合。实际映射为 4 个 theorem（3 个 private helper、1 个 public theorem），0 个定义，0 个额外生成声明。唯一公开定理为 `sourceTruncation_futureNoise_short_kernel_local_shift_budgets`。同名 JSON 记录逐 owner 类型哈希、字节数、行数、公理和审查结论。

## 冻结、字节与来源

| 绑定物 | SHA256 |
| --- | --- |
| 当地 work.lean、服务器生产源及冻结提交 blob | `f20c740beab74f76924ba4bed214817c98ceacee04389c9b5388aa0d999af012` |
| 实际 .olean | `ca63d1db6238362c8edee0a1e1c469fbd232b60f0b23798f8c3c28eaba18b065` |
| 实际 .ilean | `924efc883591d36a0118cb547dbceca53bb7d11c0306541b47cac29e01193ce2` |
| 作者最终 author-receipt.json | `c4d7d3897117f2e4fd6d8042a5bd9cd12fe1fb0ac75926f54d54e1355b4232c1` |
| 根完整声明冻结 | `6eb857bae7be7df5a6fcfcea9a5ac06b7fbe56524ec5275b1eba89304bb38ca5` |
| 完整候选声明 | `5cc51739ac7dd873702fcb43a5795abf1f54d499e6b26899901ddc7ebae14349` |
| 完整来源合同 | `ce4a386cc4b7da884f7f794375c9c739d8fef4b783c60a5eaf85f469a530fea2` |

公开陈述与候选、根冻结中的完整字面陈述在仅规范空白后相等；无假设、量词、索引或数学结论的变更。源文件13544字节、严格 UTF-8、无 BOM、LF、零 CR；禁止构造扫描无 `sorry/admit/axiom/unsafe/native_decide`。当前服务器 `workspaces/common-short-kernel-v51` 的 HEAD 为上述提交、工作树干净；父提交为已独审短核生产者 `9c258ccccfae5fe3e34110dde0822325401f8174`，本提交仅新增这一文件。作者最终收据明确 writer_released=true、heavy_in_flight=false；本审查无源写入或重型命令。

完整读取只读 `C:/game/shao/current/c12/supplement.tex` 的 LF590–650、690–710 中本单元所用定义、局部 Taylor 不等式、短核预算和后续局部事件上下文；其 SHA256 为 `b99f2ac4d2f39dd39772d98a5702b7a923c2f10f8730a08fc1b4cd6bba4742bd`。LF604–618 正是实际奇偶分解与局部位移；LF642–649 给出同一短时间索引和空间一致的加权导数预算；LF694–709 解释后续实际 regulator 的局部消费，本单元不声称已经完成该概率期望步骤。

## 来源到实际陈述

源 LF143–179 与完整实际展开类型保留了绝对 `C,epsilon0,L2` 先于所有原始概率律的次序，全部原始归一化、均值、二阶可积、截断预算和 `gamma≤y≤2` 前提。真实条件律为 `cond ν0 {|a|≤epsilon/(1+x)}`；`mu,m2,m3,gamma` 及 `T_i=(n-i)m2` 未被替换。条件律没有被假定中心或对称。

完整读取已合格生产者 `sourceTruncation_futureNoise_short_kernel_sums` 的全部消费接口：相同的原前提、真实条件律、实际 f/o/e、相同的 max-guard J、闭局部范围上的 o/e/e' 可微性，以及任意逐指标 `q,w : ℕ→ℝ` 的两条实际导数加权和。复用 `coordination/common-short-kernel-review.md/.json` 的完整独审 CORRECT，不重审其旧证明。其源 `842e13b2b1a59fa4673b6f938d3a58ba986116fdb0ba3fd72745cef1614da06d` 与对象 `77a708f2f094ccb6ceecc4dcfb110789720f0db298e710205c28969f0c3118f9` 在本轮服务器只读现物检查中精确匹配；旧审查 MD 哈希为 `87f10686b5dfa706386a556b9d5b7e2cb119a4d756807a88c6b86e2bb3efbd6c`。

完整读取实际 `sourceFutureNoiseKernel` 定义：真实未来增量产品律与 `quadraticFullNoiseLaw` 的双积分，测试函数坐标为 `(p.1+prefixSum+z.1,p.2+energy+z.2)`。因此 `f i q w` 确实把 w 放在第一坐标、q 放在第二坐标；o/e 正是在第一坐标反射。完整读取 `sourceTruncation_variance_bounds` 与 `sourceTruncation_gamma_bounds` 的消费陈述；当地接口源与服务器现物哈希相等，前二者的源/对象同时符合已接受生产者记录。

`J=range(n+1)` 内的 `n/2<i ∧ L2*gamma²≤T_i<max(L2*gamma²,y²)` 原样保留。自然数半程除法对整数指标等价于原严格半程条件；没有新增 J 非空假设或删除 i=n 端点。由 gamma>0、L2≥16384 及 T_n=0，本来就没有 i=n 的局部义务。若 J 为空，所有预算和为空和，helper 仍给出全域非负且外 J 为零的 O/E。

关键量词次序忠实：O/E 在参数和 y 之后、所有后续 q/w/u 之前选取；每个实际导数的全 q、闭 `|w|≤y/16` 上界和真实 m2 加权和都是结论。没有 supplied derivative envelope，没有把任意逐指标空间点弱化成共同空间点，也没有用确定性 regulator cap 代替真实一、二阶矩。

## 全证明核对

1. **有限统一预算，LF13–73。** 对每个 i∈J，真实值集 `S={F_i(q,w): |w|≤cap}` 在 `(q,w)=(0,0)` 非空。全域 `F≥0`、m2>0 和原任意联合选择和式给出逐项 `F_i(q,w)≤B/a`，故实上确界有界。对正上确界，存在真实空间点的值大于其一半，于是所有值≤该选点值的2倍；零上确界情形用 `(0,0)`、上确界非负及 F≥0 直接支付。外 J 取零预算。

   `choose p` 得到真正逐指标 p_i；应用原 hsum 时使用 `q_i=(p_i).1,w_i=(p_i).2`，而非强迫所有 i 取相同点。逐项 O_i=2F_i(p_i)，有限和严格等于2倍选点值之和，因此加权总预算≤2B。这里没有交换 sup 与 sum；有界性的共同点测试仅用于单项有界性，不冒充最终近最大联合测试。J 为空时 hsum 本身给出0≤B，最终预算仍成立。奇、偶家族分别选择，合法共享最终绝对常数2K。

2. **真实偶函数导数为零，LF75–84。** `g(-t)=g(t)` 是函数恒等式；实际 DifferentiableAt g 0 给出 g(-t) 在0的导数 `-g'(0)`。与同一函数的导数唯一性得到 `-g'(0)=g'(0)`，所以 g'(0)=0。未从“deriv总化值为0”误推可微。

3. **真正闭区间二阶余项，LF88–141。** u=0 单独化简。u≥0 保证0、u都在 Icc 0 u；hdd 与真实二阶导数绝对值界，通过凸区间均值估计得到 `|g'(t)|≤E*t`。随后构造 `E*t²/2−(g(t)−g(0))` 与 `E*t²/2+(g(t)−g(0))`，实际导数分别为 `E*t−g'(t)` 与 `E*t+g'(t)`，均非负。hd 给出闭区间上连续性和内点可微性；单调性比较0与u得到两侧二次界，恰为 `|g(u)−g(0)|≤u²*E/2`。

   本轮只读核对所用 Mathlib 精确接口：`norm_image_sub_le_of_norm_deriv_le` 要求凸集上逐点实际可微和导数范数界；`monotoneOn_of_deriv_nonneg` 要求闭域上连续、内部可微和非负导数。所有条件确实逐项支付。没有假定二阶导数连续、没有把系数放宽成1，也没有除以u。

4. **实际核实例化与常数，LF181–228。** 从生产者取 K>0，最终 C=2K，epsilon0/L2 完全继承。epsilon≤epsilon0≤1/2 支付桥接口；`V=m2−mu²>0` 严格推出 m2>0；实际 gamma>0 与 gamma≤y 给出 y>0，从而 cap=y/16≥0。两个 helper 分别作用于 `|deriv(o_i(q)) w|` 和 `|deriv(fun r=>deriv(e_i(q)) r) w|`，均使用生产者真实任意逐指标选择和式；没有输入新的预算假设。

5. **实际局部位移，LF229–271。** 对0≤u≤y/16，区间每个 t 均满足闭 `|t|≤y/16`，所以生产者 o/e/e' 三项可微性适用到端点。o(0)=0、e(-t)=e(t) 由真实定义展开，e'(0)=0 用上述 helper 与实际可微性得到。均值界给 `|o(u)|≤u O_i`，二次 helper 给 `|e(u)−e(0)|≤u² E_i/2`。实际代数恒等式 `f(0)−f(-u)=e(0)−e(u)+o(u)` 与三角不等式得到冻结结论。u=0 在最终实例化也明确化简，闭上端点 u=y/16 原样覆盖。最后真实 m2 加权和分别为 `≤2K*(n|mu|+nm3)` 和 `≤2K`，与唯一最终 C 一致。

## 实际所属与服务器证据

| 实际 owner 后缀 | 类型完整读取 | 类型字节/行 | 递归公理 |
| --- | --- | --- | --- |
| private even_deriv_zero | 是 | 2197 / 35 | 三项白名单 |
| private finite_uniform_budgets | 是 | 2261 / 36 | 三项白名单 |
| public sourceTruncation_futureNoise_short_kernel_local_shift_budgets | 是 | 43224 / 482 | 三项白名单 |
| private local_quadratic_remainder | 是 | 7733 / 131 | 三项白名单 |

计数由实际 `env.getModuleIdxFor?` 选取映射与完整导出交叉验证；不以名字前缀或源关键词代替。实际 `owned-audit.lean` 与当地审计源 SHA256 同为 `7a7759b0d6b6b13105402a6f1f16a05236da83abc9fffd28359aaa73e65ec903`。该脚本对每个所属常量分别执行 `Lean.collectAxioms` 并拒绝非白名单项。全部4项均仅依赖 `propext,Classical.choice,Quot.sound`；无遗漏 private/generated，实际没有需读取值的 definition。完整类型日志无省略号；读取私有类型时仅折叠展示空白，公开类型完整分段读取，没有删节数学内容。

原始 `check-02-request.json` 中 Lean 命令结束后立即保存 `shift_rc=$?`，随后输出完整日志，最后 `exit $shift_rc`；原始结果直接退出码0正确传播实际 Lean 状态。`owned-audit-request.json` 同样立即保存 Lean 的退出码，再输出末6行并传播原值；其原始结果直接退出码0。二者均使用 CPU10–13、公共 root-heavy.lock、`-M8192 -j4 -DautoImplicit=false`。本轮从未重新编译或重新执行公理审计。

当前完整 kernel 日志943字节，SHA256 `9db669dced6fc6ac1d224d304e1e426d1d638f9dab9fd1fa95a34e6e5637368b`；原始结果 stdout 去掉首行源哈希后与该日志字节完全同哈希。日志仅有弃用/样式及既有 mathlib 本地变更提示，无错误。完整 actual-owned 日志99833字节/1186行，SHA256 `966f71113b7d29f5e6c51b5e1568005974eeb531736b7d941baa60bbaafc0af9`；owned-audit.json SHA256 `fe4398cc65f89fe91c6a90d4f40cbd68ef989a377237a30850a8a7893d1ae794`。审计原结果的末6行与当前完整日志对应后缀精确匹配。

当前 lean-toolchain 文件为 `leanprover/lean4:v4.36.0-rc1`，Mathlib HEAD 为 `807d3836b165983210ee2ecf3cd28f239436949c`。服务器源、冻结 commit blob、实际对象、完整日志和审计脚本均逐一只读校验。所有读取均经共享 `tools/transport_client.py` 的 send_request；完整原日志留在服务器。原失败 check01 历史保持原样，不把其结果用于认证；未重放任何旧成功检查。

CRITICAL GAPS: **无**。REQUIRED FIXES: **无**。

接受范围仅为该精确 actual-short-Taylor 单元：真实短时间核的确定性、空间一致奇一阶/偶二阶导数预算及闭局部位移不等式。真实 regulator 二阶矩、局部修正概率期望组装、survival 生产者、大位移、微小时钟、large-y、desmoothing、C1/C2 与其他原始根组仍 OPEN；不声称论文新颖性或原概率根定理闭合。审查完成，无命令在途，仅两份审查报告写入；审查槽释放，不自行启动下一单元。
