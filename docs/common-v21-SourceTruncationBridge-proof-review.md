# SourceTruncationBridge 独立完整证明审查

STATUS: CORRECT

SCOPE: 固定源码的全部八个公开定理、六个私有辅助、源语义与冻结声明忠实性。

FORMAL COVERAGE: LEAN_FULLY_CHECKED（仅此冻结八条标量桥；作者实际执行，独立源码/证明裁决）。

本报告不是独立 Lean 执行回执。先完成下述完整数学判断，再读取、校验最终作者服务器目标/对象及全模块公理回执，全部绑定同一源码；本审查不重复已成功目标。未运行本机或服务器 Lean，未使用服务器传输，未改证明、前提、原稿、共享实现、缓存或他人文件；只写本报告。作者与本 reviewer 分离，无子实例。

## 精确冻结与实际读取

| 对象 | SHA256 |
|---|---|
| 所审 `drafts/c12/SourceTruncationBridge.lean`，705 行 | `05321c22d1b2ea178fbc116178af345f4186bfce51011c8242b4ccfd2e0dd7d1` |
| 冻结 `SourceTruncationBridge-next-scope.md` | `43c846bcb05d87b9cc4a9e38c28e905286724bc846477118adc12ddbd49d24c5` |
| 既有独立声明审查 | `5c83ba8c76cf4cc8fa69acc0291570fcc41fa4c7a58be00d8e26d9040cfda0f9` |
| 原 `C:/game/shao/current/c12/main.tex` | `beb00f718487e36de433175c97f1d500cb48e7a92ce5bd5ad5d62bb132122d06` |
| 原 `C:/game/shao/current/c12/supplement.tex` | `b99f2ac4d2f39dd39772d98a5702b7a923c2f10f8730a08fc1b4cd6bba4742bd` |

以上均为本轮实际本地字节哈希。完整读取最终实现 1–705 行；将八个实际公开完整签名从 theorem 至 proof 分界提取，与 scope 的八个 Lean 代码块逐一空白归一化比较：**8/8 完全一致，公开名字集合相同，零新增定义，六个私有 theorem**。无需以作者的签名断言代替这一检查。原源码全文直接扫描 `sorry/admit/axiom/unsafe/native_decide` 无任何 token 匹配，故没有依赖可能误删字符串/注释的扫描器获得该结论。

已实际核对原 main:355–435、546–551、622–640 与 supplement:522–533、2045–2135、3078–3099、3117–3126。读取并复用既有已接受依赖的定义和所调用完整类型，未重证旧模块。实际本地依赖字节为：

| 依赖 | SHA256 |
|---|---|
| TruncationIntegrals | `d7432b7c579c6e6e0d9980af322437941f59f8f670bebd2dd4770f6cfcf1e234` |
| TruncationSampleSize | `017a62c7f2e9e8ed43259d28d145e67b7010152a0c233d671680fcc5a01635de` |
| RetainedMoments | `512cf7a51125f18f94f42b4ef855e21290a28f7a3185865a3d375bde8100d6cb` |
| RetainedSample | `a507e549e2973dd04ce25f22e2c6973e0e6c491433a1d7fd2d88fbb082e86ca4` |
| RetainedVariance | `5361ad40f82d6c273135729df66c056d01a9cf090d1e9f80cffce44f61296fa6` |
| GaussianTail | `f166fab0061199e25d0391bbde5c977905e368513a6e0e18b492877c65160922` |

## 实际命题、量词和源对应

记 a=1+x、b=a/ε、h=ε/a、B={z:|z|≤h}、ρ=cond ν B、R=n∫F(az)dν、H=n∫F(bz)dν，F(w)=w²min(|w|,1)。N 表示真实 normalization n∫z²dν=1，M 表示原律均值 ∫z dν=0。所有 n 都是自然数，涉及实乘法时显式转实；ρ 始终固定在 x。

| 实际公开定理及实现行 | 保全的前提与实际结论 |
|---|---|
| sourceTruncation_reparameterization，17–51 | 一般 measure、平方可积、x≥0、0<ε≤1；1/b=h、闭集合相等、两个真实 cond measure 相等、H=R_n(b−1)、R/ε²≤H≤R/ε³。不要求概率、N、M 或 B 正质量。 |
| sourceTruncation_sample_size，70–129 | ν 概率、平方可积、N、x≥0、0<ε≤1/2、R≤ε³/8；推出 b≥2、b⁶≤n、Nat n≥64、H≤1/8。n>0 与 R>0 均为内部推论。 |
| sourceTruncation_tail_budget，131–205 | ν 概率、平方可积、x≥0、0<ε≤1；严格尾 Bᶜ={h<|z|} 的质量、绝对一矩、二矩预算分别为 R/ε³、R/(ε²a)、R/(εa²)。不要求 N、M 或小预算。 |
| sourceTruncation_law_data，207–260 | 与 sample_size 同一前提；3/4≤ν.real B≤1，真实 ρ 是概率、支持于 B，id、平方、绝对三次与四次在 ρ 下真正可积。 |
| sourceTruncation_paid_moments，370–445 | 再加原 M；n|μ|≤2R/(ε²a)、nm3≤2R/a³、nm4≤h·nm3，真实中心绝对三矩可积且≤8m3。μ 是真实条件均值，未置零。 |
| sourceTruncation_variance_bounds，447–535 | 同一 N/M、小预算与 ε≤1/2；3/4≤nm2≤4/3、nμ²≤1/4、真实 V=variance id ρ=m2−μ²=Eρ(z−μ)²、V>0、1/2≤nV≤4/3。 |
| sourceTruncation_nearby_payment，580–640 | 再量化任意 y≥0、|y−x|≤1/a；同一固定 ρ 下 (1+y)h≤2ε、(1+y)³nm3≤16R、真实 Λ≤20R/ε²，并给 Λ·Tail(y)≤20exp(2)R·Tail(x)/ε²。Tail 是既有真实 standardNormalTail。 |
| sourceTruncation_clock_inputs，642–703 | ν 概率、平方可积、N、x≥0、0<ε≤1/8、R≤ε³/8 与同一 y 邻域；给 (1+y)h≤1、8(1+y)²h²≤1、[8(1+y)²]²nm4≤1/2。刻意不要求 M；没有 clock probability 结论。 |

实际源 main:425–430 的 h_x 与条件化、546–551 的同一增量条件 law、622–625 的 μ/m_r/τ²/Λ 定义均被忠实保留。源 supplement:525–526 的原点矩、漂移与真实方差，以及530–531 的 Λ 预算是这里的主要标量目标。不存在用无条件律、条件于 y 的律或后续 tilted law 代替当前 ρ 的变化。

main:373–382 的 ε=min{ε0/2,1/[4(K+1)L]}、L≥1600、K=8(1+L) 确给 ε>0、ε≤1/2，并由第二分支给 ε≤1/8；D3 的 R<η(ε) 确给 R<ε³/8。这里 theorem 使用弱 ≤ 合法。最后一条的 ε≤1/8 有源参数依据，未从 ε≤1/2 错推。源 main:639 的邻域 1/(2a) 更小，可以供给当前 1/a 输入。上述源参数实例化的正式 Lean theorem 不在本文件内，不能把文本蕴含审查记为已形式证明整个 D3 实例。

## 完整证明与六个私有辅助

**换参与正性，17–129。** 1+x>0、ε>0 后反演 b，两个集合逐点相等。H 的参数是 b−1，故 1+(b−1)=b；取 c=1/ε≥1 复用实际双向 scaling，得到 ε⁻² 与 ε⁻³，未将 H 误当 R。私有 st_positive_data（53–68）先用 N 排除 n=0，推出真实原二矩>0，再用已接受预算正性得 R>0。

关键样本量证明使用旧 theorem 的实际**中间项** (1−R)³a⁶/R²≤n。ε≤1/2 与小预算给 0<R≤1/64、R²≤ε⁶/64、(1−R)³≥1/64，故 R²≤ε⁶(1−R)³。105–118 行只有在 R²>0、ε⁶>0 后作除法，推出 b⁶=a⁶/ε⁶≤n；b≥2 再得 n≥64。没有仅凭较弱 a⁶≤n 就付掉 ε⁻⁶ 的跳步。H≤R/ε³≤1/8 由真实 scaling 消去小预算。

**严格尾与真实条件概率，131–260。** B 闭、Bᶜ严格，因此 cutoff 处原子全部保留。质量先被识别为真实可积 indicator-one 的积分，再逐点以 F(bz) 控制；旧 tail-one/tail-two 在真实正 b 下给 b 与 b² 因子，结合 H≤R/ε³ 严格化出所需分母 ε²a 与 εa²。F、标记一/二矩、indicator-one 均有概率/L2 的真实 integrability 依据，未用默认零积分。

law_data 没有直接假设 conditioning mass。n≥64、H≤1/8≤1 满足旧 retainedCutoffMass_bounds 的 n≥2、b>0、h2、cut-budget 条件，得 p≥1−1/n≥3/4、p≤1。因此 p>0 后才能安装真实 retained law 的概率与支持。id/二矩/绝对三矩直接运输旧真实 retained API；新四矩由 |z|≤1/b 下 |z⁴|≤(1/b)⁴ 与有限概率常数支配得到。原 ν 不需要三矩或四矩。

**带 R 的 raw 支付，私有 st_raw_paid（262–352）。** ε≤1 给 1/b≤1/a；两个 marked cube 确实都从原 L2 获得可积性，较小闭 cutoff 的积分≤旧 cutoff 积分≤a⁻³∫F(az)。320–323 行先将真实 |z|³ 在 ν.restrict B 下的 integrability 从 marked cube 转出，再应用真实条件积分除 p 公式。p≥3/4 使 1/p≤2，保留 nm3≤2R/a³；没有把 H≤1 的粗界当作这一精确支付。h4 与 h3 都已真可积后，逐点 z⁴=|z|·|z|³≤h|z|³ 再积分，给 nm4≤h·nm3。本 helper 无 M，故最终 clock 输入没有偷偷引入原均值零。

**漂移与 centered cube，354–445。** st_integrable_id（354–360）由 |z|≤1+z² 与概率/L2 得原 id 真可积；st_compl_integral（362–368）只是可测闭 B 补集的真实 indicator 表达等式，不宣称任意 f 可积。paid_moments 随后在原 id 真可积条件下分割 B/Bᶜ，使用原 M 得 ∫_Bz=−∫_(Bᶜ)z。取范数、严格尾绝对一矩预算，再以 p>0 的条件积分公式除 p≤放大2，得到实际条件漂移。没有从原均值零直接断言 μ=0。最后复用已接受 retainedCutoffLaw_centered_moments 的真实 centered-cube integrability 与 ≤8raw-cube 条款，所投影 conjunct 与实际旧声明一致。

**真正方差，447–535。** b≥2、n≥64、H≤1 满足旧二矩 theorem，给 nm2≥1−1/b²≥3/4、nm2≤1+2/n≤4/3。用 paid drift 与 R≤ε³/8、a≥1、ε≤1/2 得 n|μ|≤1/8；504–509 行先平方后以 n≥1 单调控制，实际得更强 nμ²≤1/64，再弱化为冻结1/4。真实 ρ 概率与平方可积建立 MemLp id 2 ρ，才能调用 variance_eq_sub；旧 centered-moment identity 明确把同一 V 连到 Eρ(z−μ)²。随后真实 raw 下界减漂移平方得 nV≥1/2，n≥0 排除 V≤0。方差正性、μ=0、raw m2=V 都没有被当作输入。

**邻域与高斯支付，私有 st_nearby_ratio（537–542）、st_nearby_raw（544–578）及580–640。** x,y≥0 与 |y−x|≤1/a 给 c=1+y≥0、c≤2a。只乘非负因子，把 raw cube 支付放大为 c³nm3≤16R、ch≤2ε。原漂移同样得到 cn|μ|≤4R/ε²，ε²≤1 与 R≥0 给 Λ≤20R/ε²。最后使用真实 standardNormalTail_local_comparison 的上侧 Tail(y)≤exp(2)Tail(x)，乘法中分别供应真实 Tail(y)≥0 与20R/ε²≥0；并非从一般比较函数或未证样本正态近似推得。ρ 始终由 x 定义，未随 y 改律。

**Clock 常数，642–703。** 同一无 M 的 raw helpers 提供 ch≤2ε、c³nm3≤16R、nm4≤h·nm3。c,h,ε 与原三矩都非负，故乘界合法，逐项得到

    [8c²]² nm4 ≤64(ch)(c³nm3) ≤2048εR
                 ≤256ε⁴ ≤1/16 ≤1/2。

同时 8c²h²≤32ε²≤1/2≤1、ch≤2ε≤1。这里 ε≤1/8 足以供数值，未误用仅 ε≤1/2 的范围；也没有丢掉原 R 小因子。结论仅是标量数值，不需要、也没有构造样本 iid 或 clock event。

## 边界、剩余认证与范围

- x=0 时 a=1，无奇点。ε=1 只在第1/3条出现；ε=1/2 与 ε=1/8 的允许端点均为弱不等式，证明覆盖。所有除数均有真实正性。
- 第1/3条允许 n=0、R=0；未除 n 或 R。含 N 的条款先排除 n=0，预算 R=0 随正性不可能；样本量和 variance 不是 totalized division/integral 的产物。
- 一般 measure 的第1条只证明真实 cond 等式，不承诺零质量/无穷质量条件化为概率；第4条以后均先证明概率质量有限且≥3/4。|z|=h 的原子完整保留；原 ν 可无全局高矩。
- M 只在漂移、正 Var 和 Λ 的公开命题中出现。最后 Clock 数值使用 raw 三/四矩，不暗加 M；它没有提升到 y≥0 全域的 clock probability theorem，后者还需 y≥2、真实 iid law/支持及事件接口。
- 未证明条件化后整条样本 iid、γ比较（γ≤2h、m2≤γ²、nm3≤2r_n等）、后续平方/指数倾斜的矩搬运、频域比较、noise/smoothing/desmoothing、严格 CDF 或完整 C1/C2 根。原条件矩 lemma 的这些其它部分仍须单列，不因本八条通过而关闭。

## 数学判断后的实际作者回执绑定

完成上述独立数学审查后，实际读取 `drafts/c12/SourceTruncationBridge-author-receipt.md`，SHA256 为 `51960c445b01182add0e716d2b992a48d00b59417f3df36e33be1d0bc5670cbb`，与协调者及作者通知完全一致。再次实际复核实现05321c22…与scope43c846bc…，均未改变。未读取作者推理 notes 作为数学判断依据，也未复跑已成功目标。

回执绑定隔离 server worktree `workspaces/takeover-source-bridge`，v18 baseline `c7f54caf9d43d6ee149c9d11aa0cb88d552d0b1b`，源码单文件作者 commit `d472d38f39f7a68025a9409a47c2a11a55e0e8c1`，并记录：

- 精确目标无-o检查 exit0、无诊断；随后为审计唯一生成目标 olean 的检查同样 exit0、无诊断。两个实际日志均为空，SHA256 `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`。
- 模块审计实际 exit0；审计 script SHA256 `199d27503e1627d748fd82a00ac93124745445edad5ababd174deb27b625145f`，日志 SHA256 `3435a64a8ade6e2205150d15e4f1e6ee74d1cca6421f3e555c78c3c153221352`。按 exact defining module `Shao.Probability.SourceTruncationBridge` 选全部常量，逐项 collectAxioms；42/42 项均仅使用标准白名单，包含8公开、6手写私有、28生成证明。另核对8个目标存在、theorem种类及模块归属，并输出实际 elaborated types。
- 作者的8/8完整签名比对与本 reviewer 独立本地提取比对相符；零定义。版本为 Lean `4.36.0-rc1`/commit `c9afcddf514a6772bd4d649f7cfc04eff0b9f15e`、Lake `5.0.0-src+c9afcdd`、Mathlib `807d3836b165983210ee2ecf3cd28f239436949c`；所有 Lean 在指定服务器、激活后重新进入正确 worktree，单进程、4核限额，未写共享包缓存。

这里的执行事实来自已实际读取并哈希绑定的作者回执；审计 driver、elaborated types及完整原始日志留在服务器 `.author-source-bridge/`，本 reviewer 未独立拉取它们。源码与数学审查是独立完成，执行身份和证据级别没有混淆。

最终裁决为 **CORRECT，GAPS: None**。同一固定哈希八条完整证明、全部声明和源标量范围可以接受，不需修改前提；结合作者实际目标/对象/42项传递公理门，形式覆盖仅为本冻结模块。根协调者仍须把这份源哈希、作者回执和独立报告接入公共 imports/manifest 与集成树审计后落库；完整 C1/C2、clock probability、频域/平滑/最终尾比较等剩余目标不随本模块提升。
