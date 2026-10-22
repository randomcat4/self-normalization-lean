# Xi 导数节点的来源与 API 对应 v2

状态：只读研究完成；声明待独立审查及 root 冻结；没有 Lean 运行。

## 版本与文件身份

- root 指定基线：v39 accepted `59a531b89eff7c11e4fc53583067f2cd3b53a517`；v39 main `67df1c9775f519d34260a14b78f120485539eba3`。
- v40 已合入通知：accepted dc1604d8e9c88781166a0c797f45b84ff013673a、main 5591a25ddc767e6edfd618a88855075c2af7e375；公共 Probability 源不变，沿用已核 SHA256，不追加 API 或缓存研究。
- Lean 钉死版本：`leanprover/lean4:v4.36.0-rc1`；Mathlib `807d3836b165983210ee2ecf3cd28f239436949c`，来自 `SERVER.md`；本地 curated `lean-toolchain` 内容一致。
- `library/Shao/Probability/QuadraticFullNoise.lean` SHA256 `a280ff36549f2c59356fd4fa89b3e442eece91f2a0e3bb4eea553d3605e1a116`。
- `C:/game/shao/current/c12/supplement.tex` SHA256 `b99f2ac4d2f39dd39772d98a5702b7a923c2f10f8730a08fc1b4cd6bba4742bd`。
- `C:/game/shao/current/c12/main.tex` SHA256 `beb00f718487e36de433175c97f1d500cb48e7a92ce5bd5ad5d62bb132122d06`。
- TeX 行号以文件按 LF 分割计算；未按显示的 CR 字符或文本换行重新编号。未改 source/history。

## 原文到声明

| 原始来源 | 原文语义 | 拟形式接口 | 归属 |
|---|---|---|---|
| main LF660–666，`h:eq:fullnoise` | 两个 Fin8 弦族和实际独立标量构成 Z、Y | 既有 `quadraticFullNoiseMap`、`quadraticFullNoiseLaw` | 已接受构造，不在本轮重写 |
| main LF672–679，`h:eq:charfunctions` | `Xi(u,v) = E exp(iuZ+ivY)` | 既有 `quadraticFullNoiseChar ν u v` | 实际特征积分对象 |
| supplement LF486–498，`h:lem:noisemoments` | 实际支撑、`E|Z| ≤ 67/3 gamma`、`EZ² ≤ 70/3 h gamma` | 既有 `quadraticFullNoise_support_moments` | 已接受前置定理，不作输入假设 |
| supplement LF2595–2605，`h:supp:highderivatives(b)` | 全实平面 `|Xi_u| ≤ C gamma`、`|Xi_uu| ≤ C h gamma` | 第二公开定理的两个范数界合取项，分别采用常数 `67/3`、`70/3` | 本节点的源结论 |
| supplement LF3355 | `|Xi_u| ≤ E|Z|`，`|Xi_uu| ≤ EZ²` | 两次真实积分求导、两个积分公式与积分范数比较 | 本轮补齐原文略写的分析义务 |
| supplement LF3356 | 由 noisemoments 得全局界 | 将既有两个 moment bound 接到第一公开定理的两个导数公式 | 无额外前提 |
| supplement LF2593 | 后继需 `D_{n-i}''` 和 `(uE_{n-i})''` | 新导数及界的直接消费者 | 后继乘积/傅里叶链仍 OPEN |

噪声符号的细节：Lean 指数是 `(((u*z.1+v*z.2 : ℝ) : ℂ) * I)`，原文是 `i*u*Z+i*v*Y`；交换乘法与分配后相同。因此一阶乘子为 `I*(z.1:ℂ)`，二阶为 `-((z.1^2:ℝ):ℂ)`，没有傅里叶符号反转。

## 已接受生产接口的精确来源

文件均是本地只读 curated snapshot 下 `library/` 的相对位置。

| 文件/位置 | 已有内容 | 本节点用途 |
|---|---|---|
| `Shao/Probability/QuadraticFullNoise.lean:13–27` | `quadraticChordFamilyLaw`、输入律、实际 map、`quadraticFullNoiseLaw` | 固定真实律的身份，禁止替代律 |
| 同文件 `:29–31` | `quadraticFullNoiseChar` 的真实积分定义 | 对此定义求导 |
| 同文件 `:37` 起 `quadraticFullNoise_law_data` | 第三个分量为实际 full law 概率性 | 有限测度、常数 1 可积的依据 |
| 同文件 `:275–291` | `quadraticFullNoise_support_moments` 全输入及全结论 | AE 支撑、绝对一阶矩及二阶矩可积与预算 |
| 同文件 `:275–291` 的第 2、4、5、8 个合取项 | `Integrable |z1|`、`Integrable z1²`、`∫|z1|≤67/3 gamma`、`∫z1²≤70/3 h gamma` | 两个 dominator 及两个最终常数 |
| `Shao/Probability/SourceFullNoiseBridge.lean:37–58` | 源条件律 `rho` 的概率性、h3、方差正、支撑及 `gamma≤2h` 已从原源前提获得 | 表明新接口可由既有实际源 specialization 消费，非中心性不被删除 |

完整支撑/矩接口类型已读出，其最后八项依次为：AE 支撑、`Integrable |z1|`、`Integrable |z2|`、`Integrable z1²`、一阶绝对矩界、Y 绝对矩界、实际二阶矩独立分解式、二阶矩界。提取时保持这一次序，不把中间 Y 项误当 Z 项。

精确常数的既有来源不需在新模块重证：16 个弦坐标的一阶预算 `16*(4/3)*gamma` 加实际标量至多 `gamma`，合为 `67/3*gamma`；二阶独立分解的弦预算 `16*(4/3)*h*gamma` 加 `gamma²*E[V0²]≤gamma²≤2*h*gamma`，合为 `70/3*h*gamma`。第二项使用已接受的 `gamma≥0` 与输入 `gamma≤2h`；并未假设源律均值为零。

## 唯一一次服务器 API/source 只读研究

通过 `tools/server.py` / 现有共享连接，单个 `action=exec`、`timeout=60` 请求运行只读 Python 文件读取和指定路径 `.exists()`。远程退出码 `0`、stderr 空；没有 Lean/Lake、Git 写入、缓存加载/获取/全扫描或远端输出文件。

服务器 Mathlib 根：`/root/rivermind-data/shao-lean-20261021/lean/.lake/packages/mathlib`。

1. `Mathlib/Analysis/Calculus/ParametricIntegral.lean:284–289` 精确读取：

   ```lean
   theorem hasDerivAt_integral_of_dominated_loc_of_deriv_le (hs : s ∈ 𝓝 x₀)
       (hF_meas : ∀ᶠ x in 𝓝 x₀, AEStronglyMeasurable (F x) μ)
       (hF_int : Integrable (F x₀) μ)
       {F' : 𝕜 → α → E} (hF'_meas : AEStronglyMeasurable (F' x₀) μ)
       (h_bound : ∀ᵐ a ∂μ, ∀ x ∈ s, ‖F' x a‖ ≤ bound a)
       (bound_integrable : Integrable bound μ)
       (h_diff : ∀ᵐ a ∂μ, ∀ x ∈ s, HasDerivAt (F · a) (F' x a) x) :
       Integrable (F' x₀) μ ∧
         HasDerivAt (fun n ↦ ∫ a, F n a ∂μ) (∫ a, F' x₀ a ∂μ) x₀
   ```

   原文件 `:63–67` 的类型参数为 `α` measurable、`𝕜` RCLike、`E` normed group 与 real/𝕜 normed space；本节点取 `α=ℝ×ℝ`、`𝕜=ℝ`、`E=ℂ`。两轮均取 `s=Set.univ`。只需该 API 的第二个返回分量即可得到 HasDerivAt；第一分量同时证实真实加权积分可积。

2. `Mathlib/Analysis/Complex/RealDeriv.lean:103–104`：

   ```lean
   theorem HasDerivAt.ofReal_comp {f : ℝ → ℝ} {u : ℝ}
       (hf : HasDerivAt f u z) :
       HasDerivAt (fun y : ℝ => ↑(f y) : ℝ → ℂ) u z
   ```

   `.cexp` 不在该文件中以 `theorem HasDerivAt.cexp` 文本命中；本轮未扩大远端查询。其具体调用已有接受的 `QuadraticCharacteristicPower.lean:60–70` 同型逐点证明作为明确用例，因此这里只标“同型用例已核”，不谎称读到了它的定义源码。

3. `Mathlib/Analysis/Calculus/Deriv/Basic.lean:436–437`：

   ```lean
   theorem HasDerivAt.deriv (h : HasDerivAt f f' x) : deriv f x = f'
   ```

   同文件 `:607–609`：

   ```lean
   theorem HasDerivAt.congr_of_eventuallyEq
       (h : HasDerivAt f f' x) (h₁ : f₁ =ᶠ[𝓝 x] f) :
       HasDerivAt f₁ f' x
   ```

   第二次积分求导后的函数置换必须使用所有实数 r 的第一导数积分等式，获得邻域最终等式；单点值不够。

4. `Mathlib/MeasureTheory/Integral/Bochner/Basic.lean:970`、`:983–984`：

   ```lean
   theorem norm_integral_le_integral_norm (f : α → G) :
       ‖∫ a, f a ∂μ‖ ≤ ∫ a, ‖f a‖ ∂μ

   theorem norm_integral_le_of_norm_le {f : α → G} {g : α → ℝ}
       (hg : Integrable g μ) (h : ∀ᵐ x ∂μ, ‖f x‖ ≤ g x) :
       ‖∫ x, f x ∂μ‖ ≤ ∫ x, g x ∂μ
   ```

   新模块可直接用第二个 API，分别 `g(z)=|z1|` 和 `g(z)=z1²`，不需要加上目标结论作前提。

5. 对上述四个明确模块的 `.lake/build/lib/lean/Mathlib/.../*.olean` 做指定路径存在性查询，结果全部 `True`。这只证明缓存文件存在，不证明新声明或新生产文件已编译。

6. 同一只读请求还检查历史 `workspaces/lead-c12/Shao/Probability/QuadraticFullNoise.lean`：`False`；旧工作树 `QuadraticCharacteristic.lean` 存在、SHA256 `8fd7815191dbd1ba9180159effe8c353d8b82d998d4d0d50bb6f957355b628f5`。这是路径版本提示，未据此替换 root 提供的 accepted v39 基线，也未搜索或修改工作树。

## 接受库中的同型用例与精确 import 边

- `QuadraticCharacteristic.lean:1–6` 明确 import `Mathlib.Analysis.Complex.RealDeriv` 与 `Mathlib.Analysis.Calculus.ParametricIntegral`。
- `LowFrequencyDamping.lean:1` import `QuadraticCharacteristic`。
- `QuadraticChordNoise.lean:1` import `LowFrequencyDamping`。
- `QuadraticChordMoments.lean:1` import `QuadraticChordNoise`。
- `QuadraticFullNoise.lean:1` import `QuadraticChordMoments`；因此拟文件只需这一个生产 import。
- `QuadraticCharacteristic.lean:157–206`：两次对复值加权积分用同一 dominated-derivative API，完整 AE 条件顺序与本节点相同。
- `QuadraticCharacteristicPower.lean:60–70`：实仿射相位的复指数 `HasDerivAt`、乘子 `I*S`；`:71 起` 第一积分求导；`:96 起` 一次加权积分求导；`:143 起` 将积分导数用全域第一导数等式接回真实 `deriv` 函数。本节点复用数学路线和 API 组合，不 import 其 private 引理，不复制其额外有限 iid 上下文。

## 风险登记与下一步

| 风险 | 本提案的明确处理 | 当前状态 |
|---|---|---|
| 假定一个自由 Ξ 或候选导数 | 两公开定理均固定真实 full law/char，二阶左端为标准嵌套 deriv | 已在类型级排除 |
| 把导数的 AE 范数界变成源前提 | 全部由相位范数及已有真实矩推导 | 路线完整、待独审 |
| 少覆盖频率零点 | 全域 `s=univ`，无 u/v 分母与非零前提 | 已在声明覆盖 |
| 默加源律中心化 | 无均值前提，保留实际 variance | 已在声明排除 |
| 第二次求导只靠一点的第一导数等式 | 明确对每个 r 用第一 HasDerivAt，构造 EventuallyEq | 数学连接已写全 |
| 两个常数或实/复范数符号误配 | M1 对 `67/3*gamma`，M2 对 `70/3*h*gamma`；二阶乘子取负实平方的复嵌入 | 待独立声明审查 |
| 把 proposal 当机械通过 | 没有 Lean 运行、没有生产 proof body | `NOT_RUN_PROPOSAL_ONLY` |

此轮到此停止。由 root 安排独立精确声明审查及冻结；本节点不计入已合入的 v40，不改变任何原研究根的 OPEN 状态。CPU0–9/80GiB 外部工作及其他分线构建未被触碰。

## 最小公开面（最终候选）

只提交 quadraticFullNoiseChar_derivatives 和 quadraticFullNoiseChar_derivative_bounds。前者合取给出两个真实 HasDerivAt 及两条同一积分的标准 deriv 身份；后者合取给出两个显式常数界。第一稿拆分的六个包装已合并，不另列为公开定理、节点或完成数量。精确完整类型以 proposal.md 的两个 Lean 签名块为准；它们尚未由 Lean 检查。
