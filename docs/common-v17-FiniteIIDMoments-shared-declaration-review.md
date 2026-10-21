# FiniteIIDMoments 共享迁移独立声明审查

STATUS: CORRECT（迁移计划与声明阶段）

本报告只审查冻结迁移方案、最小依赖、公开接口与兼容门。没有新共享实现或兼容入口可供差异/证明审查，不宣称已执行迁移、Lean 检查、消费者重建、rfl 示例或传递公理认证。未运行本机或服务器 Lean，未重编旧模块，未改任何实现或 scope；服务器只读实际冻结旧源码和必要 Mathlib 源。仅新增本报告。

## 冻结绑定与实际读取

- 提案：C:/game/shao lean/drafts/c12/FiniteIIDMoments-shared-scope.md。
  SHA256：3033eb9df9d7586a8b94912ff6ceef6a597275174309af7262b53ac1c080a8db。
- 已接受旧实现：/root/rivermind-data/shao-lean-20261021/workspaces/lead-oq56/Shao/OQ5/P35/FiniteIIDMoments.lean。
  SHA256：4b2c65ec7fb03767b6a469ef5918592c9a76e993ad95262e6a7aae6840c4520b。
- 旧 RowIdentity：同一 worktree 下 Shao/OQ5/P35/RowIdentity.lean。
  SHA256：73bb0809bc6d323b31775327e468677d6320b38f8fe87363936860164f17f975。
- 消费者声明：FourierPower-next-scope.md。
  SHA256：a0c19a11198fa35d63cb78ea7c066f427b2d1a91fb159f5951d5a8b0a1074943。

本轮实际核对 scope 哈希和服务器两份旧源码哈希，分段读完旧 FiniteIIDMoments 的 539 行作依赖/迁移核对，并读取相关 RowIdentity 定义、计数定理和消费者 restricted unfolding 现场。未重新裁决已接受概率证明，也未以作者对依赖的描述代替源码观察。Mathlib 使用项目固定版本 807d3836b165983210ee2ecf3cd28f239436949c。

## 一、实际迁移对象与全部公开声明

迁移的公共接口是 3 个普通定义和 6 个原 theorem，数学参数和前提保持不变。定义本身对任意 m∈ℕ、任意类型 Ω、任意实函数族 Z:Fin m→Ω→ℝ 和 ω 定义：

\[
 S(\omega)=\sum_i Z_i(\omega),
\]
\[
 L(\omega)=\sum_i Z_i(\omega)^2(S(\omega)-Z_i(\omega))^2,
\]
\[
 P(\omega)=\sum_i\sum_j1_{\{i<j\}}Z_i(\omega)Z_j(\omega).
\]

它们分别是 finiteFeatureSum、finiteLeaveOwnSquareSum、finitePairProductSum。总和是全部 Fin m，pair 使用严格 i<j、每一对恰计一次，leave-own 的 own coordinate 确实被排除。不是二次复制一个新的概率 sum convention。

所有六个 theorem 共同量化任意 m∈ℕ、带可测结构的 Ω、概率 μ:Measure Ω 与 ν:Measure ℝ、实际 Z:Fin m→Ω→ℝ，并输入：

- 每个 Zᵢ 可测；
- iIndepFun Z μ；
- 每个 Zᵢ 在 μ 下与 id 在 ν 下 IdentDistrib；
- 实际 MemLp id 2 ν。

没有 m>0、均值零、正方差或三/四阶矩前提。记 a=∫z dν、b=∫z²dν、v=variance id ν，则六个实际结论为：

1. finite_iid_leaveOwnSquare_integrable：L 在 μ 下真正可积。
2. finite_iid_leaveOwnSquare_integral：
   \[
   E_\mu L=m\,b\{((m-1:\mathbb N):\mathbb R)b+
      ((m-1:\mathbb N):\mathbb R)((m-2:\mathbb N):\mathbb R)a^2\}.
   \]
3. finite_iid_pairProduct_memLp_two：P∈L2(μ)。
4. finite_iid_sumSquare_integral：
   \[
   E_\mu S^2=m\,b+m((m-1:\mathbb N):\mathbb R)a^2.
   \]
5. finite_iid_pairProduct_integral：
   \[
   E_\mu P=\binom m2a^2.
   \]
6. finite_iid_pairProduct_variance：
   \[
   \operatorname{Var}_\mu P=\binom m2v^2+
     m(((m-1:\mathbb N):\mathbb R)^2)a^2v.
   \]

m 与 choose 的乘数转实数；上述减法明确先在 Nat 中完成。旧源码 351–423、515–533 的完整公开签名与提案匹配，保留原 include/omit 及显式概率 binders 后，没有隐藏增加或删除的公共前提。

共享命名空间改为 Shao.Probability；旧 Shao.OQ5.P35 的这九个全限定公共名字仍须实际存在。只 open 共享 namespace 或依赖消费者改名不满足该兼容目标。

## 二、两处 RowIdentity 依赖的精确替换

### unorderedPairSum：普通定义展开，非概率改写

旧 module 30–31 行：

    finitePairProductSum Z ω =
      unorderedPairSum (fun i l => Z i ω * Z l ω)

RowIdentity:33–34 的真实 body 正是：

    ∑ i : Fin n, ∑ j : Fin n, if i < j then H i j else 0

把它展开到共享 finitePairProductSum，得到提案的相同双重 Fin m 和严格次序 i<l。只替换普通定义层，不使用交换对称性、求和置换、除二或概率 lemma；绑定变量名的差异是 alpha-equivalence。故共享 body 与旧 body 在展开 unorderedPairSum 后是定义性相等的，数学上无需任何新 equality hypothesis 或公共桥。

这也说明没有必要迁移 RowIdentity 的 kernel、row algebra、pairCount 定义或 U-statistic。共享 sum 的 pair order 和 normalization 不变。

### pairCount_eq_choose：实数 choose-two 恒等式

旧 module 470–471 行的真实 hcnt 类型是
\[
 (m:\mathbb R)((m:\mathbb R)-1)/2=(m.choose\,2:\mathbb R),
\]
proof 使用 pairCount_eq_choose m。RowIdentity:37 的 pairCount 是左侧普通实数多项式；75–82 行的 theorem 将其等于真实 Nat choose 的实值。

本轮服务器直接只读 Mathlib/Data/Nat/Choose/Cast.lean：

- 25 行附近显式声明 variable (K : Type*)，所以 K 是调用 Nat.cast_choose_two 的显式类型参数；
- 43–47 行在 DivisionRing K、NeZero (2:K) 下给
  \[
  (m.choose\,2:K)=(m:K)((m:K)-1)/2.
  \]

取 K=ℝ 后，(Nat.cast_choose_two ℝ m).symm 与上述 hcnt **精确同型**。所需实数除环和二非零由标准实例提供，不增加任何关于 m 的前提。

该恒等式对 m=0、m=1 都有效：实数 m−1 可以为负，但外部 m 因子使计数仍正确。它不是把 Nat cast 的 (m−1:ℕ) 改成实数 m−1，也不需要 m≥2。迁移只替换 hcnt 的 deterministic proof，不改任一 iid moment、mean 或 variance 假设。

本轮完整旧模块读取确认，RowIdentity 的项目级使用确实只有上述两个位置；其他 kernel/row/studentizer 声明未参与这些 generic proofs。

## 三、最小依赖和机械迁移边界

旧 FiniteIIDMoments 还 import Shao.Probability.FiniteIID，但其证明未使用该项目模块的 samplePath、iid sample-map/permutation 等公开声明；需要的 IdentDistrib 与概率积分/L2/variance 都有直接 Mathlib 来源。提案用 Mathlib.Probability.IdentDistrib 等显式导入替代该传递来源合理。

新共享 module 的拟议 imports 全部为 Mathlib，因而项目依赖方向可以是：

    Shao.Probability.FiniteIIDMoments → Mathlib
    Shao.OQ5.P35.FiniteIIDMoments → RowIdentity + 共享 module
    旧消费者 → 旧兼容入口

没有共同 Probability module 反向依赖 OQ5，也没有环。该最小性是项目依赖闭包的最小性，不声称七条 Mathlib import 每条都不可省略。Ring 明确保留合理；以后若独立编译暴露缺失的 transitive tactic，应只补正确 Mathlib import，而不能用 import OQ5 消除诊断。

原 raw-sum square 的严格闭包确是 finiteFeatureSum、subsetSum、其 L2/mean/second helpers、iid coordinate moment helpers及 sumSquare theorem。若只抽这一条同时原封保留余下 OQ5 证明，容易复制 private closure 或扩大公共 helper API。移动整个已通用的 3-definition/6-theorem 块并让旧入口只做 wrapper，是合理的单实现方案。

源码 inventory 与提案一致：2 个私有定义、17 个私有 theorem。两个 measurability helper 在原文件中未被调用，但为机械迁移保留不构成新假设或概率重复证明。其余 helper 均服务现有六结果。scope 明确保留 noncomputable section、autoImplicit false、section variables、open/scoped 和 include/omit，避免从包装变化产生新隐含参数。

允许的核心改动仅为 import/namespace、共享 pair body 的普通展开、choose-two hcnt 证明替换，以及旧公开 theorem 的共享调用 wrapper。任何额外 proof-route/数学类型变化都超出本声明审查，需要另行报告和审查。

## 四、旧定义展开行为和兼容门

保持原三个小 definition bodies 是正确的兼容选择：

- 旧 finiteFeatureSum 仍直接是原坐标和；
- 旧 finiteLeaveOwnSquareSum 仍引用**旧** finiteFeatureSum 并排除 own coordinate；
- 旧 finitePairProductSum 仍直接通过原 unorderedPairSum body，而旧入口继续 import RowIdentity。

共享 finiteLeaveOwnSquareSum 引用新共享 finiteFeatureSum，但两者继续 delta 展开到同一有限和。因此三条旧/新随机变量等式在定义性层面应由 rfl 成立；这只是源码展开核对，不是本轮已执行的 Lean 示例。

不应只将旧三个定义改为指向新定义的 abbrev/def alias。虽然完全展开后可能仍相等，但 restricted dsimp only 只指定旧名字时，可能留下未列入的共享 definition layer。旧 body 保留则避免这种行为改变。

本轮实际读取 ConditionalNumerator:243–245，存在原样：

    dsimp only [finiteFeatureSum, finitePairProductSum, ...]

这为保留旧 body 提供具体消费者依据。当前三条直接 importers 的服务器源码搜索也与提案一致：

- Shao/OQ5/P35/ConditionalStatistics.lean；
- Shao/OQ5/P35/ConditionalStudentizer.lean；
- Shao/OQ5/P35/ConditionalNumerator.lean。

本轮检查的 Shao 源树未见旧 _private.Shao.OQ5.P35.FiniteIIDMoments 前缀引用。该观察不是对外部未检消费者的普遍保证；迁移完成后必须重建所有实际发现的依赖者。

旧六个 theorem 的 proof 可以直接调用全限定共享 same-basename theorem；旧/新 definitions 普通展开后的类型定义性相等，所以不涉及随机变量或 measure/event 的实质转换。必要时只用显式展开的 simpa only 是允许的，但原 theorem signature 不得改。需要保留的是旧全限定公开类型和 restricted unfolding，不是旧 private names、旧 proof objects 或旧 .olean 二进制字节。

scope 列出的未来兼容门充分且必要：核对新旧全部九个 public 类型与 assumptions，实际编译三条 universally quantified rfl equality 示例和 caller-side prefixSum bridge，重编旧入口与三条未改动消费者，并确认新共享 module 的项目 import closure 不含 OQ5。只查看共享目标独立编译成功不足以替代这些门。

## 五、数学边界和 C1/C2 消费

本迁移不增添任何 moment assumptions。P 是不同坐标的 products，独立性与每坐标 L2 给 P∈L2，不需要单坐标四阶矩；leave-own 因子首先排除了 Zᵢ，才能依赖真正独立的其余平方和而只用 L2。保持两者原 body 是保全这一语义的关键。

- m=0：三个实际 sums 都是空和；原六结论的所有 RHS 均为零，包括保留自然减法形式的项。
- m=1：pair 和 leave-own vanish；sumSquare 是实际单坐标二矩。原 leave-own proof 的 m=1 分支必须继续先于对 m−2 的 Nat cast。
- sumSquare 与 pair variance 的 m=0 分支继续先于 Nat.cast_sub；不可在所有 m 上直接把 ((m−1:ℕ):ℝ) 改成 (m:ℝ)−1。
- 非零均值、常值 law、零方差、负坐标均保持允许；原点二矩未变成方差，也未引入样本长度或方差的除法。

对 FourierPower，只在 caller 局部将真实共享 finiteFeatureSum 与既有 prefixSum(samplePath X)ℓ 通过两者实际定义识别即可；scope 所列 simp only 路线具有正确数学类型。h2=Integrable(a²) 可转为 id∈L2 后调用共享 raw-square theorem。中心化、真实 first mean 和漂移支付留在该消费者，不需要为本迁移增加新公共 centered-sum 结论或复制 iid 二矩证明。

## 裁决与尚待执行事项

**CORRECT：固定哈希迁移计划、3 个共享定义、6 个公共签名、两处中性依赖替换及旧接口兼容方案均正确，无需数学签名修订。**

该裁决不授权直接改仍冻结的旧 PR/source，不声称任何 follow-up 已通过。按 scope，实际迁移须在 PR18 integration 及协调者授权后进行，hash-bind 原件，只将通用证明搬到共同位置，旧入口保留定义并使用 thin wrappers。随后完成 standalone/import-closure、旧兼容类型/rfl、未变消费者重建、禁项和包括新共享 helpers/生成项/旧 wrappers 的传递公理审计，再安排实际源码的独立差异审查。

本单元只解决共享封装前提，不证明新 Fourier derivative、Gaussian/clock 比较、conditional iid 或任何完整 C1/C2/OQ56 根结论。
