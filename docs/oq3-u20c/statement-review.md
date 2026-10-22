# U20c declaration review bundle

The two independent reports below are preserved verbatim. The v1 mathematical/source/API declaration review remains valid; the subsequent v2 report explicitly withdraws its proposed separate-root fallback and approves the corrected single-root read-only import view. V2 is the current environment verdict. Neither statement report is an implementation proof verdict; the separate complete proof review governs acceptance.

Original v1 report SHA256: cf2f5e05d4e34c6dc2a4d3fca637092001537bca5aaa9282d08dec804b147270.
Original v2 report SHA256: a60368937a4ca0c8d8cccb38a848b6ba5a330e1b64ed56ea92a16b8f56789648.

---

# U20c SourceCanonicalRate 独立声明审查

STATUS: IN_PROGRESS

## 不可改写盲审前缀

本前缀只依据冻结声明的两个 Lean 代码块生成；尚未读取本轮 scope 说明、R1、公共 BivariateLegendre 实现、生产者证明或任何机械凭据。
本轮为声明／来源／API门，尚无本模块实现或证明验收。
0 个公开定义，1 个公开定理；下面保留完整导入和完整类型，不把名称视为已证明语义。

```lean
import Shao.OQ3.SourceGlobalExponentialTests
import Shao.Probability.BivariateLegendre
```

```lean
theorem source_canonical_rate_unique_minimizer
    (q : ℝ) (hq0 : 1 < q) (hq1 : q < 103 / 100)
    (w : AtomicIndex → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hm : ∀ k : Fin 4,
      HasSum (fun i => w i * constraintFeature sourceEll (fixedAtom i) k)
        (constraintTarget q k)) :
    let P : Measure ℝ := originalMeasure sourceEll w
    letI : IsProbabilityMeasure P := originalMeasure_isProbabilityMeasure sourceEll w hw
      (by simpa only [constraintFeature, constraintTarget, Matrix.cons_val_zero, mul_one]
        using hm 0)
    let W : ℝ → ℝ × ℝ := fun x => (x, x ^ 2)
    let D : Set (ℝ × ℝ) :=
      {z | 0 < z.2 ∧ (Real.sqrt q / 4) * Real.sqrt z.2 ≤ z.1}
    bivariateMGFDomain P W = Set.univ ∧
      (∀ theta : bivariateMGFDomain P W,
        (0 < ∫ x : ℝ, Real.exp
          ((theta : ℝ × ℝ).1 * x + (theta : ℝ × ℝ).2 * x ^ 2) ∂P) ∧
        bivariateLogMGF P W theta =
          Real.log (∫ x : ℝ, Real.exp
            ((theta : ℝ × ℝ).1 * x + (theta : ℝ × ℝ).2 * x ^ 2) ∂P)) ∧
      ∃ theta0 : bivariateMGFDomain P W,
        (theta0 : ℝ × ℝ) = (8 * sourceEll, -sourceEll) ∧
        ((theta0 : ℝ × ℝ).1 * (q / 4) + (theta0 : ℝ × ℝ).2 * q -
          bivariateLogMGF P W theta0 = saddleRate sourceEll q w) ∧
        (q / 4, q) ∈ D ∧
        bivariateLegendreRate P W (q / 4, q) = (saddleRate sourceEll q w : EReal) ∧
        ∀ z ∈ D,
          bivariateLegendreRate P W (q / 4, q) ≤ bivariateLegendreRate P W z ∧
          (bivariateLegendreRate P W z = bivariateLegendreRate P W (q / 4, q) ↔
            z = (q / 4, q))
```

### 独立逐项翻译与待核门

1. 先任给同一实数 q，要求 1<q<103/100。
2. 再任给同一原子指标上的实权重函数 w，所有权重非负；没有假设每个权重严格正。
3. 对四个约束索引 k，真实实级数 w_i·constraintFeature(sourceEll,fixedAtom_i)_k 必须 HasSum 到 constraintTarget(q)_k。
4. HasSum 是实际收敛命题，不是一个总化 tsum 值等式。
5. P 固定为 originalMeasure sourceEll w，此后所有域、配分、率函数都引用该 P。
6. 类型内部用 hm 的第零约束和 hw 生产 P 的概率实例；调用者不用额外提交一个概率实例。
7. 这个 letI 的证明体必须能在真实约束定义展开后匹配 HasSum w 1；不能把错误的索引类型或约束当作质量。
8. W 是固定的二元统计量 x↦(x,x²)，没有任意代理统计量。
9. D 是完整的弱尾域：第二坐标 c>0，且 (sqrt q/4)·sqrt c≤第一坐标 a。
10. D 不限制 c 位于支撑内部，也不排除曲线边界。
11. 第一项结论是实际二元 MGF 有限定义域等于整个实平面。
12. 这必须从同一 P 的真实指数可积性生产，不是把域定义为全平面。
13. 第二项对域内每个 subtype 参数 theta 都给真实指数积分严格正。
14. 同一项还把 canonical bivariateLogMGF 等同于字面上的 log∫exp(theta₁x+theta₂x²)dP。
15. 因而必须核对积分可积和正值发生在实 log 使用之前；域外总化 log 不能替代该门。
16. 接着存在真正属于该 MGF 定义域的 theta0，而非只有一个未证明成员资格的实参数对。
17. theta0 的底层实参数必须恰好等于 (8·sourceEll,−sourceEll)。
18. theta0 在候选点 (q/4,q) 的有限实仿射指数测试值恰等于 saddleRate sourceEll q w。
19. 这个达到值要求同一 P、同一 q、同一 w、同一 canonical log 配分；不能靠另一个测度的归一化常数。
20. 目标同时生产候选点 (q/4,q) 属于 D，不能由调用者提供。
21. canonical EReal 值的候选率恰等于有限实 saddleRate 的标准嵌入。
22. 因而这个候选值既不是 +∞ 也不是 −∞，必须通过真实上界与达到值确定。
23. 最后对 D 的每一个点 z，候选 canonical rate≤该点 canonical rate。
24. 在同一个全尾域内，率等于候选率当且仅当 z=(q/4,q)。
25. 这是整个 D 上的达到且唯一最小结论，不是局部 Hessian 正性或临界点结论。
26. 对非候选 z，足够的真实生产路径应给一个有限实指数测试严格超过同一 saddleRate，再用 canonical 上确界接口提升。
27. 该严格分离必须覆盖 c<1、c>能量支撑上界、边界 a=(sqrt q/4)·sqrt c，以及所有允许非负原子权重。
28. 必须检查 EReal 有限嵌入保持严格次序；不能经 top.toReal 或把无穷值当有限值取消。
29. 需要实际公共接口提供每一个有限测试≤canonical rate，及所有测试上界⇒canonical rate上界；不能跨模块调用 private helper。
30. 所有存在对象都在原任意 q/w 之后，不能为了非格点或唯一性另换 q、w 或 P。
31. 本类型没有宣称 canonical 率函数与 root 的其他均值映射逆或完整最终反例结论已经接通。
32. 待核：bivariate* 定义的真实命名空间、域 subtype、log 与 EReal supremum 的具体定义。
33. 待核：原子模型的固定有界性是否在仅 hw≥0、四个 hm 下给任意实二次指数真实可积。
34. 待核：两个已接受指数测试公共 API 的全部前提是否恰好由当前类型满足。
35. 待核：theta0 成员资格、候选尾域成员资格和 EReal 比较是否均可由公开标准 API 生产。
36. 待核：当前冻结导入图及 root 已验收对象的只读补充路径是否足够，不能以缓存复制或新探针掩盖缺口。
37. 本前缀不预报 elaboration/kernel PASS；声明数学正确性、API可达性和实际未来证明验收分别裁定。

--- END IMMUTABLE BLIND PREFIX ---

## 来源与独立数学裁定（机械凭据之前完成）

审查顺序记录：上述89行6207B盲审前缀先落盘，SHA256为`3b572ceca8879ef9b8b29536aeecc276f5413da970ffab41eb4f47bb9fad15fe`。随后才读scope74全文、真实R1 161–307、root-contract 24–35及44–62、实际公共BivariateLegendre全文114行、实际SourceGlobalExponentialTests两个完整公共类型及119–324生产体、InverseTilt与FiniteConstraints相关实际定义。没有读取作者candidate/implementation/scanner或future笔记。此处评定声明是否真实、是否存在公开可实现路径，不对尚不存在的U20c证明给kernel验收。

### 1. 原义务与准确范围

R1 161–237要证明鞍点是正尾域的唯一全局率极小点。原文以相对熵／Bernoulli数据处理说明严格差，尤其193–231覆盖可实现的能量边界比例；234–237还需要从边界推广到弱尾域内部。当前声明采用已经独立验收的有限指数测试，接真正的扩展实Legendre上确界，履行同一全尾域率比较义务；不把R1的相对熵叙述当作一个尚未证明的KL接口输入。

root-contract 26明确D_x={c>0且a≥x√c}，虽保留弱不等式，该集合在整个R²并非闭集。scope的D严格保留c>0，没有偷加c=0。root-contract 28–30规定真实指数可积域、正配分及域上的实log，再以完整域上的EReal上确界定义全局率。实际公共实现与本TYPE完全吻合：不是给所有不可积参数的总化积分0取log。R1 239–257的协方差／校正常数和259–307的非格点／近共振仍是其他承重义务，本目标没有把它们由名称自动推出。

### 2. 全部四约束、同一概率律与真实全参数域

FiniteConstraints.lean35–38中feature为![1,x²−4x,x·exp(−ellY),x²]，target为![1,0,0,q]。因此hm0经过完整冻结simp列表确实给HasSum w 1；该证明不是另一条概率假设。InverseTilt.lean51–55公开originalMeasure_isProbabilityMeasure以hw和该HasSum生产P的真概率，进而已有NeZero P。类型中letI有实际证明，不靠隐藏的caller实例。

P始终为originalMeasure sourceEll w；W始终为(x,x²)。InverseTilt.lean57–60的实际AE界为1≤|x|≤4+√10；26–34公开continuous+该固定界给概率下真Integrable。因此任意实s/t的连续exp(sx+tx²)均可积；PR146公共source_saddle_exponential_value_bound119–133还直接交付这项可积性、严格正积分、全部实s/t的候选测试上界及精确达到值。没有把U16d的小球MGF界扩大为全参数结论，也不需要所有w_i>0或协方差非退化。

实际Shao.Probability.BivariateLegendre.lean20–22的域就是{theta | Integrable(exp(theta·W)) P}。逐theta消费上述任意s/t可积性即可用Set.ext证明域=univ；反向包含是univ的平凡性质。24–27的bivariateLogMGF定义字面等于本TYPE中的log积分；W与pair投影化简后rfl/simp即可，无额外解析定理。35–44的bivariateLogMGF_spec还给每个域成员的正配分及exp(log)=配分；本TYPE所需正性也由PR146直接给出。域、正性与literal值三门均由同一P产生。

### 3. 候选域成员、有限测试上界与达到

记L=saddleRate sourceEll q w，z0=(q/4,q)。PR146第119–133行的第一个合取对每个s/t有真正有限实测试s(q/4)+tq−logZ(s,t)≤L；第二合取在s=8sourceEll、t=−sourceEll给精确等号。把该原始参数对和其已生产Integrable证明组成domain subtype theta0，即得到真正的theta0成员和底层对等式；无需先由达到值反推可积。

q>1推出q>0；Real.sq_sqrt在q≥0下给(sqrt q)²=q，于是(sqrt q/4)·sqrt q=q/4，且第二坐标q>0，故z0∈D。这里只有正q的平方根恒等式，没有清除可能为零的sqrt分母，q窗口两端也未取等。

公共bivariateLegendreRate_eq_of_attained_bound56–71的全部输入是同一P/W、z0、L、对全部domain参数的有限实上界、theta0及达到等式，当前各项已生产。其实现先iSup_le配合EReal.coe_le_coe_iff给上界，再由le_iSup的实际测试和达到等式给下界。候选率因此等于(L:EReal)，不是把其他点的率也强制有限，也不取任何无穷EReal的toReal。

### 4. 整个弱尾域非候选点的严格分离与唯一性

任取z=(a,c)∈D且z≠z0。D直接交付c>0和弱尾不等式；pair不等通过Prod.ext得到a≠q/4或c≠q。PR146公共exists_source_tail_exponential_separator153–167恰以q窗口、同w/hw/全部hm、这三项门为全部前提，给有限实s/t、真实Integrable、正配分和L<s·a+t·c−logZ。组成domain subtype后就是公共通用唯一极小定理所需的hsep，无新手工globalmin/gap/KL/矩可实现性假设。

我实际读了该separator生产体168–321，确认它的公共全域性不是只在支撑内R近1成立：228–241独立处理c<1，242–255独立处理c>1+H；256以后才处理1≤c≤1+H，端点p=0或1允许；276–285的c=q、a>q/4情况使用sourceEll>0给严格差；其余R≠1情况接已验收Bernoulli有限指数测试和7/200充分间隙。弱尾边界本身允许等号，严格性来自非候选差，不是悄悄要求a>x0√c。当前调用只用这条公开定理，不跨模块引用其三个private helper。

BivariateLegendre.lean73–110公开bivariateLegendreRate_unique_minimizer_of_tests给所需完整合取。其实现先按上一条得到候选有限值；对非候选z，用EReal.coe_lt_coe_iff把有限L<test提升为扩展实严格不等式，再接46–54的test≤真正上确界。即使该z的率为+∞也保持严格；不会把top.toReal当有限数，亦不会错误推出处处有限。严格比较同时排除等号；z=z0分支给自反比较和等号双向。故全域比较与唯一性完全由实际接口生产，不依赖局部凸性、Hessian或均值映射逆。

### 5. 声明类型、作用域与消费路径

scope74第14行明确namespace Shao.OQ3，open MeasureTheory Shao.Probability，open scoped Matrix、noncomputable section；所以未限定的bivariate*确实解析为实际公共命名空间Shao.Probability，原子／源测试为当前Shao.OQ3。Fin4的向量simp在Matrix作用域下与已接受source_saddle_exponential_value_bound中134–135的同一hm0提取完全相同。Subtype、P/W/D全部let依赖顺序正确；theta0存在在q/w之后，最后forall z仍在其存在作用域内。沒有出现把hp/hm移到蕴含前件从而真空成立的问题。

可实施的最短生产链是：hm0→真P概率→PR146上界/达到→真实domK=univ和literal log→带成员的theta0→z0∈D→PR146全尾域separator→公共unique_minimizer_of_tests。所有必要数学输入均已由公开生产者交付，不输入另一个存在law，也不使用尚未交付的canonical局部均值逆或PR151 private接口。原最终反例U20b的同一个w/q日后可实例化此全称适配，不在本节点重择。

数学／来源／公共API阶段结论：当前冻结完整TYPE正确，存在不加强前提的实际公开证明路径。下面再核精确环境绑定，绝不把上述声明结论写成U20c实现已过Lean/Audit。

## 最后机械绑定与静态环境门

本节在完整数学／来源／公共API裁定之后核对，不用收据PASS替代上述论证。没有运行任何Lean、#check、API探针、成功smoke复跑、target/Audit重编或缓存写入。全部服务器项目读取均经共享broker，运行于taskset -c 14-17；未触外部CPU0–9/80GiB任务。

### 冻结字节与实际checkpoint

- 本地及remote run/scope.md均为61行6706B，SHA256 `535657a95d1f7d7dc57f8019dde4d03d733fb6f26a8f08875dfbdc4b83315460`。
- R1原件实际SHA256 `3473d34ff20bd0d334b9ef3ea3c3ee167fba4d5cc3a742849820ce54d639e662`；root-contract实际SHA256 `a3a55ceb4dcdd848967d979ec5eb1c277ac4539476728e7fdce119f01fd2757a`，其PROPOSED历史标签不被误写为新已闭根。
- 实读本地公共BivariateLegendre为114行4608B，SHA256 `d8bd5dc7099ffdbf52282ebb41ad03145a50b42547dec55bb42caacb31ed5f58`，与实际root接受树同文件hash一致。
- 实读SourceGlobalExponentialTests为324行14847B，SHA256 `24c7029298efc869d785ad4e08dae1a6ea0ca788bf47357355a4e5c564a513df`，与实际root接受树及正式v38源字典一致。
- 实际lane仍为`feat/oq3-source-remainder-not-bigo`，HEAD `9170a40f3e9a6d519a987c2a0ceaade85136cd36`，git status --porcelain为空。未建U20c分支，lane真实SourceCanonicalRate.lean不存在。
- 实际root接受工作树`/root/rivermind-data/shao-lean-20261021/workspaces/integration-bearing-v38`的HEAD为`ffdedd610d0af501c3dd4672cf7f78d80eee543c`，tree为`433377aee492752840f9396896bd00f668634442`，与本scope绑定一致；main `63f82bd7ea2a0fba92a4ad217c4ad27bfa3ead00`为协调正式公布的同批main，不假称它就是lane当前HEAD。
- 最后读取正式`library/verification/receipt-v38.json`，38229B，SHA256 `0e10017d614e4e519e64df72ee2cc09563eec174810395d3b3ea1fb159bc50de`。其13项source_files_sha256与下表及实际独立图逐项一致；只消费已接受对象与源绑定，不重复root kernel/axiom门。

### 独立一次精确双导入图

我从实际接受工作树解析精确两seed import，去除嵌套block／line注释和字符串后处理普通、public/private及meta import；module头会改变普通import的默认公开性。物理图遍历所有内部边，公开图只遍历可转导边，不把private边当公开API。

结果：物理13 Shao、2776 Mathlib；公开2525 Shao/Mathlib内部节点及189个外部停止叶；内部源缺项0。我这次物理遍历外部停止叶为211，单列口径而不强行等同公开189；这些外部名没有递归当作Shao/Mathlib源码展开，也不声称已检查整个Lean源码库。

下面为实际canonical相对路径键→SHA256字典，已独立重算compact SHA256 `f158e2cad3e7a0dc5f0c7c31d85c111820fb38cb483188a4e9fe653e8ec2ecd2`；没有读取作者candidate-cache JSON正文或scanner，也未把其图摘要作为独立结果。

| 实际前置源相对路径 | SHA256 |
|---|---|
| `Shao/OQ3/AtomicMeasure.lean` | `59ddc48fb7b395f362939e58cbd9d7911685a6ed6e6574142e8a6d4ab3ee0c39` |
| `Shao/OQ3/BinaryEntropyBounds.lean` | `291cc2afc5e632ad8326b5d98ceb619b959a41bc8d49120d2a52bd1a0b213228` |
| `Shao/OQ3/EnergyBernoulliMGF.lean` | `e3bb038b2b92fac9a5341b26d437eeba046a5fd954a753fe80a7058ce32432ad` |
| `Shao/OQ3/FiniteConstraints.lean` | `800d9db8cb6749a31ecfe611409de92b10ea8bb2aef955bfd825ede7324f0ef0` |
| `Shao/OQ3/FiniteStageMeasure.lean` | `1a32fb904e6ee9d2b0b48d92c4ebb3568452bb02500ce52a1a03eb01ae0256b1` |
| `Shao/OQ3/InverseTilt.lean` | `c7e7d19e8b70481b663bec1fd12ea9301d73313faaf35997e85aa9ba99f21811` |
| `Shao/OQ3/PositiveRate.lean` | `8e727078d3a4f1db2392384b84cc31235ff69efa13dd5e44b23eac818a788f7b` |
| `Shao/OQ3/RegularCovariance.lean` | `0add3476cc949edc593e15dc195934a6df78a41a55f4a2281f66095733d4c853` |
| `Shao/OQ3/SourceBinaryEntropyGap.lean` | `f5696cc1c953b3079f0c2987a239b3d0c0003292bb3018052c80d4f1fa9254c9` |
| `Shao/OQ3/SourceGlobalExponentialTests.lean` | `24c7029298efc869d785ad4e08dae1a6ea0ca788bf47357355a4e5c564a513df` |
| `Shao/OQ3/SourceStarter.lean` | `0e2a081619976f88149707c2ef9311dc909003e61d3d0f7c4e21e6c3dbbc5a6d` |
| `Shao/OQ3/SummableAtoms.lean` | `0ea4c64fe9ef9b45fbf44d24312771a1dbfbcc5de8448564e3e87bdf17c7178b` |
| `Shao/Probability/BivariateLegendre.lean` | `d8bd5dc7099ffdbf52282ebb41ad03145a50b42547dec55bb42caacb31ed5f58` |

所有13项与正式v38源字典匹配。Mathlib实际包路径解析到`/root/rivermind-data/shao-lean-20261021/cache-overlays/shared-v34/packages/mathlib`；Mathlib commit由固定manifest/正式receipt绑定`807d3836b165983210ee2ecf3cd28f239436949c`。lane和root的lean-toolchain均SHA256 `d581a24b57a4ae9e0b2132ca8ac7cc3ac336a9fc2751fe6b29414e2d434d54c4`，lake-manifest.json均SHA256 `40e8e3385f2b0c8ae56fa9de6947301472379cb62eeb83247944827c38b8af6e`；均逐字相同。Lean为leanprover/lean4:v4.36.0-rc1。没有升级pins。

### 仅新公共对象的可读补充路径

本次实际逐内部节点检查现成olean存在性，lane own对象唯一缺项为Shao.Probability.BivariateLegendre；lane旧树该源也不存在，符合冻结153历史状态。接受树中同源的`/root/rivermind-data/shao-lean-20261021/workspaces/integration-bearing-v38/.lake/build/lib/lean/Shao/Probability/BivariateLegendre.olean`真实存在、68600B且只读可打开。其余内部对象在lane既有路径存在；允许这一精确接受目录作为只读fallback后缺项0。

静态适用理由是：该目录下模块相对路径正是Shao/Probability/BivariateLegendre.olean，源hash及Lean/Mathlib pins与当前目标精确匹配；未来从已接受v38正常新分支后源亦匹配。若own仍无该对象，可在lake env生效之后保留own搜索优先级、把这个已接受root build目录置于其后、并保留现有Mathlib等搜索路径，供Lean只读解析；这不复制对象，不写root或cache目录，不把旧153树重置到新baseline。若root已接通own对象，可使用正常路径，无声明变化。

最后读取remote正式readiness-ack.json，SHA256 `6c5733b431d437e13a48e172af1f06c89cfc57dbf68ef1e9364acce23122c427`。其中READY_WITH_READ_ONLY_ACCEPTED_ROOT_OBJECT_PATH、source checkpoint/tree及唯一own缺项与我实际观测一致。它是环境行政说明，不是本模块elaboration或proof票。我没有执行该未来LEAN_PATH命令来冒充通过检查；实际U20c elaboration、完整实现、模块owner TYPE/公理审查均待后续，当前无U20c source/Audit/build/receipt。run在本报告上传前仅scope.md与readiness-ack.json。

## 最终裁决与剩余义务

STATUS: CORRECT

裁决仅绑定scope74上述精确SHA、0公开DEF/1完整THM及精确两导入：声明数学正确、来源对应充分、量词及同law保持，当前实际公开API可无新增假设生产全域/正log/达到/完整弱尾域canonical EReal唯一极小合取；环境已有精确接受对象的只读可行路径，无需新cache写。未发现必须修订声明的数学、类型或API阻塞。

原target→本节点拟消除义务：R1 161–237/root A的同源原律完整domK、真实有限候选canonical率及整个正能量弱尾域唯一全局极小点。直接consumer是对同一个U20b最终w/q/P的root A canonical组装，不重新选择law，也不把任意矩点的扩展实率宣称有限。

剩余：本模块尚未实施或通过Lean/Audit，必须独立完整proof审查后才能记该义务已消除；PR151实际Fin2梯度／完整Hessian到canonical对象的连接、均值映射逆邻域及其他root组装仍待各自证明。PR148几何常数、U20b标准Landau失败等既有结论不因本声明名而自动组装。一般KL9/10、统一far率间隙与概率界、其余B/C/D义务及全部原根A/B/C/D仍OPEN。不声称新颖性、最优性、整个OQ3完成或局部凸性足以代替全局极小。

本报告仅追加于原89行6207B盲审前缀，原字节不改；初始STATUS: IN_PROGRESS是落盘历史，此处STATUS: CORRECT为本次完整声明终裁。未修改任何source/scope/旧票/pins/cache/他人文件，未启动Lean/probe/build/Audit或创建新代理／commit／PR。

---

# U20c v2 独立环境修正声明审查

STATUS: IN_PROGRESS

## 不可改写盲审前缀

本前缀先只依据v2冻结Lean代码块，保全全部公开类型和独立语义翻译，未读取v2正文、作者证明体、import-view字典、失败日志或Lean查找实现。
本轮仅声明／环境修正门；本模块0公开DEF、1完整公开THM，不能把环境批准记为proof通过。

```lean
import Shao.OQ3.SourceGlobalExponentialTests
import Shao.Probability.BivariateLegendre
```

```lean
theorem source_canonical_rate_unique_minimizer
    (q : ℝ) (hq0 : 1 < q) (hq1 : q < 103 / 100)
    (w : AtomicIndex → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hm : ∀ k : Fin 4,
      HasSum (fun i => w i * constraintFeature sourceEll (fixedAtom i) k)
        (constraintTarget q k)) :
    let P : Measure ℝ := originalMeasure sourceEll w
    letI : IsProbabilityMeasure P := originalMeasure_isProbabilityMeasure sourceEll w hw
      (by simpa only [constraintFeature, constraintTarget, Matrix.cons_val_zero, mul_one]
        using hm 0)
    let W : ℝ → ℝ × ℝ := fun x => (x, x ^ 2)
    let D : Set (ℝ × ℝ) :=
      {z | 0 < z.2 ∧ (Real.sqrt q / 4) * Real.sqrt z.2 ≤ z.1}
    bivariateMGFDomain P W = Set.univ ∧
      (∀ theta : bivariateMGFDomain P W,
        (0 < ∫ x : ℝ, Real.exp
          ((theta : ℝ × ℝ).1 * x + (theta : ℝ × ℝ).2 * x ^ 2) ∂P) ∧
        bivariateLogMGF P W theta =
          Real.log (∫ x : ℝ, Real.exp
            ((theta : ℝ × ℝ).1 * x + (theta : ℝ × ℝ).2 * x ^ 2) ∂P)) ∧
      ∃ theta0 : bivariateMGFDomain P W,
        (theta0 : ℝ × ℝ) = (8 * sourceEll, -sourceEll) ∧
        ((theta0 : ℝ × ℝ).1 * (q / 4) + (theta0 : ℝ × ℝ).2 * q -
          bivariateLogMGF P W theta0 = saddleRate sourceEll q w) ∧
        (q / 4, q) ∈ D ∧
        bivariateLegendreRate P W (q / 4, q) = (saddleRate sourceEll q w : EReal) ∧
        ∀ z ∈ D,
          bivariateLegendreRate P W (q / 4, q) ≤ bivariateLegendreRate P W z ∧
          (bivariateLegendreRate P W z = bivariateLegendreRate P W (q / 4, q) ↔
            z = (q / 4, q))
```

### 完整类型独立翻译

1. 任给同一实数q，严格窗口为1<q<103/100。
2. 任给同一原子权重函数w，要求所有权重非负；没有加入全体严格正前提。
3. 对Fin4的每个约束索引，w乘真实fixedAtom上的constraintFeature有真正HasSum到constraintTarget q。
4. P在所有结论之前固定为originalMeasure sourceEll w。
5. letI由hw和hm0的真实质量约束生产P的概率实例，不向调用者新增概率假设。
6. W明确为x↦(x,x²)，不是另选的统计量。
7. D是第二坐标c>0且(sqrt q/4)·sqrt c≤a的整个弱正尾域。
8. 第一结论是真实二次指数可积域bivariateMGFDomain P W=univ。
9. 第二结论对该域每一个真实subtype成员给严格正指数积分。
10. 同项把canonical log配分绑定到同一P下字面的实log指数积分。
11. 存在带真实域成员证明的theta0，其底层实参数恰为(8sourceEll,−sourceEll)。
12. theta0在候选(q/4,q)的有限实测试值等于同一saddleRate sourceEll q w。
13. 候选(q/4,q)必须由结论生产其D成员资格。
14. 候选canonical EReal率恰等于有限实saddleRate的标准嵌入。
15. 对D的每个z均有候选率≤该点率，并且率相等当且仅当z就是候选。
16. q/w/P均不在后续存在或比较分支中重选。
17. 全tail比较包括弱边界及能量支撑之外的c>0点；不偷加矩可实现性。
18. 任何非候选点的率可能为+∞，类型不声称该处有限，也不允许top.toReal捷径。
19. 本类型没有caller提供的globalmin、KL、Hessian或域全性结论。
20. 第一代码块恰为SourceGlobalExponentialTests与BivariateLegendre两导入；实际作用域和公开可达性仍须精确绑定。

### 新环境门的独立待核问题

21. 本次不以父实例给出的环境说明预先断定可用；须读取固定版本真实模块查找实现。
22. 需要区分对整个Shao根的首个选择与对每个完整模块名逐个搜索路径这两种不同语义。
23. 如果Lean按顶层包根缓存首个目录，那么own Shao在前、root Shao在后的并列搜索不自动形成逐模块fallback。
24. 所谓import-view必须让同一个被选中的Shao根下既有own OQ3又有已接受公共Probability。
25. 符号链接应真实解析到指定只读对象目录，而不是只在JSON里声称存在。
26. 13条已冻结前置路径必须能经同一视图逐条读到实际olean；只核此新路径门，不重算已通过导入图或稳定缓存hash。
27. 公共BivariateLegendre源hash必须继续绑定已接受精确源，不能借同名对象替换定义。
28. 未来SourceCanonicalRate对象的视图路径必须沿OQ3链接归属own输出目录；不能把目标写入root已接受目录。
29. 视图首位与原Lake Mathlib等路径保留的顺序必须符合实际findOLean消费方式。
30. v1/v2两个完整Lean代码块必须逐字相同，才能把修正界定为环境问题而非暗改数学前提。
31. 失败build01只作为真实环境反证，不得把未进入证明体的失败误记为数学证明失败或成功。
32. 本门不读取或评审作者完整证明体，不运行Lean/probe/build02，也不修改任何旧票或源码。
33. 新环境即使静态成立，下一次实际import／elaboration及完整proof验收仍独立待做。
34. 所有根A/B/C/D仍OPEN。

--- END IMMUTABLE BLIND PREFIX ---

## 完整类型与修正范围

v2本地scope63行7847B，SHA256 `d716c2d9c356f3e3562605885394e75f95565c8649bc66c40a88853d11d1e351`；remote scope-v2.md实际同hash。原v1 scope61行6706B，SHA256 `535657a95d1f7d7dc57f8019dde4d03d733fb6f26a8f08875dfbdc4b83315460`。逐字节提取并比较两个版本的两个Lean代码块，两个块均完全相同：imports块SHA256 `5f18bd2491b0523a5d336702c479d395ccc5aedb01827809d27e24ae9f9bc1e6`，完整TYPE块SHA256 `c9f41f1aa83de4d9d230572d66f82afe1e4b5c3bb62d08889296a9cb0e3f94c5`。不是仅删除空白后匹配，也没有改letI证明、量词、D、EReal率或等号唯一性。

v2正文相对v1仅更新当前已有source／分支／import失败的历史状态、纠正并列搜索路径的静态适用判断，以及指定单根符号链接视图。冻结数学接口和两个imports不变。因此本次不重复v1已完成的R1／真实指数测试／canonical率数学审查，也不重新扫描13／2776图、pins、缓存或执行旧成功检查。v1数学判断的保留不意味着其环境判断仍有效。

盲前缀在读取v2正文／Path.lean／view元数据／错误选块之前完成：88行5525B，SHA256 `5e8e3e74bc3fa749796ef79f77dfc7a912252955d51ad25cd67247a7a9606057`；本终票仅在该完整前缀后追加。

## 实际Lean模块查找语义与v1纠正

我独立读取固定工具链源：`/root/rivermind-data/shao-lean-20261021/toolchains/elan/toolchains/leanprover--lean4---v4.36.0-rc1/src/lean/Lean/Util/Path.lean`，8837B，SHA256 `d882f4f9daaa9ee50c7627d9edcf12b2ce802836d2087ad5b94a4f47b2ad0d95`。未运行该工具链。

- 59–64行findRootWithExt先取mod.getRoot，对SearchPath用findM?找第一个存在根目录或根对象的条目；它并不检查该根下面的完整子模块对象。
- 66–70行明确注释findWithExt“不检查返回路径存在”，只把选中根和完整模块名通过modToFilePath拼接。
- 72–77行findModuleWithExt只在已选完整路径检查存在；失败后也没有接着搜索其他同根目录的分支。
- 121–147行oleanRootCacheRef以顶层package为键并绑定当前SearchPath；findOLean后续同Shao根直接重用选中的目录。缓存失效是搜索路径变化，不是某个子模块缺失。
- 103–107行把环境LEAN_PATH解析条目放在builtin路径之前；113–115行保存搜索路径。未来最终Lean进程中view必须实际处于所有其他Shao路径之前。应在lake env设置其既有路径之后再前置view并保留其余路径，不能依赖被Lake覆盖的外层变量。

因此我v1报告把“own Shao先、root Shao次”视为逐模块fallback的推断确实错误，现明确撤回该环境适用结论；它没有得到固定版本实现支持。顶层Shao一旦选own，即使own缺Probability/BivariateLegendre.olean也不会再试后面的root Shao。旧v1报告及scope原字节保留，当前纠正不改写历史。

只读选取build-01.log的import错误行，实际报错为SourceCanonicalRate.lean:1:0找不到own目录下Shao/Probability/BivariateLegendre.olean。日志242B，SHA256 `260cc7c835654100a3cb9b99dd704774a04f9d735d2f06db59e5a0809565dbd6`；本次未下载原始完整日志。这个错误与上述查找实现一致；没有进入证明体，不能记作数学证明失败、成功或Audit验收。

## 新视图的独立路径审查

实际视图`/root/rivermind-data/shao-lean-20261021/runs/oq3/u20c-20261021/import-view`中Shao为真实目录。Shao/OQ3是符号链接，实际readlink和resolve均指向lane的`.lake/build/lib/lean/Shao/OQ3`；Shao/Probability实际指向接受v38的`.lake/build/lib/lean/Shao/Probability`。这是单个Shao根内部组合子目录，直接满足findRootWithExt／findOLean的语义；不是重试第二个Shao根。

我逐个实际readlink并resolve检查八个顶层链接：Basic、C1、C2、Checks、OQ3、OQ4、OQ5均指lane对应既有目录，Probability指接受root对应目录；全部为符号链接且目标目录存在，没有循环或断链。只读目录引用使该目录内原有对象与同目录伴随文件沿相同路径可见，不要求把二进制复制到新缓存。

以下仅做本次新路径门的13项存在／可打开／samefile检查，没有重算它们的二进制hash或重复导入图。每一项均可经同一个view/Shao根读取，前12项samefile为lane对应文件，最后一项samefile为接受root对应文件。

| view下实际相对路径 | 解析归属 | 字节数 | 存在／可读／samefile |
|---|---|---:|---|
| Shao/OQ3/AtomicMeasure.olean | lane OQ3 | 206728 | 全部真 |
| Shao/OQ3/BinaryEntropyBounds.olean | lane OQ3 | 574016 | 全部真 |
| Shao/OQ3/EnergyBernoulliMGF.olean | lane OQ3 | 453904 | 全部真 |
| Shao/OQ3/FiniteConstraints.olean | lane OQ3 | 481688 | 全部真 |
| Shao/OQ3/FiniteStageMeasure.olean | lane OQ3 | 213248 | 全部真 |
| Shao/OQ3/InverseTilt.olean | lane OQ3 | 224136 | 全部真 |
| Shao/OQ3/PositiveRate.olean | lane OQ3 | 330192 | 全部真 |
| Shao/OQ3/RegularCovariance.olean | lane OQ3 | 866536 | 全部真 |
| Shao/OQ3/SourceBinaryEntropyGap.olean | lane OQ3 | 1297344 | 全部真 |
| Shao/OQ3/SourceGlobalExponentialTests.olean | lane OQ3 | 1276360 | 全部真 |
| Shao/OQ3/SourceStarter.olean | lane OQ3 | 2160072 | 全部真 |
| Shao/OQ3/SummableAtoms.olean | lane OQ3 | 824760 | 全部真 |
| Shao/Probability/BivariateLegendre.olean | accepted v38 Probability | 68600 | 全部真 |

缺项0是上述13条新视图路径的独立实际结果，不是照抄JSON里的actual13_objects_resolve。Mathlib等其他顶层根不在该view下；保留原Lake搜索条目时findRootWithExt会对这些不同根名继续找到其原目录，不会把Shao视图当作Mathlib根。没有必要为环境修正重跑稳定Mathlib图或旧51对象检查。

未来目标`view/Shao/OQ3/SourceCanonicalRate.olean`当前尚不存在，符合没有成功build的事实；它的父目录samefile为lane既有OQ3输出目录，非严格resolve所得完整未来路径恰为`workspaces/lead-oq3/.lake/build/lib/lean/Shao/OQ3/SourceCanonicalRate.olean`。所以未来按原own输出路径生成目标后，同一个已选择的Shao view根也会看见它；Audit导入本目标无需改选root或把目标写入root目录。本次没有创建该对象或测试其导入。

## 精确绑定与当前验收状态

已针对必要新绑定独立核实：lane和root的BivariateLegendre.lean均4608B，SHA256 `d8bd5dc7099ffdbf52282ebb41ad03145a50b42547dec55bb42caacb31ed5f58`。这只确认本次公共模块源未换，不重新审读其数学实现或稳定依赖。

当前lane实际branch为`feat/oq3-source-canonical-rate`，HEAD为`ffdedd610d0af501c3dd4672cf7f78d80eee543c`，status仅`?? Shao/OQ3/SourceCanonicalRate.lean`。该source本地／remote均99行4662B，SHA256 `cbf43455e2d182fc0a342736d415190c4898878e622f6778c96a7b4e60c7cdae`。仅读hash／大小，没有读取或评论其证明体；它仍为未成功验收的候选，不把新分支正常建立误记为旧153被改写。

正式run/import-view.json实际SHA256 `d060d63c06c0dcd5da7469194ac2016cfd98ed06982c32251acf2eb14c489c20`；其中链接和未来目标路径与独立filesystem观测一致，metadata状态为READ_ONLY_IMPORT_VIEW_METADATA_ONLY_NO_LEAN。它不是Lean成功票。该JSON只用于本次明确授权的环境元数据，未读作者candidate／implementation／future笔记。

实际run当前仅有build-01.log，Audit.lean／Audit.log均不存在；没有build02、成功target或Audit。旧v1终票仍191行21434B，SHA256 `cf2f5e05d4e34c6dc2a4d3fca637092001537bca5aaa9282d08dec804b147270`，旧scope仍535657a9完整SHA；未修改这些历史字节。

## 最终裁决

STATUS: CORRECT

本CORRECT只批准scope74-v2精确SHA下的环境修正声明：两个完整Lean代码块和数学前提未变；单个view/Shao根及其真实符号链接消除了v1按包根首选导致的import阻塞；实际13前置路径、已接受共享源和未来own目标归属均成立。使用条件是最终Lean搜索路径确实使view成为首个Shao根，并保留原Lake／Mathlib等路径；这正是v2的配置，不是新增数学假设。

本门不宣称build02已经通过、作者证明正确或本节点义务已消除。完整target首次实际import／elaboration、proof逐行审查、module-owner全部TYPE／公理和最后机械验收仍待执行。原canonical全局率适配以外的均值映射逆、其他A组装及全部A/B/C/D仍OPEN。

本次只写新v2报告及其授权远端副本；不改源码／scope／旧票／Audit／pins／缓存／视图，不启动Lean／probe／build／smoke，不重算导入图，不新agent／commit／PR。报告前88行5525B盲前缀原字节保留；首部IN_PROGRESS为历史落盘状态，本节CORRECT为最终环境裁决。
