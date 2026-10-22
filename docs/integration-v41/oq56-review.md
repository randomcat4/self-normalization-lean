# PR165：root 新鲜独立完整验收

STATUS: **CORRECT**。未发现关键缺口。仅接受 `Shao/OQ5/P53/SparseLabelLaw.lean` 的 **1定义、13公开定理、2 authored private helpers 与8生成声明**。原 P53/OQ6/RS2 仍 **OPEN**；不增加原根闭合或新颖性声明。root 与共享Ξ导数的服务器组装门仍待执行，本票不宣称完整集成已通过。

## 精确身份与边界

- PR：[165](https://github.com/randomcat4/shao-lean/pull/165)。只读 GitHub API 当场确认 OPEN、未合并、head `0ae4899501fde890587004e5112a0a0d102820e3`。
- 精确提交树 `82b2c1ef6dbe60053ea610f8ac073546d09666c1`，唯一父提交 main `5591a25ddc767e6edfd618a88855075c2af7e375`，即 v40；accepted `dc1604d8e9c88781166a0c797f45b84ff013673a`。
- 用 `git show` 读取精确 head，并未依赖已续作的作者工作树 HEAD。对父提交差异恰4新增文件、320行、0删除：1源码+3文档。
- 源 SHA256 `6f5767747a5c294beaf2b77d46c41d976bd6ace6aaab95f602944ddc7b456c57`，8195 bytes、194行，UTF8/noBOM/noCR/恰1末LF。Git blob `840d1e50725445d56e8238c3a9953df3febf2b34`。保留对象 SHA `1a009316f274b511230dd3a7cf43c8deccb7a5263cf454409b1ce4bd98e83f34`。
- 本地根目录 `unit100/SparseLabelLaw.lean` 是 warning01 历史初稿（8197B、5b2ac675…）；最终镜像仅 `proof-repair-02/SparseLabelLaw.lean`。最终镜像、合同保存的完整源码、精确 Git blob 与实际审计前8195字节相同。

本实例读取 AGENTS.md、SERVER.md、TEAM.md、math-theorem 及其验证协议、OQ56最新状态、直接原p53/p45、完整正式冻结、SOURCE/作者/独立FINAL报告及承重证据。全部新源码与两个私有证明完整人工审读。只写本报告及配套JSON；没有运行Lean、重放旧门、修改源码/对象/缓存、发布/合并或spawn。

## 原文到声明

直接原 `p53.md` SHA `0bfadbb2021248859f8b15df2ff184c73c879a7203991c27fdc4f5dd6c04f561`（5686B）；`p45.md` SHA `0b799637356615cfb18a9fef016c11d682aeefde314106e0b56eb46a853c09ca`（10799B）。p53§2先按固定α和完整x选择同一N，§3取样前固定标签概率，§4消费qj=P(B<j)、完整高层Hj与原Nat背景指数。本模块恰支付单标签测度义务；没有把p45条件代数当实际概率结论。

前驱实际定义保留 δ=3α/(8−2α)、slow的min/rpow、t/d及π的零层总化、m0=1−Σπ、正层mj=πj、Hj=Σkπ(j+k)、bj=Σk<j mk。Core的完整三个外层let及successor let未截断，仍包含N0=1、2^j≤Nj、逐步2Nm<Nj、4≤Nj、x/slow/t/d正性、幅度/移位界及两质量成本约束。exists Core才需0<α<1和原两极限；100概率/原子/前缀/真实L1及无成本两极限适用于任意α/x/N。没有隐含γ或附加参数、没有自由替代分布、没有x单调或样本尾结论假设。两项成本极限恰保留同一 Core。

零层：π0=0与残余m0≥3/4不同，μ(Iio0)=0而μ(Ici0)=1；H0只是正层总质量≤1/4，故两个Ici恒等式的1≤j是必要前提且未删除。两高层极限通过最终j≥1转移。背景指数仍是Nat `2 * (N j - 2)`；Core下j0的N0=1、0^0总化不影响atTop极限。

真实L1是Σ mj‖fj‖可和，包含残余零原子。积分结论显式保留并使用hf:Integrable，没有默认未可积积分或默认不可和tsum捷径。后续t/d矩、joint law及实际事件必须另证。

## 全部实际证明逐项裁决

以下行号均来自精确 head 的194行源码；16完整声明块、header/body/block SHA均在JSON，逐字与源码对照。

| 声明 | 源行 | 审查结论 |
|---|---|---|
| `sparseLabelMeasure` | 14–15 | 一个真实 Measure ℕ，字面为 Σj ofReal(mj)•δj；m 来自既有 sparseLabelMass，保留残余零原子，α/x/N 一次固定，不含样本量、q、τ。 |
| `sparseLabelMeasure_probability` | 17–22 | 对任意 α/x/N，直接用 m≥0 和真实 HasSum m 1 调用 HasSum.isProbabilityMeasure_sum_dirac；概率是已证 theorem 值，无循环概率假设。 |
| `sparseLabelMeasure_singleton` | 24–28 | Nat 标准可测单点满足 sum_smul_dirac_singleton；所有 j（含0）给出实际原子质量。 |
| `sparseLabelMeasure_real_singleton` | 30–35 | 展开 Measure.real=toReal，m≥0 支付 toReal_ofReal；没有从 toReal=0 倒推有限性。 |
| `label_prior_nonneg` | 37–40 | 私有证明将 b 展为真实非负 m 的有限前缀和，对 j=0 仍成立。 |
| `sparseLabelMeasure_Iio` | 42–61 | 逐点 range j=Iio j，实际有限单点求和，再用逐项非负的 ofReal_sum_of_nonneg；包含残余零原子。 |
| `sparseLabelMeasure_real_Iio` | 63–68 | 用私有 b≥0 将有限前缀公式取 toReal；全 j 有效，Iio0=∅ 且 b0=0。 |
| `label_real_Ici` | 70–83 | 私有证明只设置实际 μ 的局部概率 witness；Nat-top 支付 Iio 可测性，其补集恰为 Ici；实概率互补与 b=1−H 的 hj:1≤j 推得真实高层质量。 |
| `sparseLabelMeasure_Ici` | 85–98 | 先由概率→有限测度支付 μ(Ici j)≠∞，再用 ofReal_toReal，最后套私有实高层身份；1≤j 未删除。 |
| `sparseLabelMeasure_real_Ici` | 100–105 | 在相同 1≤j 域复用私有证明；未错误扩张至 Ici0。 |
| `integrable_sparseLabelMeasure_iff` | 107–122 | 对所有 f:ℕ→ℝ，以 c=ofReal(m) 的逐项有限性调用 integrable_sum_dirac_iff；另用 m≥0 恢复 c.toReal=m，保留完整 weighted norm Summable。 |
| `integral_sparseLabelMeasure` | 124–138 | 实际引入 hf:Integrable 并交给 integral_countable；改写真实单点质量及实 smul 为乘法，未使用默认未可积积分或不可和 tsum。 |
| `tendsto_sparseLabelMeasure_high_mass_zero` | 140–150 | 仅在最终 j≥1 识别 Ici=H，依正确方向的 Tendsto.congr′ 消费99 H→0；无Core。 |
| `tendsto_sparseLabelMeasure_high_mass_cost_zero` | 152–166 | 同一 N、同一 Core，最终 j≥1 后将 Ici=H 乘 (N j:ℝ)，消费99 NjHj→0。 |
| `tendsto_sparseLabelMeasure_low_mass_one` | 168–177 | 全 j 的真实 Iio=b 逐点转移99 b→1；无Core。 |
| `tendsto_sparseLabelMeasure_background_power_one` | 179–192 | 同一 Core、同一 N，将全 j 的 Iio=b 代入原 Nat 指数2*(N j−2)，消费99背景幂→1；未改为实数减法或加入事件概率假设。 |

## 官方条件与已接受依赖

已实读全部24 SOURCE完整类型、61 DEP实际loaded full heads，其中22个官方完整作用域。`integrable_sum_dirac_iff`需要Countable指标、NormedAddCommGroup、可测单点及每个c≠∞；取ℕ/ℝ，ofReal_ne_top支付有限性，m≥0另支付toReal恢复。`integral_countable`另需实NormedSpace/CompleteSpace及真正hf，均在实际调用满足。Nat的literal-top测度空间支付Iio可测和单点可测。概率补集公式使用真实局部概率witness；反向ofReal_toReal先从概率→finite取得集合质量≠∞。未把正向非负条件与反向有限条件混用。Tendsto.congr′的eventual equality方向及eventually_ge_atTop作用域均匹配。

五个项目源码（100→99→98→97→96）的**精确head blob SHA**与既有接受记录逐项相同，其5个缓存对象当场只读hash亦相同；2个版本pin相同。四个旧compiled依赖不重建。实际源码及对象hash全列JSON。Lean pin `leanprover/lean4:v4.36.0-rc1`，Mathlib `807d3836b165983210ee2ecf3cd28f239436949c`。39前驱完整接口与16字面体rfl（15旧体+当前measure）已由独立fresh prefix检查，不偷加目标结论到前驱。

## 原始日志、类型、公理真实性关联

本实例用只读broker直接重读远端既有prefix原始receipt/stdout，独立重新解析所有109 JSON记录，不靠报告中的计数。SOURCE24、DEPENDENCY61、LATE24；85唯一**结构化Name**，保留quoted str与num组件。109条公理和Name逐项等于canonical；48份SOURCE/LATE raw full types与清单逐项去空白相同，61份完整DEP loaded heads在实际stdout逐项吻合。SOURCE与LATE一致、无新增/缺失、没有imported-lazy或附录新增声明。24所属=14public+2private+8generated；生成项完整类型亦已读。fresh-prefix私有模块前缀仅属于本次重elaborate环境，没有冒充目标对象的私有前缀。

传递公理仅 `propext`、`Classical.choice`、`Quot.sound`。109次分布97×三项、10×propext、2×propext+Quot.sound；85唯一名分布78/5/2。源码无sorry/admit/new axiom/unsafe/native_decide；唯一option是autoImplicit false，没有linter、资源或内核抑制。

完整14冻结raw、实际13theorem headers与唯一字面definition逐字相等；正式冻结与FINAL附录两份MD中的14个Lean fence也相同。正式合同字典SHA `7591ed911f7d54f44ab80de407f3b9027bbea0e82a98b8f92c8cb0e41196e1be`。measure字面body SHA `ffd9954d84f19ffb48f4e4faf82e891d9db31c3cb00297dca9c6c2eaaecbc370`。本次重算24 SOURCE full-type bundle SHA `c2b3fd83603567a075afae7809f4147c3cba90d395fb70a335be848885b72ec6`（序列和序列化精确定义在JSON）。此typehash与完整源码prefix/log关联，不是仅给名称打hash。

| 既有实际Lean调用 | 结果 | raw receipt SHA256 |
|---|---|---|
| author01 | exit0，2条letI style warnings，3.813981360s | `5fa8e85b784f3113d7cce757a9308b51247272e5ef9738eba89bdf6f92f3591e` |
| author02 | 仅两proof-body letI→let，clean，3.742923415s | `9643bc6107ace4afe8a8694736d1f8f5f5da578df1c364c85be893b2fafa9c4e` |
| independent target | once/no-o，exit0，stdout/stderr EMPTY，4.448320714756846s | `57171edb3b2f98f282b674ffd16840a4e3cf879ab0371525118fd3dbd053929b` |
| independent exact prefix | first clean，exit0，8.056111896410584s | `02ace1fcf9de8cfca9db0ca1cfdc2b4558638a1c9f774f318cd77447f54a3e05` |

目标receipt input绑定源6f576774…；prefix input绑定audit `c05c9267a00d34b52421617724eae7474fd67c96f9a4728f7b679b25596381f2`（35479B），audit前8195字节逐字等于当前精确head。prefix stdout SHA `1daa269dd18c52c1bd4fdfa9d6d0c01c9bac0583e20bcc94dba41a94b740108e`（416551B）。目标与父target/prefix的before/after已独立比较相等；原raw/父receipt/保全对象相互链接。四次Lean共0 kernel errors；作者早期2 warnings及所有非Lean控制/报告解析失败保留，不当clean证据。所有Lean已永久STOP，heavy释放SHA `d5f87d2b8c9d4c6c0ba48ab19ddafbfebb3c42b1301a4881040067378a7da068`。

本次复用的是已完成的 **模块 LEAN_FULLY_CHECKED** 机械证据，且独立复核了其源码/日志/type关联；本实例新增Lean调用数为0。既有lead完整255物理records/roles及260当前records保全接受已核对其seal，本票只定向重读关键证据和实际承重文件，不重复所有历史metadata或1724整表。

## 证据指纹与发布内容

| 本地镜像证据 | SHA256 | bytes |
|---|---|---|
| frozen-v1.md | `a8ae147487c05db9b2c0542ae9459703bc7776703e761ed8d0a64b01c4c703a5` | 5758 |
| frozen-contracts.json | `0eb9b770afedd2f0971eb08156c5eda65dbf3d955f7c9810c96dd994adf100c8` | 8621 |
| semantic-review.md | `4a7385ae18dfeaf0ca81b17dca8c03fc58cafe461b5a69fe2c05dcddd7ba1863` | 30332 |
| author-report.md | `3c1047468756f0063195fa445df054d908ad752192a4ba6a260a7d643a3075a6` | 14011 |
| author-report.json | `799351660bcb7381749487f760acf176655260d68b72d61708b08226edb323f2` | 60734 |
| proof-review.md | `e73db54669337cb2869c3c25d61c88214c73b80b2f17524be11a47c5aebecdfd` | 17406 |
| review-final.json | `6950a7a9a94d81432abbc006497fe9721ca7dacabe021353431017b53b2219bc` | 24001 |
| review-actual-canonical-reviewed.json | `4a5103cfaae7e9dcad9633e56928c21a48198deb5fddbedd21b6bc56bf6fc324` | 138325 |
| review-final-contract-current.json | `5129ead2555e7445f1c0165912cb8972681ef1813c774fedf58970f93edae307` | 145226 |
| review-final-integrity-manifest.json | `24be79b4e93ffa3542ddacde938552d8abef92835614e3c708b1bcfcd4170ecf` | 190890 |
| lead-final-acceptance.json | `af5dd067c1e631a8c63564b49c3e265e329e36ebbcfa3c7df12aeb5238c3d6db` | 161496 |
| review-ExactSourceAudit.lean | `c05c9267a00d34b52421617724eae7474fd67c96f9a4728f7b679b25596381f2` | 35479 |

三发布文档SHA分别为 frozen `3741416d51c629bcf3a9e3adf36877b847f2fc17a13fc8aa3889ca6745f84a61`、review `1a3d67c92c26a38e686d1eaddd1ae18a02c418d1d4762e55b514d6054042c370`、scope `f80419eed0c6e8df46b5a75dd17743fc7980edb077f87c260f943d48cc2b4395`。三者均直接从精确head全文读过；frozen列全14合同，review保留四次检查及警告，scope明确原根OPEN，与实际结果相符。

## 完整14公开冻结合同

```lean
def sparseLabelMeasure (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) : Measure ℕ :=
  Measure.sum fun j : ℕ => ENNReal.ofReal (sparseLabelMass α x N j) • Measure.dirac j
```

```lean
theorem sparseLabelMeasure_probability :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ),
  IsProbabilityMeasure (sparseLabelMeasure α x N)
```

```lean
theorem sparseLabelMeasure_singleton :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) (j : ℕ),
  sparseLabelMeasure α x N {j} = ENNReal.ofReal (sparseLabelMass α x N j)
```

```lean
theorem sparseLabelMeasure_real_singleton :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) (j : ℕ),
  (sparseLabelMeasure α x N).real {j} = sparseLabelMass α x N j
```

```lean
theorem sparseLabelMeasure_Iio :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) (j : ℕ),
  sparseLabelMeasure α x N (Set.Iio j) = ENNReal.ofReal (sparsePriorMass α x N j)
```

```lean
theorem sparseLabelMeasure_real_Iio :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) (j : ℕ),
  (sparseLabelMeasure α x N).real (Set.Iio j) = sparsePriorMass α x N j
```

```lean
theorem sparseLabelMeasure_Ici :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) (j : ℕ),
  1 ≤ j →
  sparseLabelMeasure α x N (Set.Ici j) = ENNReal.ofReal (sparseHighMass α x N j)
```

```lean
theorem sparseLabelMeasure_real_Ici :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) (j : ℕ),
  1 ≤ j →
  (sparseLabelMeasure α x N).real (Set.Ici j) = sparseHighMass α x N j
```

```lean
theorem integrable_sparseLabelMeasure_iff :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) (f : ℕ → ℝ),
  Integrable f (sparseLabelMeasure α x N) ↔
    Summable (fun j : ℕ => sparseLabelMass α x N j * ‖f j‖)
```

```lean
theorem integral_sparseLabelMeasure :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) (f : ℕ → ℝ),
  Integrable f (sparseLabelMeasure α x N) →
  (∫ j, f j ∂(sparseLabelMeasure α x N)) =
    ∑' j : ℕ, sparseLabelMass α x N j * f j
```

```lean
theorem tendsto_sparseLabelMeasure_high_mass_zero :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ),
  Tendsto (fun j : ℕ => (sparseLabelMeasure α x N).real (Set.Ici j))
    atTop (nhds 0)
```

```lean
theorem tendsto_sparseLabelMeasure_high_mass_cost_zero :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ),
  SparseSelectionCore α x N →
  Tendsto (fun j : ℕ => (N j : ℝ) *
    (sparseLabelMeasure α x N).real (Set.Ici j))
    atTop (nhds 0)
```

```lean
theorem tendsto_sparseLabelMeasure_low_mass_one :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ),
  Tendsto (fun j : ℕ => (sparseLabelMeasure α x N).real (Set.Iio j))
    atTop (nhds 1)
```

```lean
theorem tendsto_sparseLabelMeasure_background_power_one :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ),
  SparseSelectionCore α x N →
  Tendsto (fun j : ℕ => ((sparseLabelMeasure α x N).real (Set.Iio j)) ^ (2 * (N j - 2)))
    atTop (nhds 1)
```

## 最终范围

CORRECT，无需修改冻结前提或证明。可供root按精确head组装验收。共享Ξ导数合并后的组装编译/整库公理/覆盖门由root另付，本票不代替该门。尚未支付B/C独立副本与符号/连续噪声、whole iid实观测/编码、feature矩和指数预算、实际秩一余项算子、TRUE分母正性/条件统计、平衡事件精确概率及最终尾。P53/OQ6/RS2保持OPEN。COMPLETE / STOP。
