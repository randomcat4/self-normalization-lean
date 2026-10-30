# 独立主 API 来源和精确接口消费

全部下列文件均是 ACT 的 119 个已验证输入之一。Mathlib 的固定提交为 `807d3836b165983210ee2ecf3cd28f239436949c`；原始绑定 JSON 已读，哈希与本地完整原始文件一致。本审稿人没有联网、探测 API 或运行 Lean。这里的原始源码阅读只核对使用的主 API，不声称重新证明 Mathlib。

| 原始输入 | 实际完整阅读范围 | 本候选消费与条件核对 |
|---|---|---|
| unit283/parent-api-01/.../Measure/Prod.lean | 1–70，165–224，393–451 | `Measure.ae_ae_of_ae_prod` 的完整 HEAD/body，SFinite 右因子环境；μ 概率满足。仅使用产品 a.e. 到截面 a.e. 的方向。 |
| unit283/parent-api-02/.../Constructions/Pi.lean | 1–86，125–127，276–438 | `quasiMeasurePreserving_eval`、`pi_of_empty`、`pi_univ` 的完整 HEAD/body 和有限/σ 有限环境。η 的有限性明确证明；空积在定理内部消去空域上的 σ 有限要求；T04 零因子 σ 有限。 |
| unit283/parent-api-04/.../Measure/Restrict.lean | 1–72，229–251，626–657 | 完整 `restrict_eq_zero` 和 `ae_restrict_mem`；前者不要求集合可测，后者由 C/Cᶜ 可测供给。 |
| unit283/parent-api-04/.../Measure/Module.lean | 1–56，176–198 | `ae_smul_measure` 正向对任意标量成立；没有使用需标量非零的 iff。 |
| unit283/parent-api-05/.../ConditionalProbability.lean | 1–185 | 实际 `cond=(μ s)⁻¹ • μ.restrict s`；`cond_isProbabilityMeasure` 需原 μ 有限和 μs≠0；`cond_absolutelyContinuous` 无非零要求。 |
| unit284/parent-api-01/.../L1Space/Integrable.lean | 1–168，395–490，525–541，1009–1042 | 完整 `mono'`、`congr`、`integrable_zero`、有限和、常数/加减/常乘接口。主函数为 ell²*w²，平方 norm 等于其自身；中心常数只在 ν 概率分支用可积性。 |
| unit284/parent-api-01/.../L2Space.lean | 1–119 | 完整 `MemLp.integrable_sq`、`memLp_two_iff_integrable_sq`；实值可测函数的 a.e. 强可测由实数值域供给，不要求 Ω 有拓扑。 |
| unit284/parent-api-02/.../Group/Arithmetic.lean | 1–85，783–849 | `Finset.measurable_fun_prod` 的 to_additive 生成源及定义环境，得到候选使用的 `measurable_fun_sum`；实数为可测加法交换幺半群。 |
| unit284/parent-api-02/.../Bochner/Basic.lean | 1–21，139–305，615–706，968–1010 | 完整有限和积分、加减、常乘、a.e. congr、非负积分、a.e. 单调、常数积分和常数范数上界。所有需要的可积前提由 hci/hsq/中心平方构造逐项供给；ν 为概率用于 μ.real univ=1。 |
| unit284/parent-api-03/.../Order/BigOperators/Group/Finset.lean | 1–41，360–380 | 完整 `abs_sum_le_sum_abs` 与加法交换群/线序/有序加法条件；实数满足。 |
| unit284/parent-api-03/.../BigOperators/Group/Finset/Basic.lean | 1–112，429–484 | 完整 `prod_coe_sort` 生成的 `sum_coe_sort`，含 variable(f s) 的实际参数顺序；T05 以 Finset 在前、函数在后调用正确。 |
| unit284/parent-api-04/.../BigOperators/Ring/Finset.lean | 1–78 | 完整 `sum_mul`/`mul_sum`，NonUnitalNonAssocSemiring 环境；提取实数常量合法。 |
| unit284/parent-api-04/.../Group/Finset/Defs.lean | 1–70，645–690 | 完整 `prod_inv_distrib` 的 to_additive 生成源得 `sum_neg_distrib`，DivisionCommMonoid 对应的加法交换群由实数满足。 |
| unit284/parent-api-04/.../Group/Finset/Sigma.lean | 1–134 | 完整 `prod_comm` 的 to_additive `sum_comm`，有限双和交换保留 r(xa,xi) 两参数方向。 |

T01 的其余基础运算是实数平方非负、非负乘法单调、绝对值三角、有限和非负/单调及 ring/linarith 代数。这些步骤的每个数学前提均在 REPORT/PROOF-COVERAGE 中核对；本件不将无运行的静态检查表述为 API 编译成功。

## 176 精确实际公共类型

容器 SHA256 `8a2a3b79f518b8fe2a6935dfd53e6f1417f11fd0937a2772e50ca30e1fcf58dc`，241348 字节。公共名 `Shao.OQ6.ConditionalVarianceMean.actual_conditional_variance_mean`。实际 TYPE SHA256 `fb0aa27d11246907aa1f47eb8be5f351bcf7629a584fe955a2b5a4053216b905`，237079 字节，2201 显示行、2200 LF。完整阅读顺序 1–290、291–800、801–1500、1501–2201；重复行正文用早先完整正文加精确缩进表示，8 个大小写折叠差异（255/299/937/1185/1212/1290/1435/1602）已逐一取原文复核，尤其 G/g 与 B/b 未混淆。READ-COVERAGE 记录这种显示方式而不声称 TYPE 源字节被改写。

与本候选承重相关的实际 TYPE：1–156 全部原全局前提；157–165 原 g 和 r；217–278 cutoff 与 lam、C/π/d/ν/b/c；316–454 ν 概率/绝对连续、g 可测及原矩；455–587 w 在 μ/ν 的 L2 和 ν 平方积分≤W2²/d；645–724 是原 μ-a.e. `Integrable(r o) μ ∧ Integrable(r o) ν ∧ integralν(r o)=-(integralCᶜ(r o))/d ∧ |integralν(r o)|≤c*w o`。其后 725–2201 完整已读但未将 H/G/σ²/均值或方差近似引入本候选。所有显式实例均为相同 Ω 可测结构和实数结构，没有隐藏 StandardBorel 假设。

已 qualified 源 `78762108ee542e89ea114a5f4047c53cad464a385e58ec7c20fd49a37537cbb8` 与首原对象 `2296aafb7853a96b11f01506dd97efbd047a0c89e45a277ba68897641ad56c4b` 匹配，原独立审稿和同首对象内核/全实际所有者传递公理 RC0 复用。该公共接口不是本角色新生成的机器记录。

## 278 三个精确实际定义

容器 `qualified278-selected-complete-TYPE-VALUE.json` SHA256 `8f43c52e1ffb63e0719ad3f5befe5e2a798d005d81bdc3b31457e4f820a1bef2`，6102 字节。三个定义的全部实际 TYPE 和 FULLVALUE 共 6/11 显示行（逐项原元数据 2+2+2 / 3+4+4）均完整阅读，连同 rawOwnedJSON、实际名字组件、defnInfo 和传递公理字段。

| 定义 | 实际 TYPE SHA256 | 实际 FULLVALUE SHA256 | 精确含义 |
|---|---|---|---|
| anomaly | 625e2d2ea0c5bfd7bec0573c49842f4aa51cf6e160d73342e8a0b034c68e033a | dea46567de20182227a42c140f39bba22c4aa5e7ef4e46603a230cbf6d37b101 | Fin n 上 univ\B，固定 n 的补集。 |
| anomalyWeight | d73c2c1bccd4de508845b66a4cfcd775cc72dbc61ee1e1ded762a6f3e00f3b93 | ad6068c7e315935aec2820b55a0df2755d1c6cca2c8774b788ff1895523b4853 | 对 anomaly B 的原 w 有限和。 |
| crossPairSum | 87762428883f0625c520a866ea6863c658f96dfea27ed73f9c2936108a2f1867 | 89fce930366d9c0a7e9eeadae84c86a7a5f9fdc1a4e5e5c7e7ae90a56fa5f6f3 | 外层 a∈anomaly B，内层 i∈B，r a i。 |

源 `8481562684fc7a3c5455e8ab99d6f85b15f4778860fa414da93099b83b4adcb8` 与首原对象 `fbd3913b99528f0e63e8301180570ff9c7c0b95af37a4eff6509e9e52003149c` 和 qualified278 包一致。对已接受供应证明的复用不代表重新执行、重新认证其全部证明，也不声称当前 unit284 的所有实际定义值已产生。
