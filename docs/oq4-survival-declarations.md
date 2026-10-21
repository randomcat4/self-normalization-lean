# FiniteSurvivalLaplace 全声明机械清单

当前源SHA256：`49241958f2ae692b56db5fe0aa021a5e88b0020ac6487ddb463d05efb69518cb`。

已在实际同时import全部21个OQ4模块的环境中，按所属moduleidx枚举30个新常量 = 28显式（4定义、24定理）+ 2生成；30条传递公理记录逐项同名匹配，未用namespace或根名筛选。

每个常量的完整传递公理集均仅 `{propext, Classical.choice, Quot.sound}`。原始逐项输出仅在server `repro_outputs/oq4-survival/namefixAudit.log`。

## 显式声明

- `Shao.OQ4.maxLaplaceIntegrand`
- `Shao.OQ4.endpointLaplaceIntegrand`
- `Shao.OQ4.maxLaplaceMean`
- `Shao.OQ4.endpointLaplaceMean`
- `Shao.OQ4.measurable_maxLaplaceIntegrand`
- `Shao.OQ4.measurable_endpointLaplaceIntegrand`
- `Shao.OQ4.maxLaplaceIntegrand_bounds`
- `Shao.OQ4.endpointLaplaceIntegrand_bounds`
- `Shao.OQ4.integrable_maxLaplaceIntegrand`
- `Shao.OQ4.integrable_endpointLaplaceIntegrand`
- `Shao.OQ4.maxLaplaceMean_bounds`
- `Shao.OQ4.endpointLaplaceMean_bounds`
- `Shao.OQ4.maxWithZero_empty`
- `Shao.OQ4.maxLaplaceMean_zero`
- `Shao.OQ4.finiteSumLaplacePayment_eq_one_sub_endpoint`
- `Shao.OQ4.prefix_projection_map_pi`
- `Shao.OQ4.prefix_projection_prefixSum`
- `Shao.OQ4.prefix_projection_max_le`
- `Shao.OQ4.measurable_paymentLaplaceIntegrand`
- `Shao.OQ4.maxLaplaceMean_antitone`
- `Shao.OQ4.summable_maxLaplace_series`
- `Shao.OQ4.summable_endpointLaplace_series`
- `Shao.OQ4.summable_paymentLaplace_series`
- `Shao.OQ4.maxLaplace_original_sp_to_normalized`
- `Shao.OQ4.maxLaplaceMean_bound_of_cdf_and_original_sp`
- `Shao.OQ4.measurableSet_closedUpper_laplace`
- `Shao.OQ4.closedUpper_probability_le_laplace`
- `Shao.OQ4.closedUpper_bound_of_cdf_and_original_sp`

## 生成声明

- `Shao.OQ4.maxLaplaceIntegrand.eq_1`
- `Shao.OQ4.maxLaplaceMean.eq_1`

名称修复历史：旧63f候选的Shao.OQ4.measurableSet_closedUpper与已接受BoundaryOccupation同名，standalone检查未能发现共存冲突，已撤回旧候选。当前仅将本新helper和1处内部调用改为measurableSet_closedUpper_laplace；旧Boundary API未改。数学前提、结论和proof语义不变。旧源/summary/Audit/收据与原始log保留历史。

审计方式：env.getModuleIdxFor?对应env.header.moduleNames[idx]==Shao.OQ4.FiniteSurvivalLaplace，覆盖任何跨常量namespace生成helper。本模块生成项只有上述2个自身定义方程。此文件为作者机械收据，不是独立审查票。
