# LaplaceTail 全声明清单

实际按所属模块索引枚举：29 项 = 23 项显式声明（4 个定义、19 个定理）+ 6 个生成辅助声明。未用命名空间或根名称前缀筛选。

每项均实际运行 `#print axioms`；29 条记录与29个模块所属常量逐项同名匹配。公理集均为 `{propext, Classical.choice, Quot.sound}` 的子集，实际25项为三者全体、4项仅 `propext`；没有意外公理。原始逐项输出仅在服务器 `repro_outputs/oq4-laplace/audit.log`。

## 显式声明

- `Shao.OQ4.positiveLaplace`
- `Shao.OQ4.laplacePayment`
- `Shao.OQ4.laplaceWeight`
- `Shao.OQ4.positiveLaplace_bounds`
- `Shao.OQ4.integrable_positiveLaplace`
- `Shao.OQ4.laplacePayment_bounds`
- `Shao.OQ4.laplaceWeight_nonneg`
- `Shao.OQ4.measurable_strictTail`
- `Shao.OQ4.integrable_laplaceWeight`
- `Shao.OQ4.integral_laplaceWeight`
- `Shao.OQ4.integrable_laplaceTail`
- `Shao.OQ4.laplaceWeight_primitive`
- `Shao.OQ4.laplacePayment_eq_strictTail`
- `Shao.OQ4.standardGaussian_positive_mass`
- `Shao.OQ4.standardNormalCDF_zero`
- `Shao.OQ4.integrable_mul_laplaceWeight`
- `Shao.OQ4.integral_mul_laplaceWeight`
- `Shao.OQ4.strictTail_lower_bound_of_cdf`
- `Shao.OQ4.laplacePayment_lower_bound_of_cdf`
- `Shao.OQ4.finiteSumLaplacePayment`
- `Shao.OQ4.iid_integrable_positiveLaplace`
- `Shao.OQ4.finiteSumLaplacePayment_bounds`
- `Shao.OQ4.finiteSumLaplacePayment_lower_bound_of_cdf`

## 生成声明

- `Shao.OQ4.laplacePayment_eq_strictTail._simp_1_1`
- `Shao.OQ4.laplacePayment_eq_strictTail._simp_1_2`
- `Shao.OQ4.standardGaussian_positive_mass._simp_1_1`
- `Shao.OQ4.standardGaussian_positive_mass._simp_1_2`
- `Shao.OQ4.standardGaussian_positive_mass._simp_1_3`
- `Shao.OQ4.standardGaussian_positive_mass._simp_1_4`

审计方式：`env.getModuleIdxFor? name` 对应的 `env.header.moduleNames[idx] == Shao.OQ4.LaplaceTail`。该方式也覆盖对导入名称生成的辅助常量；本模块实际未生成此类跨根名辅助项。

源 SHA256：`
664df6aa0c3221b9a0212580a20b141b7f0a0eea1d8adbeb4af15d486dcf68e2
`。

本清单是作者的机械收据，不是独立数学或形式审查票。

格式维护历史：原源 SHA `5ceb63a9c3955f8479b6c0def43e9c2fdeb9ac2f915aa23553cb2243c3f8ffb9` → 当前源 SHA `664df6aa0c3221b9a0212580a20b141b7f0a0eea1d8adbeb4af15d486dcf68e2`。仅将5处 CRLF 改为 LF，并删末尾4个空行，保留单个最终 LF；15121→15112字节，代码token不变。旧源完整副本保存在 server `repro_outputs/oq4-laplace/LaplaceTail.before-format-5ceb.lean`；旧summary另存本机 `summary-before-format.json` 及server同名历史文件。实际重新目标/唯一olean/moduleidx 29项审计均 exit0，前两者日志为空；olean哈希不变。新原始日志分别为 `formatTarget.log`、`formatOlean.log`、`formatAudit.log`。匿名proof原始snapshot与旧独立票未修改。
