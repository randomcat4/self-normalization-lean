# AveragedResidual 全部新声明清单

最终源 SHA256：`ffe155446ff31b1f1e20dc6ff1b8dc14b1c5274b2593a4cc774183b053491aa2`。

生成本模块olean后，实际import并动态枚举全部8个新常量，逐项执行`#print axioms`。所有8项的传递公理均恰为`[propext, Classical.choice, Quot.sound]`，全部在项目白名单内。

| 完整名称 | 作用 |
|---|---|
| `Shao.OQ4.cosineResidual` | 用正式Kcos与自由ρ定义残差r(w) |
| `Shao.OQ4.overshootPotential` | 参数超越量期望ψ(w)的定义 |
| `Shao.OQ4.measurable_Kcos` | 由二元可测核和参数积分定理得到Kcos对w可测 |
| `Shao.OQ4.measurable_overshootPotential` | 由二元连续核得到ψ对w可测 |
| `Shao.OQ4.integrable_overshoot_integrand` | 每个固定h,w处的ν超越核可积，只有一阶矩前提 |
| `Shao.OQ4.integrable_abs_cosineResidual` | 显式证明有界核ν可积和全局|r|≤2，从而任意有限κ下|r|可积 |
| `Shao.OQ4.averaged_cosine_residual_bound` | 完整冻结v2主声明；κ仅AE支持/子概率，给出可积性及两个精确上界 |
| `Shao.OQ4.cosineResidual.eq_1` | 自动生成定义方程 |

主声明内部还实际证明ψ对κ可积、各层系数可积/非负、层上界、有限层支付、R6有限期望支付以及I≤1+β；这些局部证明没有新增全局假设或独立常量。

没有新增结构、实例或公理。动态枚举按以上七个声明根及其全部子名称筛选，排除只读导入依赖，但传递公理审计仍包含这些依赖。

完整日志：服务器`repro_outputs/oq4-averaged/audit-06-import-all-axioms.log`，exit 0。本文仅报告作者机械证据，不自签独立审稿。
