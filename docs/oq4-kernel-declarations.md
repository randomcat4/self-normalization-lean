# KilledKernel 全部新声明清单

最终源SHA256：`f90c1996f4c220473371b0f5ea3c74a7b8287e8f997f1a2cd3f0831cd6bd626f`。

本模块olean生成后，实际import并动态枚举全部15个新常量，对每项执行`#print axioms`。所有公理均在项目白名单内。

## 十项主要声明

| 完整名称（前缀Shao.OQ4） | 作用 |
|---|---|
| `translationKernel` | 确定性起点核与常值ν核乘积后经加法映射的真实Kernel |
| `killedKernel` | 将平移核限制到闭输出区间的真实Kernel定义 |
| `translationKernel_apply` | 每行精确为平移ν像测度 |
| `killedKernel_apply` | 每行精确为平移ν后restrict闭[-h,h] |
| `killedKernel_isFiniteKernel` | 统一有限核实例 |
| `killedKernel_mass_le_one` | 每行ENNReal总质量≤1 |
| `killedKernel_real_mass_le_one` | 每行实总质量≤1，可供平均支付接口实例化 |
| `killedKernel_ae_support` | 每行测度下AE输出|w|≤h |
| `killedKernel_integral_bounded` | 任意有界Borel实测试两侧可积，且积分公式精确成立 |
| `killedKernel_integral_cos` | 每个实频率的余弦测试积分恰为已审Kcos |

这十项的传递公理均为`[propext, Classical.choice, Quot.sound]`。

## 五项自动生成常量

- `Shao.OQ4.killedKernel.eq_1`：`propext, Classical.choice, Quot.sound`。
- `Shao.OQ4.killedKernel.congr_simp`：`propext, Classical.choice, Quot.sound`。
- `Shao.OQ4.killedKernel._proof_1`：`propext, Classical.choice, Quot.sound`。
- `Shao.OQ4.killedKernel_integral_bounded._simp_1_1`：仅`propext`。
- `Shao.OQ4.killedKernel_integral_bounded._simp_1_2`：`propext, Quot.sound`。

没有新增结构或公理。新增有限核实例仅针对本模块的killedKernel对象。枚举按以上十个声明根及全部子名称筛选，排除只读导入依赖；传递公理审计仍包括全部依赖。

服务器完整日志`repro_outputs/oq4-kernel/audit-04-import-all-axioms.log`，exit 0。本清单仅报告作者机械证据，不自签独立语义或数学审稿。
