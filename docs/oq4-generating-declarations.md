# LaplaceGenerating 全声明机械清单

源SHA256：`eab53afb87248fc0f9b94ddf84e986eedae51f2446e9b7ea176e517c4a861ed8`。

按所属moduleidx实际枚举25个新常量 = 15显式（2定义、13定理）+ 10生成。25条传递公理输出与25个所属模块常量逐项同名匹配，未按命名空间或根名过滤。

公理集均为 `{propext, Classical.choice, Quot.sound}` 的子集；实际18项为三者、6项仅propext、1项为propext与Quot.sound，没有意外公理。完整逐项原始输出仅保留服务器 `repro_outputs/oq4-generating/audit.log`。

## 显式声明

- `Shao.OQ4.laplaceW`
- `Shao.OQ4.laplaceG`
- `Shao.OQ4.summable_laplaceW`
- `Shao.OQ4.summable_laplaceG`
- `Shao.OQ4.exp_neg_reciprocal_gap`
- `Shao.OQ4.generating_upper_of_W_lower`
- `Shao.OQ4.antitone_coefficient_bound_of_generating_bound`
- `Shao.OQ4.reciprocal_log_step`
- `Shao.OQ4.finite_harmonic_log_bound`
- `Shao.OQ4.sqrt_reciprocal_step`
- `Shao.OQ4.finite_sqrt_tail_bound`
- `Shao.OQ4.reciprocal_sqrt_tail`
- `Shao.OQ4.laplaceW_lower_bound`
- `Shao.OQ4.laplaceG_upper_bound`
- `Shao.OQ4.laplace_coefficient_bound`

## 生成声明

- `Shao.OQ4.laplaceW_lower_bound._proof_1_1`
- `Shao.OQ4.laplaceW_lower_bound._proof_1_2`
- `Shao.OQ4.sqrt_reciprocal_step._simp_1_1`
- `Shao.OQ4.sqrt_reciprocal_step._simp_1_2`
- `Shao.OQ4.sqrt_reciprocal_step._simp_1_3`
- `Shao.OQ4.sqrt_reciprocal_step._simp_1_4`
- `Shao.OQ4.sqrt_reciprocal_step._simp_1_5`
- `Shao.OQ4.sqrt_reciprocal_step._simp_1_6`
- `Shao.OQ4.sqrt_reciprocal_step._simp_1_7`
- `Shao.OQ4.summable_laplaceW._proof_1_1`

方法：`env.getModuleIdxFor? name` → `env.header.moduleNames[idx] == Shao.OQ4.LaplaceGenerating`。该方法覆盖任何生成在导入名称下的helper，本模块实际未出现这种跨根名项。

本清单为作者机械收据，不是独立数学或形式审查票。
