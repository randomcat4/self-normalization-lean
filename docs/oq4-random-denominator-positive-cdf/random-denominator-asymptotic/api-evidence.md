# 固定版本直接接口证据与实现边界

本文件记录作者177直接读取的主要来源和精确消费者计划，不是编译、旧证明复审或形式资格收据。数学和声明提案分别为 `proof.md` 与 `declarations.lean.txt`。全部写入仅限本目录。读取 math-theorem 的主技能及 prompt-library/openai-workflow/lean-verification；使用中文输出约定，并读 Windows UTF-8守则。项目与父指令禁止本轮本地/服务器Lean、解析器、测试、Git、缓存和安装，故未执行这些操作；通用技能的机械核验建议不覆盖本轮明确的提案权限。

## 1. 版本、所有权与只读来源

已读 AGENTS.md、SERVER.md、当前 TEAM 前部、REGISTRY 所需所有权字段、TAKEOVER、streamlined-acceptance-current 和 OQ4 resume-current 的相关选择字段。当前 root `01a16680-f408-7391-8c52-d1d5041bda8b`，OQ4 lead `01a1669c-2422-7fa2-9f3c-16bb5bd2dfc4`，旧写者释放/新写者激活；本作者只持有 `drafts/oq4/random-denominator-center-middle-author-v1/` 草稿权限。未更改共享、library、状态、原始来源或其它作者文件，未生成子实例。

SERVER.md 与 `library/lean-toolchain` 直接读值为 Lean `leanprover/lean4:v4.36.0-rc1`；mathlib 固定提交 `807d3836b165983210ee2ecf3cd28f239436949c`。未运行工具链探测、Lean或Lake。本地 library 仅为只读源快照。

完整数学原文与当前观察到的 SHA256：

| 文件 | SHA256 |
|---|---|
| `C:/game/shao/current/oq4/denom01.md` | `71b4f28df03edfe3cc8a4ff5f95beb7d80b716d4b7c64fed01a2dc6989448d3f` |
| `C:/game/shao/current/oq4/energy01.md` | `2e0387f0a35ca677853e45fff271cc2fb0e87db9ee9c6b2f00d3bcf56b51d9e6` |
| `C:/game/shao/current/oq4/b01/proof01.md` | `7c51246eb02a0d694a366ce3ab5a3a9cca03723160c1291bce29dd817f68bc38` |
| 父 intake `drafts/oq4/random-denominator-center-middle-next-math-notes-v1.md` | `31f7d9fabad8b4b119185d472095849ee1c48734505effb68321b9ee39595c30` |

父 intake 全文已读，包括完整 E6范围审计；当前观察哈希与较早 resume-current 内的 `86643fd8...` 不同。本作者未修改该文件，也不声称旧哈希覆盖当前字节；本文只依赖已再次读取的相同中心/中间数学路线，E6段仍属未支付范围。父实例应在冻结时绑定当前 intake 字节，而不是复制旧描述哈希。

## 2. 精确生产者、资格与引用合法性

175冻结声明 `drafts/oq4/frozen-uniform-conditional-energy-formal-v1.lean.txt` 直接完整读取并哈希为 `266d5706d4efaf8dfc979c5bd405b2c6a5aee822554735732fd27fb186b65f05`；其作者完整证明 `50cc4ac09aa001780969a8e52977fe0d2833fbb3955e228009b8101e5da1be4f` 和 API 证据 `b9b8903e05d17582ed6842711b21b929ee33d9c2dbfe26cd0b5c9ae8febb3b7e` 均已完整读取。数学冻结 `905428db...` 的状态依父通知，未将其等同于源代码资格。

实际171源的公开 K 头直接读取，其源 SHA256 `17e19402ea95a8fc8602dade897707594d0b89b5369d3d45b6b9023c5d97fdfd`；当前父接受文件实测 SHA256 `594df95a14306789856a758eb4f44500a858c138ac0a092a1aa42af2d90edda2`。该接受文件状态为完整 fresh176 审查后的无条件 S/AC/K/Kv 范围接受。本文经175公开接口消费它，不重跑或复审已经接受的旧源证明，也不调用私有 `fixed_law_closedStrip_relative_asymptotic`。

实际 FAR 源的8个定义与17个公开头清单读取，直接消费的完整 `far_tail_relative_tendsto_zero` 实际头读取；实际源 SHA256 `2388a74ec1537453148f31736be689907f758d0961052e1c5df23bf4eb667cc5`，688LF。父接受文件实测 SHA256 `1a99d019368aa24076ce197b30391dba87806b37e2447a22f323f1182098888b`。其整个 Q≥2n 的结论按已资格旧证据复用，本作者没有读取或再认证旧 FAR 全证明。

E4冻结完整公开/私有头读取；源预期 `95ac402d7b5f3fc9ecdab93d7e795e5a9072991574c5fd9a1682ef9c830dcb22`。E4和175在派发时分别为174唯一重检查与175局部实现，二者实际资格未由本作者观察为完成。本单元数学消费者可写，形式实现/服务器调用仍必须由父实例冻结并授权，最终消费对象需绑定其实际资格源/对象映射。本提案不改变E4的固定实s接口，不增加移动Laplace参数版本。

本单元实际调用的175公开头及参数计划：

| 上游公开头 | 直接用途 |
|---|---|
| `energy_deviation_finite_bound` | H11，b=middleHeight，h为原尺度，偏差参数为(j:ℝ)*ε，固定s>0；只消费实际有限 Markov，不假设生存正性。 |
| `uniform_closedStrip_energy_controls` | H17、H19、H21；C=1或2，实际窗口[h/2,Ch]，固定s，任意固定容差；同时取得实际G最终正、字面K误差、实际J/G控制。 |
| `uniform_closedStrip_boundary_ratio_bound` | H21，C=2，一次共同尾覆盖全部当前有限层。 |
| `uniform_energy_concentration` | H20，C=2，原始阈值εh²，选取实际下中心；没有改成εb²。 |

上述全部公开类型只有原始 ν 概率、h3、均值0、二阶矩1和三尺度等条件；新最终头亦仅保留这些条件。`middle_finite_bound` 的数值 hcontrols 是有限不等式模块的局部前提，H21内部由175支付，未上移成根定理前提。任何旧私有辅助引理都不作为合法可导入API。

## 3. 实际继承对象的完整定义值

以下值从项目主源直接读取，保持原定义，未重建新替代值。

```lean
-- library/Shao/Basic/FinitePath.lean，源89826289...：
abbrev Shao.Path (n : ℕ) := Fin n → ℝ
-- 在 namespace Shao 且 variable {n : ℕ} 下：
def prefixSum (a : Path n) (k : ℕ) : ℝ :=
  ∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val < k), a i
def energy (a : Path n) : ℝ := ∑ i, (a i) ^ 2

-- library/Shao/Basic/ClosedSurvival.lean，源bb6f334d...：
def closedStrip (h : ℝ) : Set (Path n) :=
  {a | ∀ k : ℕ, k ≤ n → |prefixSum a k| ≤ h}

-- library/Shao/OQ4/RademacherScalarBounds.lean，源12670bd3...：
def lambda : ℝ := Real.pi ^ 2 / 8

-- 在 Shao.OQ4.RandomDenominatorFarTail：
noncomputable def randomDenominatorEvent (n : ℕ) (h : ℝ) : Set (Shao.Path n) :=
  {a | a ∈ Shao.closedStrip
    (h / Real.sqrt (n : ℝ) * Real.sqrt (Shao.energy a))}
noncomputable def farMainTerm (n : ℕ) (h : ℝ) : ℝ :=
  (4 / Real.pi) * Real.exp (-(Real.pi ^ 2 / 8) * ((n : ℝ) / h ^ 2))

-- 在 Shao.OQ4.UniformConditionalEnergy；精确175冻结值：
noncomputable def energyCoshExcessIntegral
    (ν : Measure ℝ) (n : ℕ) (b h s : ℝ) : ℝ := by
  classical
  exact ∫ a : Shao.Path n,
    (if a ∈ (@Shao.closedStrip n b) then
      (Real.exp (s * (Shao.energy a - (n : ℝ)) / h ^ 2) +
        Real.exp (-(s * (Shao.energy a - (n : ℝ)) / h ^ 2))) / 2 - 1
    else 0) ∂Measure.pi (fun _ : Fin n => ν)
```

完整本地源哈希：FinitePath `898262898f9c088e2d10e6238e411b4397387b21b1b71a2b545c5edef936e1bb`；ClosedSurvival `bb6f334d2a7956ebf2d727d2feabd0765c30af33da4e8b4197f1fd658921811f`；RademacherScalarBounds `12670bd33a813849156b245cad28f5efb783a55919f8a0743fcf3fb9fbff329f`。相应旧资格按父现有收据复用。本单元未写或重新认证这些源。

FAR公开 `zero_energy_mem_randomDenominatorEvent` 明确保留任意长度/任意h的全零能量原子；`randomDenominatorEvent_eq_absMax` 仅在n>0、h≥0给绝对最大值表述。本单元有限几何一律先有n>0、h>0，渐近目标不人为加入全指标正性，也不在Fin0宣称非法absMax身份。

## 4. 直接读取的固定提交主要 mathlib API

所有链接钉死同一提交；这是源读取证据，未宣称当前服务器对象/导入缓存可用。没有下载或保存原始远端文件。

| 固定主要来源 | 直接核对到的接口与作用 |
|---|---|
| [Floor/Semiring](https://raw.githubusercontent.com/leanprover-community/mathlib4/807d3836b165983210ee2ecf3cd28f239436949c/Mathlib/Algebra/Order/Floor/Semiring.lean) | 158行 `Nat.add_one_le_ceil_iff`；166 `Nat.le_ceil`；168–171 `ceil_mono/ceil_le_ceil`；176 `ceil_eq_iff`（要求自然目标非零）；329–331 `ceil_lt_add_one`（要求实参非负）。H07以w>1支付ceil(w)≥2及自然减1；H09以t/ε>0支付ceil上界。 |
| [Finite intervals of naturals](https://raw.githubusercontent.com/leanprover-community/mathlib4/807d3836b165983210ee2ecf3cd28f239436949c/Mathlib/Order/Interval/Finset/Nat.lean) | 31–39自然LocallyFiniteOrder及其 `Finset.mem_Icc` 值；44 `Nat.Icc_eq_range'`；70 `range_succ_eq_Icc_zero`。覆盖是实际有限 `Icc 1 ceil(...)`。H13也可将区间写成range后直接归纳。 |
| [Real square root](https://raw.githubusercontent.com/leanprover-community/mathlib4/807d3836b165983210ee2ecf3cd28f239436949c/Mathlib/Analysis/Real/Sqrt.lean) | 132 `sqrt_nonneg`；163 `sq_sqrt`要求非负；166 `sqrt_sq`要求非负；192 `sqrt_le_sqrt`；262 `sqrt_pos`。H02先证明根号参数非负，再平方与用非负平方唯一性；H03/H09按序比较根号，没有把负数的sqrt平方还原。 |
| [Real-valued measures](https://raw.githubusercontent.com/leanprover-community/mathlib4/807d3836b165983210ee2ecf3cd28f239436949c/Mathlib/MeasureTheory/Measure/Real.lean) | 48 `measureReal_nonneg`；80 `measureReal_mono`需上事件有限，实际产品概率自动支付；124 `measureReal_union_le`；132–140 `measureReal_biUnion_finset_le`无额外可测性前提。H05/H06/H15只需这些覆盖不等式，无须伪造新measurability证明。 |
| [Complex/Exponential，实数部分](https://raw.githubusercontent.com/leanprover-community/mathlib4/807d3836b165983210ee2ecf3cd28f239436949c/Mathlib/Analysis/Complex/Exponential.lean) | 196 `Real.exp_add`，216 `exp_nat_mul`，223 `exp_neg`，225 `exp_sub`，260 `exp_pos`，274–292严格/弱单调。H12的精确exp-pair因式分解、q^j和主项相除均由这些源恒等式及实域代数支付，未依赖不明coshAPI。 |
| [SpecialFunctions/Exp](https://raw.githubusercontent.com/leanprover-community/mathlib4/807d3836b165983210ee2ecf3cd28f239436949c/Mathlib/Analysis/SpecialFunctions/Exp.lean) | 139–141 `Real.continuous_exp`；162–164 `Filter.Tendsto.rexp`，并非名为Tendsto.exp；206–209在0趋1。H19可用continuous_exp.tendsto作复合；H23取ε↓0用同一连续性，明确双侧阶邻域。 |
| [Topology/Algebra/Order/Field](https://raw.githubusercontent.com/leanprover-community/mathlib4/807d3836b165983210ee2ecf3cd28f239436949c/Mathlib/Topology/Algebra/Order/Field.lean) | 68–71 `tendsto_inv_atTop_zero` 与 `Tendsto.inv_tendsto_atTop`，支付1/t→0；此模块公开导入AtTopBot.Field与Topology.Algebra.Field。H18不用未核对的div_atTop别名，普通商极限仅在极限分母1非零时调用。 |
| [Topology/Order/Basic](https://raw.githubusercontent.com/leanprover-community/mathlib4/807d3836b165983210ee2ecf3cd28f239436949c/Mathlib/Topology/Order/Basic.lean) | 118–121 `tendsto_order`精确要求每个a<目标的最终严格下界及每个b>目标的最终严格上界。H21的非负+任意正τ上界与H23的ε夹逼均完整满足这两个量词，不把liminf/limsup记号当存在性证明。 |
| [Integrable](https://raw.githubusercontent.com/leanprover-community/mathlib4/807d3836b165983210ee2ecf3cd28f239436949c/Mathlib/MeasureTheory/Function/L1Space/Integrable.lean) | 94–96 `Integrable.mono'`接受真实AEStronglyMeasurable函数与a.e.范数支配；149 `integrable_const`要求有限测度。H01从1+|x|³支配x与x²，未访问171私有lower_moments，也未把二阶可积提升为根前提。 |
| [Ordered finite sums/products](https://raw.githubusercontent.com/leanprover-community/mathlib4/807d3836b165983210ee2ecf3cd28f239436949c/Mathlib/Algebra/Order/BigOperators/Group/Finset.lean) | 156–163的 `prod_le_prod_of_subset_of_one_le` 由 `to_additive`生成 `Finset.sum_le_sum_of_subset_of_nonneg`；其补集项条件要证明非负，H13用q≥0逐项支付。H15的点态有限求和比较也用标准sum_le_sum。没有靠只搜索字面sum名称断言API缺失。 |

`Mathlib.Algebra.BigOperators.Intervals` 固定主要源也已打开，模块确实存在，但未从中找到字面 `sum_Icc_succ_top`；提案没有依赖这一未经核对的名称。H13采用上文有限range归纳与实际集合相等的路线，所有有限几何恒等式是新私有证明内的局部推导。项目已资格源 `RademacherSpectralTail.lean`442–453有同类range归纳使用 `Finset.sum_range_succ`、`pow_succ` 的主源实例，另478行直接消费同一sum_subset API；只作为拼写/用法证据，不调用其私有定理。

失败/纠正的读取如实保留：本地曾查找不存在的 `Shao/Basic/Path.lean` 和 `PathStatistics.lean`，随后定向搜索定位真正 `FinitePath.lean`；旧路径 `Mathlib/Data/Real/Sqrt.lean`实际为deprecated shim，故精确导入使用真正 `Mathlib.Analysis.Real.Sqrt`。未为这些查找执行工具链、下载或修补旧源。`squeeze_zero'`不是本单元必要API，未宣称在已读Basic中存在。

## 5. 全清单覆盖与未验证事项

6个定义的完整值在声明提案里，无省略体。24个头逐一覆盖：H01低阶可积；H02–H03有符号中心几何；H04–H06实际包含与概率界；H07–H10全部有限层覆盖/窗口/偏差包含；H11有限实际Markov；H12–H14完整数值和；H15全部有限中间概率；H16正尾；H17实际K主项；H18精确指数差；H19中心比；H20中心误差；H21整个中间相对0；H22全部FAR换分母；H23实际E/G→1；H24实际E/m→1。

16个导入包括两个项目生产者、9个上述数学模块（Floor、自然有限区间、有限区间求和、sqrt、exp、实测度、Integrable、有序域拓扑、阶拓扑）与5个显式基础tactic模块。1个选项仅autoImplicit false，未放宽心跳、递归或公理。不会新增编译/格式执行包装器。

形式语法、elaboration、精确tactic可用性、实际新常量/生成常量数量、服务器对象资格与传递公理均尚未检查。当前提案的30个源声明数不是实际审计常量数。后续必须先父实例冻结每个头/值/导入/选项，才可实现；实际实现完成后接受一次源哈希绑定的服务器内核/全所属传递公理收据和新鲜独立完整源到声明/证明审查。允许公理仅propext、Classical.choice、Quot.sound。无正式证明信用或原根关闭声明。
