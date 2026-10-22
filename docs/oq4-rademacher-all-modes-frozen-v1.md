# OQ4 全部模态真实有限幂与未化简生存谱：冻结数学接口 v1

STATUS: FROZEN_PENDING_STATEMENT_REVIEW
CANDIDATE_STATE: FROZEN_BY_LEAD
IMPLEMENTATION_AUTHORIZATION: HOLD_PENDING_UPSTREAM_LEAN_CERTIFICATION_AND_MATH_GATES
SPECTRUM_STATUS: OPEN
ROOT_STATUS: OPEN

Lead 冻结以下 D1、D2 数学接口；候选原稿 c365c3e2f510351861a1490bfe799be971c3c499adfbf82f8a4c2869c9aef176 保留原字节。它仍待独立来源语义核验，不是证明或 Lean 认证。RademacherIteration 的数学审查已通过、canonical39 最终形式审查中；RademacherFiniteBasis 的独立数学审查已通过、仅私有 Lean 实施中。二者尚未全部形式认证，当前只能作为已固定数学接口使用，不得运行/导入未认证实现或宣称本后继已闭合。来源语义、匿名数学证明及独立数学审查可先行；本模块的 Lean 实施须再等两个上游完整形式认证与 lead 明确授权。

## 1. 来源和最小范围

固定原始来源 C:/game/shao/current/oq4/c01/spectrum01.md，commit 35d4580b61e22e7145f47730045a09874ef93259，SHA256 b65f9e0c2f9b40a28d092491b479bd20d0b8ee8a9ac940c3c4760cfff7d2670b。

本冻结命题仅连接：原第 11–21 行的一步全部模态与真实有限幂，以及第 24–30 行生存公式中尚未化简的有限谱和。零起点奇偶值、有限 cot 和与 S1 的显式奇数模态系数另叶；S2–S4 与一般分布 OQ4 均保持 OPEN。

固定薄模块 Shao/OQ4/RademacherAllModes.lean，namespace Shao.OQ4.RademacherAllModes，只交付下列 D1、D2。任意有限数据、任意实测试函数的完整谱与逐原子核谱不是本冻结命题的公开目标。

## 2. 固定对象和全部量词

沿用 frozen-rademacher-finite-basis-v1.md 的同一对象，不另立自由特征值或替代核：

- m : ℕ，1 ≤ m；H := (m : ℝ) + 1。
- I_m := Finset.Icc (-(m : ℤ)) (m : ℤ)。
- J_m := Finset.Icc (1 : ℕ) (2*m + 1)。
- ν_R := Shao.OQ4.RademacherCosine.law = (1/2 : ℝ≥0∞) • δ_1 + (1/2 : ℝ≥0∞) • δ_(-1)，使用已有内部概率实例。
- θ_m,j := (j : ℝ) * Shao.OQ4.RademacherCosine.angle m = (j : ℝ)*π/(2*H)。
- μ_m,j := Real.cos θ_m,j。
- φ_m,j(w) := Real.sin (θ_m,j * (w + H))，v_m,j(s) := φ_m,j((s : ℝ))。
- c_m,j(F) := (1/H) * ∑ s∈I_m, F(s) * v_m,j(s)。
- G_m := {w : ℝ | ∃ s : ℤ, s∈I_m ∧ w=(s : ℝ)}，与冻结 Iteration 的实际整数网格相同。

对所有 h : ℝ 满足 (m : ℝ) ≤ h 且 h < (m : ℝ)+1，对所有 r : ℤ 且 r∈I_m，对所有 n : ℕ（包含 0）。D1 另对每个 j : ℕ 且 j∈J_m。

真实对象始终是现有 closed killedKernel ν_R h、killedIterKernel ν_R h n、killedAction ν_R h n 和 killedMass ν_R h n。前置网格保持与 B0–B3 是需先认证的上游结论，不能变成新自由假设来冒充本源特例的证明。

## 3. D1：全部模态的真实有限幂

对上面全部量词，有真正可积性

Integrable φ_m,j (killedIterKernel ν_R h n (r : ℝ))，

以及精确等式

killedAction ν_R h n φ_m,j (r : ℝ)
  = ∫ w : ℝ, φ_m,j(w) ∂killedIterKernel ν_R h n (r : ℝ)
  = (μ_m,j)^n * v_m,j(r)。

第一处 action/积分同一性是现有定义，不另算原始义务。积分形式不得被新递归函数或新矩阵的有限幂替代。j=1 与已有主余弦接口的兼容只作一致性核对，不能替代全 J_m 的结论。

## 4. D2：常数一的重建落到实际生存质量

令 F₁ : ℤ → ℝ 为 F₁(s)=1，仅为 B2 的一个固定使用点；令

q_m,j := c_m,j(F₁) = (1/H) * ∑ s∈I_m, v_m,j(s)。

对全部合法 m、h、r、n，有

killedMass ν_R h n (r : ℝ)
  = (killedIterKernel ν_R h n (r : ℝ)).real Set.univ
  = ∑ j∈J_m, q_m,j * (μ_m,j)^n * v_m,j(r)。

此处双层有限和均是未归一化计数和，唯一的 1/H 正是 B1 范数/B2 系数的 1/H，不改成 1/(2*m+1)。不要求、也不除以 killedMass；零质量时仍用同一等式。

现有 killedMass_eq_path_probability 已把左侧等同于 ν_R 的 n 步乘积律下 shiftedClosedSurvival h (r : ℝ) 的真实概率；r=0 时现有 killedMass_eq_closedStrip_probability（0≤h 由既有范围推出）给原 closedStrip 概率。无需把一般路径桥重新列为新原始义务。

## 5. 必须保留的边界

1. h=m 的弱端点保留 ±m，实际吸收点为 ±(m+1)；不得切换 strict strip、支付不明的格点位移或把退出行重新归一化。
2. J_m 全部保留，特别是 j=m+1 的 μ=0 与 j>m+1 的负特征值。幂为实数自然数幂，约定 0^0=1；不得以 |μ|^n 替代，也不得因正步零模态消失而删除 n=0 的项。
3. n=0 时真实核是 δ_(r:ℝ)，D1 恢复 v_m,j(r)，D2 的谱和恢复 1；不得把零步核先行杀死，亦不得删除 r∈I_m 后声称结论扩展到区间外起点。
4. 保留整数起点与全部自然时间，不增加正生存、平稳/不变概率律、无周期、混合性、正特征值、非零特征值、奇数 j 或奇偶匹配前提。真实链的周期与谱符号所产生的消去应自然保留。
5. 不扩展到非整数起点的其他 coset，不扩展 m=0 或原 0≤h<1 分支，不以主模态 ρ^n 代称无权生存概率。

## 6. 后续门和排除范围

本文件不提供匿名证明。先经全新独立来源翻译审查 CORRECT，才由新作者给完整匿名数学证明，再由全新独立数学审查者找关键缺口；不依赖其他 intake/candidate/review 推理。上游冻结的真实网格支持和 B0–B3 可作为明示的已固定数学引理接口，但最终 Lean 模块不得把它们换成自由假设或重复声明未证明公理；实际导入必须等各上游认证完成，接口不得漂移。

本模块 Lean 实施还须上游完整形式认证、独立匿名数学 CORRECT 与 lead 明确授权；canonical 写入/唯一 olean emit 要再单独释放单一窗口。所有 Lean/重计算仅指定服务器，shell workdir C:/game/shao lean。旧源/common/root/pins/旧产物哈希保护；author 唯一新 emit，独立 canonical no-o、完整原 source 全部 getModuleIdxFor?=none 不做 name/namespace 筛选、actual 全冻结 imports owner OR namespace 审计所有 private/generated/outside-name 常量及传递公理，source/import 完整原名/kind/universe/fullExprtype/axioms/定义体/实例标记 exact。lead import-only。禁止 sorry/admit/new axiom/unsafe/native_decide；仅 propext、Classical.choice、Quot.sound。原始日志/类型/二进制仅服务器。本冻结不声称 S1 或 Spectrum/OQ4 已关闭。

下一叶才处理 v_m,j(0)=sin(jπ/2)、偶数模态消失、奇数模态有限正弦和等于 cot(jπ/(4H))，并用已有 closedStrip 桥合成 S1。S2 的正负配对与统一余项、S3 的布朗比较、S4 的实阈值格点位移及其渐近条件均不在此候选内。
