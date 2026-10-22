# OQ4 零起点显式有限 S1 与低阈值分支：独立来源语义审查 v1

STATUS: CORRECT
REVIEW_KIND: SOURCE_TO_FROZEN_STATEMENT_ONLY
REVIEWED_FROZEN_SHA256: e2e9240f739e737c83195f177dcd54707c023151cf3e4faf7f1d862e87b585fe
REVIEWED_FROZEN_BYTES: 10956
PROOF_REVIEW: NOT_PERFORMED
LEAN_REVIEW: NOT_PERFORMED
SPECTRUM_STATUS: OPEN
ROOT_STATUS: OPEN

本报告由全新独立上下文完成，只核验原始来源到冻结数学接口 C1–C5 的语义忠实性。结论不表示这些目标已有数学证明、可导入的实现或 Lean 认证。未发现需要另立冻结版本的量词、系数、相位、指标、端点或概率对象偏差。仅写本报告；未修改冻结稿、原始来源、证明、实现或状态文件。

## 1. 审查对象与证据边界

原始来源固定为 `C:/game/shao/current/oq4/c01/spectrum01.md`。派发与冻结稿标注来源提交 `35d4580b61e22e7145f47730045a09874ef93259`；本轮未调用 Git 核验提交关系，仅实际核验文件 SHA256 与字节数。

| 对象 | 实测 SHA256 | 字节数 |
| --- | --- | ---: |
| 原始 spectrum01.md | b65f9e0c2f9b40a28d092491b479bd20d0b8ee8a9ac940c3c4760cfff7d2670b | 4306 |
| frozen-rademacher-finite-s1-v1.md | e2e9240f739e737c83195f177dcd54707c023151cf3e4faf7f1d862e87b585fe | 10956 |
| frozen-rademacher-iteration-v1.md | 15851002ccadaa118035107c8b9b8266dd825fdebdf36728f3ac7a97f7330b80 | 5464 |
| frozen-rademacher-finite-basis-v1.md | 4672baa6bc550de2a97ca9adc0730b5633f71458b2c3da8b02c2318131e05a7f | 9862 |
| frozen-rademacher-all-modes-v1.md | dac2fd30e7c759137e14ebd64c4d7457155a201da04a7226449304d0b4abbe10 | 6845 |
| rademacher-cosine/declarations.md | e9ec045fccfd4ed68f5b6515f1b28310ab90bf71609cb7bba87a0c1b4d7f850c | 39048 |

三个上游文件仅作为固定数学接口读取：Iteration 的真实整数网格保持，FiniteBasis 的同一 I_m、J_m、正弦族和范数 H，以及 AllModes D1/D2 的真实有限幂与 F₁=1 未化简质量和。没有把它们改成任意输入假设或把其冻结文本当作认证实施。派发所述 Iteration 已正式认证发布 PR82，FiniteBasis canonical40 最终形式审查中，AllModes 数学独审 CORRECT 而未 Lean，均未通过读取状态文件、其他审查报告或实施源码作二次验证。

本报告不审查数学证明、新颖性、完整形式实现、传递公理或机械执行。RademacherCosine 的既有认证来源标识 `c0ba478f9ed6b5aa75d7010d70835b37065a92e9878c65b086d3c3ff24e7f861` 来自派发及冻结接口；本轮只核验获准声明账的指纹与相应公开类型。

## 2. 原始对象、量词与真实概率对象

原第5–7行固定 Rademacher 分布、S₀=0。冻结第28–44行使用已有 `RademacherCosine.law`、内部概率实例、`Path n = Fin n → ℝ` 与 n 次真实乘积律，且 p(n,h) 明确是 `P_n.real (Shao.closedStrip h)`，不是另设矩阵的行和定义。获准 law.eq_1、halfENNReal.eq_1 与概率实例类型与这一定义一致。

原第11–17行的范围 h≥1、m=floor(h)、H=m+1、j=1,…,2H−1，冻结第46–60行改写为所有 m:ℕ、1≤m，以及全部 m≤h<m+1、n:ℕ。H_N、H_Z、H 是同一 m+1 的自然数、整数和实数表示，没有引入自由吸收位置。I_m 的整数状态为 −m,…,m，J_m 为 1,…,2m+1=2H_N−1。已有 angle.eq_1 的类型给 angle m=π/(2*((m:ℝ)+1))，相位与源第16、20行一致。

获准透明定义确认 `prefixSum` 是按 i.val<k 求和，`closedStrip h` 含所有 k≤n，特别含 k=0；`shiftedClosedSurvival` 只量化 1≤k≤n。公开 `shiftedClosedSurvival_eq_closedStrip` 与 `killedMass_eq_closedStrip_probability` 均要求 0≤h。冻结第44、69行保留这一桥接条件：C4 的 1≤m、m≤h 足够保证该条件，C5 则直接要求 0≤h。n=0 的 closedStrip 对这些 h 是源第33行的空路径事件约定，不借用未定义的空集最大值。

获准 killedKernel 定义及 apply 签名确认实际转移是平移后限制于闭区间 [−h,h]，没有重新归一化。killedIterKernel 是该核的自然数幂，killedAction 是对真实迭代核的实积分，killedMass 是常数一的 action；其公开 mass_eq_real 类型返回真实核的总质量。`killedIterKernel_zero` 明确零步为起点 Dirac。故冻结第64–69、104–108、118–119行引用的是相同真实对象。

## 3. C1–C5 逐项来源映射

| 冻结项 | 原始来源 | 精确映射与审查结果 |
| --- | --- | --- |
| C1，第75–81行 | 第20、22行 | v_j(0) 的全 J_m 陈述是 sin(jπ/2)，不是只对奇数 j 的身份。偶数恰为 j=2k、1≤k≤m；奇数恰为 j=2ℓ+1、ℓ∈range(m+1)，值分别为 0 与 (−1)^ℓ。起点仍是 0。CORRECT。 |
| C2，第83–90行 | 第20、23行及第28–30行 | 仅对奇数 j 的未归一化有限正弦和取 cot(jπ/(4H))，即 cot(θ_j/2)。q_m,j 的定义再乘唯一的 1/H；没有换成状态数倒数，也没有多乘一次 1/H。CORRECT。 |
| C3，第92–98行 | 第17、22行与第28行 | 源全指标 J_m 的奇数子集与 range H_N=range(m+1) 精确对应；ℓ↦2ℓ+1，逆向只在奇数 j∈J_m 上使用 (j−1)/2。首末为 (ℓ,j)=(0,1)、(m,2m+1)，偶数补集恰为 2,…,2m。没有吸收端点 j=2H_N。CORRECT。 |
| C4，第100–112行 | 第24–33行，特别 S1 第27–30行 | 所有 m≥1、m≤h<m+1、n:ℕ 的实际 p(n,h) 等于同一 killedMass，再等于 (1/H)∑_{ℓ=0}^{H_N−1}(−1)^ℓ cot((2ℓ+1)π/(4H)) cos((2ℓ+1)π/(2H))^n。因子、相位、上限和 n 的范围与原式逐项相同。CORRECT。 |
| C5，第114–121行 | 第33–34行，结合第33行空路径约定 | 对全部 0≤h<1 和所有 n:ℕ，实际 p 与 killedMass 均等于 if n=0 then 1 else 0。这是一支独立的真实概率结论，不把 S1 扩成 m=0 的全谱目标。CORRECT。 |

C2 的实数 cot 定义为 cos/sin。其参数的实际范围为
0 < jπ/(4H) < π/2，
因为指标仍是源的正奇数首末 1 与 2H_N−1。这没有增加新的角度假设；相应正弦分母非零。C2 不承诺额外的偶数有限正弦和公式，偶数项在本零起点质量和中的消去依据是 C1 的真实起点值。该公开范围忠实于源第22–23行。

AllModes D2 的固定接口是对所有 j∈J_m 的
∑ q_m,j * μ_m,j^n * v_m,j(0)。
它的 F₁=1 系数尚未被当成显式 cot 系数；C1、C2、C3 与实际概率桥正是本叶必须交付的后继语义。冻结没有把 raw mass sum、主余弦积分或单一主模态当作 C4 已证，也没有让它们代替 C4 的显示式。

C5 所指的 `RademacherCosine.killedKernel_row` 公开 fulltype 对 m:ℕ 只要求 m≤h<m+1，没有主余弦积分定理的 hm:1≤m，也没有 r∈I_m 的额外前提；因此其 m=0 使用点在现有接口范围内。`killedKernel_integral_principal` 的 hm:1≤m 则原样保留。本项只核对合法依赖接口，不给 C5 添写证明。

## 4. 零谱、负谱、时间和阈值边界

1. C4 不删 n=0。冻结第112、135行明确自然数幂 μ^0=1，包括 μ=0；该显示式在 n=0 本身必须等于 1。零谱位于 j=H_N=m+1；当 H_N 为奇数，即 m 为偶数时，它确实属于奇数和，对应 ℓ=m/2，cot 参数 π/4，零步系数为 (−1)^(m/2)/H。只有正步才可由该项的 0^n 消失。H_N 为偶数时该 j 由偶数起点值为零消去，不被说成“零谱永不贡献”。
2. 源第34行允许负特征值。冻结第136行保留全部 j>H_N 的有符号 μ^n，包括末项 j=2m+1、ℓ=m；没有以 |μ|^n 取代，也没有只交正主模态。冻结第137行没有加入正生存、无周期、混合、非格点、正谱、非零谱或 n 与模态／状态奇偶匹配条件。
3. 原第11–13行的弱事件在整数 h=k≥1 时取 m=k、H=k+1。冻结第125、138行保留 ±m 的状态，吸收在 ±(m+1)，不是 ±h，也不是 strict 事件所用的 ceil(h)。边界退出质量丢失，未归一化为一。
4. 低阈值端点 h=0 在 C5 内，h=1 在 C4 的 m=1 内。两支都包含 n=0，且一致采用空路径概率一；h<0 则没有被扩入结论。冻结不依赖生存质量为正，也不除以该质量。
5. C1–C4 的 1≤m 与上游范围一致；C5 不要求这些全谱接口在 m=0 成立。起点固定 0，没有把整数状态谱延伸到非整数起点的其他 coset。

## 5. 全部非负阈值的覆盖与未关闭范围

冻结第123–131行的 floor 总述准确保留原第11–12行：对 h≥1，取自然数 floor ⌊h⌋₊ 与原整数 floor 的非负值一致，并落入 m≥1、m≤h<m+1 的 C4。对 0≤h<1，使用 C5。因此 C4 与 C5 共同覆盖所有 h≥0 的有限生存概率。统一 if/floor 显示式只是可选导出 helper；两支交付本身是强制要求，不能仅交 cot 恒等式或仅交高阈值一支。

本 CORRECT 只接受这一有限 S1 加低阈值分支的语义范围。原第36行以后的 S2–S5、正负配对的统一余项、布朗基准、格点位移与临界子列，strict 事件分类、其他 coset、sharp01 及一般 OQ4，均未因此关闭。Spectrum/OQ4 根保持 OPEN。实现授权、上游认证与后续匿名数学审查、形式审查仍服从冻结稿的独立门。

## 6. 实际访问记录与操作记录

读取的协作和技能指引：`C:/game/shao lean/AGENTS.md`、`SERVER.md`、`coordination/TEAM.md`；math-theorem 的 SKILL.md、prompt-library.md、openai-workflow.md、lean-verification.md；chinese-output-style 与 windows-shell7 的 SKILL.md。检查了 drafts、drafts/oq4、drafts/oq4/translation 下的精确 AGENTS.md 路径，均无附加文件。

数学输入实际读取范围：原 spectrum01.md 第1–119行；本次冻结第1–149行；Iteration 冻结第1–46行；FiniteBasis 冻结第1–119行；AllModes 冻结第1–81行。只读取固定 frozen 文件，文件名清单检索没有打开 candidate、intake 或 review 内容。

Cosine 声明账只读取获准的第148–179、213–224、240–259、269–278、334–453、518–529、549–622行。使用的公开对象为 angle/eq_1、halfENNReal/eq_1、integer_closed_iff 的类型、principal integral 与 row 的 fulltype、law/eq_1、概率实例、rho/eq_1；未读取该模块的证明或未获准区段。

旧库先只取得文件指纹、顶层声明名称／行号及变量／namespace 元数据，随后按明确目标读取如下必要透明定义或公开签名。所有 theorem 均在证明赋值符号 := 截断；具名参数中的 (n := n) 不作为证明起点。

| 只读文件 | SHA256 | 实际语义访问 |
| --- | --- | --- |
| library/Shao/OQ4/KilledKernel.lean | f90c1996f4c220473371b0f5ea3c74a7b8287e8f997f1a2cd3f0831cd6bd626f | 第20–27行 translationKernel/killedKernel 透明定义；第36–37行 killedKernel_apply 签名。 |
| library/Shao/OQ4/KilledIteration.lean | 03b97e5708ffa552cfa4eccec5cf3c042da9805f9ab69561f4cb3e2701a690b5 | 第19–28行 killedIterKernel/action/mass 透明定义；第29、82–83、118、121–124行 zero、mass_eq_real、action_zero、action_one 签名。 |
| library/Shao/OQ4/KilledPathLaw.lean | 1f1b664d81e551bb6a58ca335c3b568cfbd684e991e12b733f599a5ed2eada9f | 第15–17行 shiftedClosedSurvival 透明定义；第33–34、165–166、248–249、259–260行零步事件与真实路径／closedStrip 桥签名。 |
| library/Shao/Basic/ClosedSurvival.lean | bb6f334d2a7956ebf2d727d2feabd0765c30af33da4e8b4197f1fd658921811f | 第26–29行 closedStrip 透明定义；第44–45行 mem_closedStrip_iff_absMax_le 签名。 |
| library/Shao/Basic/FinitePath.lean | 898262898f9c088e2d10e6238e411b4397387b21b1b71a2b545c5edef936e1bb | 文件名定向检索后，仅第18行 Path 与第23–24行 prefixSum 透明定义。 |

未读取任何 intake/candidate/review 推理、作者 checkpoint、匿名证明、新 FiniteBasis/AllModes/FiniteS1 实施源码或旧 theorem proof body；未执行 Lean、数学重计算、Git、网络访问或服务器操作。所有 shell 的 workdir 固定为 `C:/game/shao lean`。本报告写入前不存在同名文件，未覆盖其他作者产物。最终只对本报告做 UTF-8 无 BOM、无 CR、末尾恰一个 LF 与 SHA256／字节数检查。
