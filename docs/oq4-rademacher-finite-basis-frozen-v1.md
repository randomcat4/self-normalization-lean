# OQ4 完整有限正弦特征基：冻结数学接口 v1

STATUS: FROZEN_PENDING_STATEMENT_REVIEW
REVIEW_STATUS: NOT_REVIEWED
IMPLEMENTATION_STATUS: NOT_STARTED
SPECTRUM_STATUS: OPEN
ROOT_STATUS: OPEN

Lead 采用独立 intake 后冻结本文件中的 B0–B3 数学接口；候选原稿 f327e358d24d079f6c2785675fb23bfc25d6ceef22abd92cb4431328d7ac452d 保留原字节。本冻结仍待全新来源翻译审查，不是数学证明、Lean 实施或认证。本文件不替代待审 RademacherIteration 的任何结论；来源审查 CORRECT 前不授权匿名证明，匿名数学独审 CORRECT 前不授权 Lean。

## 1. 来源、范围与最薄交付

固定原始来源 commit 35d4580b61e22e7145f47730045a09874ef93259：
C:/game/shao/current/oq4/c01/spectrum01.md
SHA256 b65f9e0c2f9b40a28d092491b479bd20d0b8ee8a9ac940c3c4760cfff7d2670b。

本冻结命题只翻译原第 11–21 行：真实整数状态、全部有限正弦模态、平方范数、正交/完备以及全部模态的真实核一步特征身份。第 22–30 行的起点/有限 cot 和/生存公式，以及第 36 行以后的谱渐近，均不纳入本叶。

固定新模块 Shao/OQ4/RademacherFiniteBasis.lean，namespace Shao.OQ4.RademacherFiniteBasis。无需为了本冻结命题读取或依赖未认证的 RademacherIteration 实现：本叶没有时间参数 n，只使用已认证 RademacherCosine 的实际 law/angle/rho/二点行以及既有 killedKernel。全部有限幂必须另叶冻结。

## 2. 固定的实际对象与量词

对所有 m : ℕ，保留 1 ≤ m。记自然数 H_N := m + 1，实数 H := (m : ℝ) + 1，整数 H_Z := (m : ℤ) + 1；这些只是同一吸收位置的不同强制转换，不是独立参数。

真实概率律固定为现有
ν_R := Shao.OQ4.RademacherCosine.law
     = (1/2 : ℝ≥0∞) • δ_(1 : ℝ) + (1/2 : ℝ≥0∞) • δ_(-1 : ℝ)。

不得把 ν_R、概率性、角度、特征值或目标特征关系作为新的自由输入或新前提。

用有限集合精确定义：
I_m := Finset.Icc (-(m : ℤ)) (m : ℤ)，元素 s、r 为整数；
J_m := Finset.Icc (1 : ℕ) (2*m + 1)，元素 j、k 为自然数。
所以 I_m 与 J_m 都有 2*m+1 个元素，源指标 j=1,...,2H_N-1 逐一对应 J_m；不做循环重标号，不遗漏首末模态。有限求和均按计数测度的未归一化有限和解释。

对每个 j : ℕ 定义实际实函数和有限向量：
θ_m,j := (j : ℝ) * RademacherCosine.angle m
       = (j : ℝ) * π / (2*H)；
μ_m,j := Real.cos θ_m,j；
φ_m,j : ℝ → ℝ，φ_m,j(w) := Real.sin (θ_m,j * (w + H))；
v_m,j : ℤ → ℝ，v_m,j(s) := φ_m,j((s : ℝ))。

φ 是全实轴上的明确正弦函数；其在实际核下积分，不把一个未解释的有限向量直接放入实测度积分。有限向量 v 只在 I_m 上作基/完备断言；不得扩展为整个实区间的基。

对每个 F : ℤ → ℝ 和 j : ℕ，定义有限 Fourier 系数
c_m,j(F) := (1/H) * ∑ s∈I_m, F(s) * v_m,j(s)。
F 在 I_m 外任意，其外部值不参与系数及重建。这里不要求 F 的可测性、有界性或有限支撑；这是有限和，不是对 F 的实轴积分。

仅在真实核结论中另量化所有 h : ℝ 满足
(m : ℝ) ≤ h ∧ h < (m : ℝ) + 1，
并量化所有 r : ℤ 且 r∈I_m。实际核始终是现有
Shao.OQ4.killedKernel ν_R h (r : ℝ)，
即平移 ν_R 后限制在闭区间 [-h,h] 的次概率测度。不得改成条件存活后的归一化转移或新造矩阵。

## 3. 冻结的精确结论

以下全是待证明目标，不能作为新的假设输入证明者。

B0. 透明的主模态兼容性。对每个 m : ℕ、1≤m，
θ_m,1 = RademacherCosine.angle m，
μ_m,1 = RademacherCosine.rho m，
且对所有 w : ℝ，
φ_m,1(w) = Real.cos (RademacherCosine.angle m * w)。
这只核对新族的首项确为现有主余弦；可作为透明/helper 签名，不算另一项原始谱输入。

B1. 完整未归一化正交与范数。对每个 m : ℕ、1≤m，对所有 j,k : ℕ，若 j∈J_m 且 k∈J_m，则
∑ s∈I_m, v_m,j(s) * v_m,k(s)
  = if j = k then H else 0。
特别地每项平方范数严格为 H。不得把 H 换成状态数 2*m+1，也不得在没有说明的情况下改用概率归一化内积。

B2. 对所有有限数据的显式完备重建。对每个 m : ℕ、1≤m，对所有 F : ℤ → ℝ 和所有 r : ℤ，若 r∈I_m，则
F(r) = ∑ j∈J_m, c_m,j(F) * v_m,j(r)。

B2 是完备性的数学交付，不能只说“有若干线性无关向量”或只重建 F=1、F=主余弦。允许实现用一个 Lean Basis 对象或矩阵辅助，但对外必须回到以上同一 I_m、J_m、实际正弦值与显式系数。若改用 Fin(2*m+1)，必须内部明确并证明与源指标 j=k+1 的对应。

等价的对偶完备身份可作为导出接口，不另算独立原始义务：对所有 r,s∈I_m，
(1/H) * ∑ j∈J_m, v_m,j(r) * v_m,j(s)
  = if r = s then 1 else 0。
不能只给 B1 而把 B2 或等价的完整重建留作“显然”。

B3. 全部模态的真实一步特征身份及真正可积性。对每个 m : ℕ、1≤m，对所有 h : ℝ 满足 (m:ℝ)≤h<(m:ℝ)+1，对所有 j : ℕ 且 j∈J_m，对所有 r : ℤ 且 r∈I_m，
Integrable φ_m,j (killedKernel ν_R h (r : ℝ))，
并有
∫ w : ℝ, φ_m,j(w) ∂killedKernel ν_R h (r : ℝ)
  = μ_m,j * v_m,j(r)。

此处没有 ν_R 的额外输入，没有自由 λ_j，没有假设 Kφ=μφ，也没有仅对新矩阵给一步递推。B3 必须接已认证真实二点行/真实积分；不能把主余弦定理直接代换成任意频率而省略两个吸收端点与源正弦相位。

必要的透明 def、有限性/索引转换、正弦可测有界性、积分可积性及精确同一对象 helper 可随本薄模块提交。实际公开声明数应由最终源码与全 owner 审计测量，不按 B0–B3 编号机械计数。

## 4. 必须保留的退化、端点与禁止解释

h=m 的弱闭端点保留 ±m；吸收格点是 ±(m+1)，不是 ±h。r=±m 向外一步的质量丢失，向内保留质量仍为 1/2；不把边界行改成总质量 1。h 为任意 m≤h<m+1，而非只测非整数 h。

J_m 全部保留，包含零模态 j=H_N 和负特征值模态 j>H_N，包括最末 j=2*m+1。不加入 μ_m,j>0、μ_m,j≠0、非格点、无原子、aperiodicity、奇数 j 或任意 parity 前提。完整源族同时含奇数余弦型与偶数正弦型；不能只保留主模态或零起点最终有贡献的奇数族而称完整基。

起点只为整数 r∈I_m。对非整数 z 可达的是 z+ℤ，不能套用本 I_m、同一 H 与同一族。源 0≤h<1 的独立分支和严格事件 M_n<h 不在本冻结命题范围；没有把它们改定义或删出源问题。

本叶不含 n，不建立真实 killedIterKernel 的全部模态幂或无权生存质量。本叶日后的幂结论必须覆盖所有 n:ℕ，包括 n=0，并使用自然数幂 0^0=1。当前保留零模态不是允许后继把该项在 n=0 删除；负模态也不能以绝对值代替。真实格点幂的 parity 零项不能被任意正性/混合假设抹去。

## 5. 本叶之后仍缺的独立接口

D1. 借助已认证整数网格保持，推到每个 j∈J_m、每个 n:ℕ 的真实 killedAction/killedIterKernel 模态幂，含 n=0/零/负模态；当前主模态幂只对应 j=1。

D2. 把 B2 用到真实有限网格支持上，给任意合法整数起点的真实核原子质量或有界可测测试函数的完整有限谱表示，并给 F=1 的真实 killedMass 谱表示。一般路径桥已存在，不把另造矩阵递归当成此连接。

D3. 原第 22–23 行的零起点奇偶值与奇数模态有限 cot 和；再与 D2 及真实 closedStrip 概率桥合成原 S1（所有 n≥0）。

D4. 源 S2–S4 的正负配对、统一余项、布朗基准与格点位移渐近；最后才到 sharp01 的必要性。原 OQ4 一般分布正向链更不由本叶关闭。

上述只是未展开缺口清单，不是本文件的已证推论或额外实施任务。证明者不得改 measure、指标、相位、范数、起点类、端点或量词；任何修改须由 lead 另立版本。

## 6. 角色与验收边界

冻结状态 FROZEN_PENDING_STATEMENT_REVIEW。下一步由全新独立上下文只读原始来源及此冻结命题完成来源到数学陈述翻译审查；通过后才由新作者写匿名数学证明。作者完整证明必须再经全新匿名数学独审 CORRECT，之后才可指定服务器私有 Lean 实施。独立最终形式审阅不得依赖其他审阅推理；canonical 写入/唯一新 olean emit 还须 lead 另行释放单一窗口，不得与 RademacherIteration39 同时新增规范模块。

本冻结文件没有数学证明或 Lean 执行，也不声称 CORRECT、PROVED 或 LEAN_FULLY_CHECKED。只使用已认证 RademacherCosine 的真实定义/签名，本叶不依赖正在审查的 RademacherIteration 源码。必要透明 def 和 helper 不得静默改变 B0–B3；公开声明数由最终源码实测，不把等价辅助接口数当原始独立义务数。

所有 shell workdir 固定 C:/game/shao lean；全部 Lean/重计算仅指定服务器 workspaces/lead-oq4，旧已认证源、common/root/pins 和旧产物哈希保护。作者唯一新 target emit，独立 canonical target no-o、完整原 source 所有 getModuleIdxFor?=none 无 name/namespace 筛选、actual imports 与全部冻结旧 OQ4 共存，按 owner OR namespace 审计 private/generated/outside-name 常量及传递公理；source/import 完整原始 name/kind/universe/fullExpr type/axioms 与定义体/实例注册标记逐项 exact，lead import-only。禁止 sorry/admit/new axiom/unsafe/native_decide；白名单 propext、Classical.choice、Quot.sound。完整日志/类型/二进制仅服务器，local 仅精炼可审阅证据。完整 Spectrum/OQ4 根保持 OPEN。
