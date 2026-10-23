# U22q + U22r 独立完整最终证明审查

STATUS: CORRECT
Q_NORMAL: CORRECT
Q_TAYLOR: CORRECT
R_PRIVATE: CORRECT
R_PUBLIC: CORRECT
BATCH_INTERFACE: CORRECT
PRECISE_GAPS: NONE_IN_FROZEN_BATCH_SCOPE

日期：2026-10-23。本上下文是本批次唯一 fresh 独立完整最终审查员，与作者分离，按调度使用 gpt-6.1-sol / xhigh，未切换模型。采用 math-theorem，不采用 math-ultra，未派生其他上下文。没有可靠的输入、缓存输入、输出与推理子集 token 计数可报告，故不编造用量或订阅百分比。

本次完整审查全部 244 行冻结 Lean 源码、两份完整冻结范围、四个实际模块所有者的完整导出类型，以及所有新数学推理和必要依赖接口。结论独立来自逐步数学核对，同时复用与精确源码绑定的既有服务器内核和全所有者传递公理证据。没有重新编译、重新审计、修改实现或依赖、改缓存、联网查文献或启动后续任务。唯一写入工件为本报告。

## 1. 精确版本、所有者与定义值覆盖

本地工件目录为 C:/game/shao lean/drafts/oq3/。服务器工作树为 /root/rivermind-data/shao-lean-20261021/workspaces/lead-oq3，分支 feat/oq3-boundary-laplace，凭据记录父提交 3346440dea28ce226bad375c62b288163ea7479e。

| 单元 | 模块及冻结源 | 完整源行数/字节数 | SHA256 |
| --- | --- | --- | --- |
| Q | Shao.OQ3.LocalBoundaryTaylor；u22q-source.lean | 101 行 / 5137 B | 0d566a0932a0c63bb9501abe6d0a25c17fc035046396186ef8b410cbdac89cf4 |
| R | Shao.OQ3.OpenDomainBoundaryTaylor；u22r-source.lean | 143 行 / 7772 B | b13cfa5a2a75b6375bf87fd530bf0921a5776dff613046a0573b769a9186ea8e |

两份新 Lean 源均为 UTF-8、LF、CR=0；本地冻结文件、服务器当前对应源码及成功归档 Q/source-04.lean、R/source-02.lean 逐字节同哈希。冻结范围全部读取并核对：ninety-eighth-unit-scope.md 为 3229 B / 38 行，SHA256 3dce38e6137302551eea1943021c450b095437f6f7ba0d7cb48f7f13ea1ba002；ninety-ninth-unit-scope.md 为 4520 B / 74 行，SHA256 8beddc13f568dba038568a11bab37c5ae15f00dcd35a7e380aa4c004190122dd。服务器各自 scope.md 同哈希。实现没有改变冻结声明的对象、前提、量词或结论。

| 单元 | 实际所有者 | 类型及数学覆盖 |
| --- | --- | --- |
| Q | Shao.OQ3.exists_uniform_normal_increment_bound_at_zero | 完整类型与全证明，源码 9–62 行 |
| Q | Shao.OQ3.exists_uniform_boundary_taylor_bound_at_zero | 完整类型与全证明，源码 64–98 行 |
| R | _private.Shao.OQ3.OpenDomainBoundaryTaylor.0.Shao.OQ3.boundary_tangent_derivatives | 完整私有实际类型与全证明，源码 9–37 行 |
| R | Shao.OQ3.open_domain_quadratic_tilt_boundary_taylor | 完整公开实际类型与全证明，源码 39–140 行 |

Q 实际所有者 2、实际定理 2、公开定理 2、私有/生成定理 0；R 实际所有者 2、实际定理 2、公开定理 1、私有定理 1、生成定理 0。四个所有者全部是定理，实际定义总数为 0；因此没有遗漏的公开、私有或生成定义值待审查。证明中的 let 是已检查的局部对象，不能与额外模块定义混淆。

u22q-actual-types.txt 的全部 23 行 / 961 B 和 u22r-actual-types.txt 的全部 60 行 / 4081 B 均完整读取，并与服务器完整审计输出核对。前者 SHA256 c468368674851db889517940c70989afbfa9df47adedf5004ad93b5664df4dc3；后者 SHA256 440aaf60aeaf2723fda90c0a2f79deadaf12e82bb27173cb4f8baf05b71d3827。完整类型如下；排版中的参数名、let 与实际导出打印的 have 是同一绑定，未省略参数或量词。

~~~lean
theorem exists_uniform_normal_increment_bound_at_zero
    (F : (ℝ × ℝ) → ℝ) (hF : ContDiffAt ℝ 2 F (0, 0)) :
    ∃ rho C : ℝ, 0 < rho ∧ 0 < C ∧ ∀ r z : ℝ,
      |r| ≤ rho → 0 ≤ z → z ≤ rho →
      |F (r, z) - F (r, 0) - (fderiv ℝ F (0, 0) (0, 1)) * z| ≤
        C * (|r| * z + z ^ 2)

theorem exists_uniform_boundary_taylor_bound_at_zero
    (F : (ℝ × ℝ) → ℝ) (hF : ContDiffAt ℝ 3 F (0, 0)) :
    ∃ rho C : ℝ, 0 < rho ∧ 0 < C ∧ ∀ r z : ℝ,
      |r| ≤ rho → 0 ≤ z → z ≤ rho →
      |F (r, z) - F (0, 0) - (deriv (fun t : ℝ => F (t, 0)) 0) * r -
        (fderiv ℝ F (0, 0) (0, 1)) * z -
        (deriv (deriv (fun t : ℝ => F (t, 0))) 0) / 2 * r ^ 2| ≤
        C * (|r| ^ 3 + |r| * z + z ^ 2)

private theorem boundary_tangent_derivatives
    (F : (ℝ × ℝ) → ℝ) (hF : ContDiffAt ℝ 2 F (0, 0)) :
    deriv (fun t : ℝ => F (t, 0)) 0 = fderiv ℝ F (0, 0) (1, 0) ∧
      deriv (deriv (fun t : ℝ => F (t, 0))) 0 =
        (fderiv ℝ (fun w => fderiv ℝ F w) (0, 0) (1, 0)) (1, 0)

theorem open_domain_quadratic_tilt_boundary_taylor
    (mu : Measure ℝ) [IsProbabilityMeasure mu] (theta : ℝ × ℝ)
    (htheta : theta ∈ interior
      (Shao.Probability.bivariateMGFDomain mu (fun x : ℝ => (x, x ^ 2))))
    (hdet : (parabolaCovariance
      (mu.tilted (fun x => theta.1 * x + theta.2 * x ^ 2))).det ≠ 0)
    (level a0 : ℝ) (hlevel : 0 < level) (ha0 : 0 < a0) (hnegative : theta.2 < 0)
    (hmean : (∫ x : ℝ, x ∂mu.tilted (fun x => theta.1 * x + theta.2 * x ^ 2),
      ∫ x : ℝ, x ^ 2 ∂mu.tilted (fun x => theta.1 * x + theta.2 * x ^ 2)) =
        (a0, a0 ^ 2 / level ^ 2))
    (hsaddle : theta.1 = -2 * a0 * theta.2 / level ^ 2) :
    let Omega : Set (ℝ × ℝ) := interior
      (Shao.Probability.bivariateMGFDomain mu (fun x : ℝ => (x, x ^ 2)))
    let nu : (ℝ × ℝ) → Measure ℝ := fun p =>
      mu.tilted (fun x => p.1 * x + p.2 * x ^ 2)
    let means : (ℝ × ℝ) → (ℝ × ℝ) := fun p =>
      (∫ x : ℝ, x ∂nu p, ∫ x : ℝ, x ^ 2 ∂nu p)
    let K : (ℝ × ℝ) → ℝ := fun p => Real.log
      (∫ x : ℝ, Real.exp (p.1 * x + p.2 * x ^ 2) ∂mu)
    let D : Matrix (Fin 2) (Fin 2) ℝ := parabolaCovariance (nu theta)
    let pr0 : (ℝ × ℝ) →L[ℝ] ℝ := ContinuousLinearMap.fst ℝ ℝ ℝ
    let pr1 : (ℝ × ℝ) →L[ℝ] ℝ := ContinuousLinearMap.snd ℝ ℝ ℝ
    let row0 : (ℝ × ℝ) →L[ℝ] ℝ := D 0 0 • pr0 + D 0 1 • pr1
    let row1 : (ℝ × ℝ) →L[ℝ] ℝ := D 0 1 • pr0 + D 1 1 • pr1
    let B : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) :=
      pr0.prod ((2 * a0 / level ^ 2) • pr0 - pr1)
    ∃ L : (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ),
      ∃ e : OpenPartialHomeomorph (ℝ × ℝ) (ℝ × ℝ),
      (L : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)) = row0.prod row1 ∧
      (e : (ℝ × ℝ) → (ℝ × ℝ)) = means ∧
      theta ∈ e.source ∧ means theta ∈ e.target ∧ e.source ⊆ Omega ∧
      let J : (ℝ × ℝ) → ℝ := fun z =>
        (e.symm z).1 * z.1 + (e.symm z).2 * z.2 - K (e.symm z)
      let G : (ℝ × ℝ) → (ℝ × ℝ) := fun w =>
        (a0 + w.1, (a0 + w.1) ^ 2 / level ^ 2 - w.2)
      let F : (ℝ × ℝ) → ℝ := fun w => J (G w)
      let v : ℝ × ℝ := (1, 2 * a0 / level ^ 2)
      let Lambda1 : ℝ := 2 * theta.2 / level ^ 2 +
        (L.symm v).1 + (2 * a0 / level ^ 2) * (L.symm v).2
      0 < -theta.2 ∧ ContDiffAt ℝ ∞ F (0, 0) ∧
        HasFDerivAt F ((-theta.2) • pr1) (0, 0) ∧
        (∀ u v : ℝ × ℝ,
          (fderiv ℝ (fun w => fderiv ℝ F w) (0, 0) u) v =
            (L.symm (B u)).1 * (B v).1 + (L.symm (B u)).2 * (B v).2 +
              (2 * theta.2 / level ^ 2) * u.1 * v.1) ∧
        (∀ᶠ w in 𝓝 (0, 0),
          Shao.Probability.bivariateLegendreRate mu (fun x : ℝ => (x, x ^ 2)) (G w) = (F w : EReal)) ∧
        ∃ rho C : ℝ, 0 < rho ∧ 0 < C ∧ ∀ r z : ℝ,
          |r| ≤ rho → 0 ≤ z → z ≤ rho →
          |F (r, z) - F (0, 0) - (-theta.2) * z - Lambda1 / 2 * r ^ 2| ≤
            C * (|r| ^ 3 + |r| * z + z ^ 2)
~~~

## 2. 全部源码逐段覆盖

下列互补区间覆盖所有源码行，包括导入、局部别名、空行、闭合命令。没有抽样证明段，也没有仅审查公开名称而遗漏私有证明。

| Q 源码行 | 审查内容 |
| --- | --- |
| 1–8 | 全部导入、namespace/scoped/noncomputable section；无新公理或检查设置。 |
| 9–14 | 第一定理全部量词与条件，实际中心法向导数、闭矩形、严格正 rho/C。 |
| 15–25 | H(w)=DF(w)(0,1) 的真实可微性、正 Big-O 常数及 F 的邻域可微性。 |
| 26–38 | 单一正 delta、rho=delta/2、乘积最大范数下整个闭矩形落入开球；在 r,z 前固定见证。 |
| 39–46 | 每条法向线的实际链式导数及减去中心法向线性项。 |
| 47–56 | 整条闭区间上的统一导数界、凸集均值不等式及两个端点条件。 |
| 57–63 | 余项代数身份、范数到绝对值、z 非负时的乘法与精确最终界；分隔空行。 |
| 64–76 | 第二定理完整声明及真实切向截面 g 的 C³。 |
| 77–83 | 复用 P、调用第一定理；正半径取最小、常数取和；两组适用条件全部提供。 |
| 84–98 | 两个误差的精确代数分解、三角不等式及最终非负交叉项控制。 |
| 99–101 | 空行及 section/namespace 闭合，无额外声明。 |

| R 源码行 | 审查内容 |
| --- | --- |
| 1–8 | 全部导入、作用域与 section，无实现或逻辑绕过。 |
| 9–14 | 私有辅助定理完整实际类型，真正嵌套 deriv 与真正 fderiv Hessian 的双切向评估。 |
| 15–20 | g/gamma 的定义、每一点的路径导数以及中心一次链式法则。 |
| 21–29 | 真正 DF 映射在中心的可微性、沿路径求导及连续线性映射固定向量评估。 |
| 30–37 | 有限 C² 产生邻域可微性、连续路径拉回、邻域导数身份及二阶导数转移。 |
| 38–49 | 分隔及公开定理全部原始参数、条件。 |
| 50–77 | 所有 let、协方差/行映射/B、同一 L/e 的存在与所有图表条件；J/G/F/v/Lambda1 的完整定义。 |
| 78–90 | 全部保留 jet、全方向嵌套 Hessian、完整邻域 EReal 等式及统一闭矩形余项量词。 |
| 91–108 | 与声明相同的局部别名；唯一一次 O 应用及原样前提传递。 |
| 109–119 | 用该次 O 的同一 L/e 构造 J/G/F/v/Lambda1，降低光滑阶数并调用私有 helper。 |
| 120–126 | 切向一阶为零、法向为 -theta.2、B(1,0)=v 的真实导数计算。 |
| 127–132 | 全 Hessian 对双切向评估产生实际 Lambda1，所有乘法顺序与曲率项核对。 |
| 133–140 | 从同一 F 的 C∞ 降为 C³，实例化 Q；原样携带同一全部见证/jet/全局率等式，替换系数完成余项。 |
| 141–143 | 空行及闭合命令，无未覆盖声明。 |

全源词法扫描没有 sorry、admit、新 axiom、unsafe、native_decide、implemented_by 或 set_option。noncomputable 不绕过内核，也不引入结论性前提。

## 3. Q 法向增量的独立数学审查

设 F 在零点为 C²，令 H(w)=DF(w)[(0,1)]。C² 先给出 DF 在零点的 C¹，再经固定向量的连续线性映射评估给出 H 可微。由可微性而来的锚定 Big-O，存在 K>0，使某个完整零点邻域内有 |H(w)-H(0)|≤K‖w‖。这不是预设所需 Taylor 界，也不是把 H 在两任意近点之间的 Lipschitz 性当作已知；所需的只是相对于固定中心的界。

有限阶 C² 的局部性另外保证 F 在零点某邻域的每一点可微。将两种邻域性质相交，取 delta>0 使其在 dist(w,0)<delta 成立。实数乘积使用最大范数。取 rho=delta/2，则 |r|≤rho、0≤t≤rho 蕴含 max(|r|,|t|)≤delta/2<delta。因此包括所有闭边和角点在内的同一矩形均处于有效开球内；不需要 rho 随 r 或 z 改变。

固定任意满足该矩形条件的 r,z。令 g(t)=F(r,t)-H(0)t。对每个 t∈[0,z]，路径 t↦(r,t) 的导数为 (0,1)，F 在路径点可微，故 g'(t)=H(r,t)-H(0)。由于 0≤t≤z，有 ‖(r,t)‖=max(|r|,t)≤|r|+z，因而整条线段统一满足 |g'(t)|≤K(|r|+z)。闭区间凸，两个端点 0,z 均属于区间。均值范数不等式直接给出

|g(z)-g(0)| ≤ K(|r|+z)|z| = K(|r|z+z²)。

准确展开左边即第一定理。K、rho 均在任意 r,z 之前选取，可以依赖 F，但不依赖矩形中的点。z=0 时误差和右边均为零；r=0、r<0、r=±rho、z=rho 均被覆盖。没有除以 r 或 z，没有遗漏零点，没有把 punctured 邻域误写成完整闭矩形。Q_NORMAL: CORRECT。

## 4. Q 完整 Taylor 余项的独立数学审查

令 g(t)=F(t,0)。路径 t↦(t,0) 光滑，由 F 的中心 C³ 得到 g 的中心 C³。已独立完整审查且已完成 LF 精确门的 P 接口给出正 rhoT、CT，使闭双侧 |r|≤rhoT 上，真实二次 Taylor 余项受 CT|r|³ 控制；其系数是 deriv g 0 和 deriv(deriv g)0。Q 第一定理由 F 的 C² 给出正 rhoN、CN，控制同一 F 的法向误差。

取 rho=min(rhoT,rhoN)>0、C=CT+CN>0。一个 rho 同时保证两组界。源码 heq 是完整代数身份：目标二维余项等于法向余项加切向二次 Taylor 余项；没有多余或缺失常数项，也没有法向项符号错误。三角不等式后得到 CN B+CT A，其中 A=|r|³≥0、B=|r|z+z²≥0。它不超过 (CT+CN)(A+B)，差恰为 CN A+CT B≥0；源码 nlinarith 提供的两项非负性与此一致。

因此获得整个同一闭矩形上的 C(|r|³+|r|z+z²)，保留真正一、二阶切向系数与真正中心法向系数。没有要求 Hessian、混合导数或三阶导数的现成统一界，也没有把所需余项当假设。两个符号的 r 以及 z=0 的切向边均有效。本结论对每个固定 F 局部统一，不声称对任意概率律或 saddle 参数族统一。Q_TAYLOR: CORRECT。

## 5. R 私有辅助定理的独立数学审查

令 gamma(t)=(t,0)、g=F∘gamma。所有 t 上 gamma'(t)=(1,0)。F 的中心 C² 保证中心可微，第一次链式法则给 g'(0)=DF(0)[(1,0)]，恰是第一合取项。

二阶部分先由 C² 推出实际函数 w↦DF(w) 在中心可微。沿 gamma 使用链式法则，再对固定向量 (1,0) 评估，得到 t↦DF(gamma(t))[(1,0)] 的真实一阶导数，值为 D(DF)(0)[(1,0)][(1,0)]。评估乘法法则的额外项是 DF(0)[0]=0，源码 map_zero/add_zero 的化简准确。

关键是尚不能仅对 g'(0)=DF(0)[(1,0)] 的单点等式再求导。源码另用有限 C² 的 eventually 得到 F 在一个真正邻域内处处可微；gamma 在零点连续且 gamma(0)=0，将此拉回成零点完整邻域。对其中每个 t 应用实际一阶链式法则，证明 deriv g 与上述评估函数在邻域内最终相等。EventuallyEq.hasDerivAt_iff 的 mpr 方向从评估函数的实际导数转移到 deriv g，再取 .deriv 得到嵌套 deriv 的值。

所以没有对孤立点身份求导，没有依赖不可微点处总函数 deriv/fderiv 的默认值，没有偷用全局 C²。该私有声明是实际模块所有者，并确实纳入完整内核/公理输出。R_PRIVATE: CORRECT。

## 6. R 公开定理、同一见证与批次接口

R 仅一次调用 O 的 open_domain_quadratic_tilt_boundary_coordinate_jet，原样传入 mu、theta、htheta、hdet、level、a0、hlevel、ha0、hnegative、hmean、hsaddle。随后所有结论都使用这一次得到的同一 L/e。局部 nu、means、K、D、pr0/pr1、row0/row1、B、J、G、F 与声明和 O 接口逐项相同；没有第二次存在选择，没有把一组图表的光滑性用于另一组图表的率，也没有把不同 covariance 的逆映射混用。

令 c=2a0/level²、v=(1,c)。O 的实际 DF(0)=(-theta.2)pr1 通过私有 helper 给切向 deriv g 0=0，通过 (0,1) 评估给实际法向 DF(0)[(0,1)]=-theta.2。严格正性 0<-theta.2 由 O 原结论保留，来源是明确的 hnegative。它不是由协方差非奇异性推出来的。

B(1,0)=(1,c)=v。私有 helper 将实际切向嵌套 deriv 改写为完整 Hessian 的双 (1,0) 评估。O 的所有方向 Hessian 公式于是给出

g''(0) = (L.symm v).1 + (L.symm v).2*c + 2*theta.2/level²
        = 2*theta.2/level² + (L.symm v).1 + c*(L.symm v).2 = Lambda1。

曲率修正项的符号是加 2*theta.2/level²；该项本身在当前 hnegative 下为负，不能遗漏，更不能借此断言 Lambda1>0。L 的行映射等于真实协方差 D 的矩阵作用，因此 L.symm 是同一真实 D 的逆作用；该式正是源的 v D⁻¹ vᵀ 加曲率修正。没有额外对称性/正性假设被藏进 ring。

对同一 F，O 的中心 C∞ 降为 C³ 后调用 Q 全余项定理。用已经证明的切向一阶零、法向 -theta.2、切向二阶 Lambda1 精确替换其三个系数，即得到新界。rho/C 在 r,z 前选取，均严格为正。结论原样保留 hL/he/hs/ht/hsource、中心 C∞、完整 HasFDerivAt、任意 u/v 的完整嵌套 Hessian 和真实全局 EReal 率的完整邻域最终等式；并非只保留切向 Hessian 或局部变换的形式定义。

量词细节：hglobal 是对完整 𝓝(0,0) 的最终等式，rho/C 是 F 余项的矩形见证。声明没有明确说其展示的这个 rho 也满足矩形中每点的 hglobal；它保留了二者的同一 F 与完整邻域信息。若后续消费者需要一个同时满足率身份和余项的闭矩形，可从 hglobal 的正邻域半径与现有 rho 再取正的较小值。此为现有结论的直接缩小半径后果；本报告没有把声明中的最终等式误读为全空间等式，也没有把 rate 定义为任意选择的局部 J。

必要依赖按照精确版本复用：P 最终 LF 源为 7ecd01d72c2f28ec06080d628f5d5370b3ae03b312acbae18a104569f8fef1b6，其独立报告 u22p-proof-review.md 为 3848e294838fc344b42e3eaac08b5e563a8e00c665af74996e9d557a730b3571；已读其所需完整接口及最终 LF 差异/成功证据部分，LF receipt 为 93c635cbe7c01579a9fba5abaca8e7273c51e396cdb5ee76cdd0a0150491eb87。O 精确源为 c77549b105f0a13168f9909e54f856ec21efa1ac23dca852a2122b44e4dfedfa，独立报告为 adb7cc5e7139f64be3ee27d5cffa4eb7a807f77e4161c18430bbaaff3d68d1e0；其全部实际公开接口已读。本地这些哈希与服务器当前直接依赖源码一致。未因更换审查上下文或 Q/R 到达新节点而重审已接受旧证明或重复旧门；O 已冻结的历史 CRLF 字节也未被修改。

R_PUBLIC: CORRECT。BATCH_INTERFACE: CORRECT。本批没有未覆盖的数学接口、见证不一致、循环依赖或证据版本缺口。

## 7. 原源忠实性与明确限制

原源为只读 C:/game/shao/current/oq3/proofs/r2/repair01.md，SHA256 9d2e554838aa15b645aaf74a42468d423fed606aa91c1181d0dddf4e87c57cfd。本次完整读取相关 111–180 行，特别是式 (8)–(11) 的全部 124–159 行，并读取该文 1–40 行及 R2 report.md 的 36–79 行以核对源参数、根假设和外部结果归属。

level 对应源固定 x，theta 对应 (hat s0,hat t0)。G(r,z)=(a0+r,(a0+r)²/level²-z) 是式 (8) 的准确逆坐标，第二坐标的负号保持。源 F 是该坐标下的实际率；本批 J/G/F 沿 O 的同一真正局部逆，且保留对整个真实参数域定义的 EReal 率等式，故其 germ 对应实际率而非任意光滑替代物。常数项是 F(0,0)；中心 G(0,0)=(a0,a0²/level²)，且率等式在中心也成立。

式 (9) 的切向一阶零、法向 lambda=-theta.2>0 均保留。式 (10) 的实际二阶系数公式成立，但其中额外的 Lambda1>0 不在本批结论内，也未被本批假装消去。式 (11) 的固定小闭矩形、z≥0 一侧、双侧 r、真实二次系数和 C(|r|³+|r|z+z²) 余项已经由 Q/R 给出。该界是对每一固定 admissible 参数/图表的局部界，不是关于整个紧倾斜族的统一常数结论。

后续的 Lambda1 正性、c(z+r²) 局部正下界、a>0/q>0 和原尾域与 z≥0 的等价、绝对 Jacobian 为一、振幅/协方差行列式控制、Laplace/Edgeworth/胞元和真正远场概率、原 B/D 根结论均不在本批闭合范围。全局率的邻域最终等式不等于远场概率界，局部 Taylor 也不能替代它们。原统一谱界、严格 0<beta<2/5 的弱 Cramér 条件、统一矩条件、正则/唯一全局 saddle、Lambda1 正性及修正后明确远场概率前提均继续按原根范围保留；本批没有削弱、证明或重新解释它们。Song 的统一 Edgeworth 输入及其他原有外部归属保持原样，本报告没有作新的外部定理或新颖性认证。

hlevel、ha0 等原几何条件均保留；本局部微积分结论只须其中实际用到的解析条件，不宣称这些一般条件自动构造一个原根所需的 admissible saddle。原源 x∈(0,1) 等概率范围未被本地 level>0 的更通用微积分辅助接口替代。所有原研究根的完成状态按当前项目范围维持，不能用这两个局部分析模块宣布原 B/D 闭合。

## 8. 固定主 API 的来源与条件核对

全部主 API 从指定服务器只读 Mathlib 包视图读取，没有联网更新。实际 mathlib HEAD 为固定 807d3836b165983210ee2ecf3cd28f239436949c；下列实际所用源码文件均逐字节等于该 commit 的 Git blob。已知包视图 Lake 警告因而没有掩盖这些 API 的源码修改。

| 主源码与已读行 | 条件及本证明的使用 |
| --- | --- |
| ContDiff/Comp.lean:724–730、505–507 | fderiv_right 要求 m+1≤n；这里 m=1,n=2。clm_apply 由实际有界双线性评估保光滑，固定向量为常值函数。 |
| ContDiff/Defs.lean:1035–1037 | eventually 的条件 n≠∞；Q/R 私有 helper 均在有限 n=2 应用，R 的 C∞ 先降为有限阶。 |
| FDeriv/Basic.lean:838–840 | 可微推出以固定中心为锚的 Big-O；没有断言任意点对 Lipschitz。 |
| Asymptotics/Basic.lean:79–81；Defs.lean:69–79 | exists_pos 给严格正 K；IsBigOWith 是范数最终不等式，不用除法或排除零分母。 |
| MeanValue.lean:695–699 | 需要区间内每点 HasDerivWithinAt、统一导数范数界、凸集和两个端点属于集；Q 全部给出，z=0 也合法。 |
| Deriv/Comp.lean:375–377 | 真正 HasFDerivAt 与路径 HasDerivAt 的链式法则，无缺失邻域或单射假设。 |
| Deriv/Mul.lean:581–583 | 连续线性映射评估的真实乘法求导；常向量导数为零，额外项消失。 |
| Deriv/Basic.lean:611–613 | 完整邻域 EventuallyEq 允许转移 HasDerivAt；R 实际构造该邻域身份，未从单点等式推导。 |

上述文件 SHA256 依次为：ContDiff/Comp a616137e4d47245bbb576430d569109a2020e7478faa01b8dfd8286eb2d3de5a；ContDiff/Defs c436e0c185d3a52da5be9be371a3c954e7a63714288aaba7ae67bc769f32b825；FDeriv/Basic ec95a9dadc68ab0164909db152763d4581c73cb36282914bcc195acb85a7a690；Asymptotics/Basic b45ad8c93b8a12fc6309ded66210ec81417cb6ff8393ef02bac86867b45f2b6f；Asymptotics/Defs 68ef9c1b2d13f99770bcd0c679a23f078f634ea344ff914d7d634ba1682104ed；MeanValue 0f10e5afeb80809192b023486b09e98939d0a6bd0920ab3882bddb41a715d947；Deriv/Comp 4e9fe6ea155c453158432d02e291ece4458b4fd331bdac00c3030e7537ab1e28；Deriv/Mul 668434e58a11f6fe2c599adc9655494d0f23ba42937662499884df02daaa8c7c；Deriv/Basic 31e8aceba6c650a5628a321b25feaff0d2e1f4e198cc5f540e64b80d31ee51b3。

同时定向读取已接受依赖的真实定义：BivariateLegendre.lean:20–33 是指数可积性域及对其整个 subtype 取 EReal 上确界的真实率，非仅局部驻点值；其 56–71 行给真正全域上界和达到值推出相等。该文件服务器 SHA256 d8bd5dc7099ffdbf52282ebb41ad03145a50b42547dec55bb42caacb31ed5f58。RegularCovariance.lean:20–24 用 X 与 X² 的真实方差/协方差组成对称二维矩阵，服务器 SHA256 0add3476cc949edc593e15dc195934a6df78a41a55f4a2281f66095733d4c853。此处核对必要定义语义，不重复旧模块完整证明验收。

## 9. 精确服务器内核与全所有者传递公理凭据

Q run 为 /root/rivermind-data/shao-lean-20261021/runs/oq3/u22q-20261023；R run 为同目录下 u22r-20261023。两次作者首个成功门分别是 Q attempt 4：exit 0、5.856044622138143 s；R attempt 2：exit 0、6.934249088168144 s。首个全实际所有者审计分别 exit 0、6.573224429041147 s 与 exit 0、5.7012829054147005 s。资源记录均为 CPU14–17、native memory 8192 MiB、jobs4、autoImplicit=false；实际工作树 lean-toolchain 为 leanprover/lean4:v4.36.0-rc1，lakefile 保持上述 mathlib pin 与 autoImplicit=false。

两份成功 build 日志及两份完整 audit 日志均已读取。成功内核日志只有已知薄包视图 Lake 警告；没有 Lean 错误。审计源完整读取：按 getModuleIdxFor? 实际模块所有权遍历环境中全部常量，不以公开清单或 namespace 前缀冒充完整所有者；拒绝 owner axiom；对每一实际所有者执行 Lean.collectAxioms 递归传递收集并拒绝白名单外公理；另确认所有冻结目标实际存在且为定理。所有四个实际所有者显示的公理均严格为 [propext, Classical.choice, Quot.sound]。输出 Q frozen definitions=0、frozen theorems=2、all theorems=2、all declarations=2、PASS；R 相应为 0、1、2、2、PASS。私有 theorem 真实出现在 R 的输出中。无 sorryAx 或未覆盖定义值。

| 工件 | Q SHA256 | R SHA256 |
| --- | --- | --- |
| receipt.json / 本地 u22q、u22r-receipt.json | b1c9e8da3f4793ffec4cbe99102a3b04c03414a02ee51ea82a41c33175428b32 | 9c0f682462f000c01cbc0d3422b647601b5b6fec02110f042bb34b129dcc0ba9 |
| Audit.lean | 51b5fadd7908258201aa8766aabd862ea85d53566131728717b6fece6645cec7 | 29fa71e93315ff46adefc2d20bbeae6d307c1673b6038995df99bcb99ddb65d9 |
| build-history.json | ba94ef7499cba17467132b789e83eb792fb1410f1c72e115be43ea475691d529 | 844804810dc8fb9ffeca9733e3cf62b5c2fdb3b62fff5f42855fd8d423195035 |
| audit-record.json | a685122552ff3cf4569efa8a46fd520879d51aac8ccee76aeb478b0af759d17f | d4cb950c17e32e36daaa72c49e3c9d43fd22b0980452939aa4f946eab06e9d4c |
| audit-environment.json | 6052d170421307526e0272f38000f1ed186bbd4c64b02e493d86098262db85f3 | ae9262c61733d38480cba3a9d2558b53b894faa803af20798d7884ff26d52861 |
| 成功 build-04.log / build-02.log，均 133 B | fe9a6b741bba0630c9977614157f0259907b0b7ebce576a9400b542ee4518626 | fe9a6b741bba0630c9977614157f0259907b0b7ebce576a9400b542ee4518626 |
| 完整 audit.log，1208 B / 4328 B | b9a103d991f5a905ef9d0b0040a7874203063024f40619fec7cf43d6bf93693c | baa426a5f18c46cde3fddecde72eb2a1c991c24ffd21cf49df305152beebf251 |

以上本地对应工件与服务器文件全部直接核对同哈希。actual-types、scope、最终源绑定见第 1 节。环境清单保持 root 授权的 accepted-source-view，只添加 lane 自有新对象，不写共享缓存。

定向检查只读导入视图的 P/Q/O/R 对象路径，四者都解析到该 lane 工作树对应自有对象；同一路径读取的 SHA256 为 P ac1d743f360f14e70d84d3a0ab4de0d0347009b85f26a38f347aa123ab390bdd；Q 5e6a3ce2f66a9bbd3338c03d7c6d8a465e1cbe5003da85314b68bde62e5fac9e；O d593a9c439572b7bfbdc6e451876513372b0dbb8a2f43e8fb10101c4043e3f50；R 79dbfe6730c023911f392ebeba0a4d7296478acf5f03b9e4e6f57e725608b383。这是精确所用路径的观察，不是全包缓存清洁性或新全项目构建声明。

Q 的失败 attempt1–3 和 R 的失败 attempt1 的完整历史及归档 source/log 文件仍在各自 run 中；最终成功不能覆盖失败分母。已核对各归档源哈希与完整 receipt 内的相应历史一致。没有重新执行任何已通过内核/公理门，亦没有按当前基线推进而重复旧门。

## 10. 最终裁决与停止点

四个实际定理及本批接口全部 CORRECT：Q 从真实中心 C²/C³ 产生固定正闭矩形上的法向/混合和完整 Taylor 界；R 的私有 helper 正确联结嵌套切向导数与真实 Frechet Hessian；R 公开定理对 O 同一实际 L/e/J/F 给出原式二次系数和余项，并保留 O 完整 jet 与真正全局 EReal 率的邻域最终等式。全部 244 行、4/4 owned 类型和 0/0 definition 值覆盖完整，精确源码服务器证据齐全；在此冻结范围内没有关键缺口。

本批是原源局部分析依赖的闭合，不是 Lambda1 正性、式 (13) 正下界、振幅/Jacobian/尾域等价、Laplace 或原 B/D 根的闭合，也不构成数学新颖性声明。最终文件字节数、行数和 SHA256 由外部最后完整性检查报告封存。本审查员在该检查后停止全部工具调用和写入，不开始下一任务。

