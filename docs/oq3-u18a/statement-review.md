# U18a v3 独立声明／来源／固定 API 聚焦审查

STATUS: IN_PROGRESS

## 1. 先行持久化的完整类型盲译

本轮先仅提取冻结 v3 唯一 Lean fence，尚未读取 v3 正文或 v2/v3 差异及本轮机械材料。已有 v1 数学审查及 v2 参数名拒绝背景明确存在；以下重新翻译实际两个完整类型，不能以旧结论代替 v3 字节核对。零公开定义，不存在需另译的公开定义体。

```lean
theorem stage_normalLayerConditionalLaw_weak_tendsto (mu : Measure ℝ)
    [IsProbabilityMeasure mu] (J : ℕ) (q a : ℝ)
    (hb : ∀ᵐ x ∂mu, |x| ≤ 4 + Real.sqrt 10)
    (hq : (∫ x : ℝ, normalValue x ∂mu) = q)
    (ha : (∫ x : ℝ, x ∂mu) = a) (hS : 0 < normalVariance mu)
    (hD : 0 < (parabolaCovariance mu).det)
    (hrange : ∀ᵐ x ∂mu, x ∈ Set.range (fun i : Fin 4 ⊕ Fin J =>
      stageAtom (fun j : Fin J => addedAtom j.val) i))
    (hpos : ∀ i : Fin 4 ⊕ Fin J, 0 < mu.real
      {stageAtom (fun j : Fin J => addedAtom j.val) i})
    (d : ℕ → ℝ) (hd : ∃ M : ℝ, ∀ n : ℕ, |d n| ≤ M)
    (hlayer : ∀ᶠ n : ℕ in atTop, ∃ k : ℤ,
      d n + (n : ℝ) * q = dyadicMesh J * (k : ℝ)) :
    Tendsto (fun n : ℕ =>
      (⟨normalLayerConditionalLaw mu q a (d n) n,
        normalLayerConditionalLaw_isProbabilityMeasure mu q a (d n) n⟩ : ProbabilityMeasure ℝ))
      atTop (nhds (X := ProbabilityMeasure ℝ)
        (⟨ProbabilityTheory.gaussianReal 0 (Real.toNNReal (transverseVariance mu)),
          by infer_instance⟩ : ProbabilityMeasure ℝ))

theorem stage_normalLayerConditionalLaw_real_tendsto (mu : Measure ℝ)
    [IsProbabilityMeasure mu] (J : ℕ) (q a : ℝ)
    (hb : ∀ᵐ x ∂mu, |x| ≤ 4 + Real.sqrt 10)
    (hq : (∫ x : ℝ, normalValue x ∂mu) = q)
    (ha : (∫ x : ℝ, x ∂mu) = a) (hS : 0 < normalVariance mu)
    (hD : 0 < (parabolaCovariance mu).det)
    (hrange : ∀ᵐ x ∂mu, x ∈ Set.range (fun i : Fin 4 ⊕ Fin J =>
      stageAtom (fun j : Fin J => addedAtom j.val) i))
    (hpos : ∀ i : Fin 4 ⊕ Fin J, 0 < mu.real
      {stageAtom (fun j : Fin J => addedAtom j.val) i})
    (d : ℕ → ℝ) (hd : ∃ M : ℝ, ∀ n : ℕ, |d n| ≤ M)
    (hlayer : ∀ᶠ n : ℕ in atTop, ∃ k : ℤ,
      d n + (n : ℝ) * q = dyadicMesh J * (k : ℝ))
    (A : Set ℝ)
    (hfrontier : ProbabilityTheory.gaussianReal 0 (Real.toNNReal (transverseVariance mu))
      (frontier A) = 0) :
    Tendsto (fun n : ℕ => (normalLayerConditionalLaw mu q a (d n) n).real A)
      atTop (nhds ((ProbabilityTheory.gaussianReal 0
        (Real.toNNReal (transverseVariance mu))).real A))
```

第一目标的量词：对同一个真实实数概率测度 μ、自然数阶段 J、实数 q 与 a，假设 μ 几乎处处 |X|≤4+√10，实际 Eμ[normalValue X]=q、Eμ[X]=a；同一 μ 的 S=normalVariance μ 严格正、parabolaCovariance μ 的行列式严格正。μ 几乎处处属于四个固定基点与 J 个新增 stageAtom 的有限范围，并且每个该实际索引单点的 μ.real 质量严格正。给定全自然数实序列 d，存在一个同一实 M 对全部 n 控制 |dₙ|≤M；仅要求最终全部 n 满足 dₙ+nq=h_J*k（某整数 k，h_J=dyadicMesh J）。

第一结论：把每个实际 normalLayerConditionalLaw μ q a dₙ n 与公开的全 n 概率证明封装成 ProbabilityMeasure ℝ，此自然数序列在 atTop 下趋于同一真实 Gaussian 概率测度，均值 0，NNReal 方差参数为 Real.toNNReal(transverseVariance μ)。目标 nhds 显式选择载体 X=ProbabilityMeasure ℝ，序列点与目标匿名 pair 均显式标为同一类型；语法意图是使用该类型已有的标准拓扑实例，未引入新拓扑、局部实例或假设。

第二目标保留完全相同的 μ／J／q／a／有界与真实均值／S及det正／有限阶段范围与全部正单点／同一 d 的全序列有界与最终格相容。对任意实数集合 A，唯一集合门是同一目标 Gaussian 对 frontier A 的实际测度为零；结论为实际条件律的 .real A 质量趋于该 Gaussian 的 .real A。没有添加 MeasurableSet A、有界 A、目标 A 质量正等条件；该实质量结论的 nhds 载体为 ℝ。

显式边界：J=0 和全 n（含0）保留；类型未输入早期层质量正，也未删去实际条件律零层时的补定义。q/a 受各自真实积分门约束而没有被改成 q/4；d 无须趋于常数。T 的正性必须由同 μ 的 S、det 正性解释，不能只靠 toNNReal 夹零。此盲译只记录实际 v3 类型；X 参数名、拓扑实例与精确版本差异留在后续独立核对。

## 2. 独立精确差异与实际参数名

首读检查点已持久化为57行／4630字节／SHA256 26891658840f93c844141e8b4f49c357e6bb8dd4cb5fb977ae88d63a8894638e。本节只追加，不覆盖该盲译或任何 v1/v2 文件。

独立提取 v2/v3 唯一 fence，逐字符比较得到：v3 精确等于 v2 将唯一 `nhds (α := ProbabilityMeasure ℝ)` 换为 `nhds (X := ProbabilityMeasure ℝ)` 的文本结果。第二完整目标全体字符相同；第一目标除此 binder 名外全体字符相同。还核对完整原 `# OQ3-U18a` 历史正文尾段，亦仅有同一替换；四 imports、namespace、open、全部假设、量词顺序及结论均未变。新增 v3 说明前缀仅记录修复历史，不能替代 frozen fence。

本轮定向重新读取固定 Mathlib/Topology/Defs/Filter.lean 118–135行：第122行确为 `variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]`，第131行确为 `irreducible_def nhds (x : X) : Filter X`。因此新 v3 的 `X :=` 与真实载体 binder 精确匹配，清除了 v2 的错误具名参数。该文件的实际定义用既有开放集生成该载体上的邻域滤子，不增加第二种拓扑。

固定 IrreducibleDef.lean 93–108行本轮亦重新定向读取：先按原 declSig 定义 definition，再封装 wrapped，最后 def nhds := val_proj @wrapped，保留原函数类型及其 X binder；后续只生成等式和 irreducible／eqns 属性，没有改 binder 名或引入特殊拓扑。故此修复有真实生成语义支持，不是猜测熟悉的参数名。

显式 X=ProbabilityMeasure ℝ 在匿名 pair 前先给出载体，后续 TopologicalSpace 的所需目标就是具名的 ProbabilityMeasure ℝ。ProbabilityMeasure.lean 299、305–309行实际标准实例明确由 toFiniteMeasure 诱导弱拓扑；在 ℝ 的既有 TopologicalSpace／Borel／OpensMeasurableSpace 下可用。这里没有新增或遮蔽全局／local instance，没有改变序列测度、目标测度或选择任意 subtype 拓扑。实例存在与修改后的声明实际 elaboration 成功是两项事实：前者由原库及既有诊断成立；后者本轮未运行，仍待作者后续验证。

## 3. 沿用并自足说明的来源与数学/API门

原 R1 第314–329行针对同一固定有限有界 law，EY=q、EX=a、S=Var(Y)>0、τ²=detCov(Y,X)/S，以及可达有界层 dₙ，输出连续集上的混合层极限；339–346行通过条件特征函数、Gaussian 积分和 Lévy 定理完成桥，不要求切向密度。v3 没有改变此数学问题，也没有把一般 a 偷换成 q/4 或把仅有界 d 变成收敛 d。

实际 U13c 的 normalLayerConditionalLaw.lean 12–18行是同 μ 的真实 n 重产品：零原层质量时 dirac0，否则实际 cond 再 map 统计量 (ΣX−na)/√n。公开42–50行给每个 q/a/d/n 的真概率证明，所以 n0、早期零层或离格仍是 ProbabilityMeasure 序列元素；不能删 fallback，亦不能在这些项上取消 sqrt0 或除层质量。140–154行公开 stage_normalLayerConditionalLaw_charFun_tendsto 在本目标完全相同的全部模型门及最终格相容下，对任意实 s 给实际特征函数趋 exp(−T*s²/2)。晚期层质量正与 n≥1的约分门已在 U13c 真正证明，不是本 v3 偷加或假设。

同 μ 的 RegularCovariance 实际定义为 S=variance(normalValue)、T=det(parabolaCovariance)/S。hS>0 和 hD>0 先给 T>0，随后才用 Real.toNNReal 的非负实 coercion 还原成 T；gaussianReal 的 NNReal 参数是真方差，不是标准差。hb 与真概率保证相关真实 L2／可积和协方差语义，不靠不可积 variance 总化。Gaussian.Real 481–486行实际 charFun_gaussianReal 为 cexp(t*mean*I−v*t²/2)；mean=0、v=toNNReal T 并使用 T≥0，准确匹配上述 U13c 的负号、平方和二分之一系数。

第一目标的实际主 API：LevyConvergence.lean 39–40行要求实有限维 inner-product、可测／Borel，ℝ 满足；201–203行 ProbabilityMeasure.tendsto_of_tendsto_charFun 消费实际全 n 概率序列对全部频率的逐点特征函数收敛，输出同一概率类型的弱 Tendsto。204–205行由目标 charFun 连续性产生 tightness，不需输入新的 tightness、全频率统一速率或 hcont。ProbabilityMeasure.lean 365–371行把其实际弱拓扑刻画为全部有界连续实函数积分收敛，故修复后的 nhds 仍是来源所需真正弱拓扑。

第二目标的实际主 API：本轮再次读 Portmanteau.lean 334–341行 prime 版本的全部长类型。其门是弱 Tendsto、ℝ 标准 OpensMeasurableSpace／HasOuterApproxClosed，以及目标 measure(frontier A)=0；结论是底层 ENNReal-valued measure A 的 Tendsto，确不另需 MeasurableSet A 或 A 有界。目标是真 Gaussian 概率，measure_ne_top 保证目标 A 的质量不为∞，可复合 ENNReal.tendsto_toReal 得实际 .real A 收敛。非 prime 版本的 NNReal apply 不被误报为 real；0目标质量也允许，不需正质量。

J0 仍含四个实际正基点；n0／空层／空集／全空间／目标 A 零质量均保留正确概率语义。q/a/J/μ 在全 n、全频率与全部目标集合前固定；没有按 n 重选 law 或偷偷输入新的 ell／energy／hsecond／q 窗口。所有边界及数学量词与原已核 v1 相同，v2 拒绝的唯一实质是错误具名 binder；v3 已按固定 API 修复该点。

## 4. 环境复用边界与当前未实现义务

本轮是 focused 声明门，依赖图与 imports 完全不变，沿用 v1 已独立验证的实际 public／public meta 可达证据和 root51 readiness，不重复扫描完整图或重算稳定51对象。既有真实四 imports 是 NormalLayerConditionalLaw、LevyConvergence、Portmanteau、Gaussian.Real；标准 ProbabilityMeasure 弱拓扑、Gaussian charFun、Portmanteau prime／toReal API 均来自该既有公开图。末节只绑定必要当前字节／pins／git 和已有收据，不把缓存绿灯当数学证明。

本 v3 尚无作者 target elaboration 或实际 proof 通过事实，本票不能预报 kernel PASS、Audit PASS 或新对象存在。旧88行失败候选仍只作历史材料；本轮不读其证明体、不重复三次失败、不读作者 TopologyAPI 程序或任何 candidate／future／implementation 笔记。v1 的数学可行声明票、v2 的 INCORRECT 票和全部旧scope都应保留，不被 v3 透明修复追改。

原目标→本门只批准 R1(15) 条件 Lévy 与连续集质量桥的两个修复声明；拟消除→真实有界相容层条件特征函数到弱收敛／任意连续集的接口；直接消费者→同实际前缀 law 的 hcont 及已接受 moving 曲边／sign-tail／层和后继；剩余→完整作者实现及独立 proof 终审、实际 hcont 家族实例化、无条件15/19／hW／最终 diagonal／根组装。既有条件式后继不等于这些原始义务已无条件完成。

## 5. 末阶段必要机械绑定及不重复检查的范围

冻结 v3 scope 两端实际69行／8608字节／SHA256 7176c01d07c69de87e6a27de35d91da9cfbeeb5bf723ea71a227fd721b69cd6c；第1节完整 fence 与该版本精确一致。旧 v1 声明票两端仍154行／20145字节／SHA256 3e1b61d8d54646f1bff76f5b005c958fc63cd0994d2b9125db87e7b56c5fbf25，旧 v2 INCORRECT 票两端仍121行／16324字节／SHA256 6c800d9dca1c37eaa0f1c84bd4a8f32319b09f68cdd1208c1b53633160420350，均原字节保留。本新报告57行盲译检查点在追加最终部分前再次核 SHA 一致，未追改历史。

定向重新读取并绑定的实际 Filter.lean 为361行／15799字节／SHA256 700acc36eb3f275a42212da01f1c35b01010cef40b30300b9623e382e8146891，IrreducibleDef.lean 为112行／3676字节／SHA256 aa96532c21124803fd7a0788ce45cc9e453a31934dc911503833c91c4024b726。U13c 直接承重源 NormalLayerConditionalLaw.lean 仍199行／10634字节／SHA256 94e2507a83dfc232280043567f6a2f07950d39da10b45699777ac1316f24281a，没有为 v3 修改任何已接受源。

root 正式 readiness.json 当前仍71行／6339字节／SHA256 f3cbc33970a4c1705e3785fa381a6869a4bc68595687461a59509329cbc10468；旧 TopologyAPI-receipt.json 当前7行／421字节／SHA256 5a46f01ef3aad499106dfd593c58433672585175948f389b0faa495d11006654。本轮只绑定收据 hash，不再逐项重验稳定51对象或重复 root 两 import smoke，也未重复既有目标性实例诊断。诊断的旧 exit0 支持实例存在，不被误报为 v3 类型或证明通过。旧 v1 三次失败和 coded error 事实保留在 v2完整票，本轮未下载／重读完整原日志或重放失败。

固定 Mathlib HEAD 807d3836b165983210ee2ecf3cd28f239436949c；lean-toolchain SHA d581a24b57a4ae9e0b2132ca8ac7cc3ac336a9fc2751fe6b29414e2d434d54c4、lake-manifest.json SHA40e8e3385f2b0c8ae56fa9de6947301472379cb62eeb83247944827c38b8af6e 与已核 v1/v2相同。原四 import 公开/meta 图的24 Shao／2973 Mathlib物理与0缺项证据沿用 v1正式终票，不因当前仅改具名参数而重扫大图；canonical24源 map 原SHA5bc830200958e3f4b7eb77a6ed68f257313ad01622fba41f50a6e4073917829a只作为既有审查证据，不虚称本轮重新计算。overlay 行政通知不被当作原共享 cache 或版本变化。

本轮观察 lane branch 为 feat/oq3-normal-layer-weak-convergence，HEAD69e4e9e0177e75294ebac5eb28d5304dcc74c4cc，status 仅 NormalLayerWeakConvergence.lean untracked。该旧 v1失败候选仍88行／4349字节／SHA59da27f11a232a03e572566801d72b68d306350028336654137c4e4dc86ad6bd；只读 hash，未读取候选实现体。没有 v2/v3 作者 source／probe／成功 target／Audit 的新验收事实，本票不预报它们。

仅写本新报告及授权 run/statement-review-v3.md；所有远端项目命令 taskset -c 14-17 只读，未占重型 Lean 槽。没有 Lean／#check／probe／build／rebuild、cachewrite、spawn、commit、发布、source／scope／旧票／shared／pins／心跳修改或 raw完整日志下载，不干预外部 CPU0–9／80GiB。作者 candidate／future／implementation 笔记与 TopologyAPI 程序体没有被读取。

## 6. 最终独立 v3 声明裁决

STATUS: CORRECT

JUSTIFICATION: v3 唯一新增的显式载体参数使用固定 nhds 的真实 X binder，精确清除 v2 的错误具名参数，同时选择现成 ProbabilityMeasure ℝ 标准弱拓扑；两个完整类型除这一语法修复外的数学量词／假设／对象与原 v1/v2完全相同。全 n真实条件概率及零层dirac0补定义有效，U13c 对同一有界相容 d 给真实特征函数极限；先由 hS/hD 得 T>0，再合法还原 Gaussian 方差参数，恰能消费固定实数 Lévy 接口。Portmanteau prime 覆盖任意 frontier-null A，有限目标质量再接 toReal，准确得到第二 .real 结论，无额外可测条件、隐藏正层或总化伪值。

本裁决批准冻结 v3 scope（SHA7176c01d...1b69cd6c）的来源／数学/API／静态声明修复可行性；实际作者 elaboration 尚待进行，本报告没有 kernel PASS／target／Audit成功结论，也不替代未来完整独立 proof review。v1/v2 scope及全部旧票保持历史效力与字节不变。实际 hcont、无条件15/19、hW／最终 diagonal／generalKL、根 A/B/C/D 等仍 OPEN。
