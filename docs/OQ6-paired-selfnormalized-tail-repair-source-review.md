# 单元199 repair01独立受影响源码与完整组合审查

STATUS: SOURCE_CORRECT

qualified=false；actual owned=UNKNOWN。此裁决确认完整新helper及其与未改源码的组合在源级成立，不代表新源已通过Lean内核或递归公理审计。native02尚未运行。本审查与作者及父级声明冻结独立；唯一新写入目录为本目录，旧源码、旧SOURCE报告、旧覆盖及seal均未改动。

## 精确输入与复用边界

新源为C:/game/shao lean/drafts/oq56/unit199/author-01/stage2/repair-01/PairedSelfNormalizedTail.lean，SHA256 23d5e22f5bd8669f8e7d41afec78cf1b5bcf8150052ec666fc2bfbac507a7d8b，7364B/169LF/0CR/无BOM，UTF-8往返一致。完整读取新旧169行，旧完整证明仅按SOURCE-REVIEW的73c6701d1acebc4cfd7e7fbd17378cab32d86b489ec797379da9922a6e10f939（11669B）及SOURCE-COVERAGE的fbcfbc3d99078fc059f37803187239e84021295134efa6d571dde8aa9803f641（44298B）复用。没有重审或重跑旧producer；新helper、新API及完整T03组合在此独立审查。

唯一事前repair冻结是parent-repair-freeze01-indicator-helper.json，SHA256 c8c000bfae786801d8a853a5ac13ffc97b1b539cccd815c709b82136379d13bf。已完整读作者7项payload、manifest、DONE、CHECKPOINT、RELEASE0与全部指定输入；39次哈希/字节比较覆盖25个唯一文件，全部匹配。作者释放的writer/execution/heavy/inflight/pendingExternal/children全部0。

旧源60425a4454af45f28c22e3e81bb9a23344953c074f3f38108e08509dc55fecc6为7295B。独立重建得到：旧[0,5248)与新[0,5248)相同，5248B/hash8cfe7a997558cff8343ef1ffa0a221b73389118354b7060e22bba0ca55a077cf；旧完整hint[5248,5448)200B由新[5248,5517)269B替代；旧[5448,7295)与新[5517,7364)相同，1847B/hash33837d4281cc33695bb10a194061771cbaf654f151be261eb88232e6e92039b2。新源恰为旧前缀+父冻结新完整helper+旧后缀，其余7095B相同，唯一差异为125–126两行。

## 完整新hint推导与准确API

122–126行命题仍对任意固定s : Fin n→Bool断言I_s的配对律积分等于D的实数概率；完整命题头、s绑定及n/Ω/mΩ/μ/hμ/g/hg/t外层望远镜未改。原hI_eq s精确给I s = (B s).indicator (fun _ : Fin n→Ω×Ω => (1:ℝ))。125行先以它重写被积函数，再用integral_indicator_const (μ := pairedLaw n μ) (1:ℝ) (hB s)。准确特化为X=Fin n→Ω×Ω、E=ℝ、μ=pairedLaw n μ、集合B s、e=(1:ℝ)，可测性正是hB s。得到目标(pairedLaw n μ).real (B s) • (1:ℝ) = (pairedLaw n μ).real D。

126行simpa only [smul_eq_mul, mul_one] using hmass s用规范实数标量作用等于乘法，再用乘1归约。原hmass s完整类型正是(pairedLaw n μ).real (B s) = (pairedLaw n μ).real D，方向、测度、集合与实数化一致。因此完整helper闭合，没有添加可积性、矩、正能量、有限测度或新概率假设。显式e=(1:ℝ)只把已冻结T03.one常函数的值交给API，不是新数学数据或选择器，不改变阈值。

Primary packet pinned-paired-tail-primary-source.json的SHA256是054ace8b4bd05684cdc9d5b447c21aeef26e737028ba70c4b3c7d32bb9177337（232609B）。其中Mathlib/MeasureTheory/Integral/Bochner/Set.lean重新算得e4d90b9fde463a9123e1ac3321ce25c0714e19ce92e172f297e062d9de16be75（61504B）。沿用Lean leanprover/lean4:v4.36.0-rc1与mathlib807d3836b165983210ee2ecf3cd28f239436949c，没有TYPE探针。

完整读取从文件开头至新API之前所有时间顺序前缀。Unicode码点[0,25348)hash d7a5b9a5f60b3c877b7e28ec1712ebdaa944b73c4f7c57fde39749e08c1c071c；原SOURCE更长[0,25579)hash a908c69841652b46b49518c326313bc50da656412d0f796c1b281d73e90bb083也精确匹配，并含完整新const证明。新API仍处于MeasureTheory命名空间的NormedAddCommGroup节，实际ambient是{X Y E F : Type*}、{mX : MeasurableSpace X}、[NormedAddCommGroup E]、[NormedSpace ℝ E]、{f g : X→E}、{s t : Set X}、{μ : Measure X}。前面的定理局部PartialOrder E、局部绑定和证明let不向后泄漏。

完整原文为：

    @[simp]
    theorem integral_indicator_const [CompleteSpace E] (e : E) ⦃s : Set X⦄ (s_meas : MeasurableSet s) :
        ∫ x : X, s.indicator (fun _ : X => e) x ∂μ = μ.real s • e := by
      rw [integral_indicator s_meas, ← setIntegral_const]

完整头hash60882c706416b479d0f69435876046ba0cae18ecef33edf8f01f7eb9a35b1f8a。声明局部要求CompleteSpace E，e，s与可测性，局部s覆盖ambient s。Y/F/f/g/t不在实际有效头，不成为新前提。专门化到ℝ使用规范NormedAddCommGroup ℝ、NormedSpace ℝ ℝ、CompleteSpace ℝ和原mΩ诱导的Pi/乘积可测空间；不创建新局部实例。公式没有隐藏的Integrable、概率、矩或有限测度参数。紧邻integral_indicator_one原证明也用同一const公式加smul_eq_mul/mul_one链，准确支持此次实数归约。

## 完整T03组合与数据作用域

T03为72–133行。82–83行原instP派生不变，84–93行D/B/I初始化不变；s固定在z之前。94–106行D可测、B s为固定swapSample原像及B可测；107–115行指标识别与可积性；116–121行固定交换保测度给实数质量等式。这些原范围全部按精确旧完整审查与7095B相同证明组合。新hint只消费原hI_eq、hB、hmass，没有依赖z选择符号。hint真实终点126，127行change为同级命令；原作者显示终点127仅是旧元数据误差，本次采用原独立覆盖126而不修改旧表。

127–133行全字节未改：展开cubeMean权重；用hI_int做有限和积分交换；132行simp_rw [hint]将每个固定符号积分化为同一D质量；133行用符号立方体基数2^n及自然数到实数转换归一。新hint输出与旧头相同，有限和消费点没有新增义务。T04完整头与证明未改，继续消费T03相同陈述和已合格198点态尾界；旧185/187/198证明、编译与AX均不重放。

6个事前冻结完整声明头逐字匹配；D01/D02完整声明和两个全局RHS逐字匹配。源码仍2def/4theorem、3个数据let D/B/I、2条letI instP、10个显式类型命题头。全部28项冻结数据的类型、初始化、term/type/complete captures、匿名绑定器与作用域逐项核对原完整覆盖及frozen-data-source-map，均不变。完整28行和逐项比较保存在SOURCE-COVERAGE.json。跨hint的T03.P/signIntegralFamily/constantProbabilityFamily三个词法范围含新证明字节，但其中数据表达式/类型未变；没有声称这三个整个范围的证明字节都未变。

两条概率实例仍为IsProbabilityMeasure (pairedLaw n μ)，初始化inferInstanceAs (IsProbabilityMeasure (Measure.pi (fun _ : Fin n => μ.prod μ)))，类型捕获n/Ω/mΩ/μ，初始化额外消费hμ。T04实例属于自己的望远镜，不继承T03局部实例。原10个普通命题完整头/匿名分支覆盖精确复用，只有hint证明重新审查。没有新数学data、choice、selector、instance、假设、imports、attributes或universe命令；禁止词扫描为空。数值文字21→22，唯一新出现是125行显式实数1，6个字段投影不变。

原n=0、零能量、t=0、严格等号边界、原子法则和任意可测空间边界保留；T02/T03仍允许任意t，T04仍需t≥0。无新增n>0、t>0、L1/L2、指数矩或标准Borel前提。本源只证明实际配对差值尾界；原S11单样本转换、C2/C12/OQ56仍OPEN，OQ3仍PAUSED_BY_USER，原C1 immutablev85完整状态及p54/外部归因/124边界保留。

## 失败保留与下一机器门

原native01确定自然结束RC1、1error/5warnings/无O。唯一错误是integral_indicator_one的indicator 1模式未匹配显式lambda指标；完整失败及5条warning保留。native02未跑，不把旧失败重放为未知在途请求或成功结果。

本审查本地静态工具有两种格式误比较：重建多加已由后缀保留的LF；冻结RHS展示的首行缩进处理不正确。原静态结果均保留，最终半开字节重建和冻结完整声明文本比较通过。另有一次写报告调用因代码字符串分隔符产生解析错误，发生于执行前、无文件修改，记录单独保留。这些不是Lean或数学失败；作者输入完全未改。

下一步由父级对精确新源23d5e22f…执行native02。成功后只用该首个原对象发现全部actual owned，覆盖全部TYPE、所有非theorem FULLVALUE、完整名称/宇宙/body presence及逐常量递归AX，白名单仅propext、Classical.choice、Quot.sound。然后可在新machine子目录继续独立组合；本SOURCE报告不回写为已机器通过。本轮服务器/Lean/AX/上传/Git/API/child全0；实际model/effort与输入/缓存输入/输出/推理子集计量无法从接口取得，均为null。
