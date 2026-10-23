# 实际 Fourier 测试核独立完整审查

STATUS: CORRECT

审查员 /root/common_kernel_review，gpt-6.1-sol / xhigh，全新上下文，与作者分离。只写本报告及同名 JSON；未修改源码，未启动子实例，未重跑已经成功的 Lean 或公理门。

精确版本：commit 22a68e78abc981e898f823bef7f019efa3731504；parent baef8950b5c30ff3fb49b7ebe1cc755b91f7eaca。服务器工作树干净，本提交仅新增 Shao/Probability/SourceFourierTestKernel.lean。源码 SHA256 151fe42cda5414873ea9c9ea3359d256e971132073ea9d1c714ea0105af234d3；对象 SHA256 f3d751f7a84fa991841a6a005e009b1d6ee28cb2347f55a0280417637adaaeba。两项旧 centered/power 源哈希保持收据值，未复审其已接受内部证明；本核直接只导入 mathlib。

已完整阅读冻结声明、候选六项公开声明、原文 main610–615 / supplement2346–2353、新源全部213行、全部36个实际所属类型及全部5个实际定义值。候选 SHA256 fdba5163434fab44c7c62e86d58e16cd5b6da0286f922f680c0314488d895f96 与冻结记录一致。实际六项公开常量的定义、量词、前提及结论逐项相符。

数学核对：

- χ 是实际 ContDiffBump，中心25/16、内半径23/16、外半径47/32。闭支撑为[3/32,97/32]，严格包含于(1/16,4)；[1/8,3]恰是内闭球。C∞、紧支撑和0≤χ≤1均由实际 bump 性质推出。
- H_y 是实际 χ(q) 乘严格事件 |w|<y√q。q≤0 时平方根为0，严格事件为空；y=0 时同样恒零。没有自由核、自由变换或结论性可积性前提。
- 可测性来自开事件集；非零测试函数的支撑落在[-2y,2y]×[1/16,4]，范数≤1。有限测度紧矩形的指示函数给出实际 L1 支配。复相位连续且模为1，故实际二维变换绝对可积，之后才使用 Fubini。
- 内积分确为开区间(-a,a)，a=y√r≥0，对所有实r成立。Ioo与Ioc的勒贝格限制测度相等，随后使用-a≤a的区间积分恒等式；非零频率的复指数原函数给出2sin(ua)/u，负号相消正确。u=0用单独常数积分分支，a=0、y=0及坐标轴均覆盖。
- 最终先由产品勒贝格测度和绝对可积性得到外r内w的积分顺序，再用逐点内积分身份，得到冻结的精确公式。相位保持 exp(-i(uw+vq))，没有2π或额外归一化因子。u=0的值与源要求的连续延拓值一致；本单位不额外声称已形式化独立的u→0极限定理。

服务器证据复用：targeted03 exit0；36所属=31定理+5定义，公开3定理+3定义。审计按实际 module owner 选择所有私有及生成常量，并对每项调用传递 collectAxioms；全部只依赖 propext、Classical.choice、Quot.sound。完整实际类型导出为40879字节，SHA256 f5ef725c77acd723d58bffe20a90f60da719c178e53e9145f330b631d58952ec。导出36名字集合与审计集合相等，5个定义值集合也相等。源码无 sorry/admit/新增axiom/unsafe/native_decide。所有收据引用的服务器源码、对象、日志及审计/导出脚本哈希均已只读重核。Lean 4.36.0-rc1 / mathlib 807d3836b165983210ee2ecf3cd28f239436949c 保持。共享只读符号链接包视图产生的 local-changes 提示不构成源码偏离：五份相关 mathlib 源文件已逐字节对照固定提交；所用 bump、端点零测、复指数积分和 Fubini 接口条件已核对。

逐声明覆盖如下；完整所属名、实际种类、公理及具体理由见同名 JSON。所有行结论均 CORRECT。

| 声明（省略统一命名空间） | 源行 | 核对点 |
|---|---|---|
| negativePhase.eq_1 | 105-106 | Generated defining equation agrees with the complete actual definition value. |
| sourceKernelCutoff | 14-17 | Actual definition: center 25/16, rIn 23/16, rOut 47/32; no free cutoff parameter. |
| sourceKernelCutoff._proof_2 | 14-20 | Generated elaboration obligation: Nat.AtLeastTwo 16. Actual type fully read; no extra mathematical hypothesis. |
| sourceKernelCutoff_data | 22-41 | All five frozen properties: C-infinity, compact support, [0,1], plateau [1/8,3], closed support strictly inside (1/16,4). |
| sourceKernelCutoff._proof_1 | 14-20 | Generated elaboration obligation: Nat.AtLeastTwo 25. Actual type fully read; no extra mathematical hypothesis. |
| negativePhase_add | 115-121 | exp-add identity with the negative sign preserved. |
| inner_transform | 166-197 | For every real r, actual integrand is indicator of (-a,a) with a=y*sqrt(r)>=0; phase factors and exact interval integral gives frozen inner formula. |
| interval_phase_integral._simp_1_5 | 160-164 | Generated simplification lemma: 3 is not zero under the declared NeZero instance. Actual full generalized type read; assumptions are explicit library algebraic instances only. |
| negativePhase_continuous | 111-113 | Continuity of the actual exponential composition. |
| interval_phase_integral._simp_1_9 | 160-164 | Generated simplification lemma: integer powers of a nonzero element are nonzero in GroupWithZero. Actual full generalized type read; assumptions are explicit library algebraic instances only. |
| test_support | 70-88 | For y>=0, nonzero test implies cutoff support and |w|<=2*y, so support lies in the stated compact rectangle. |
| sourceKernelCutoff._proof_6 | 14-20 | Generated elaboration obligation: 0 < (23/16 : Real). Actual type fully read; no extra mathematical hypothesis. |
| interval_phase_integral._simp_1_4 | 160-164 | Generated simplification lemma: 2 is not zero under the declared NeZero instance. Actual full generalized type read; assumptions are explicit library algebraic instances only. |
| sourceFourierTest_integrable | 90-103 | Integrable compact-rectangle indicator dominates the measurable actual test pointwise. |
| test_measurable | 51-60 | Open strict-event set and measurable cutoff give an actual indicator representation and measurability. |
| sourceKernelCutoff._proof_8 | 14-20 | Generated elaboration obligation: HasContDiffBump Real with the standard real inner-product structure. Actual type fully read; no extra mathematical hypothesis. |
| interval_phase_integral._simp_1_3 | 160-164 | Generated simplification lemma: complex sine of a real cast equals cast of real sine. Actual full generalized type read; assumptions are explicit library algebraic instances only. |
| transform_integrable | 123-131 | Complex lifted actual H times unit-modulus continuous phase is absolutely integrable for all u,v. |
| sourceKernelCutoff._proof_4 | 14-20 | Generated elaboration obligation: Nat.AtLeastTwo 47. Actual type fully read; no extra mathematical hypothesis. |
| negativePhase | 105-106 | Actual negative unit-frequency complex exponential. |
| sourceFourierTest | 43-45 | Actual real cutoff times strict event |w|<y*sqrt(q), not an unconstrained function. |
| interval_phase_integral | 133-164 | Ioo-to-Ioc null-endpoint conversion and oriented interval conversion; u=0 handled separately; nonzero complex exponential integral gives 2*sin(u*a)/u. Includes a=0. |
| interval_phase_integral._simp_1_2 | 160-164 | Generated simplification lemma: complex cosine of a real cast equals cast of real cosine. Actual full generalized type read; assumptions are explicit library algebraic instances only. |
| sourceKernelCutoff._proof_3 | 14-20 | Generated elaboration obligation: Nat.AtLeastTwo 23. Actual type fully read; no extra mathematical hypothesis. |
| interval_phase_integral._simp_1_7 | 160-164 | Generated simplification lemma: a product of nonzero factors is not zero in a NoZeroDivisors structure. Actual full generalized type read; assumptions are explicit library algebraic instances only. |
| sourceFourierTest.eq_1 | 43-45 | Generated defining equation preserves both coordinates, strict inequality and event branches. |
| sourceKernelCutoff._proof_5 | 14-20 | Generated elaboration obligation: Nat.AtLeastTwo 32. Actual type fully read; no extra mathematical hypothesis. |
| sourceFourierTestTransform | 47-49 | Actual complex Lebesgue integral on R x R with phase exp(-i*(u*w+v*q)); no normalization factor. |
| interval_phase_integral._simp_1_6 | 160-164 | Generated simplification lemma: 4 is not zero under the declared NeZero instance. Actual full generalized type read; assumptions are explicit library algebraic instances only. |
| interval_phase_integral._simp_1_10 | 160-164 | Generated simplification lemma: cast n plus one is nonzero in a characteristic-zero AddMonoidWithOne. Actual full generalized type read; assumptions are explicit library algebraic instances only. |
| kernelBump | 19-20 | Actual private bump has identical data and is definitionally the public cutoff bump. |
| test_norm_le_one | 62-68 | Both event branches checked; nonnegative cutoff bounded by one gives the norm bound. |
| sourceKernelCutoff._proof_7 | 14-20 | Generated elaboration obligation: (23/16 : Real) < 47/32. Actual type fully read; no extra mathematical hypothesis. |
| negativePhase_norm | 108-109 | Pure imaginary exponent has norm one for every real argument. |
| sourceFourierTestTransform_eq | 199-211 | Product Lebesgue measure and absolute-integrability Fubini give outer-r/inner-w order; pointwise inner_transform completes exact frozen equality. |
| interval_phase_integral._simp_1_8 | 160-164 | Generated simplification lemma: natural powers of a nonzero element are nonzero under the stated IsReduced structure. Actual full generalized type read; assumptions are explicit library algebraic instances only. |

接受范围仅为这个实际测试核、L1性质及精确变换公式。尚不包含未来增量/噪声乘积式、反演、marknorm/mark-sine、分部积分边界、区域积分或概率界；C1/C2与原研究根的OPEN状态不变。后续若接 mathlib 反演，仍须显式支付2π频率重标定和(2π)^(-2)因子。本审查不作新颖性主张。

没有关键缺口或必需修改。下一依赖是另行冻结的实际正向平移 future/noise Fourier 乘积消费者。审查已完成；无审查员 Lean/审计进程或子实例运行，本报告不持有后续源码写权限。
