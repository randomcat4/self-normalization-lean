# QuadraticFullNoiseMarkedOutside 独立完整审查

STATUS: **CORRECT**

审查者 `/root/common_region35_review`，新鲜独立上下文，按 `math-theorem` 执行；指定模型 `gpt-6.1-sol`、`xhigh`。作者与审查者分离。本次完整阅读新模块 746 行源码及证明、全部 28 个模块所属实际类型（包括 10 个生成定理）、模块所有权清单和全部逐项传递公理收据。模块无定义，因此需要额外阅读的定义值为 0。没有修改实现、没有创建下属、没有运行 Lean 或重跑审计门。

## 精确版本与可复用证据

- 冻结提交：`3cb6bcbd05fb53dff8e538468d13d8068c78cb16`。
- 模块：`Shao/Probability/QuadraticFullNoiseMarkedOutside.lean`，42437 字节、746 行，UTF-8/LF、零 CR、无 BOM。
- 源码 SHA256：`1a876e82b81195320278d8e8274374bbd9de293da7e1e6e58fb345e1e8f9ec48`。
- 对象 SHA256：`b1102c4dbbd7d04d9a22c48770c2fa73c9636fbb0fd50c66f5cf82863c727a95`。
- 本地草稿、服务器工作副本与冻结提交中的源码 blob 逐字节一致。审查开始时 HEAD 即冻结提交；结束时 HEAD 为 `a6c19bb33e15f5ae5e2a4893931127541d949f24`，冻结提交是其祖先，新增差异仅 `QuadraticFullNoiseMarkedRegionFour.lean`。本模块 Git 路径干净、源码及对象哈希保持不变。
- 作者收据：`drafts/c12-cone-derivatives/marked-outside-region35-author-receipt.json`，SHA256 `f68a0fa1e10ff77f0a678568281f633f4f491351e422f335761805314588739d`。
- `marked-region35-check07.log` SHA256 `e737184c2f87adf2667327bab4abebab172f4f20d49ec8e12bd6dc6246ad139b`；精确源码作者门 exit 0。完整日志仅有既有 mathlib 工作树提示，无源码诊断。
- `marked-region35-actual-owned-types-values-and-axioms.log` SHA256 `950effa0fa4d1480fcc28ac49a3aaf5f0d9ad3a314e4e00fb98473a32e3a6c1d`，306838 字节、3584 行。全部 28 个 `TARGET_DECL` 的名字、类别、公理列表与模块所有权 JSON 逐项一致。JSON SHA256 `531ecd65c206f7665465d73338213a8c6b448a19d445473df1562d1b027a1453`。
- 所有 28 个常量均为定理：2 个公开、16 个非生成 private、10 个生成 private；定义 0、其他常量 0。逐项 `Lean.collectAxioms` 为传递审计，全部仅含 `propext`、`Classical.choice`、`Quot.sound` 的子集；两个最终定理的 `#print axioms` 与此相同。
- 钉死版本：Lean `v4.36.0-rc1`；mathlib `807d3836b165983210ee2ecf3cd28f239436949c`。复用作者 CPU10–13、共享 `root-heavy.lock`、`-M8192 -j4` 的成功门，不重复执行。

实际类型逐条阅读采用确定性的标准实例/运算显示折叠，保留数学参数、量词、实/复类型、实导数、测度与限制测度、所有边界和指数；十个生成类型另直接阅读原始完整展开。伴随 JSON 为每条类型保留原始导出行号和原始文本 SHA256，未用源码声明代替实际类型。未读取重复的第二份公开类型来增加覆盖计数。

## 冻结声明及原始来源忠实性

完整候选声明 SHA256 `6c6172fb7a973f2d43584cda22f3768693652f07f28b3a8275af056c7ac64e36`；完整来源契约 SHA256 `350b0692d5216ad7c93ad6615693b240c17aedfd9759c958c38b4ae505a9b8e8`；根冻结文件 `coordination/public-region35-marked-declaration-freeze.md` SHA256 `302a0056eebc1afa531bb9be1e6750fd8efb4bea68962f7fedb992381e0ea019`。两条公开声明分别与冻结候选仅去空白比较相等。未增加、删除或重解释任何前提或结论。

原始输入 `C:/game/shao/current/c12/supplement.tex` SHA256 `b99f2ac4d2f39dd39772d98a5702b7a923c2f10f8730a08fc1b4cd6bba4742bd`。完整阅读 LF2571–2590、2636–2650、3508–3518、3539–3547，并补读 LF2468–2476 的区域定义。

- 原源的两个相位为 `u(y√r±w)`；这里 `|sigma|=1` 精确覆盖两个实符号，使用真实相位 `u(y√r+sigma*w)` 和真实振幅 `chi(r)/(√r+sigma*w/y)^2`。`y>0`、`|w|≤y/16` 推出闭范围 `|sigma*w/y|≤1/16`，未另假设振幅或导数预算。
- `rho` 是原截断条件律；`m=n-i`，`T=m*∫z² d rho`，`gamma=(∫|z|³ d rho)/variance(id,rho)`。`D` 为实际奇部分乘完整噪声，`W=uE` 为实际偶部分乘 u；两者都仍依赖 v。
- 第 3 区域严格为 `|u|≤kappa/gamma` 且 `|v|>kappa*|u|/gamma`，等于给定低 u 区域扣除原 `calL`。第 5 区域严格为 `|u|>kappa/gamma` 且 `|v|>|u|/(4h)`；低界正，故 u 不为 0，正是原 `calC` 的补集部分。
- `b=gamma/kappa` 保留为参数关系。第 3 区域小性 `b*y≤delta`，第 5 区域小性 `(4*h)*y≤delta` 都是显式 guard，未声称每个原源参数设置已经支付。常数 `C,delta` 在原律、截断和尺度参数之前选取，因此 C 不依赖 kappa。
- 两种积分都保留 `y^-2`。低区域得到 `b*(T+h*gamma)` 及 `b*(sqrt(T)+gamma)+b²*(T+h*gamma)`；高区域得到 `(4h)^31*b^30*(T+h*gamma)` 及 `(4h)^31*(b^30*(sqrt(T)+gamma)+b^29*(T+h*gamma))`。这是原文固定 kappa 后幂次的精确参数版本，不把 kappa 的代价隐藏进绝对常数。

## 完整证明检查

1. **联合可测性（源码20–108）**：一阶实导数由 `t_n=1/(n+1)>0` 的可测实差商逐点极限得到；二阶导数对真实一阶导数族再应用同一事实。没有将分离可测性误作联合可测性。实际联合特征函数用单位范数支配收敛证明连续；完整噪声的概率律实例在消费者内由已有真实律数据支付。实际标记正弦核由紧支撑连续振幅的 `|a|` 支配证明联合连续。导数关于 u、v 为真实参数，未冻结 v 后错误推广积分界。
2. **移动区域 Fubini（110–216）**：先将非负真实被积函数乘可测移动区域的 indicator，逐 u 证明 v 截面可积；再用可积的 u 控制函数支配 `u ↦ ∫‖f(u,v)‖dv`。`integrable_prod_iff` 因此给出真实二维可积性，随后才调用 `integral_prod`。乘积控制引理在点上使用 `F(u,v)≤g(u)`，之后才乘 `K(u,v)`、积分 v、应用真实核尾界并积分 u。`g≥0` 由 `F(u,0)≥0` 和统一界推出；所有乘法与除法比较的符号已支付。这没有把仍依赖 v 的固定-v u 积分乘上 v 核积分。
3. **低阶 profile（218–405）**：正负两条幂尾通过反射、端点零测和不交并计算，精确值为 `2*(-a^(p+1)/(p+1))`。低 profile 以 `[-b,b]` 上的常数及外侧幂尾作真正可积支配。两矩的上界为 `4b` 和 `4b²`；支配中的边界重复只增加上界，不破坏可积性。`profile_compare` 对任意可测子集从真实非负线性控制 `c0+c1|u|` 推导积分上界。
4. **高阶 profile（407–464）**：在 `|u|≥a>0`，`(1+|u|/d)^-31≤d^31|u|^-31`。常数项、线性项分别积成至多 `a^-30`、`a^-29`；正负两尾的系数 `2/30,2/29≤1` 可合法舍去。乘 d^31 后得到冻结的 31/30/29 指数，没有少一个积分维度或因子。
5. **真实核适配（467–496）**：选已审查实际振幅族的 k=2、theta=`sigma*w/y`，闭参数范围和紧支撑由已有族定理支付。真实 `sourceKernel_marked_outside_norms` 的正弦核 j=0 截面可积性和尾估计被正确选取；将 `min(y|u|,1)` 以上界 1 舍去只放宽结果。C 与 delta 在 aStar、y、w、sigma 前选择。
6. **第 3 区域组装（498–620）**：源预算给 gamma>0、h>0、实际条件律与完整噪声律为概率；T≥0，因而 N=`T+h*gamma`、S=`sqrt(T)+gamma` 非负。已有全局定理对所有实 u,v 给 `‖D''‖≤Cg*N` 与 `‖W''‖≤Cg*S+Cg*N*|u|`。选择 aStar=b，付清 b*y 小性，应用低 profile 和移动积分。`|u|/b=kappa*|u|/gamma` 精确还原区域；最终常数是 `4*Ck*Cg`。
7. **第 5 区域组装（622–744）**：使用同一真实导数的 uniform-v 界，选择 aStar=4h，并支付 `(4h)*y≤delta`。严格高 u 区域包含于闭尾 `|u|≥kappa/gamma`；令 a=`kappa/gamma`，则 `a^-1=b`。高 profile 给 `(4h)^31*b^30` 与 `(4h)^31*b^29`，移动积分再保留 `Ck/y²`，最后常数为 `Ck*Cg`。

十个实际生成类型分别为并集成员、Iic/Ici 成员等式，以及 numeral 2/3/4 非零、乘积非零、自然数幂非零、整数幂非零、`n+1` 非零的 simp 等式。完整阅读其泛型类型与类型类前提，逐项对应幂尾计算中的 `simp`/`field_simp`，没有新的数学假设或未列定义值。全部 28 条单独结论与源码位置见伴随 JSON。

边界与量词检查包含：`i=n`/`m=0`/`T=0` 无额外正性假设；任意正 kappa；两相位符号与 theta 两端点；`y=2`、`|w|=y/16`；u=0 和区域阈值的闭/开边界；无须把全局导数估计限制到锥内。源码禁用构造扫描无 `sorry/admit/axiom/unsafe/native_decide`。

## 依赖复用和接受范围

下列源码及对应对象均与已有独立 CORRECT 审查精确相等，仅核对接口和哈希，未重审其旧证明或重跑旧门：

| 依赖 | 源码 SHA256 | 已有审查 |
|---|---|---|
| QuadraticFullNoiseGlobalOddEven | `7256c6f101d86a76f78f713f06c031cba4ec75c7174bb9d73d0fdb629956008c` | `coordination/common-global-review.json` |
| SourceKernelAmplitudeFamily | `1a5c4ca17ab1cfbad4565412827f3546de519512a577a7e4041347f9c48e9970` | `coordination/common-amplitude-review.json` |
| SourceKernelMarkedOutside | `dadbe680967951cc91272055c4cd99688616631b4125cbc999ff5c602b63c868` | `coordination/common-marked-outside-review.json` |

本次接受范围仅为两条冻结公开定理所述的**实际二维移动区域、真实 D''/W'' 与真实标记正弦核的后分部积分非负范数积分、其可积性及定量界**。没有把这些范数积分等同于原始概率/Fourier 贡献；没有支付整条 u 轴的分部积分等式、边界项、其他区域、源参数预算适配、反演或去平滑。C1/C2 与其他原根保持 OPEN，不声称历史新颖性。

审查完成并释放。报告文件归审查者；冻结源和第 4 区域继续由其原作者所有。无审查进程、重型命令或下属留在运行。
