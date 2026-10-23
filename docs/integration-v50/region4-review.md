# 实际第四区标记积分：最终独立审查

STATUS: CORRECT

审查者 /root/common_odd_region4_review，fresh gpt-6.1-sol/xhigh，独立于作者。使用 math-theorem；没有实现改动、下属、Lean/公理重跑或缓存写入。

- 模块：Shao.Probability.QuadraticFullNoiseMarkedRegionFour；冻结commit a6c19bb33e15f5ae5e2a4893931127541d949f24。
- 全部532行/29294字节源码已完整逐行读完；SHA256 b921940ad68c9b35125b29a81d543e6c1d999a0d06b10b9f90ca6e68f538d58f。本地完整稿、服务器工作文件和冻结Git blob哈希一致；UTF-8/LF。
- 对象SHA256 1ef36c40d6b61aea8460c2a8a121c172ea3141c05c7bdaff78189a9d4ad923a8。本报告只接受冻结blob，与后续HEAD是否前进无关。
- 根冻结coordination/public-region4-marked-declaration-freeze.md；完整候选SHA256 ba468450cfe8d9b0588f60dd56f1ef202f85ca22df38b77b9e8a70820d6dc856；契约SHA256 95a61318286f4b2441421bbc1e0336bb21143460ed7c936ec6097d3aa4d5761d。单一公开完整签名在仅规范空白后精确相等。

## 原文到陈述和证明

直接读原supplement.tex LF2571–2652、3508–3547；原文件SHA256 b99f2ac4d2f39dd39772d98a5702b7a923c2f10f8730a08fc1b4cd6bba4742bd。两次u分部积分后原幅函数为chi(r)/(sqrt(r)+sigma*w/y)^2，正弦相位为sin(u(y sqrt(r)+sigma*w))，共同y^-2在结论内显式保留。本模块证明的是该真实标记核与真实D″、W″（W=uE）的二维非负范数积分，没有把尚未证明的whole-u等式或原概率贡献纳入结论。

所有源条件完整保留：实际ν0概率律、二阶矩、n*m2=1及源均值0、x>=0、0<epsilon<=1/2、截断预算、i<=n、epsilon/(1+x)<=h、kappa>0、L2>=20、kappa sqrt(L2)>=1、0<y<=2、|w|<=y/16、|sigma|=1和L2 gamma²<=T<y²。ρ为实际条件律，m=n-i，T=m*实际ρ二阶矩，gamma=实际ρ三阶绝对矩/variance，b=gamma/kappa；没有以自由常数或假设替换这些对象。

实际theta=sigma*w/y落在闭[-1/16,1/16]，含两个端点。已验收实际幅族k=2的统一M同时支付a、a′、a″及紧支撑；再用sourceMarkSine_norms取得真实标记在全v线上的L1与积分界。只有取得L1后，才把min(y|u|,1+sqrt(y|u|))放宽成1+sqrt(y|u|)。Ck=C*M在所有源参数之前选择，没有输入自由幅函数预算或结论性振荡界。

真实特征积分的联合连续性由单位模支配收敛给出。实际全平面D、W的两阶可微性使正向可测差商逐点趋于真实u导数；重复一次支付二阶导数的联合可测性。随后在闭锥上调用真正对v一致的点态界Cg/(T^5|u|^12)、Cg/(T^5|u|^11)。没有将一个固定v的已积u尾界错误地乘以v积分。

移动闭锥的指示函数可测；先通过v切片L1及可积u主控得到真实二维乘积L1，再合法Fubini。范数非负性允许先在v积分中使用uniform-v界并扩大到全v线。双侧u尾在a=kappa/gamma>0处拆为不交Iic(-a)和Ici(a)，用反射、端点零测及实幂积分支付两侧。对k=12或11，分别得到

- 2*(a^-11+sqrt(y)*a^-10*sqrt(a^-1))；
- 2*(a^-10+sqrt(y)*a^-9*sqrt(a^-1))。

以a^-1=b转换后，C=2*Cg*Ck给出精确的C/y²/T^5乘(b^11+sqrt(y)b^10 sqrt(b))及(b^10+sqrt(y)b^9 sqrt(b))。常数先于全部源/尺度参数选择；kappa仍量化时没有把其负幂偷偷吸收到绝对常数。闭边界|u|=kappa/gamma及锥边界均真实覆盖；这是对原严格高频区域的有效加强。由原guards支付gamma,h,T,b的正性；没有新增m>0前提，i=n虽语法保留但T=0不能满足原L2 gamma²<=T。

## 完整类型、公理和机械证据

19实际所属常量均为定理，含5生成定理、1公开定理；没有定义值。所有19实际类型、5生成关系、全部所属传递公理及重复的完整公开#check均完整读取。名字集合与实际所属审计精确一致，重复公开类型与所属类型规范空白后精确相等。各项类型哈希及日志行号见配套JSON。

完整实际类型/定义值/公理日志位于服务器outputs/common-cone-derivatives-v44/marked-region4-actual-owned-types-values-and-axioms.log，207567字节，SHA256 8143a9e73177c655363b4d5e20fe7e516b59451fae7951b196d914bca0c8441d。读取使用45项完整平衡子表达式的无损缩写，全部字典和余式读完，逆序展开精确恢复规范空白原文。没有⋯或…占位，任何量词、假设、实例、测度和实际数学参数均未省略。

实际所属审计根据getModuleIdxFor?逐个选择全部私有/生成常量，逐项collectAxioms传递收集；19项均仅使用propext、Classical.choice、Quot.sound白名单（个别生成项使用其子集）。审计JSON SHA256 1d913a24495887c9944320019742a8bc822a75797ee93b7e58193d18abc2c7d6；审计器源码完整读完。

复用作者精确source-bound内核成功收据drafts/c12-cone-derivatives/region4-marked-author-receipt.json，kernel exit0；marked-region4-final-check.log SHA256 e737184c2f87adf2667327bab4abebab172f4f20d49ec8e12bd6dc6246ad139b。固定Lean v4.36.0-rc1/mathlib 807d3836b165983210ee2ecf3cd28f239436949c、CPU10–13/root-heavy.lock/-M8192/-j4条件不变。日志仅有既有mathlib工作区提示，无证明错误；禁用构造源码检查为空。本审查没有重跑成功门。

直接消费的RegionFour、GlobalOddEven、实际AmplitudeFamily及MarkNorms完整接口均已读；其当前源和对象哈希与各自合格旧审查完全一致。完整复用coordination/common-region4-review.json、common-global-review.json、common-amplitude-review.json、common-mark-review.json的未变证明证据，不再重复其内部证明。具体源/对象/旧报告SHA256列于配套JSON。

## 逐项覆盖

| 声明（省略统一命名空间） | 对应源码行 | 独立核查 |
|---|---:|---|
| `actualQuadraticChar_continuous` | 64–67 | 将一般联合特征积分专用于实际(z,z²)。 |
| `abs_tail_rpow._simp_1_2` | 173–217 | 集合并的成员关系恰为两个成员关系的析取。 |
| `abs_tail_rpow._simp_1_4` | 173–217 | 显式Preorder下Ici b成员关系等于b<=x。 |
| `tail_envelope._proof_1_1` | 218–284 | k>=3蕴含1<=k，支撑Nat.cast_sub的精确边界。 |
| `jointSecondDerivative_measurable` | 39–47 | 在实际一阶导数族上再次应用差商引理；全平面两阶可微前提均已提供。 |
| `actualGlobalMarkedKernelData` | 362–392 | 实际k=2、theta=sigma*w/y落在闭[-1/16,1/16]，统一M支付0/1/2阶真导数；从sourceMarkSine_norms取得真实v-L1后再将min放宽到1+sqrt(y\|u\|)。 |
| `tail_envelope` | 218–284 | k>=3保证两个实幂尾可积，保留sqrt(y\|u\|)分解及Nat减法条件，得到含sqrt(a^-1)的双侧界。 |
| `jointDerivative_measurable` | 19–38 | 用t_n=1/(n+1)正向趋零的可测差商逐点收敛到真实u导数，支付联合可测性。 |
| `abs_tail_rpow` | 173–217 | a>0、p<-1时，真实双侧闭尾分成不交Iic(-a)与Ici(a)，反射和端点零测给出精确2*(-a^(p+1)/(p+1))。 |
| `actualJointChar_continuous` | 48–63 | 实际概率律下单位模复指数支配收敛；只需两坐标可测，没有隐藏矩假设。 |
| `compare_tail` | 285–313 | 先对非负可测F构造真实尾主控L1，再由集合包含与积分单调性得到2c倍界。 |
| `abs_tail_rpow._simp_1_3` | 173–217 | 显式Preorder下Iic b成员关系等于x<=b。 |
| `sourceTruncation_odd_even_fullNoise_region4_actual_marked_postIBP` | 393–531 | 完整冻结签名一致；真实条件律、D及W=uE、全局两阶可微和闭锥uniform-v点态界合用，再支付移动二维L1及双侧尾；C=2CgCk在全部参数之前选择，b=gamma/kappa及全部guards保留。 |
| `movingConeMarkedIntegral` | 314–361 | 先以对v一致的F<=g(u)乘真实K建立各v切片L1，先界v积分再用gL的u可积性和移动锥Fubini；保留y^-2。 |
| `actualMarkedSine_continuous` | 89–108 | 以紧支撑连续幅函数的\|a(r)\|为真实可积支配，支付实际移位正弦及负v相位的联合连续性。 |
| `movingConeNonnegativeIntegral` | 109–172 | 移动闭锥的可测指示函数；先用v切片可积性及可积u主控得到真实乘积L1，再Fubini和非负比较；没有循环假设二维可积。 |
| `actualOddEven_continuous` | 74–88 | 真实phi(±u,v)^m、Xi与uE的连续性，全部幂和符号保留。 |
| `tail_envelope._proof_1_2` | 218–284 | k>=3蕴含2<=k，支撑第二个Nat.cast_sub的精确边界。 |
| `actualFullNoiseChar_continuous` | 68–73 | 将一般联合特征积分专用于真实完整噪声律的两坐标。 |

## 结论边界

无关键缺口、无必需修复。接受精确冻结的真实高频闭锥二维post-IBP范数可积性和定量界。whole-u分部积分、概率贡献识别、其他源区域、预算适配、时间求和及去平滑仍需后续证明；不关闭C1/C2或其他尚开放根，也没有新颖性声明。审查已完成并释放，没有持续运行的检查或实现写权。
