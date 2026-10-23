# 实际奇偶标记反演：最终独立审查

STATUS: CORRECT

审查者 /root/common_odd_region4_review，fresh gpt-6.1-sol/xhigh，独立于作者。使用 math-theorem；没有实现改动、下属、Lean/公理重跑或缓存写入。结论只绑定下列冻结版本。

- 模块：Shao.Probability.SourceFutureNoiseOddEven；commit 4162f0318ddb5468367853b8a545484b71968f43。
- 完整源码363行/17906字节，SHA256 7de2d26d13baadc2a487a00a7ab19c5e7ede121f808ab7a16ee0bf34abd05542。本地完整稿、服务器工作文件和冻结Git blob逐字哈希一致；UTF-8/LF。
- 对象SHA256 f4d6d31b22933ef66ad85862bc69779f109bb2a289e0697c6ff0eafcbeb3a3c8。审查接受冻结blob，后续HEAD前进不会改变本报告的覆盖范围。
- 根冻结 coordination/public-odd-even-inverse-declaration-freeze.md；完整候选SHA256 1e243a8cbccebf8d2e6e492d99d15c9191f8d73f75500005935b6140bc05c2fc；契约SHA256 bb7689d5a304d39646117ff7d60320d43337bf42d49497ef7a019b1d313cd1c1。两条完整签名均与候选在仅规范空白后精确相等。

## 原文到陈述和证明

直接读原 supplement.tex LF2354–2367及其邻接设置，原文件SHA256 b99f2ac4d2f39dd39772d98a5702b7a923c2f10f8730a08fc1b4cd6bba4742bd。原式o′/e″使用实际未来增量与完整噪声核的奇偶部分。现有形式化使用实际f(r,q)，o=(f(r)-f(-r))/2，e=(f(r)+f(-r))/2；f的一、二阶可微由精确已验收反演生产者支付。链式反射负号得到o′=(f′(w)+f′(-w))/2，e′=(f′(w)-f′(-w))/2，并对实际deriv e再次求导，得到标准嵌套二阶导数，而非一个替代符号。

令F为真实Hhat*Xi*phi^m，M_k(F)=u^k exp(ivq)cos(uw)F。首坐标反射R(u,v)=(-u,v)保二维Lebesgue体积，且cosPhase不变，故∫M_k(F∘R)=(-1)^k∫M_k(F)。真实Hhat及Xi的u偶性来自已有生产者；没有假设原增量律对称或均值为零。直接从真实Hhat公式得到u Hhat=2 Bsin(chi,y,u,0,v)，u=0两侧均为零，故这里的乘后恒等式逐点成立，无额外非零频率条件。

逐点代数给出Godd=(M_1(F)-M_1(F∘R))/4，Geven=(M_2(F)+M_2(F∘R))/4。因此两者积分均为相应M_k积分的一半。两项均先用真实u^kF的可积性及有界cosPhase支付L1，再合并/反射积分；没有把所需标记可积性当作前提。正相位平均给出2 I^k，从而奇系数恰为2i/(2pi)^2，偶系数恰为-2/(2pi)^2。偶项的额外uE完整保留。内层正弦标记w槽为0，cos(uw)与exp(ivq)在r积分外。

全部m:Nat含0、y>=0含0以及任意w,q均保留。m=0奇项为零、y=0核为零，证明不需要正m或正y假设。ν的概率性、三阶绝对矩、正方差和实际有界支撑条件恰为冻结输入。

## 完整类型、公理和机械证据

已完整读取本模块实际所属36常量：32定理、4定义；含11生成定理，公开接口为2定理/0定义。36实际类型与4定义值均完整读取，名字集合与实际所属公理审计精确一致，生成的sourceMarkSine.eq_1也对照实际已验收定义。各项完整类型/定义值规范空白哈希与行号列于配套JSON。

完整导出位于服务器 outputs/common-centered-characteristic-v44/odd-even-complete-actual-owned-types-and-definition-values.log，116736字节，SHA256 ab0275c4a8e0b28f02d2e7ce57e928ae7f65bccbaf97032529579999b12ae195。读取采用44项重复完整平衡子表达式的无损缩写；字典、全部余式均读完，逆序展开逐字符恢复规范空白后的原日志。原日志无⋯或…占位，没有省略真实量词、假设、实例或测度。

实际所属审计按getModuleIdxFor?选择每个常量，逐项collectAxioms传递收集；完整32定理及4定义的公理集合均在propext、Classical.choice、Quot.sound白名单内。审计JSON SHA256 695da8e0f2d08176c61a024a15ff1f48b5e106ff6b38206d55a6533e6fc0ab91；完整公理日志SHA256 2cf970eb41727a6a3ab051de40031d4172a85bfbb626e344be7f524a35c3b0bb。实际选择器和导出器源码均已读。

复用作者source-bound成功targeted/object内核门（04及05-object日志均SHA256 fba92798401e89109ac7d84c8cea11527992a1f6b153b3c1d2aada0eebf025a2）及drafts/c12-centered-characteristic/odd-even-author-receipt.json。固定Lean v4.36.0-rc1/mathlib 807d3836b165983210ee2ecf3cd28f239436949c，原CPU10–13/root-heavy.lock/-M8192/-j4条件不变。日志只有既有mathlib工作区提示，无证明错误。禁用构造源码检查为空。本审查没有重跑这些成功门。

已核对反演、实际特征乘积与标记接口的完整所用签名；六份前置冻结源哈希不变，直接反演及标记对象与合格旧审查绑定一致。旧证明内部没有重复审查，完整复用coordination/common-inversion-review.json及其精确生产者证据；其SHA256和所有接口/对象绑定见配套JSON。

## 逐项覆盖

| 声明（省略统一命名空间） | 对应源码行 | 独立核查 |
|---|---:|---|
| `testTransform_mark._simp_1_3` | 147–160 | 显式Zero/OfNat/NeZero下3不等于0。 |
| `phase_norm` | 29–31 | 正纯虚指数的模等于1。 |
| `bounded_mul_integrable` | 59–65 | 连续模至多1的乘子乘真实L1函数仍L1；可测性及范数控制均已支付。 |
| `phase_moment_sum` | 123–137 | 先以两项真实可积性合法合并积分，再用phase_sum；外系数为2 I^k。 |
| `testTransform_mark._simp_1_5` | 147–160 | 显式Mul/Zero/NoZeroDivisors下非零乘积不为0。 |
| `reflect_integral` | 18–22 | 使用该保测映射及乘积可测等价的嵌入，获得真实Bochner积分换元；无额外可积性前提。 |
| `sourceMarkSine.eq_1` | 147–160 | 生成的实际sourceMarkSine方程完全展开accepted SourceMarkFourierNorms.lean:17–19的真实r积分；a,y,u,w,v及负v相位均完整一致。 |
| `phase.eq_1` | 23–25 | 生成定义方程；已对照实际定义值及所有参数逐项核对。实际定义值是exp(i(uw+vq))，保持正相位约定。 |
| `cosPhase_norm_le` | 32–37 | 复指数模1与实余弦绝对值不超过1给出统一乘子界。 |
| `phase_moment_integrable` | 66–75 | 真实u^kF的L1、phase模1和I^k常数给出微分反演所用真实矩积分可积性。 |
| `cosPhase.eq_1` | 26–28 | 生成定义方程；已对照实际定义值及所有参数逐项核对。实际定义值是exp(ivq)cos(uw)，余弦独立于r积分。 |
| `even_second_hasDerivAt` | 228–238 | 先逐点识别标准deriv e，再对真实deriv f使用odd_hasDerivAt，得到标准嵌套二阶导数。 |
| `reflect` | 10–11 | 实际定义值为(-u,v)，仅反射首坐标；已核对标准乘积空间及Lebesgue体积。 |
| `reflect.eq_1` | 10–11 | 生成定义方程；已对照实际定义值及所有参数逐项核对。实际定义值为(-u,v)，仅反射首坐标；已核对标准乘积空间及Lebesgue体积。 |
| `even_hasDerivAt` | 218–227 | e的一阶导数为(f′(w)-f′(-w))/2，反射链式负号正确。 |
| `cosPhase` | 26–28 | 实际定义值是exp(ivq)cos(uw)，余弦独立于r积分。 |
| `even_mark_identity` | 185–207 | 同样给出Geven=1/4(M2F+M2F反射)，真实额外u因子完整保留。 |
| `testTransform_mark._simp_1_8` | 147–160 | 显式AddMonoidWithOne/CharZero下Nat.cast n+1不为0。 |
| `testTransform_mark._simp_1_6` | 147–160 | 显式MonoidWithZero/IsReduced下非零元素自然幂不为0，含指数0。 |
| `markedMoment_reflect_integral` | 106–122 | 反射积分和cos偶性给出精确(-1)^k因子，适用于实际Bochner积分。 |
| `odd_mark_identity` | 161–184 | 实际Hhat与Xi偶性、真实原律带符号phi幂给出Godd=1/4(M1F-M1F反射)；逐点代数未引入对称律。 |
| `sourceFutureNoiseKernel_odd_derivative_inverse` | 239–298 | 完整冻结签名一致；真实空间导数、1阶矩、反射及相位平均给出真实G的L1和2i/(2pi)^2系数，全部m/y/w/q量词保留。 |
| `odd_hasDerivAt` | 208–217 | 链式法则对f(-r)产生负号，o的一阶导数为(f′(w)+f′(-w))/2。 |
| `sourceFutureNoiseKernel_even_second_inverse` | 299–362 | 完整冻结签名一致；真实e和deriv e均可微，2阶矩与反射平均给出标准嵌套e″、真实G的L1及-2/(2pi)^2系数，额外uE未丢失。 |
| `phase_sum` | 38–54 | 指数加法和two_cos给出phase(w)+phase(-w)=2cosPhase；频率及空间符号均正确。 |
| `reflected_moment_integrable` | 89–105 | 先保测反射再乘(-1)^k，利用(-1)^(2k)=1恢复u^k；含k=0。 |
| `testTransform_mark._simp_1_7` | 147–160 | 显式GroupWithZero下非零元素的任意整数幂不为0。 |
| `testTransform_even` | 138–146 | 直接从真实Hhat公式逐点检查u=0及u≠0分支，sin奇性与分母取负抵消。 |
| `markedMoment_integrable` | 79–88 | cosPhase有界乘子将真实矩L1转为实际标记矩L1。 |
| `testTransform_mark._simp_1_2` | 147–160 | 显式Zero/OfNat/NeZero下2不等于0。 |
| `reflect_preserving` | 12–17 | 实数取负保Lebesgue测度，与第二坐标恒等映射取积，支付反射换元。 |
| `markedMoment` | 76–78 | 定义值为u^k cosPhase F；没有将F、相位或测度替换为抽象替身。 |
| `testTransform_mark` | 147–160 | 直接证明u Hhat=2 Bsin(chi,y,u,0,v)；u=0两边为0，无新增非零频率条件，也无需丢弃零频率直线。 |
| `phase` | 23–25 | 实际定义值是exp(i(uw+vq))，保持正相位约定。 |
| `cosPhase_reflect` | 55–58 | u反射不改变cos(uw)；v相位不变。 |
| `testTransform_mark._simp_1_4` | 147–160 | 显式Zero/OfNat/NeZero下4不等于0。 |

## 结论边界

无关键缺口、无必需修复。接受范围是两条冻结的真实奇偶标记反演恒等式、可微性与真实双频积分L1。尚未支付D/uE的whole-u分部积分、原概率贡献、后续区域汇总或去平滑；不关闭C1/C2或任何其他尚开放根，不声称数学新颖性。审查工件已完成并释放；没有持续运行的检查或实现写权。
