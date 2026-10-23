# 真实四区域积分：独立完整终审

STATUS: CORRECT

JUSTIFICATION: 对精确冻结版本完成原文到声明、全部证明与局部值、全部实际所属类型及传递公理的独立审查，未发现关键缺口。该版本证明真实移位轮廓积分的四区域界、真实未来／噪声核的一阶及二阶导数界和两条粗界。结论只在完整冻结前提下成立；本报告不认证原始 growingkernel 的全部宏观／短时钟实例化、q>5 消失或 C1/C2/OQ 概率根结论。

审查者 `/root/common_growing_region_full_review`，fresh `gpt-6.1-sol / xhigh`；与作者分离。作者在派审前已 FINAL_RELEASED。本次仅写本报告、配套 JSON、逐名覆盖表及 `drafts/c12-growing-region-review/`，没有改动 Lean、冻结文件、作者凭据、原文或只读库；没有 Lean 命令、旧生产者重编、旧审计重放、子代理、PR 或合并。

## 精确版本与机械证据

- 模块：`Shao/Probability/SourceGrowingRegionIntegrals.lean`，完整读取 1–2581 行及所有局部 `let` 值。132537 字节，UTF-8/LF，无 CR、BOM。
- 源 SHA256：`8b2c32195f774bb71eb9d3a21856fd4e4aaba3759674aa3a7cc97f1fee8b3a76`。
- source-only commit：`2e94f63a4b6aab77c4d334c36b435d62b0495ea6`，parent `7b8d55bd2aa5d610a1f1fb3db6867552ce7d0ae5`；唯一改动为该模块。
- 分支／服务器工作树：`feat/common-growing-region-integrals`／`workspaces/common-centered-characteristic-v44`。
- 冻结 SHA256：`008767c7abab97e4d77eeaa10ca1aa2882a487bed92c5c4da29dd8ac0048095d`；完整唯一公开头与冻结逐 token 相同，仅忽略空白。候选声明、证明草稿、作者 scrutiny、完整 handoff 亦已读取。
- 原首次完整 check018：rc0，997.4479830265045 秒；原对象 `b61578b1dc79976ce5f427b19a2767550255afab40a5f24c55e163bb302a9284`，原日志 `f863ea5398ca73eeab505de4a4b11af4024e21777ebfabdc8c188d0e390d6722`。归档回执绑定同一 source/object。check008 只是局部成功，check001–017 均不充当完整成功。
- 原 audit001：rc0，9.063975811004639 秒；审计脚本 `8d81ac721b323b5b1e1064ca3029ec79d80addf03918837937f29f6652911562`，日志 `bfa395912f98431ba3ec71ff5cf7529be0cc39861bb5c4fbcbc4e822dc362191`。审计前后 source/object 未变。
- 实际类型文件：493665 字节，SHA256 `3e5a45f96ecbc79c6f9d1ac915eeb353ca98c7760e2b194b115725ef53e670dd`。所属公理表 SHA256 `6ef47bb04a94b6a1044a8329b8b5783081871b7079db86e392210f81a803b44f`。
- 直接检查真实 owner 选择逻辑：`env.getModuleIdxFor?` 对目标模块的全部常量逐项取 `collectAxioms`，并检查 kind。109 个实际所属常量全部是 theorem，0 definition／0 other；38 个显式声明（37 private + 1 public）和 71 个生成 theorem。不是由源码行数或描述性计数推断 0 定义。
- 逐名类型与 AX 集合完全对齐，无重复、缺失或实际省略标记。33 项只用 `propext`，32 项用 `propext, Quot.sound`，44 项用全部标准三公理。无非白名单公理。源码中 `sorry/admit/axiom/unsafe/native_decide` 均为 0。
- 复用原服务器命令的既定 Lean 4.36.0-rc1、mathlib `807d3836b165983210ee2ecf3cd28f239436949c`，CPU10–13、root-heavy.lock、M8192、j4、autoImplicit=false。私有 2M／公开 8M heartbeat 没有改变逻辑公理。保留的 trace／linter 警告不形成数学缺口，也无需为清理警告改动已冻结字节。

`common-growing-region-full-review-coverage.json` 是完整逐名覆盖。为阅读 pp.all 的重复实例，先将空白段抽为 46 个格式字典因子，再对保留全部数学 token 的文本作 657 个可逆括号子串因子；已完整读全部 657 因子、109 条残余类型和 46 种空白值。每条保存精确空白位置，逐项逆变换等于原完整类型，并用外层原始段复原整份 493665 字节原件。没有用 pretty 摘要代替实际类型。生成 `_simp` 类型均为相应数值／零因子／幂／集合归属恒等式，生成 `_proof` 类型均为源码算术侧条件；其全部类型和 AX 已逐条读审。

## 原文与实际对象

完整原文范围：`C:/game/shao/current/c12/supplement.tex` 471–475、758–840、2700–3048、3710–3850；`main.tex` 622–625、646–694。原文 supplement SHA256 `b99f2ac4d2f39dd39772d98a5702b7a923c2f10f8730a08fc1b4cd6bba4742bd`，main SHA256 `beb00f718487e36de433175c97f1d500cb48e7a92ce5bd5ad5d62bb132122d06`。

源文的未来时钟是 `T=(n-i)m2`。本接口推广为任意正自然数 m 的 `T=m*m2`，保持实际原始二阶矩，未替成中心方差时钟；最终源实例仍须取 m=n-i。一般有界概率律 nu、正方差、可能非零的 mu 及全部真实噪声对象都保留。没有对任意 nu 偷用仅限截断律的结论。

源文 `K` 为偏置二点差经三角律所得弦噪声的特征函数，`Xi=K(z,zeta)^8*K(-z,zeta)^8*S(z)`。已完整读实际 chord/full-noise law/map、复特征函数、实际 cutoff/test/mark/amplitude、真实 future/noise kernel 及轮廓积分子的字面定义。full-noise map 的第二个八项族在第一坐标取负，在第二坐标取正；真实 kernel 由同一 nu 的 m 个增量与独立 full-noise 积分定义。两个反射分支共用同一 Xi(z,zeta)，没有换成 Xi(-z,zeta) 或拟合乘子。

原文完整 `Lambda=(1+y)n|mu|+(1+y)^3*n*m3`。仅有三阶矩项 eta≤Lambda 不足以支付宏观均值漂移；本公开头根本没有 Lambda，并明确保留 `n|mu|+n*m3`，因此没有隐藏丢失均值前提。

## 证明逐段核对

1. **原始矩、符号与时钟**（18–63、616–656、1860–1915）：由 `V=m2-mu²` 得 0<V≤m2；积分非负多项式 `(abs(a)-sqrt(m2))²*(2abs(a)+sqrt(m2))` 得 `sqrt(m2)*m2≤m3`，继而 m2≤gamma²、m3>0、gamma>0。`20gamma²≤T=m*m2` 确保 m≥20，故 `(m-1)m2≥T/2`；并由 nm2≥3/4 得 m≤(4/3)nT，不需 m≤n。q≥0、N≤7 给 T≤7。N≥1/16 使 sqrt(N)≥1/4，lambda≥y/sqrt(N) 给非负 lambda、s≤lambda² 与 s*h≤lambda。两个 sj 的零／非零分支均支付 tilt 头的独立条件。

2. **归一化与 Xi 指数账**（657–726、945–1020、1042–1137、1917–1931）：`bj*Zpm^m≤E0` 先独立证明；j=1 时 `-s*q-s*T=-s*N=-lambda*y*sqrt(N)`。只有该标量进入高频 matching，不把已含 Xi 的 majorant 再乘第二份 Xi。低频奇差丢一份最大 normalizer 时，用 Z≥exp(-2lambda*h) 支付 exp(2lambda*h)。由 m3≤h*m2≤2hV 得 gamma≤2h；真实 full-noise 支持 `|Z|≤34h, |Y|≤64h²` 与 s*h≤lambda 给 `norm Xi≤exp(98lambda*h)`。与源产品式的 16 个 chord 和一个 scalar 的预算一致。

3. **标量积分与合法积分**（64–615、727–944）：幂差由真几何和证明，m=0 的一般辅助边界也成立，实际消费 m≥20。绝对值 rpow 尾积分在 a>0、p<-1 下用正负半轴反射求值；Gaussian abs moment 先在两半轴证明可积，再用正 a 缩放，半次幂没有在负 u 上错误解释。取 a=exp(-2L+log(T)/2)；k=0..3 给统一 exp(9L) 倍的实际 Jk。profile 的实际实现用 compact core 加幂尾得到 4b、4b² 的充分界，并非依赖草稿的精确有理积分公式。weighted-tail 用截止上的 sqrt(|u|)≤16sqrt(Gamma)|u| 比较，严格导出整数幂／sqrt(Gamma) 尾项。Fubini 使用真实全平面 L1；切片不是以非可积 Bochner 积分默认取零来制造不等式。

4. **点态低频与实际四区行**（1167–1313、1481–1560、2017–2158、2220–2411）：在区域 I，对实际 a^m-b^m 保留 m-1 衰减与一份 normalizer 损失，得 T/256 Gaussian；真 odd defect 的 mu、m3、|v|+sj 三部分均在。积分同时消费无权和 |v| 权真实 mark 界，c 的四项展开精确还原 `|mu|U+m3*Vpoly`，包括 `(s+Delta^-1)U+y(J2+lambda J1)`。实际指数成本 odd=101+9=110，even=99+9=108（此处实现统一 Gaussian 9，未冒称较尖的 104），均≤200。偶行用两幂之和与真 `iz(exp(izw)ap+exp(-izw)am)`，没有强加 odd 小因子。

5. **区域 II–IV**：II 的 aStar=128Gamma，`(y+lambda)Gamma≤1/2048` 确实支付 aStar*y≤1/16；直接以概率特征函数幂≤1、真实 outside31 及全实 u profile 积分得 `Gamma Delta^-1` 和 `Gamma²Delta^-2+lambda Gamma Delta^-1`，成本99。III 真 u≠0 由严格外区截止推出；同一次 matching 头以 b=lambda、ell=m 给正／负 tilted law 与同一 Xi 的两界，保留 `4752^8 exp(162lambda*h) PJ/|u|^16`，相位至多再付1。积分导出 `PJ R1tail` 与 `PJ(R2tail+lambda R1tail)`，Gamma 正性保证 sqrt 分母合法；没有第二份 Xi 支付。IV 用独立的 aStar=4h 和 y*h≤1/64，outside31 产生 |u|^-31，额外 |u| 行为 |u|^-30，故 Gamma^30／Gamma^29 正确，固定 4^31、128 的幂只进常数。

6. **边界、分区、导数**（1561–1588、1955–2016、2413–2487）：四个集合均可测；`|u|=kappa/Gamma` 归 I/II，低频 cone 等号归 I，真实 chord cone 等号归 III，u=0 也由 I/II 覆盖。任意阈值的 indicator 和恒等式由四个穷尽分支证明，再实例化实际阈值，互不漏计。全平面 L1 来自已资格 contour 原对象。实际 integrand 精确等于 bj 乘 unscaled real-identity integrand；bj 只一次。先积分四区再作两条 j 的有限和／范数三角不等式，系数 norm((2pi)^-2)≤1；消费的确是 f'(0)、f 在 w 的可微性和 deriv f 在 w 的可微性，以及实际 f''(w)，无 surrogate。

7. **粗多项式与最终支付**（1314–1480、1589–1732、2489–2577）：令 b=Bstar≥1；各 Jk≤2b^4，U≤4b^5，Vpoly≤44b^7，PJ≤256b^16，R1/R2≤2Gamma*b。Gamma≤1、h≤1 均由原头推得。实际四个 A 行界依次 308Rn*b^7、2Gamma*b²、512Gamma*b^17、2^31Gamma*b^62；四 B 行为 4b^5、6b^4、1024b^18、2^32b^63。每个外区 A 保留一份 Gamma，再用 `Gamma≤16exp(8lambda*h)n*m3≤16exp(8lambda*h)Rn`。私有 coarse_table_sums 的全部八个行等式在实际消费处均由 rfl 实例化，不是把目标作为任意表假设。总和常数2^40足够；同一最终 C=2^50*Ctab 同时支付行界、两条 j、总和及粗界，量词位于所有律／参数之前。

8. **512 与 alpha**：Ebase 保留 24 的 cubic 和 200lambda*h。外区奇项的一份 exp8 在比较之前加入，`200+8≤512` 且 `24exp(lambda*h)≤512exp(512lambda*h)`，全部乘子非负，故 `Ebase*exp(8lambda*h)≤E512`。没有比较后再追加 Gamma 的指数，也没有改变 exponent128、源 literal512 或 alpha=1/1024。已读参数模块三个完整兼容头；短时钟其 E 的字面表达式与本 E512 相同。

## 已资格依赖复用与相互作用

完整读取所有实际消费头：contour displacement／real boundary identity、localized mark 的全部积分结论、joint tilt normalizer、tilted low frequency、quadratic complex characteristic data、full-noise law/support、complex matching；另读 amplitude split/localization、complex extension/product、512 majorant 和参数支付头以核对语义与后继兼容。只复用旧完整审查与原对象，不重读旧证明或重放其生产者。

| 依赖 | 精确源 SHA256 |
|---|---|
| SourceComplexBoundaryContour | 1d919177fd95da2151a6858b9a8c4bdb822c53e3c175dadc6c48dcbf51bc0da5 |
| SourceComplexBoundaryAmplitude | ad51e5f6ffc1a80c750c90b71f90fa70fc21ebfdde8b78f8a811c9ee369f06aa |
| TiltedLowFrequency | 10f1dfeed068fa5f521b220f5f5d138992603dae5447dd034da0462ef44dd159 |
| BoundedQuadraticTilt | 93c302d9de61bc4bf0cb238e82a4ed5b7f66e0ddbd2e833fec5bc6bbb25a8257 |
| QuadraticComplexChord | e0b7eaaf0bdf026a8c12a7e65aa76c4532a0a1c745b68c03a8d82cfb6a01fed4 |

contour 根资格凭据明确绑定源1d919177、对象 `d84fb64ec7d9b1a198a6c68a985f4cd7f6446cdbbe62e45c81669805655ed2bf`、commit7b8d55bd。参数模块完整审查 CORRECT 绑定源 `d1dfeec4877ecc871d1984b0dcb7e28f4cd2cd373d48fd3e3c6b420fe3de5c69`／对象 `0485050d99a1bd12964f6c74bca019540cd6b74f4401bc7b61937513e34bca90`。当前只读库相应源与这些精确版本一致。

## 认证范围与明确剩余

接受唯一公开 theorem、37 个私有辅助证明、71 个生成 theorem 的精确版本。它是原文 fourregions 及 generalcomplexbound 的有条件、真实对象形式化辅助结果，不作新颖性或原根解决宣称。

后继仍需把当前显式前提在原固定 x 的截断律及 m=n-i 上实例化；完成真实宏观表和 Ebase 的固定常数支付、短时钟的 Bstar／E512／尾概率组合，以及 q>5 的实际核和导数消失。参数模块保留 q>5 析取，不能直接丢弃。原始 kappa*sqrt(L2) 约束、未来若需更大 L4 的选择及相应 alpha 兼容都不是本声明的自动结论；改变512或alpha必须重新冻结受影响范围。微时钟、其他概率／生存／无条件二阶矩与 C1/C2/OQ3/OQ4/OQ56 原根仍 OPEN；p54 修复和外部结果归属未改变。

终审无 required fix、无 critical gap。根可复用本次完整审查及原 source-bound kernel／全所属 AX 凭据，只补实际接口／交互／聚合集成差额，不因进入 PR 或上下文更换自动重审旧证明。审查写权在三份终审产物完成后释放；无在途命令、锁或子任务。下一项为根的范围接收与实际源 growingkernel 消费，未由本 reviewer 启动新写任务。

使用模型／强度按派审为 gpt-6.1-sol／xhigh，未切换。input、cached input、output、reasoning subset 计数不可见，均记录 null；不推算信用或订阅百分比。
