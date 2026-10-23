# SourceComplexBoundaryContour 完整独立审查

STATUS: CORRECT

JUSTIFICATION: 唯一字面定义及三个完整公开声明符合冻结。新源码全部2233行、全部65个实际模块所属完整类型及唯一完整定义值已独立读完。真实整函数、闭条带衰减、水平/竖边L1、四个边界极限、两次矩形位移、完整实核导数联系及常数512主界均无缺口。原始服务器整源内核和全部所属常量传递公理收据精确绑定同一版本，无未覆盖项。

审查者 /root/common_contour_full_review，gpt-6.1-sol / xhigh，全新作者独立上下文；作者 /root/common_complex_growing_candidate。采用math-theorem，未用math-ultra，未开子上下文或侧栏。只写本MD、同名JSON及coverage，不修改数学源码、共享指令、注册表或他人文件。完成时间 2026-10-23T19:10:09.040Z；审查写权在完成时释放。

## 精确版本

- 唯一新源 Shao/Probability/SourceComplexBoundaryContour.lean，2233行、114895字节，UTF-8/LF、CR=0；SHA256 1d919177fd95da2151a6858b9a8c4bdb822c53e3c175dadc6c48dcbf51bc0da5。
- source-only commit 7b8d55bd2aa5d610a1f1fb3db6867552ce7d0ae5，parent a3efbda23e4a89e8d8d322728999b44816c86b05；该提交只新此源。读取时服务器提交、本地审查源、提交内容和服务器源一致。
- 原对象 SHA256 d84fb64ec7d9b1a198a6c68a985f4cd7f6446cdbbe62e45c81669805655ed2bf。
- 冻结 coordination/public-complex-boundary-contour-declaration-freeze.md，SHA256 08653cfb7035a8b9e40140dd2f23fd2f79324d31f8eff6f76a5dd9b478321c79。

独立比较只规范空白：sourceComplexBoundaryContourIntegrand的完整字面定义，以及sourceComplexBoundary_contour_displacement、sourceFutureNoiseKernel_complex_boundary_identity、sourceComplexBoundary_exponential_majorant三个完整公开头（全部参数、假设、let、常数和结论），四项完全相同。没有改变数学前提。冻结文件中已于v59验收的QuadraticComplexCharacteristic整源不重复审查。

## 原服务器证据与覆盖

原成功contour031直接rc=0、59.54111289978027秒，原成功命令本身用-o产生上述对象。全日志SHA256 5f8958790de1af0e5c8284ee260303a3040c44f9f0db892f31415bce13e34ab6。已读原请求，确认直接返回码在任何打印或日志尾处理之前保存；原本地收据与当前服务器哈希一致。源码错误0；114条警告为弃用、未用参数/策略、策略提示等，不是未闭合证明。

原唯一实际最终owned audit直接rc=0、7.2284650802612305秒。审计器SHA256 a166a3511a9b641fc1cb69307be7e4d2826239f7887e036752a442ea859e506a；owned JSON SHA256 a52aa6299617ee2d0cd5b5e372554c86b03ea557ba67c12bc7ea41a666ba3b84。完整类型/值日志保留服务器，362927字节/5226行，SHA256 018ec31b81647436afcdaaa72d2e36bf3fed16fa8bad8355dc1ea2bfd509855e。首次导出即用pp.all、pp.maxSteps=10000000、pp.deepTerms、pp.proofs；65类型和1值没有字面省略号。

实际所属65常量=64定理+1定义，包括41个显式源定理和23个生成proof/simp定理。审计按env.getModuleIdxFor?实际模块身份选取，逐常量Lean.collectAxioms递归检查。已将65个owner/kind/name与实际类型记录逐项匹配；每个AX集合都包含于propext、Classical.choice、Quot.sound，无额外公理。无sorry、admit、new axiom、unsafe、native_decide。

源码1–2233全读，无缺行；65类型包括private/generated全部完整读，唯一定义值完整读。生成项的泛型量词、类型类和结论均已核对；其证明由所读源策略产生并受原内核检查。逐声明源/证明区间、逐实际类型SHA256、生成项源父声明、逐项AX集合和唯一值SHA256见coordination/common-contour-full-review-coverage.json，SHA256 94abe5d21b14d1f8ece3d6e5f1b5665b6bb6d738af114e4efcbe431d7b1162de。

完整阅读159项重复实例构造/投影字典，随后完整阅读65残余类型和唯一残余值；没有省略数学表达式、量词或隐式参数。每条记录经字典逆展开与原记录空白规范结果全等，再保留原空白布局恢复：66条恢复字符串与原字符串逐字节相等，并绑定原SHA256。coverage保存实际在残余中使用的64项完整字典及各记录原/残余哈希；另95项是没有被残余引用的冗余子表达式，全部已读。没有把计数或前缀抽样当成类型阅读。原完整日志未复制到本地。

原环境：Lean v4.36.0-rc1，mathlib 807d3836b165983210ee2ecf3cd28f239436949c，shared-v34只读包视图，CPU10–13/root-heavy.lock/-M8192/-j4/autoImplicit=false。本审查新Lean执行0、AX重跑0、旧producer重编0、对象重发0、原生图遍历0，本地Lean/缓存修改0。一个可选只读哈希探针发现consumer没有BoundedQuadraticTilt源码，随后精确匹配其已验收来源源码和实际消费对象；没有Lean执行或状态改变。

## 完整数学与原文对照

main SHA256 beb00f718487e36de433175c97f1d500cb48e7a92ce5bd5ad5d62bb132122d06；supplement SHA256 b99f2ac4d2f39dd39772d98a5702b7a923c2f10f8730a08fc1b4cd6bba4742bd。本轮直接读main610–723，supplement463–550、758–826、1976–2043、2342–2462、2700–2785、3551–3711，包含h:supp:contour完整证明。新单元范围是contour(a,c)及其真实解析合法性；contour(b)属于已验收振幅producer。这是原文与经典解析论证的形式化，没有新颖性/优先权主张，也不领取原外部概率输入（含既存Lindley/Spitzer）的证明功劳。

1. 17–458行：唯一新全局定义使用冻结的未移位c_j边界积分、实际phi、同一完整Xi及两个真实导数因子。相位/分支transport从字面指数代数推出。weighted_entire验证真实中心L1、公共参数邻域、导数可测与导数L1 majorant，应用已读ParametricIntegral接口。支持上y√r和r分别界于2|y|和4；sqrt光滑只在需要分部积分的正支持区间使用其真实光滑延拓。实际phi/Xi联合整函数与乘积、自然幂给出完整F的联合复可微性，没有把目标位移或导数身份作前提。

2. 503–1055行：从固定sourceScalarDensity及真实指数倾斜构造紧参数光滑族，平移到[1,3]后消费旧Fourier32原语，再按实际gamma>0缩放给出scalar8。gamma正性来自同一nu的正方差与原始三阶矩正性。Xi确为K(z,zeta)^8*K(-z,zeta)^8*S(z)，两个K闭条带有界、实际S给出八阶衰减。boundary3自行构造局部递归幅度∂r(J/q)，证明光滑、支持、L1及真实反复IBP；远v区取t=-uy/v，|t|≤1/16，q=t/(2√r)-1在闭支持不为零；近区真范数界付(1+|u|)^3。未以sharp或growing-y结论作输入。

3. 1057–1407行：scalar8、boundary3、phi幂、空间/时间指数与d因子实际相乘，得到冻结指数(5-d.val,3)。B严格正且对四个j,d选择和条带频率一致，但允许依赖全部显示固定参数。真实profile3整线积分=1，较大指数积分≤1。用product Lebesgue volume及限制乘积测度支付真实水平/竖边L1，原字面EU≤lam*B/(1+|R|)^(5-d.val)、EV≤s*B/(1+|R|)^3。四个atTop/atBot边界极限分别挤压推出，j=0零高度亦覆盖。B不被提升为随y增长的一致界。

4. 460–501、1260–1554行：rectangle_limit真正调用有限Cauchy矩形定理，再用两条真实L1水平线及竖边两端极限取整线极限。已核对Mathlib矩形四边方向和improper-integral条件。先移z的[-lam,0]，再移zeta的[0,s_j]；三个已证product-L1使相应Fubini次序交换合法，得到真实二维volume积分身份，没有抽象shift假设。

5. 1556–1899行：chi=c0+c1的紧支持积分重组与原Fourier-test正弦恒等式逐点成立，包括u=0。先分别证明k=0,1的两项一侧moment积分L1，才用保持实际volume的u反射。只使用实际Xi第一坐标反射性质，不要求nu对称或中心化。直接消费原sourceFutureNoiseKernel_spatial_derivatives在0及任意w的完整f/deriv(deriv f)身份，得到负(2pi)^(-2)。二阶导数是完整f的真实二阶导数，不是偶部分的替代品。

6. 1902–2085行：实际nu.tilted在b=lam、-lam与同一s_j下的概率性和严格正Z来自完整all-real tilt接口；负支真实频率为-u。移位边界mark和bj各出现一次，时间相位也一次，两个反支乘同一个完整Xi(z,v+i*s_j)。正bj使G等于实际移位F除以bj，所以G真L1已付。公开头所有let及其交互均逐项核对。

7. 40–149、2087–2231行：s≤lam²由lam下界单独证明；s*h≤lam另由sqrtN≥1/4和y*h≤1/4证明。m3≤h*m2及显式m2≤2V付gamma≤2h，实际噪声支持34h/64h²付exp(98lamh)，空间因子再付lamh。真实正归一化常数的自然m次幂、b*mu≤lam|mu|、精确s(q+T)=lam*y*sqrtN及24≤512、99≤512合成字面E。mu完整保留，m3一直是∫|a|³；无隐含Gamma小量、零均值、增量对称或守卫偷换。

## 复用的依赖及明确边界

复用精确v59的427模块：main b6bdf7333a514f9f908c838ddd0161b5617e422e，receipt 30f1cbf1885bfbd141c23a68844696af992cb4b31eb21afc93b6d912da425ccc。只重新读真正消费的完整头、字面值及新应用交互；十个直接依赖本地源与实际消费版本逐哈希一致。九个私有原语按准确模块和private数值index=0的Lean.Name绑定，其完整新wrapper实际类型与旧头/markedPhase定义一致，没有靠同名保证同一值。

复用的独立完整review：AMP coordination/common-amplitude-final-review.md，SHA256 86d664cba7f3a0e3d8077107180b44abed0cb71ffcc950a947ddd0befa1f906c，连同type-only无损补充，由amplitude-root-qualification.json绑定精确源码、对象及完整类型/值覆盖；QCC coordination/common-complex-characteristic-review.md，SHA256 ba9ade3a5d426a93c7613ffc46a834288b0d5350607ee37cd1f8e41f4d651bbb；Chord coordination/common-complex-chord-review.md，SHA256 03d155c83c2ca01f1c187a3fb0f9d76834348a24fe7885dbac93736615d5c3ef。完整源/对象哈希、所读接口和证据路径在JSON/coverage；本轮不声称重读旧producer整源证明或其全部actual-type导出。

本结论绑定固定7b8d55/source1d919177/objectd84fb64e。其他作者在同一worktree另开branch或新增后续模块，不会扩大本审查范围，也不要求整worktree永远不变；根已告知未来SourceGrowingRegionIntegrals属于另行激活作者，本审查没有读取或接受该未来候选。

B的非一致性不能支付growingkernel(i)–(iii)。四区域积分、实际macro/short倾斜时程、q>5支持特化、大y概率/生存/调节项/去平滑及根闭合不由本单元声称。C1/C2、OQ3、OQ4、OQ56原OPEN根保持OPEN。没有待补类型/值/AX覆盖或关键数学缺口。

审查完成；本审查没有在途Lean命令或source写入，报告写权释放。下一步由root对精确contour单元验收/发布，后续独立作者按其单独冻结推进。最终回合不是持久继续机制。
