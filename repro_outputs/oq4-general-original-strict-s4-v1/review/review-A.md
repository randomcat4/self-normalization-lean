# A：RademacherGeneralStrictS4 独立完整终审

STATUS: CORRECT

审稿人为 context217，fresh gpt-6.1-sol / xhigh，独立于作者216及本批次B作者。只写本审稿目录，未改冻结、实现、状态、注册表、Git或缓存。完整读原 spectrum01.md 四节；本单元直接对应第4节的严格格点边界，并推广其 S4 表达至冻结的任意序列。未审判尚未交付最终源绑定的 B。

精确对象是 attempt002/Source.lean，SHA256 `935753f46f606adb975c944598896ebc4e0ff75da0a3ce92111f5dd0292de034`，14578 bytes、301 LF、无CR/BOM；冻结 `3acc0366edd9cea7b202fefd95f4a2b8e433b4d1426877ef8a90405ec28bf664`。三个透明定义的完整值与两个定理完整签名逐一匹配冻结，公开定理没有增加前提。完整301行实现均已逐步审阅。

## 源义、量词与证明

`delta h = Nat.ceil h - h`、`correction n h = (π²/4)(n/h³)delta h`，`Q` 是规范有限 Rademacher 路径严格正前缀事件的真实概率除以给定实际布朗运动的弱上确界概率。已读 native 定义值，及 strictEvent/strictP/pathLaw、BrownianSup.probability 的实际完整类型和值。路径法则为独立 ±1 各半；布朗分母并非自由概率函数。

假设恰为 h→∞、n/h²→∞、n/h³ 最终有一个固定正上界。n 为任意自然数值序列，无单调性；h 为任意实序列，无全局正性。结论同时返回共同尾部三项正性、修正对数误差趋零和除以修正指数后的比值趋一；目标正性没有被当作前提。

令 m=Nat.ceil(h)−1、a=(m:ℝ)。在 h≥2 的尾部才消费已合格 ceil_boundary_bridge：自然数截断可转为实减法，h−1≤a<h、h≤2a、m≥1，且 strictP(n,h)=p(n,a)、delta(h)=a+1−h。整数 h 时 a=h−1、delta=0，非整数时为正确前驱格点。桥的逐点部分只在整数前缀条件下成立；本证明消费的是桥已证明的真实概率等式，没有偷升格为任意路径集合等式。

由这些不等式严格推出 a→∞，n/a²≥n/h²→∞，n/a³≤8(n/h³)≤8M。调用旧 `S4_EVENTUAL` 的阈值确是合法弱左端点 a=m，而非可能为右端点的原 h。已完整阅读旧 S4Outputs、TimeLegal、ProbabilityLegal、LogIdentities 的 native 类型及定义值、definition_bridges 与 S4_EVENTUAL 的类型和消费语义；旧证明资格复用。它返回 y=a/√n→0，及同一尾部 √n>0、平方恒等式、p(n,a)>0、b(y)>0、弱 Q>0。投影位置与完整 conjunction 顺序一致。以 0<x=h/√n≤2y 得 x→0。

布朗平移完整接口要求 x、y 最终为正且趋零，全部已供给；其比值为 b(y)/b(x)，对数中心符号是 λ(1/x²−1/y²)=λn(1/h²−1/a²)，λ=π²/8。符号与乘法分解 Qstrict=Qweak·b(y)/b(x) 一致。弱左端点的原 w 正好为2λn/a³。

private `center_remainder_bound` 不含概率或结论性假设。h≥2、h−1≤a<h 给 a>0、h≤2a、0≤d=h−a≤1，继而 h²≤4a²、h³≤8a³。两个有理恒等式分别给 |a⁻³−h⁻³|≤24h⁻⁴ 和 |h⁻²−a⁻²+2d h⁻³|≤12h⁻⁴。第二项精确分子为 −d²(h+2a)/(h³a²)，第一项为 d(h²+ha+a²)/(a³h³)。组合为 λn[2(a⁻³−h⁻³)+(h⁻²−a⁻²+2d h⁻³)]，故常数为2·24+12=60。整数墙 d=1 及 n=0 也满足该界；未用 d<1 或 n>0。

0≤n/h⁴≤M/h 在正尾部成立，故 n/h⁴→0。三个误差（弱 S4、实际布朗平移、中心余项）相加给目标对数误差。所有消分母及 log_mul 均在共同正尾部完成；最后 exp(logQ−correction)=Q/exp(correction) 也只在 Q>0 尾部使用。有限早期的 h≤0、a=0、n=0 由实数总定义表达式容纳，不影响滤子极限。未发现数学缺口。

## 完整实际声明与机械证据

完整阅读 owned-interface.txt 的全部15个 native 类型和三个非定理的完整值。native 清单独立核为 public4 + private1 + generated10；3 definition /12 theorem；源头仅 delta、correction、Q、private center_remainder_bound、strict_S4_EVENTUAL。私有实际名是 `_private.Shao.OQ4.RademacherGeneralStrictS4.0.Shao.OQ4.RademacherGeneralStrictS4.center_remainder_bound`。十个生成项全部计入：Q.congr_simp、correction._proof_1、correction.eq_1、strict_S4_EVENTUAL._simp_1_2 至 _simp_1_8。它们分别是定义同余/方程、数字 AtLeastTwo 见证、数字非零、乘积非零、自然/整数幂非零及自然数加一非零的辅助命题，无隐藏实质假设。

18份compact工件逐字节与其manifest绑定，包含 source、Combined、audit suffix、native/graph/interface/AX、首次对象和执行收据。未过滤 environment difference、module ownership、stage2 三集合均恰为这15项；每项完整类型非空，定义值完整，私有映射唯一，全部 owned 的AX根都有对应记录。直接外来 type/value 引用集合恰为563个接口，其中33个项目接口；本证明消费的项目接口完整类型及全部非定理值已阅读。

另一次服务器仅阅读已保存 audit-native.json 并独立遍历其 type AND value 引用：由15根可达全部61222个节点，无多余或缺失节点；项目声明646、项目模块29、实际导入项目模块100均由图实际归属重算。对每个owned根分别遍历并计算 axiom-kind 集合，均等于该根保存的collectAxioms输出；整体恰为 propext、Classical.choice、Quot.sound，未见其他axiom或unsafe/partial。audit-native 的已保存哈希是 `923412b222d5b19303f20b6ca7245f7d7fbc5824ead048964cc1d2a1fa0be8ef`。

复用首次成功 kernel receipt，actual exit0、未超时、进程已回收，固定 Lean v4.36.0-rc1 / mathlib807d3836，autoImplicit=false、skipKernelTC=false、trustLevel1025。执行收据 `b0f83ae928476ad332807bf48f23f3fedf7af0dcb2fa026e60f6a4fd8f576930`；Combined `b73f07c2b85ba910da1d79b370a20ac8c0c011c39c8e15dfe72459ec24d22e60`；首次对象 `254979a4f54a94a91a0bd273d86f93ed737b85f4b2be4eebc8dcf459abcac7c7`。当前实际对象stat精确相同：device64947/inode4981026/size1542640/mtime_ns1792823065034903399。服务器实际编译的Combined文本哈希仍相同。旧两个直接输入只做stat复用，未读/重hash旧binary，未重编旧producer。

新依赖 RealStrictBoundary/BrownianBoundaryShift 复用214的合格独立完整终审及其精确source/object绑定；没有重审其旧证明。相关source分别为009ec079…、a1afd98a…，214 receipt 为3a1fe5b6…，两个lead acceptance均已读。A自身的源义、完整新证明和每个新增声明均由本审稿独立完成审查。

本审稿新 Lean/parser/build/nativewalk 命令均0，旧对象内容读取/重hash/旧producer重编均0。仅进行一次服务器 savedJSON/新编译文本/对象stat只读核对。界面工件首行遗留通用 sparse-critical-denominator 显示标题，与实际mainModule、源、对象及声明清单无冲突，属于非阻断文字残留。

此结论只认证固定 Rademacher 规范严格一般序列 S4。它不认证一般增量分布、尚未交付的B、严格临界全部相位/极限点集，亦不关闭原 OQ4 或其他原根；原根保持 OPEN。新颖性/会议价值未作评定。
