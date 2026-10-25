# 189 独立完整源码、题意与证明审查

STATUS: CORRECT

这是对精确源码 `7a8e60e20b22966be13643cef37664031ce5b5b88b4beec8bc3240a2324028e9` 的**源码层面**结论；当前 `qualified=false`，实际自有常量数 `UNKNOWN`。尚未收到该源码的服务器内核、同一 object 的完整模块索引实际 TYPE/non-theorem FULLVALUE 和递归公理证据。本报告没有以文本审查替代机械证据。

审查角色为 `/root/oq56_chaos189_final_review01`，与作者 `/root/oq56_chaos189_stage1` 和父级冻结者分离。只写 `drafts/oq56/unit189/final-review-01/`；服务器、Lean、网络、Git、上传、缓存写入和子上下文调用均为零。按任务要求使用 math-theorem，未启动 math-ultra。请求模型/推理强度是 gpt-6.1-sol/xhigh；运行时未暴露实际模型、实际强度和分类 token 用量，均记 null。

## 精确对象、范围和冻结

源为 `author-01/stage2/FiniteQuadraticSignChaos.lean`，29812 字节，672 LF、0 CR，UTF-8。已逐行读取 1–672 行，包括全部四个定义原值、九个完整证明、私有声明、局部数据与作用域。作者原 RELEASE0 的 source/manifest/hash-bindings 与实测相符；其 activeWriters、inflightWrites、inflightServer、inflightLean、inflightUploads、activeChildren 全为 0。

基础冻结 `323c3f3b6277b7effd4fafe62e19617333d9846358c44a09e93c89b8b197e9a8` 的 raw prefix、四个定义、九个头和 suffix 与源码精确一致；11 个有名局部数据的完整类型和初始化值只差排版空白。匿名连接补充冻结 `fb63d888df292691d8685ee6359e57e894d3f4ca970fff34845ccabe6ebce49c` 在实现前获父级授权，其十个表达式及外层 binder/自由参数与真实使用相符。没有新增 ambient variable、universe、instance、类型别名、选择器或额外数学前提。普通 Prop 的 have、case binder 与证明 lambda 不作为新增数据接口。

原源 p44 完整字节 SHA256 为 `3d6a674252a81b7ca051fd54aa0a621511ebce94af2f0bdf9b4eca8715bc5239`。本单元支付 p44(5) 的有限符号二阶混沌部分：任意自然数 n、任意实矩阵 D、显式零对角和任意实 q≥2，ordered 二次式 q 矩根至多 16q√E，half-ordered 至多 8q√E；另在显式 hsym 下给出逐实路径 Q=2 upper(i<j)。它没有建立原随机观测/鬼样本外层、原 F 的积分矩、包络随机矩、尾概率、DC 或根结论。

完整读 p51、p54 以核对范围：p54 对条件 p 矩只要求统一有界/收敛而非任意多项式变化率的修正保持；source upper 的真实坏事件和严格余量付款未被本模块替换。Shao–Zhou 的 Theorems 2.1/2.2、Remark 2.2、(92)、仅 DC 分支的 Lemma 6.1 及其上游输入仍为明确外部依赖。本模块没有取得它们的所有权，也没有宣称新颖性。

## 全部声明与完整证明责任

| 行 | 声明 | 独立核查 |
|---|---|---|
|16–17|quadratic|完整有序双和 ∑i∑j Dᵢⱼwᵢwⱼ，未插入 1/2、对称化或上三角过滤。显式 n,D,w，没有前提。|
|19–20|entryEnergy|完整按列外和 ∑j∑i Dᵢⱼ²，与欧氏列能量严格相符。|
|22–24|private bilinear|输入 s、t 为两个独立有限立方参数，分别读取 s i、t j；未把它们识别为同一个符号输入。|
|26–29|private cutMatrix|仅 δi=true、δj=false 时返回 Dᵢⱼ，其他为零；所有行列均仍在 Fin n。|
|31–70|cubeMean_abs_rpow_jensen|c=(2ⁿ)⁻¹≥0，立方基数=2ⁿ，故权重和为 1。先以 -|x|≤x≤|x| 证明绝对平均≤平均绝对值，再在 Ici 0 对 |f s| 用真实有限 Jensen；rpow 单调所需底数非负和 q≥0 均给出。该头只需 q≥1。|
|72–121|cut_entry_mean|flip k 是显式逐坐标对合，源码完整证明其单射和满射。i≠j 下四种布尔值使四个 chi 之和为 1；三次双射重排令四个有限和相同。只除非零 2ⁿ 和常数 4，得到真正均值 1/4；没有假设 n≥2。|
|123–180|partition_mean|先逐 i,j 检查：i=j 时切割恒零且原 Dᵢᵢ=0；i≠j 时把固定 Dᵢⱼwᵢwⱼ提出，调用 1/4 比例。然后两次交换完整有限和，归一化恰好 Q/4。这里是零对角的实际使用点。|
|182–252|cut_average_eq_decoupled|swapPair 在每个坐标按 δ 保留或交换两个布尔值，完整逐坐标证明对合/双射。选中项上第一新坐标为 s i、第二索引值为 t j，故 bilinear=cut quadratic；其余项两侧均零。积类型重排后第二立方只贡献精确基数 2ⁿ，N⁻²N=N⁻¹。任意 phi，不需可测性或独立性前提；真实两个全立方双平均实现所需独立均匀分布。|
|254–298|scalar_sign_moment_bound|uᵢ=toLp 2 (Fin1 上常值 aᵢ)，真 EuclideanSpace 而非普通 Pi 范数。逐坐标符号和、平方范数与非负平方比较证明 norm=abs；energy=∑aᵢ²。唯一最终调用是 qualified185 n/1/u/q/hq，保持实 q。|
|300–417|decoupled_power_moment_bound|vⱼ 是真欧氏列向量，a(t,i)=∑j sign(tj)Dᵢⱼ，Y(t)=signSum v t，完整证明 Y 坐标、平方范数及 energy=E。固定 t 先用标量头；正 q 下把根界转回幂界并提出 K^q。再用 qualified185 n/n/v/q/hq 控 Y 的 q 矩。K=2√q，K²=4q，得到 (4q√E)^q。没有未付款的混合范数交换或逐行绝对值粗估。|
|419–549|finite_quadratic_sign_moment_bound|每个 cut 平方项≤原平方项，故 cut energy≤E。先由完整切割重排加 decoupled 幂界控每个 cut 的矩。逐 s 用 partition_mean 和 Jensen 得 |Q|^q≤4^q Aδ|C|^q；完整有限双平均换序并平均每个 cut 界，常数 4×4=16。最后显式非负矩/非负 RHS 和 q>0 用根幂 iff 取根。任意实非对称 D 可用。|
|551–620|finite_half_quadratic_sign_moment_bound|从 ordered 根界转回 q 幂，逐 s 证明 |Q/2|=(1/2)|Q|，提出 (1/2)^q，乘积幂给常数 8，然后同样取正实根。未添对称前提。|
|622–668|quadratic_eq_two_upper|三歧关系把每项分成 i<j 和 j<i，对角由 hdiag 消去。下三角换序后，用 hsym j i 与实数乘法交换使其逐项等于上三角；双和相加得因子 2。w 是任意真实路径，未限制为符号路径。|

上述全部证明均与阶段一 13735 字节完整推导逐段一致；没有把原题等价改写藏作尚未证明的输入。概率 producer 185 的旧内部证明未重审、未重编译。

## 实际全部局部数据、匿名连接和作用域

完整冻结作用域文本已读，而非只读清单。11 个有名数据为：c（L36，捕获 n）；flip（L77，捕获类型 n；k,δ,r 局部绑定）；chi（L80，捕获 n,i,j）；swapPair（L190，捕获 n,δ；p 及两个 i 局部绑定）；u（L262，捕获 n,a；i,_r 局部绑定）；v（L306，捕获 n,D；j,i 局部绑定）；a（L310，捕获 n,D；t,i,j 局部绑定）；Y（L313，捕获 n,v，传递 D）；K（L315，只捕获 q）；C（L428，捕获 n,D；δ,s 局部绑定）；R（L431，捕获 n,D,q）。hq/hdiag 的证明值不进入这些数据初始化。

顶层作用域为 autoImplicit=false、指定 namespace、noncomputable section、open MeasureTheory、BigOperators ENNReal scopes 和明确的 FiniteHilbertSignMoments open。标准 Fin/Bool 有限性、实数和欧氏结构来自固定版本实例。所有源码头 binder 显式。ENNReal scope 正确解释 toLp 参数 2 : ℝ≥0∞，没有把 (Fin n→ℝ) 原范数改成欧氏范数。

已读并逐使用核对十项匿名连接：P1 在 L139–162 的选中因子函数，捕获 n,D,w,i,j；D1 在 L368–383 的 t↦‖Yt‖^q，D2 在 L384–400 的 t↦K^q‖Yt‖^q；M1 在 L444–454 固定 δ 的 s↦|Cδs|^q，M2 在 L500–511 的外 δ/内 s 平均，M3/M4 在 L512–534 的外 s/内 δ 平均与乘 4^q，M5 在 L493–511 的常值 R^q；H1 在 L591–605 的 (1/2)^q|Q|^q；U1 在 L630–667 的下三角函数。其全部完整函数类型分别为冻结的 Ωn→ℝ 或 Fin n→Fin n→ℝ，自由参数和外层 δ/i/j/s binder 均相符。原冻结还完整覆盖 Jensen 权重/绝对值/rpow 函数、flip 复合、swapPair 的两个积型 integrand、q 次幂测试函数、C·s 及上三角函数。没有未冻结的实质数据 helper/selector/instance。

## 185 两次调用、真实类型和值绑定

唯一已合格概率 producer 精确源为 `f5e4f873f4e6a2b10dfad014a2e3ac0341fb277bf970a206091342c95121350a`；父级资格 `7b87ea13149166c7eff3d3c8f88477d35981d789c10dbbe2e295190e8526c3bd` 和独立资格证据复用。完整实际 13 个 public TYPE、8 个非 theorem VALUE 已读，且独立比对 `producer-qualified-bindings.json` 与原 actual-owned-metadata：全部精确相同。185 的源和相关资格/metadata 哈希也实测匹配，未以 186/188 候选作为输入。

实际承重类型是 `∀ (n d : Nat) (v : Fin n → EuclideanSpace ℝ (Fin d)) (q : Real) (hq : 2≤q), Real.rpow (moment n d v q) (1/q) ≤ hilbertConstant * sqrt q * sqrt (energy n d v)`，无额外 n/d 正性、能量正性或偶整数 q 前提。实际完整展开 norm 明确使用 PiLp.instNorm p=2；实际 VALUE 确认 hilbertConstant=2、cubeMean=(2ⁿ)⁻¹∑、moment 为 norm signSum 的 real rpow、energy=∑norm²、signValue true=1/false=-1、signPath 逐坐标 signValue、signSum 为实 scalar 的欧氏有限和。

L298 输入 n,1,u,q,hq；u 的坐标与能量在 L266–296 支付。L377 输入 n,n,v,q,hq；v 的坐标、Y 与能量在 L318–336 支付。中间 L355 的 scalar 调用输入 n,(a t),q,hq，其中 t 明确在当前完整立方上固定，a t : Fin n→ℝ。没有捕获未允许的观测数据或替换矩阵维度。

## 固定 Mathlib 非平凡接口条件

全部接口来自绑定的完整主源包，已读取实际使用的完整声明与所有活跃 ambient；这里不是环境 TYPE probe。

* global convexOn_rpow：{p:ℝ}, hp:1≤p，定义域 Ici 0。L64–69 取 p=q，权重 c≥0、sum=1、点 |fs|≥0。ConvexOn.map_sum_le 的 Field/LinearOrder/strict ordered ring、AddCommGroup、ordered additive module 等 ambient 全部用实数标准结构，ι=Fin n→Bool；无缺失条件。
* Real.rpow_inv_le_iff_of_pos：ambient 实 x,y,z，条件 x≥0、y≥0、z>0，结论 x^(z⁻¹)≤y ↔ x≤y^z。L364–366、381–383、547–549、571–574、618–620 均分别证明矩非负、RHS 非负和 q>0。one_div/Real.rpow_eq_pow 是同一实幂记法转换。该接口容许零底数。
* Real.mul_rpow 需要两个底数非负，指数任意实；源码所有使用均为 4、1/2、K、norm、sqrt 或其非负乘积。Real.rpow_nonneg 只需底数非负；Real.rpow_le_rpow 另需底数顺序与指数非负，源码逐点提供。没有在负底数上套常规幂法则。
* WithLp 的 p,V,K ambient、toLp/ofLp 结构、ofLp_toLp、ofLp_sum 的 AddCommGroup V 与有限集参数、ofLp_smul 的 SMul K V 已完整读；PiLp=WithLp p (∀i,αi)、CoeFun=ofLp、toLp_apply 与标准 p=2 内积范数已核对。EuclideanSpace.real_norm_sq_eq 的唯一数学 ambient 是有限索引类型与真实欧氏元素；本单元取 Fin1/Fin n，均有标准 Fintype。
* Function.Bijective.sum_comp 和 Fintype.sum_prod_type 的主源显式 to_additive 生成关系已读。前者有有限源/目标及 AddCommMonoid 值域；源码明确给出 flip、复合和 swapPair 的完整双射证明。后者把积类型上的和等同两个 fiberwise 和；本单元值域是实数，两因子均 Ωn。L233/L244 的顺序与 hsum 中 t/s 顺序由显式有限和交换衔接。不能把这些原源生成声明误记为本审查执行过 Lean TYPE probe。

## 边界、禁止项及剩余证据

n=0 时完整立方仍有一个空函数而 2⁰=1，矩阵和/欧氏零维向量都合法。n=1 且 hdiag 时矩阵为零。cut_entry_mean 的 i≠j 分支在这两种维数没有实例，证明不要求额外维数下界。任意 E=0 时所有根幂步骤仍在非负底数/严格正指数下成立；全程未除以 E、√E 或矩。q 是任意实 q≥2；没有取整、偶数或自然数化。非对称矩阵的 ordered/half 两个矩界均保留，只有最后确定性桥接需要 hsym。若删零对角，partition_mean 本身会在 n=1,D00=1,w0=1 失败；该前提未被省略。

显式源中 sorry/admit/axiom/unsafe/native_decide token 均为 0；这只检查本源码显式内容，不能替代递归 axiom 审计。`source-static-verification.json` 保留一个已纠正的本地 multiline 文本解析器初版失败；该失败只涉及审查脚本的 `$` 锚点，源文件未动，纠正后 11/11 类型/值一致。

机器证据到达后，同一独立上下文仍须读全模块索引发现的所有 actual TYPE、所有 non-theorem FULLVALUE（包含 private/generated）、递归 AX，并与精确源、同一 object、源声明和冻结数据全面对应。当前不猜 owner 数、不把 13 个显式源声明当实际总数、不按 namespace 过滤实际 owner。只有完整证据符合白名单 propext/Classical.choice/Quot.sound 后才可形成 qualified 最终证据。
