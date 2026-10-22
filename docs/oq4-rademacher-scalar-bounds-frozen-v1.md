# OQ4 原72行：a/rho标量余项冻结接口 v1

STATUS: FROZEN_PENDING_STATEMENT_REVIEW
CANDIDATE_AUTHORITY: ADOPTED_AS_FROZEN_V1
INTAKE_STATUS: INTAKE_ONLY
SOURCE_GATE: FRESH_SOURCE_REVIEW_REQUIRED_IF_ADOPTED
PROOF_STATUS: NOT_WRITTEN
LEAN_STATUS: NOT_RUN
IMPLEMENTATION_AUTHORIZATION: HOLD_PENDING_OWN_GATES_AND_LEAD_RELEASE
S2_STATUS: OPEN
S3_S5_BROWNIAN_STRICT_COSETS_ROOT_STATUS: OPEN

Lead 明确采纳 SCA0 全部合法性及 SCA1/SCA2 的全 m≥1 定量结论为冻结 v1；原候选 6e761d8c15f86253a9cee120d4ee0772c18cdc2052384fb16f74daf5aaeec5e6 保持原字节。固定将来模块 Shao/OQ4/RademacherScalarBounds.lean，namespace Shao.OQ4.RademacherScalarBounds。第5节 C_log/C_tan 仅为后继派生需求，不在本冻结范围。当前待全新独立来源语义审查，不是数学证明或 Lean 认证；纯标量叶只需已认证透明定义，其概率应用另接 S1/Pair，不添加这些未认证接口作本叶前提。数学和实施须分别过门并由 lead 明确授权。

## 1. 唯一新来源及精确范围

唯一新数学义务选自 C:/game/shao/current/oq4/c01/spectrum01.md，commit 35d4580b61e22e7145f47730045a09874ef93259，SHA256 b65f9e0c2f9b40a28d092491b479bd20d0b8ee8a9ac940c3c4760cfff7d2670b，4306 bytes。

- 11–12行固定弱格点域m=floor(h)、H=m+1。
- 36行定义真实a_H=H^(-1)cot(π/(4H))、rho_H=cos(π/(2H))。
- 60行定义λ=π²/8。
- 70–72行在S4中明确使用 log cos z=-z²/2+O(z⁴) 和 a_H=4/π+O(H^(-2))。
- 66–67行显示S3所消费的n log(rho_H)和log(πa_H/4)；76–77行显示后继S4的系数及误差阶。

本叶只把第72行在真实角度上的两个展开规范化为全m≥1的绝对定量界。它不把Taylor界假定为额外输入，不额外要求H≥H0，也不把吸收位置H扩为独立实变量。不加入原文没有写出的a二阶系数或logcos四次系数。

## 2. 固定定义、类型与对象识别

m:ℕ。仅量化1≤m。定义实数

H(m):=(m:ℝ)+1，
u(m):=π/(4H(m))，
z(m):=π/(2H(m))，
a(m):=(1/H(m))*(Real.cos(u(m))/Real.sin(u(m)))，
rho(m):=Real.cos(z(m))，
λ:=π²/8。

cot采用cos/sin的固定意义。a(m)、rho(m)与原文a_H、rho_H及Pair的a_m、rho_m是同一明确表达式，不是自由序列或待选参数。

可选的已认证定义接口为 Shao.OQ4.RademacherCosine.angle、rho。lead明确许可的公开声明账 C:/game/shao lean/drafts/oq4/rademacher-cosine/declarations.md，实测SHA256 e9ec045fccfd4ed68f5b6515f1b28310ab90bf71609cb7bba87a0c1b4d7f850c，39048 bytes；本轮只读148–179与599–622行的公开类型/生成等式类型：

- 157行：angle : ℕ→ℝ。
- 169–177行：angle m=π/(2*((m:ℝ)+1))，故是上面z(m)的同一透明定义。
- 608行：rho : ℕ→ℝ。
- 620行：rho m=Real.cos(angle m)，故是上面rho(m)的同一透明定义。

这些是定义对接，不是为候选添加数学前提；未读任何旧定理证明体。a可以直接由Real.sin/cos与除法定义，log直接用Real.log；不存在必须先假设S1、Pair或U1才能谈论这些标量的问题。

与实际概率的识别另属依赖边：Pair固定接口 C:/game/shao lean/drafts/oq4/frozen-rademacher-spectral-pairing-v1.md，SHA256 69c5cf5822044e19520e10c4a6de4a31e0e8f43d296e477982a9c5637c85c6fb，8661 bytes，37–60、75–79、83–98行，把同一a、rho绑定到实际Rademacher谱主项。将来把本标量结果用于p(n,h)时，须接S1/Pair真正认证的概率身份；这条应用边不是本纯标量叶的上游假设。

## 3. SCA0：全部定义合法性，不是自由假设

对每个m:ℕ且1≤m，必须在同一固定定义下核对以下结论：

H(m)≥2，H(m)>0，H(m)^2>0，H(m)^4>0；

0<u(m)≤π/8<π/2，
0<z(m)≤π/4<π/2；

Real.sin(u(m))>0，
Real.cos(u(m))>0，
Real.cos(z(m))>0；

a(m)>0，
0<rho(m)<1，
π*a(m)/4>0。

故cot及所有显示分母都非零，log(rho(m))和后继log(π*a(m)/4)有真实正自变量。这些合法性不是候选前提，不能让证明者通过添加sin≠0、rho>0或a>0假设绕过固定域核对。m=1与m=2必须保留。

候选本身不含n、sqrt(n)、实际概率对数或Brownian概率分母；因此不需要额外正时间、正生存或Brownian正性前提。

## 4. SCA1/SCA2：冻结的最小核心声明

存在两个绝对实常数C_a、C_rho，满足C_a>0、C_rho>0，使对每个m:ℕ且1≤m，按第2节定义有：

SCA1：
|a(m)-4/π| ≤ C_a/H(m)^2。

SCA2：
|Real.log(rho(m))+λ/H(m)^2| ≤ C_rho/H(m)^4。

量词顺序完整写为：

∃ C_a:ℝ, ∃ C_rho:ℝ,
  0<C_a ∧ 0<C_rho ∧
  ∀ m:ℕ, 1≤m →
    (|a(m)-4/π|≤C_a/((m:ℝ)+1)^2 ∧
     |Real.log(rho(m))+(π²/8)/((m:ℝ)+1)^2|
       ≤C_rho/((m:ℝ)+1)^4)。

SCA0是同域必需合法性结论，与上述核心一起接受完整边界审查。C_a、C_rho先于m选定；不依赖m、h、n、奇偶、任何尺度序列或S4中n/h³有界性的常数。禁止改为逐m常数、仅一条序列的界、H≥任意H0、m充分大或自由Taylor余项假设。

SCA2中的领先项恰为原72行-z²/2在z=π/(2H)处对应的-π²/(8H²)；不改变原系数或误差H^(-4)。这里仅声明拟证明内容，没有给出任何推导。

## 5. 与原h、尺度及派生便利输出的关系

本核心无h或n前提。应用于原文时，只允许对全部m≥1及全部实h满足m≤h<m+1使用同一H=m+1。实际弱端点h=m对应δ=H-h=1；一般δ∈(0,1]，不是可自由取值的参数。不得在整数h处改成strict的δ=0。

来源后继尺度仍照原文：

- S2：任意弱格点序列(m_k,h_k,n_k)，H_k→∞且n_k/H_k²→∞。
- S4：h_k→∞、n_k/h_k²→∞、n_k/h_k³=O(1)。最后一个条件精确指存在M>0及K，使k≥K时n_k/h_k³≤M。
- 原n_k/h_k⁴=o(1)、倍率趋一、临界子列与极限点集均不在本叶结论内，不能换成新前提。
- 本核心C_a、C_rho与这些序列及M无关；不增设更强尺度来回避边界。

后继会需要 log(π*a(m)/4)=O(H^(-2))（原67行）与 tan²(u(m))=O(H^(-2))（原56行）。若另列全域便利输出，其准确候选语义分别应是：

∃ C_log>0, ∀m≥1, |Real.log(π*a(m)/4)|≤C_log/H(m)^2；

∃ C_tan>0, ∀m≥1, |Real.tan(u(m))|^2≤C_tan/H(m)^2，

其中C_log、C_tan同样绝对且先于m量化；Real.tan在这里与sin/cos的固定意义对接，分母非零由SCA0检查。

这两项只记录同一a展开及固定定义之后的派生接口需求，不作为第三、第四个独立新来源叶，也不暗中作为本候选已冻结或已证的结论。最小建议采纳范围为SCA0+SCA1/SCA2。若lead需要把这些便利输出也写入将来冻结声明，须明确列入并另受相应声明审查，不能从本候选文本推定已获认证。

## 6. 依赖账：定义边与概率/Brownian边分开

| 依赖或使用 | 本叶是否需要 | 准确边界 |
| --- | --- | --- |
| Real.sin/cos/log、实数代数与固定m/H定义 | 需要 | 透明定义；估计及合法性是本叶待证内容 |
| 已认证RademacherCosine.angle/rho公开定义 | 可选对接 | 公开等式类型已定向核对；不消费任何概率定理 |
| S1/Pair实际谱身份 | 纯标量叶不需要 | 把a/rho解释为实际p(n,h)主项的后继应用才需要；未认证接口不能当自由假设 |
| U1同一R的统一指数界 | 纯标量叶不需要 | S2及S3误差汇总的后继依赖 |
| 真实Brownian U及尾渐近 | 不需要 | S3实际概率比较的独立外部输入；不准以任意F或自由尾假设取代 |
| n/h³有界与δ位移估计 | 不需要 | S4父级确定性位移及误差组合仍OPEN |

U1固定接口为 C:/game/shao lean/drafts/oq4/frozen-rademacher-spectral-tail-v1.md，SHA256 b220e1ca9f89e5f9a3328131b430fb54b9656e5113b93241adbde1aad627354a，8952 bytes，84–104行。精确Pair+U1承诺已覆盖原S2第38–55行的核心；后续assembly/双尺度表述不另算新原始叶。

Brownian来源核对只用原文60–61行明确指向的 C:/game/shao/current/oq4/frozen01.md，SHA256 ea50b9fe0d742cbc9481fb126476ae2a788c7b0ec42d4e60636d757baf7cbc5a，1491 bytes。其3行是实际U=sup_{0≤t≤1}|B_t|；9行只给首项等价渐近~。spectrum01.md 61行所称相对O(exp(-8λ/x²))余项没有在该冻结原输入出现，故不能当已获证输入。S3显示的o(1)只要求首项相对渐近及真正正性/对数合法性；更强指数速率若要单独使用，须由真实Brownian来源补齐。这项外部义务与本标量候选无依赖关系。

本轮没有独立Brownian owner或认证声明可引用；其来源强度及作者分配由OQ4 lead负责，涉及共享B/U定义则按AGENTS.md交root。不能藉本候选关闭Brownian或S3。

## 7. 门与排除范围

本轮仅按lead派发登记：Iteration/Basis/AllModes fully formal PR82/86/91；S1 PRIVATE/no-o实施中；Pair及U1各有匿名数学CORRECT、未Lean。本轮未读取这些证明或审查，不重新认证其状态。纯标量叶无须把它们设为数学前提。

候选不冻结。lead若采纳，应先冻结精确声明并交fresh source语义门；其后数学证明、全新独立验证与形式实现另行派发。本轮没有给任何数学证明、Lean或Git动作。

S2父级、S3–S5、Brownian、strict事件、一般实cosets、Spectrum及OQ4 root全部保持OPEN。不扩展为自由H，不默加H0，不改变原领先系数/指数，不以待证Taylor/余项估计作为自由假设。
