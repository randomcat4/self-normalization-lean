# FL249 独立完整最终审查

STATUS: CORRECT

JUSTIFICATION: 最终源码逐字实现冻结声明，保留 FI246 的同一实际白化、倾斜律、独立样本推前及六阶累积量多项式包。新增真实加权复振荡积分由已资格化 FK248 支配于同一加权绝对误差积分；在同一常数下以独立于参数与物理位置的自然阈值证明两类积分的 n³ 倍一致趋零。全部 116 处声明 let、完整新证明及全部 3 个实际 TYPE/0 个 VALUE 已审查；现有服务器原生编译和同一首次对象的全实际所有者递归公理收据与最终精确源码绑定。未发现额外数学前提、量词削弱或关键证明缺口。本裁决限于本冻结截断窗口结论，原 OQ3 根仍 OPEN。

## 身份、隔离及完整覆盖

审查者 `/root/oq3_fl249_final_review`，新鲜独立最终审查上下文，配置 `gpt-6.1-sol/xhigh`；作者为父实例 `/root`。使用 math-theorem、chinese-output-style；未启用 math-ultra。本角色只写本报告，所有数学源、冻结、旧报告、协调及执行工件只读。未修订前提、证明或证据，未开子实例，未连接服务器，未运行 Lean/AX，未上传、Git/API 发布或向其他聊天发消息。

依次完整阅读冻结声明 456 LF、最终源码 525 LF、全部实际类型 1149 LF；实际类型显示仅去前导缩进，未省略任何行。源码 1–525 行和整个最终证明 466–522 行均已读。完整阅读 scope、freeze-retained-FI、new-oscillatory-conclusions、bearing/qualified/server-dependency/own-firstO-view 四类绑定、receipt、audit-record、build-history 和 Audit.lean；并检查 attempt01 至最终源的完整差异及证明正文逐字相等。

完整阅读 FI246 源公开声明 418 LF（旧证明已接受，未重审），并逐行完整阅读其全部 950 LF 实际类型；完整阅读 FK248 源公开声明 13 LF、全部 12 LF 实际类型。已资格化旧完整证明/内核/全所有者证据精确复用，不重新审其旧证明。父已 ENTIRE 全读的 FI151LF、FK97LF 报告有精确资格绑定，本轮核对报告文件哈希并阅读有关归档限制、来源及证据范围的段落。

原始只读来源完整覆盖：`C:/game/shao/current/oq3/proofs/r2/report.md` 1–158、220–235、493–523 行；`repair01.md` 全 226 LF；`C:/game/shao/current/OQ3/verdict.md` 全 58 LF。原文件 SHA256 分别为 `572e74aa9c12e2771f5543a5709a2807666eeea0a4076e7a3263e5c7bcf87f55`、`9d2e554838aa15b645aaf74a42468d423fed606aa91c1181d0dddf4e87c57cfd`、`fd0a5732845aa96ab1725e6d1e52676502092e49d2c00225ce1fde26ac06f3b5`，本轮本地散列相符。

## 精确字节与冻结核对

以下均为本轮本地只读计算的 SHA256；B/LF 为字节数及 LF 数。最终源、冻结、类型及保存失败源都是 UTF-8、无 BOM、零 CR，末尾有 LF。

| 工件 | SHA256 | B / LF |
|---|---|---|
| u22fl-frozen-declaration.lean.txt | `0ee3f0b3abe60ea974acb20b6c61513e7ef405c964ccf9bb3a63d3442c19a9fc` | 29963 / 456 |
| u22fl-source.lean | `d7f92e2bc3345af07d24422830928c6d5e334b11f99eac4a8909bdcef35ca920` | 33069 / 525 |
| u22fl-attempt01-source.lean | `8a811569534ccb828f33dee6ace990d4a5784a33d594c7ae8acff0f2882dc89e` | 32995 / 524 |
| u22fl-actual-types.txt | `425188ae3ff903bb3a15961acc53b48e95f62c4ae061ad7f4304a0c56dda2247` | 122924 / 1149 |
| two-hundred-forty-ninth-unit-scope.md | `8b679cb48fa760721341dcd02a1e78e11ed28d1f606543b2e40077ec1689c1a4` | 2449 / 37 |
| u22fl-Audit.lean | `49917131c925cd2d850ba9110b2f0b418e4cedf3170d5e8b1000817de1abe041` | 2062 / 47 |
| u22fl-receipt.json | `d014f3ed5e621f58d5ec7271dbcb896947b8d19f101b1c05fd27b9e859ecbc1b` | 8122 / 269 |
| u22fl-audit-record.json | `c6bec40a6f9a20a894d411d5a39d32f5335845299ceb46fb86672ba4a8c99970` | 3242 / 105 |
| u22fl-build-history.json | `aad7d2da0d87e35ab455a4a7f27ccbd7a093ea8fd306b1b85532e053b9b8ec6b` | 4534 / 164 |
| u22fl-qualified-dependency-binding.json | `c2b463d77325a10f2419693a5eebb812c7205962e0c76a91cfb825f2e691e738` | 3387 / 61 |

其余完整已读绑定 SHA256：freeze-retained-FI `4d11d011d0219874400043f537651cd9a8370f6bf49d6bb0ceaf446198456b8d`；new-oscillatory-conclusions `c36f78fda7465dc71c075b81d7c8f028a85aaaf640d39f5d8b6d858c5ec79fef`；bearing `cdf469e5d665dbd8027d365c52d238d3b37d31edac7998074b3be74ce9889e63`；server-dependency `3bdb3d4b7e6d90a07a7e08b0f7ebafae20bb75bd95bd5933f73a3f443b858eb0`；own-firstO-view `49aa0f5d1320b0c66ccc6aec1146dda483875b4d1e20ead9ecfd3a214e76653b`。

从最终源 `theorem` 起到证明分隔符 ` := by` 前逐字提取，补一个结尾 LF 后与冻结文件字节完全相等。new-oscillatory-conclusions 的完整公式与该声明最后整个新增包逐字相等。FI 声明到最后 all-k 窗口包之前的全部前缀仅改定理名即逐字相等；在最后包只移除新 kernel、追加振荡结论和第二渐近包，并恢复外层 forall 括号后，得到 FI 原末包逐字原文。未删旧前提或旧结论。

FI 的 103 处 let 全部保留，新增第 104 处 kernel 和第二模型包 12 处 let，合计 116。计数包含第 70 处以 `(let X` 开头的括号内 let；只匹配行首 let 的正则会漏掉它，不能据此记成 115。两次最终模型包从 Qsample 到 kernel 的完整文字逐字相等。

## 全部声明内接口与原题语义

| let 序号 | 完整覆盖的对象 | 数学作用及核对 |
|---|---|---|
| 1–9 | tilt,D,s,t,A,means,Y,laws,Phi | 实际二次倾斜、协方差、显式逆平方根白化、实际均值、中心化白化变量、推前律及其特征函数；无自由替代律 |
| 10–13 | L,U,cA,RA | 同一 lo/hi 及原 c,R,beta 的明确变换；旧正性、谱界及弱 Cramér 包保留 |
| 14–15 | P,Q | 原 Taylor、四阶对数展开的实际投影矩；未改其截断阶与误差 |
| 16–20 | Qsample,M,T,rho,Qn | 第一个真实独立样本乘积律与白化样本均值推前；真实三四阶对数式 |
| 21–25 | Qsample,M,T,rho,Qn | 相同模型的指数式及高斯阻尼估计 |
| 26–30 | Qsample,M,T,rho,Pn | 原低阶特征函数多项式；旧包完整保留而未冒充新六阶式 |
| 31–35 | X,X,X,kappa,Q8 | 实际方向投影、实际 CGF 导数及八阶对数式 |
| 36–42 | Qsample,M,T,rho,X,kappa,Qn8 | 同一 E 与 laws 的归一化八阶累积量展开及真实 CF 等式 |
| 43–49 | Qsample,M,T,rho,X,kappa,Qn8 | 同一模型八阶指数近似与阻尼误差 |
| 50–57 | Qsample,M,T,rho,X,kappa,a,Pn | 真实三至八阶累积量、逆 sqrt(n) 次幂与加权总次数≤6的有限指数多项式 |
| 58–69 | envelope,Qsample,M,T,rho,X,kappa,a,Pn,small,weight,error | 小频半径 deltaInt*sqrt(n)，真实绝对误差的高斯可积包络；真实连续、可积、非负积分及 O(n^(-7/2)) |
| 70–75 | X,kappa,a,Pn,tail,f | 全族同一六阶 Pn 的高斯增长界与任意多项式率尾积分 |
| 76–79 | Qsample,M,T,rho | 原 n³log(n) 远频点态实际 CF 衰减 |
| 80–85 | Qsample,M,T,rho,far,f | 原对数立方窗内远频加权实际 CF 积分 |
| 86–92 | nu,Q,M,T,rho,middle,f | 任意 delta>0、H 的中频实际模型；原独立乘积 Q，未换用旧整窗低阶结论 |
| 93–104 | Qsample,M,T,rho,X,kappa,a,Pn,window,weight,error,kernel | 第一个完整最终实际窗口与新增真实复振荡积分 |
| 105–116 | Qsample,M,T,rho,X,kappa,a,Pn,window,weight,error,kernel | 第二个渐近包，全部定义与 93–104 逐字相同 |

原前提是概率测度 mu、紧集 Theta 位于二元 MGF 有限域内部、0≤beta<2/5、c>0、R≥0、每点真实倾斜协方差行列式正及族上一致弱 Cramér。形式声明保留 FI 的 `0 ≤ beta`；原修复来源的使用范围仍为严格 `0<beta<2/5`，该正指数范围完整包含在形式声明内。不能把源修复表述的严格正下界误写成 Lean 的字面前提，也不能据此声称 beta=2/5 或以上成立。

所有实际 Qsample 都是 `Measure.pi (fun _ : Fin n => tilt p)`，M 是原总和/n 与 `Shao.energy/n`，T 是 `sqrt(n) • E p (M−means)`，rho 是这一 T 对原乘积律的推前。E 来自 FI 同一次调用；未引入第二个白化选择、随机耦合、独立性额外假设、自由 error/Pn 或 coherence 前提。X 的方向投影与 kappa 的实际 CGF 导数不变；a 的阶数 j+3、分母 sqrt(n)^(j+1)、q:Fin7 与 sigma 加权总次数≤6不变。

最终窗口始终是 `{z | sqrt(z₁²+z₂²) ≤ n³ log(n)}`；既不是旧 n³ 窗口，也不是全平面。所有集合积分使用实际类型中的 `MeasureTheory.volume`，复核了真实复值 integrand 和实权重转复数的位置。k=0、零频点、空 Theta 均不需要新增前提；n≥N≥2排除了新增渐近推导的零分母问题。k 任意但固定；不声称常数对所有 k 同一。

## 承重依赖资格与复用范围

| 项 | FI246 | FK248 |
|---|---|---|
| 源 SHA256 | `b2c8a569775bcb27ced07d4aa0272053d40e44f4d65cd10d720df09edf1c09a4` | `2e51edd82d8da7151cf9fcd8ea0381c7065c48886cd300498a1f226346bc8796` |
| 源 B/LF | 38666 / 637 | 1995 / 48 |
| 类型 SHA256 | `e1f0feff2df18ad5c1e80a646c2e1c1948c159d1a797d3594d71f2d7cf0ff858` | `dd8717250f76de598e7bd1c48cdd7f6da88b873d082edefa2572870c104827f4` |
| 类型 LF、实际 TYPE/VALUE | 950，3 / 0 | 12，1 / 0 |
| 资格 SHA256 | `1ce857ba2cafeb5a8a2a501f699b85e0fdeaa10843f9fd9c6301de9381612a8c` | `29d726280f3f887d82c561b6331472a1a9311329bd2e1e8894ed71238f91db11` |
| 已完整独立报告 SHA256 | `bd2e53247870f87ef6424f9edc4955c834f9234b7df5a986d7ef2e5d64ea017b` | `4e368d96cd86505346a120e1eb95af8559e3f841c66a6fb45ed703699135135c` |
| 旧 receipt SHA256 | `6bff49d8429051568103980d49fe518406110785fe8076550a90887f837b5f0a` | `75c0e3ed482a17cdf3a4043883d6c232aab0db0dc8e6bd312bc5380b980d6cfc` |
| 首次原始 O SHA256 | `cc7d825b6659f3bdc8af5bdf59fde0f2bb37bb212ad256382a1c46eb7f942c62` | `5de2badad586e9c72065aa7a5ce1a588f1043d57027f1073315638837d06f712` |
| 首次原始 O 字节 | 4077048 | 87760 |

FI 三个类型为公开定理、`_proof_1_1 : ∀ NM NF NG n, ¬1≤2 → False` 和 `_simp_1_2 : ∀ {α} [Preorder α] a, (a≤a)=True`；全部类型已完整读，生成结论是合法基础事实，不承载额外原题前提。FK 唯一公开类型要求连续误差 e 和其真实径向 k 次权绝对误差在任意集合 s 上可积，结论为所有 x 的明确 `exp(-I⟨x,z⟩)` 核加权复积分可积，范数≤同一绝对误差积分；本轮完整核对其参数、两处 let、限制测度及量词。

新 qualified binding 的 FI/FK 两段与各自 qualification.json 的解析内容逐项完全相等；本轮本地源、类型、报告、资格和旧 receipt 哈希均相符。server-dependency 的两源/首次对象哈希分别与该资格一致，qualified binding 明确两者最终审查前 COMPLETE_QUALIFIED、从 FL kernel 起源/O 未变。历史 bearing 中 FK 尚处最终审查中的状态保留为真实历史，不回写。服务器绑定最初记录的是 attempt01 预期源 8a811569…；这不冒充最终源绑定，最终 d7f92e2b… 由成功002、全所有者 receipt 及 own-firstO 单独绑定。

FI 的自身首次 O 哈希有本次精确资格记录；经 FI 继承的 DF/BV/DB 旧 own-firstO 归档局限仍然存在。DF 旧 receipt 未归档自身首次 O：后续当前保留对象 `086dcf81db4f696a5c06650a8f9a058e51c4fed8ad6c9567a9dbccc8b91a196a` 仍只是当前观察，`exactFirstOriginalO=null`，不能回称历史首次。FI 报告保留的 FH→BV/DB 限制未被 FL 消除；FK 报告继承的 CY 历史对象限制亦未扩大为新历史证明。这些是可追溯性限制，不是新数学假设。

## 新证明逐步数学核对

466–477：`classical` 后引入声明内实际 let；FI 仅调用一次，传入全部相同冻结前提。解构得到同一 lo,hi,E 及各旧包；重构保留其所有矩、连续白化、Taylor/对数/八阶/六阶、多项式高斯尾、远点、远积分和中频结论，只证明最后新增包。未抄写或重新运行 FI 旧证明。

478–487：固定 k，从 `hwindow k` 取得 C>0、N≥2及对全部 n≥N、p 的同一真实窗口包。C,N 先于 n,p,x。`h.1` 为 rho 概率性，`h.2.1` 为 Pn 连续，`h.2.2.1` 为 error 连续，`h.2.2.2.1` 为真实加权绝对误差可积，`h.2.2.2.2.1` 为积分非负，`h.2.2.2.2.2` 为 C/(n³sqrt(n))。六项投影完整保留，未错位使用。

固定任意 x 后，FK 以这个真实 error、其连续性、同一 window、同一 k 和真实绝对可积事实实例化。其径向 weight 与本地 weight、显式 kernel 与本地 kernel 均按定义相同。得到真实复值 `kernel x z * (weight z : ℂ) * error z` 的 IntegrableOn 与范数≤绝对误差积分；传递到 FI 同一 C/(n³sqrt(n))。FK 的单位模长核不会增加 x 相关常数，故第一包一致于全 x。此处包含真正复可积性，不是利用不可积集合积分约定值冒充估计。

488–499：对任意 epsilon>0，Archimedean 选择自然 J，使 `(C/epsilon)² < (J:ℝ)`；然后明确选 `Ne=max N (J+1)`。Ne 依赖既定 k 的 C,N 及 epsilon，不依赖 n,p,x。n≥Ne给出 n≥N≥2及 J+1≤n，故 J<n；自然数转实数保持严格不等号，n>0，sqrt(n)>0。

500–503：`(C/epsilon)²≥0` 且 `(C/epsilon)² < J < n`，严格单调平方根给出 `sqrt((C/epsilon)²)<sqrt(n)`。因 C/epsilon≥0，可把左端的绝对值化为 C/epsilon，得到 `C/epsilon<sqrt(n)`。严格性由 J 的严格选择保留，未由平方比较错误跨越符号分支。

504–507：epsilon>0使上述比值不等式等价于 `C<sqrt(n)*epsilon`；sqrt(n)>0再推出 `C/sqrt(n)<epsilon`。两次乘除均有相应严格正分母，nlinarith 只是实数乘法交换与该不等式的整理。

508–516：对任意实 I，只要 `I≤C/(n³sqrt(n))`，以非负 n³乘两边合法。已得 n>0与sqrt(n)>0，故 `n³*(C/(n³sqrt(n)))=C/sqrt(n)` 的 field_simp/ring 消去合法。无需假设 I≥0；实际应用的绝对积分本身仍保留非负性。结尾用严格小于 epsilon，得到真实 scaled little-o 估计。

517–522：第一次以同一 hwin n hnN p 的真实绝对误差积分上界代入 hscale；第二次对任意 x 用同一 FK、同一模型取得实际振荡范数上界再代入 hscale。二者共同使用同一个 Ne；没有在 x 或 p 引入后重新选择阈值。第二包虽不重列第一包的概率性、连续性和可积性，n≥Ne≥N可直接使用第一包，因此没有丢失这些实际定义事实。

## 全实际所有者、机器绑定及失败影响

全 1149 LF 的 actual-types 确含且仅含以下 3 个 TYPE，0 个非定理 VALUE；不只审公开定理：

| 实际所有者（共同前缀 Shao.OQ3.compact_open_domain_six_order_log_cubic_oscillatory_window） | 完整类型作用 | 传递公理 |
|---|---|---|
| 公开定理本身 | 全部冻结参数、116let、保留包及新增两包；公开 TYPE 已逐行全部读 | propext, Classical.choice, Quot.sound |
| `._proof_1_1` | `∀ (N J n : ℕ), J+1≤n → ¬J<n → False`；自然严格序合法推论，N 为未用参数 | propext, Quot.sound |
| `._proof_1_2` | `∀ (N J n : ℕ), 2≤n → ¬0<n → False`；自然正性合法推论，N,J 为未用参数 | propext, Quot.sound |

Audit.lean 通过 env 的真实 module owner 枚举全部常量，拒绝新 axiom，对每个所有者调用 `Lean.collectAxioms` 并逐项限于三项白名单，输出完整 TYPE，对任何 defnInfo 输出 VALUE；还确认公开目标为 theorem、实际目标计数1、owner集合非空。新模块实际3条全为theorem，所以零VALUE有实物枚举依据，两个生成定理不在审计外。源中无 sorry/admit/new axiom/unsafe/native_decide；本轮静态禁用词扫描为空。

保存的 native001：2026-10-27T19:00:12.163413Z，8a811569…、32995 B/524 LF，天然 RC1，5.3982159197330475秒；日志 SHA256 `08c510b44d8c9d5d499ddb6301bb1ad2b7fee5a62361029da5ef6d2fedfd0f1a`、261 B。失败为旧第64行 Matrix 转置记号缺命名空间而解析失败，无成功对象。完整失败源仍原字节保留。

attempt01 到最终源的完整差异仅三项：`open MeasureTheory` 恢复为 `open MeasureTheory ProbabilityTheory Matrix`；`open scoped BigOperators Topology` 恢复为 `open scoped BigOperators RealInnerProductSpace`；在定理前恢复原 `set_option maxHeartbeats 2000000 in`。最终声明逐字冻结相等，整个 ` := by` 后证明正文也与失败版逐字相等，故是命名空间/记号及执行配置修复，未借解析失败修改数学。声明内局部 option 只控制心跳上限，不绕过内核。

保存的 native002：2026-10-27T19:01:37.216256Z，最终 d7f92e2b…、33069 B/525 LF，天然 RC0，59.352288307622075秒；日志 SHA256 `93ae51b19cfb7532b3d8a75c200a150581a67635f85487a7be3011f395405987`、1136 B。作者交付说明为4个警告，本轮未读取服务器原始警告文本，不能伪称另作实机复测；成功与精确版本依据为既有绑定收据和实际类型。

首次成功原始 O 为 `cd0a47b8628be1bacbaa8a2030b4792a739c16096b5216ed35e974baada93ae3`、2831840 B。同一首次 O 的新全所有者审计保存为天然 RC0，6.1743647158145905秒，2026-10-27T19:02:06.863621Z；审计日志 SHA256 `201cd7397e887d590d2223c4e7788b38355ae3c2a08789535f913568502d074b`、123176 B。实际类型的完整 SHA/B/LF 与 receipt 相符；receipt 和 audit-record 的所有共同字段逐项相同，receipt.build_history 与独立 build-history JSON 完全相等。

own-firstO-view 将该源与同一 O 绑定到 lead-oq3 构建对象及 accepted-source-view 链接；新增自己的首次对象链接1，旧条目修改0、共享 cache 写0、二进制拷贝0。服务器依赖观察先记录新 FL 源/对象缺席、己方 heavy空、锁空闲；两次尝试只有第二次成功，再以该同一成功对象作全部新owner审计。现有记录没有旧 producer/旧成功 proof/leafAX 重跑：本模块唯一一次成功，失败001与日志保留；FI/FK旧证据精确复用。本轮没有发起任何机器重跑，也未把当前对象观察包装成历史首次归档。

本地只读 pin 是 Lean `leanprover/lean4:v4.36.0-rc1`、mathlib `807d3836b165983210ee2ecf3cd28f239436949c`，与 SERVER 规定一致。保存执行资源为 ROOT_OQ56_OQ3_40，CPU36–39/44–47，native -M8192 -j4；内存准入仅扣有界干净 inactive_file，保留 raw used/headroom、project140/guard180/hard200GiB 和系统60GiB。内嵌 helper 的旧 phase39 标记是策略来源，不能覆盖外层实际执行 phase40。本审查不声称重新观察实时进程、锁、对象字节或内存。

## 原来源边界与裁决

原 report 的截断确为 n³log(n)，最弱远弧指数为 n^(1−5beta/2)/(log n)^beta；原修复要求严格0<beta<2/5。repair01 第一节及 verdict 已把统一性归属改为 Song Theorem2.1 的 uniform-in-law、s=8；report 旧 Angst–Poly 对角一致性论证不恢复，也不声称 FL 形式化了整个外部 Song 定理。

保留 p54/v_corr 修补：`v_corr=−t0*sqrt(det Delta)*sqrt(Lambda1)` 及其边界 Laplace 因子没有被 FL 删改、重证或用于反推密度。原真正联合非格点不足的 accepted counterexample、远区率间隙或外部概率局部化条件及充分修复而非最弱边界的性质均保留。原 report 220–235 行的 Hermite 修正密度与小胞求和并不是本冻结公式的结论。

FL 认证的是同一实际模型在原增长但仍截断的窗口上，所有固定自然权重 k 的真实复振荡误差 IntegrableOn、对全 x 同一 Ck/(n³sqrt(n)) 范数界，以及绝对误差与振荡范数的 n³ 倍一致趋零。全 ℝ² 实际 CF 可积性、密度存在、傅里叶反演、Hermite 修正识别、平滑/去平滑、exterior 概率、B–D 和原 OQ3 根仍 OPEN。不能从这些随 n 增长窗口上的积分估计推出全平面可积或密度，也不能把这里的径向加权控制自动说成已完成全部空间导数/反演步骤。没有独立新颖性或历史首次认证。

裁决 STATUS: CORRECT，覆盖这一精确最终源、完整冻结声明、全部实际所有者、新证明与上述精确机器证据；受所列原题范围及继承的历史对象可追溯性限制约束。由父实例 ENTIRE 全读本报告后自行完成资格化，本报告不提前替代其最终接收动作。

实际 token telemetry 不可用：input_tokens=null，cached_input_tokens=null，output_tokens=null，reasoning_subset_tokens=null；不估造订阅份额或精确费用。

运行状态：COMPLETED_STOPPED。交付后本审查者唯一报告 writer/审核权限释放，writer=0，children=0，Lean/AX/heavy=0，inflight=0，pending=0，uncertain=0。无后台继续执行或待发请求。
