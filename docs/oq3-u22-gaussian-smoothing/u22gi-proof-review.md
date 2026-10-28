# GI272 独立完整最终审查

STATUS: CORRECT

受审对象为 `Shao.OQ3.IndependentSumThickeningBounds` 的最终56LF源码。两个公开声明、两处完整 `rho` 局部定义、全部证明及全部实际类型均正确，且与13LF冻结逐字节相符。结论限于任意二维概率律的实际独立和在任意可测集合上的闭扩张、内缩与实数概率夹逼；不接受高斯尾率、原始曲边小胞统一误差、去平滑完成或 OQ3 正面根闭合。

## 角色、权限和读取边界

- 本上下文是 fresh 非作者最终审查者 `/root/oq3_gi272_final_review`，没有编写或修订受审证明；唯一写权限为本报告，其他源码、冻结、qualification、status 和 coordination 均只读。未读取或消费正在另行编写的 GJ 源码或审查结论。
- configuredModel=`gpt-6.1-sol`，configuredEffort=`xhigh`；actualModel、actualEffort、inputTokens、cachedInputTokens、outputTokens、reasoningSubsetTokens 均为 `null`。本上下文没有可核验的实际模型/计量接口，不编造使用量或订阅百分比分配。
- 已完整读 math-theorem 的 SKILL、prompt-library、openai-workflow、lean-verification 及 chinese-output-style；本轮没有启用 math-ultra，没有再委派。
- 已读 SERVER、TEAM 的必要所有权/当前字段优先规则、streamlined-acceptance-current，以及 AGENTS 的独立性、恢复和最新 OQ3 明确恢复规则；REGISTRY 只提取当前 Root/OQ3 和 currentAuthoritativeState 的有关字段。TEAM/顶层历史 coordinator 的旧编号不覆盖当前权威字段。
- 人类2026-10-27指令“oq3开启，继续推进。”恢复当前 OQ3 owner `01a16c48-80ee-7520-a9d9-faeeb6d05c78`；Root 为 `01a17d3c-6dfd-7cc0-94ed-35d758a423a5`。完整 phase40 文件已读并核得6181B/222LF/SHA256 `2b69e1eb2251724f2236bd8176623e7445a794dbb12a4f17a346885469fba480`。
- phase40 的 OQ3 child1、CPU36–39/44–47、历史名 `c12-heavy.lock`、native `-M8192 -j4`、项目140GiB/系统及其他60GiB/180GiB guard/200GiB hard limit 是保存的授权。本审查 heavy0，不借此启动任何服务器、Lean、AX、上传、Git/API、缓存或跨聊天操作，也不冒称新服务器进程观察。

## 实际阅读及精确字节

已完整阅读最终源码、失败源码、完整冻结、scope、bearing、attempt02-binding、final-source-binding、server-binding、两份 primary API、Audit、actual-types、receipt、audit-record、build-history、own-firstO-binding。下表由本上下文从磁盘字节实际重算；全部严格 UTF-8、CR0、无 BOM。

| drafts/oq3/ 下的文件 | B | LF | SHA256 |
|---|---:|---:|---|
| u22gi-source.lean | 2848 | 56 | `f31b67d111ae1937b7df2da427f0836142d873da7838ecfa241f72707d527c62` |
| u22gi-attempt01-source.lean | 2848 | 56 | `c6bad8d5bc0e9e9464995c2889c64602909d60035e004f6aefc7c56801d1df09` |
| u22gi-frozen-declaration.lean.txt | 944 | 13 | `f3b2e5c1c9d8a800fd4e70775e822fa1c29cd464be9ed01bc0786e505bbcc6e3` |
| two-hundred-seventy-second-unit-scope.md | 2262 | 17 | `af8624c8166dff97b24edb5cc3c957161395c3846a0e9019dffe79ead90e599e` |
| u22gi-bearing-dependency-binding.json | 2208 | 44 | `a8c8dd272ae6bd83cf8cd5c6378e5b9003003e51874627bd17ec75599f1a9f1c` |
| u22gi-attempt02-source-binding.json | 513 | 8 | `b4ab65173370ed6ec019660ccea83fea557d0bbc5b1d6c89943dee3d25cfe073` |
| u22gi-final-source-binding.json | 655 | 10 | `c4fffeefe99fba3175467c6909a7c779a544535c486949e6a447510048d981ce` |
| u22gi-server-dependency-binding.json | 611 | 20 | `c85b1ab92ed15a9c15318ea3c8b28e43043dd2d0f393298868a5eea685cbd224` |
| u22gi-primary-api.txt | 3426 | 63 | `560ff1508cc71c8af3f854549ac255feb1a9c4ec9ab66dc9e06d97630134ee14` |
| u22gi-primary-real-api.txt | 1747 | 26 | `e8dd656c86e59e128b27a68a5f0a2dcf0ec5fda4f259c02de3010ac14fb88fb5` |
| u22gi-Audit.lean | 2159 | 49 | `84d73e994fdc9ece35bbb812d9209834e7e43d73a22040b08440b136dd808665` |
| u22gi-actual-types.txt | 1137 | 20 | `46abc6038d1d3531a0e23812bb2e90689402838727df566870e3396886826fdd` |
| u22gi-receipt.json | 7946 | 268 | `9eb16d6c10c9356ba40087af3626eb2b6e54af80800ff1fb1035846cd33ea525` |
| u22gi-audit-record.json | 3073 | 104 | `d2cc195d210761267c5b864d3e78ce728e74a8822abc988f044772b83ca66863` |
| u22gi-build-history.json | 4527 | 164 | `fe883094280559ae2a912fcff18171e774823f6dbdb4bfeae7ad4e91b84102d5` |
| u22gi-own-firstO-view-binding.json | 567 | 10 | `e36be90cb1863b788714c9894033f0230098a6cb80e59ee9f8910a30a59de858` |

实际抽取源码中每个 `theorem` 至 `:= by` 之前的完整声明，以冻结已有空行连接，所得字节与冻结文件完全一致。两处完整 `rho` 都是 `(nu.prod eta).map (fun q => q.1 + q.2)`，没有任意化为附加测度参数。完整冻结如下。

```lean
theorem independent_sum_cthickening_bounds
    (nu eta : Measure (ℝ × ℝ)) [IsProbabilityMeasure nu] [IsProbabilityMeasure eta]
    (s : Set (ℝ × ℝ)) (hs : MeasurableSet s) (eps : ℝ) :
    let rho : Measure (ℝ × ℝ) := (nu.prod eta).map (fun q => q.1 + q.2)
    nu s ≤ rho (Metric.cthickening eps s) + eta {y : ℝ × ℝ | eps < ‖y‖} ∧
      rho ((Metric.cthickening eps sᶜ)ᶜ) ≤ nu s + eta {y : ℝ × ℝ | eps < ‖y‖}

theorem independent_sum_cthickening_real_sandwich
    (nu eta : Measure (ℝ × ℝ)) [IsProbabilityMeasure nu] [IsProbabilityMeasure eta]
    (s : Set (ℝ × ℝ)) (hs : MeasurableSet s) (eps : ℝ) :
    let rho : Measure (ℝ × ℝ) := (nu.prod eta).map (fun q => q.1 + q.2)
    rho.real ((Metric.cthickening eps sᶜ)ᶜ) - eta.real {y : ℝ × ℝ | eps < ‖y‖} ≤ nu.real s ∧
      nu.real s ≤ rho.real (Metric.cthickening eps s) + eta.real {y : ℝ × ℝ | eps < ‖y‖}
```

冻结本地创建/写入 UTC22:05:24.8314484，bearing22:05:39.1103972，源码创建22:06:04.2380388，均为2026-10-27。bearing 的保存状态为 `sourceImplemented:false`；native001 的保存时间22:07:05.511584+00:00。文件时间本身不是防篡改证明，但与冻结状态、源码逐字节相符和保留失败链一致。没有冻结后补改假设的迹象。首次失败稿整体执行 `Replace('∞','⊤')` 与最终源码逐字节相等；恰有三处，均在42–44行证明局部有限性命题中。声明、全部 let、import 和其他字节未变。

## 唯一项目依赖及固定库接口

唯一直接项目依赖为 GF269 `Shao.OQ3.IndependentSumSmoothingBounds`。已完整阅读其138LF独立报告、qualification、receipt、13LF完整冻结、22LF全部实际类型、26LF scope、102LF primary API，并读取被消费源码的全部 import/namespace/完整公开接口及两处 `rho`。按精确证据复用规则，没有再次完整审查 GF269 旧 proof 或重跑其成功门。下列字节绑定均重算一致。

| GF269 文件 | B/LF | SHA256 |
|---|---:|---|
| u22gf-source.lean | 2403/49 | `350e1bda8efa06edad6788dcf0c706826ba0cf9c5f7529b7015fb60744980982` |
| u22gf-proof-review.md | 19007/138 | `9444a2d1ff60680bf30e49106bd1cc2ccb0af6b9f9161bf30308b2c4ef618852` |
| u22gf-qualification.json | 1243/24 | `ac5c9f6025a13c08431056903fc7a58c02f46d5673c2427cc94c1bf4b11f9c03` |
| u22gf-receipt.json | 5507/187 | `1b3b8c7b3af3062d6b793fb2f926dde6df1d3407d46217488abd94cd10aa756b` |
| u22gf-frozen-declaration.lean.txt | 863/13 | `1e1bde6fe030a140f0c95feb76c85043a9a4b720f3f6c0a4ea4ff84f9f9737ee` |
| u22gf-actual-types.txt | 1106/22 | `4a38a6bb63b76d93ac53145a3384c99b8ecbe6d0a90af330d01618692be9a497` |
| u22gf-primary-api.txt | 5039/102 | `3df5c7aaa5ade664da526670e66755394a1b536382bcc8a2484dfbc21097ed48` |

GF269 的第一接口在 `∀x∈s, ∀y, ‖y‖≤eps → x+y∈t` 下给出 `nu s ≤ rho t + eta E`；第二接口在 `∀x y, x+y∈s → ‖y‖≤eps → x∈t` 下给出 `rho s ≤ nu t + eta E`，其中 `E={y | eps<‖y‖}`。两集合各具明确可测性前提，两个完整 `rho` 都是同一独立乘积加法像。其实际2TYPE/0VALUE及两个 let 与冻结一致，传递公理均为白名单三项；已合格首对象 `a856103fee01684713a4a987e326daa85ade702ca3bd103e71a74840aa5cd867`/51016B，native/同对象AX均RC0。GI 的 server-binding 明确该依赖及首对象精确且 viewSameOriginal；这里核的是保存证据，没有新服务器访问。

GI 的新固定库 primary 原文逐项核对如下。所读是已保存的固定库来源及相关完整声明/上下文，不声称重读全部 mathlib 源文件或新抓取服务器。

1. `Thickening.lean` SHA `6429465471cb6e7121b79c0509583ea258efadd837133350e9faf7c47775a220`：已读175–214的完整变量范围、定义、成员条件、两条 membership 引理、闭集声明与证明，以及297–316的闭包/自身包含上下文。`cthickening δ E = {x | infEDist x E ≤ ENNReal.ofReal δ}`，其闭性只要求伪扩展度量结构，不要求 E 闭/开/可测；本稿的标准平面满足条件。`mem_cthickening_of_dist_le (x y) δ E (h:y∈E) (h':dist x y≤δ)` 只要求伪度量结构，实际证点正好满足。距离下确界无需达到，证明没有偷用最近点存在。
2. GF269 primary 中 `Constructions.lean` SHA `098a249c756acb481b5ca22d6563e3f21e29dd7318689034eabaf971a12e1216` 的实际 `Prod.toNorm`、`Prod.norm_def`、坐标界和 sup 范数结构已读。`ℝ×ℝ` 的噪声范数和距离均为同一默认 max 范数，即 `max |y.1| |y.2|`，本稿没有局部更换为欧氏二范数。
3. `Measure/Real.lean` SHA `1b9d1490fa5acbffc570eac67f465d3d6ab0520aa3e54464f7520d60d6619b8d`：两份 GI primary 全读；又从现有 `oq56/.../comparison-probability-pinned-api-01.json` 读其1–55的 import、变量与定义含义上下文，以及同包 `Typeclasses/Finite.lean`1–57完整原文。有限测度源 SHA `a8ef0ba0a9b953a5aae9fb16188cd7ad93e0e8d5767c564d02e9f2e8c57eedf2` 的 `measure_ne_top (μ) [IsFiniteMeasure μ] (s)` 对任意集合成立，无可测性/正质量前提。
4. 补读已有 `p53-label-law-measurable-real-api-addendum.json` 的 parsed_payload 中 `MeasureSpaceDef.lean`81–111实际源码，SHA `3853c6899a36759a64c9658969fb2f1ea97f0d026598c0f0468c30fe2a5d7356`。完整字面定义为 `protected def Measure.real ... (μ) (s) : ℝ := (μ s).toReal`，105–108为 `measureReal_def` 及别名；无穷集合映到0，所以本稿必须先处理有限性。没有把 `.real` 当成自动保持所有 ENNReal 序关系的转换。
5. 补读现有 `p53-label-law-real-conversion.json` 中 Basic/ENNReal/Real 的35–53、61–79原文；保存 full_source 的15950B重新散列等于 `da5573e6bb7b196bd109724302c3db8eda3a3efab72c8db958ce2ddbf643cecf`。`toReal_add` 明确要求两加数均非顶；`toReal_mono (hb:b≠∞) (h:a≤b)` 只要求上界有限，并在内部推出下界有限。补读 `p53-label-law-extra-operations.json` 中174–183原文；31529B full_source 重算等于 `9c5ae45fe78f42b7b3c6336c49cd4f837ebf083f64677b4cddd91f609bb3bf7e`。`add_ne_top : a+b≠∞ ↔ a≠∞ ∧ b≠∞` 给本稿所需两个上界有限性。
6. 从已有 `oq6-original-selfnormalized-tail-202/author-stage1-01/primary-probability-prefix.txt` 读概率类、概率到有限测度实例及111–132的 map 概率完整上下文。概率源 SHA `00ef2a106c0ae4032944cec021ad58d04c370cc9b84547bed95462ca5205e25b`。`rho` 的局部概率实例可由字面乘积概率和 map 实例得到；同时加法实际可测已由 GF269 的完整合格语义审查覆盖，故没有把 total map 的备用分支误作实际独立和。其他 lane 的这些文件仅提供保存的 mathlib 原文，不引入其数学项目定理为依赖。

## 逐步证明与全部局部值

记 `P=ℝ×ℝ`、`rho=(nu.prod eta).map(add)`、`E={y:eps<‖y‖}`、`O=cthickening eps s`、`I=(cthickening eps sᶜ)ᶜ`。两个声明的量词均是任意概率 nu/eta、任意可测 s、任意实 eps；没有矩、中心化、密度、非原子性、凸性或边界正则性前提。

源码9–31的 ENNReal 夹逼：15行 `intro rho` 引入冻结 let 的具体值，并不生成任意比较律。16–19行的 `hout` 由闭扩张闭性得到 Borel 可测，`hin` 由补集可测得到；`sᶜ` 不需先是闭集。21行对 GF269 第一接口取原集合 s、目标 O，精确提供 `hs`/`hout`。22–24行对每个 x∈s 和每个 ‖y‖≤eps，用 `dist(x+y,x)=‖(x+y)-x‖=‖y‖` 得 `x+y∈O`。`add_sub_cancel_left` 消去的正是左端 x；没有噪声符号或交换因子错误。这证明 `nu s≤rho O+eta E`。

25行对 GF269 第二接口取源集合 I、目标 s，提供 `hin`/`hs`。26–31行对 `x+y∈I`、‖y‖≤eps，反设 x∉s 即 x∈sᶜ；同一距离等式及 membership 引理得到局部事实 `hm : x+y∈cthickening eps sᶜ`，与 hxy 的补集成员身份直接矛盾。因此 x∈s，得到 `rho I≤nu s+eta E`。此处确实证明了反向包含，没有把第一方向简单倒置。两个不等式始终在 ENNReal 内只用加法和序，无任何 ENNReal 减法。

源码33–53的实数夹逼：39行引入完全相同的 rho；40行 `letI` 仅设立这个实际像测度的概率证明，`dsimp only [rho]` 保留字面定义。41行的 `hu`/`hl` 分别是刚得出的上/下方向。42–44行 `hn`、`he`、`hr` 分别证明 nu(s)、eta(E)、rho(O) 非顶，所需有限性来自实际概率实例，没有从待证实数夹逼反推。

45行对 `hl` 使用 `toReal_mono` 时，上界为 `nu s+eta E`，由 hn/he 与 `add_ne_top` 得有限；46行对 hu 的上界 `rho O+eta E` 用 hr/he。下端 rho(I) 本身也是概率质量，且 `toReal_mono` 只需上界有限，因此没有缺失内缩测度有限性的必要证明。47–48行分别用准确的两加数非顶证据改写 `toReal_add`；49–52行的 `change` 仅按 `Measure.real` 字面定义重写。最终 `linarith` 从 `rho.real I≤nu.real s+eta.real E` 作实数加减得到 `rho.real I-eta.real E≤nu.real s`，右方向直接为 hur。

证明中全部 `rho`、`hout`、`hin`、`hm`、局部概率实例、`hu/hl`、`hn/he/hr`、`hlr/hur` 的内容和使用处均已覆盖；没有未审的 proof-local 值。actual-types 中两个 `have rho := ...;` 是冻结 let 的打印形式。输出恰有2TYPE/0非定理VALUE，无额外私有或生成声明；不存在应打印却遗漏的模块定义 VALUE。

## 边界与量词攻击

- `eps<0`：范数非负，故好噪声条件 ‖y‖≤eps 不可能、E为全集、eta(E)=1，GF269 的两个包含条件空真，界合法但退化。注意 `cthickening` 通过 `ofReal eps` 截断，负半径不意味着外扩空集；本证明没有依赖那种错误解释。
- `eps=0`：闭扩张可包含 s 的闭包，内缩对应内部，不能替换成 s 本身；好事件包含零噪声，坏事件严格排除零噪声。因集合包含证据允许等号，即使边界带原子也成立。对 eps>0，恰落在 ‖y‖=eps 的噪声仍在好事件，外扩闭边界正好覆盖它。
- s=空集时 O与I均为空，测度为0，实数下界为非正；s=全集时 O与I均为全集，两个概率都为1。两端没有空集合距离下确界或全集补集造成的例外。
- s可以既非开又非闭、不规则、有曲边或裁剪边；这里只要求 hs。闭扩张无需 s闭，内缩无需 s开，边界是否零测从未使用。实际 B_Q 的可测性与几何误差需在消费者中另行建立。
- nu、eta均可有原子，且可以不同。对确定噪声 y₀，若 ‖y₀‖≤eps 则坏概率0，结论是实际平移包含给出的界；否则坏概率1，仍合法。没有依赖密度或连续分布。独立性由字面 `nu.prod eta` 固定，结论不推广为任意相关耦合。

## 首对象和全拥有传递公理证据

本轮只核对并复用保存的 exact-source 服务器证据，没有任何编译或审计重跑。GI 的 receipt、audit-record、build-history、actual-types 和 binding 一致。

- native001：失败源码 `c6bad8…df09`/2848B/56LF，RC1，4.084229091182351秒；日志SHA `6951965f5bf0e07f7a0befd7f4fb6d426db9c77078d0e41a86422d8f0b301f72`/1074B。保留失败/noobject，不将错误恢复产生的 placeholder 当证明或成功证据。三处∞未开 scope 的失败原因来自保存的修复说明和委派说明；本审查没有亲读服务器 raw log，源码差异已独立核准。
- native002：最终源码 `f31b67…7c62`/2848B/56LF，RC0，4.155222428962588秒；日志SHA `e566ecdf9c1f70a861fbfd672d193e6ed3a996b2f3c3198c8373447bfbb98a76`/498B。首原始O的SHA `a85c050bb313a0700b9dea736420d4ce084196266ab689590f18dcf818b7a5a7`/84512B。
- 同首对象全拥有AX：RC0，5.084215885028243秒；日志SHA `09a967cdf53ad76bbcd7d1d3f779759ed5051bf8924a5a56a4e467574b80a4a6`/1389B。own-firstO-binding 绑定实际 lead-oq3 对象及 accepted-source-view 链接，记录新own链接1、旧项改动0、共享缓存写0、二进制复制0。没有假称本轮重新读取了服务器O字节。
- 完整49LF Audit 先验证两个冻结目标存在且为 theorem，再用 `env.getModuleIdxFor?`/`env.header.moduleNames` 枚举实际所属本模块的所有环境常量。它拒绝新增项目公理，逐项 `Lean.collectAxioms`，拒绝白名单外传递公理；若有定义则要求 `.safe` 并打印完整 VALUE。没有仅按名字前缀或公开列表抽样。
- 实际完整20LF输出中恰为 `Shao.OQ3.independent_sum_cthickening_bounds` 与 `Shao.OQ3.independent_sum_cthickening_real_sandwich`，2owned/2theorem/2TYPE/0VALUE，两个完整rho都已核读。两个实际传递公理列表均精确为 `[propext, Classical.choice, Quot.sound]`，没有 sorryAx 或额外公理。源码独立词法检查无 sorry/admit/新增axiom/unsafe/native_decide。
- native/AX 保存的资源为 phase40、CPU36–39/44–47、native-M8192-j4。内嵌 memory 的 `ROOT_OQ56_OQ4_39` 是 phase40 明文保留的固定 helper 历史标签，helper SHA `0b3119b972b736fec56c818717462cfa8f1fea897dea94baa2120a19d2b1acda`；不代表按旧暂停状态授权。没有更改资源或重写回执。
- 委派说明保留一项 letI 风格警告；本轮未亲读 raw warning，不为风格重写成功源码。该说明不替代源码、内核或AX证据，也不影响本次数学裁决。

## 原始来源、意义与开放范围

已读只读 `C:/game/shao/current/oq3/proofs/r2/report.md` 的1–158、165–215、220–235、493–523；整文件20102B/523LF，实际SHA `572e74aa9c12e2771f5543a5709a2807666eeea0a4076e7a3263e5c7bcf87f55`。已完整读 `repair01.md`226LF/5846B，SHA `9d2e554838aa15b645aaf74a42468d423fed606aa91c1181d0dddf4e87c57cfd`；完整读 `verdict.md`58LF/3041B，SHA `fd0a5732845aa96ab1725e6d1e52676502092e49d2c00225ce1fde26ac06f3b5`。未修改原来源或历史。

report 的 A_Q=Q∩D_x，B_Q 是其经 `sqrt(n)Delta(theta_Q)^(-1/2)` 的平移线性像，边界含变换后的胞边和真实尾域曲边。GI 以任意可测 s 为对象，能够容纳这种曲边/裁剪集合，没有把 B_Q 偷换成轴平行矩形；但没有因此证明其管状邻域面积或高斯平均加权振荡估计。

已完整读 `u22gh-source-repair-clarification.json`1043B/14LF，实际SHA `fcae6fa034386b312b8d8a0e86f313cdd67bd2d081c36a0ec3c4ef95951d953c`。原 report 的 h=n^-3/log n；显式高斯修复使用 delta=n^-3、b=delta²/2、eps=delta log n=log n/n³，宽度大 log²，不能继承原式(9)的同h误差。实际曲边/裁剪 B_Q 上的新几何及加权振荡应另证到 `O(n^(-7/2)log n+n^(-6)(log n)^2)=o(n^-3)`；本GI只给集合概率夹逼，这项后续GJ义务仍开放。

repair 的 Song uniform-in-law weak-Cramér Edgeworth 输入保留为外部结果归属，不能把 report 的旧对角统一性论述或自然语言 PROVED 自动视为本工程已形式化的外部引擎。严格 `0<beta<2/5`、p54修复 `v_corr=-hat_t0*sqrt(detDelta)*sqrt(Lambda1)`、jointnonlattice不足的已接受同律反例均原样保留。实际高斯坏噪声概率的定量尾界、原cell一致误差、去平滑、原始外区、B–D及OQ3正面根仍 OPEN。本报告不认证新颖性、历史首次、最优阈值或研究根完成；这是可用于后续真实去平滑链的通用辅助接口。

## 最终裁决和释放

最终精确源码与完整冻结、两个实际TYPE/全部let、唯一合格项目依赖、所用固定库条件和首对象全拥有传递公理证据一致。两个集合包含方向与有限概率转实数均完整，未发现量词弱化、分布替换、范数偷换、假设暗改或关键证明缺口。最终为 `STATUS: CORRECT`，仅接受上述GI272局部范围。

RUN_STATE: COMPLETED_STOPPED

RELEASE: 完成本报告最终磁盘整份回读后，释放唯一报告写权，此后不再写入。sourceWrites=0；freezeWrites=0；qualificationWrites=0；statusOrCoordinationWrites=0；serverCalls=0；LeanCalls=0；axiomCalls=0；uploads=0；GitAPICalls=0；cacheWrites=0；children=0；heavy=0；inflight=0；pendingExternal=0；uncertainWrites=0。报告自文件 SHA256/B/LF/CR/BOM/UTF8 在整份回读后单独交付，避免自引用哈希。
