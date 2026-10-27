# FG244 独立完整终审：实指数预算与原始对数立方截断

STATUS: CORRECT
JUSTIFICATION: 最终冻结四个完整声明、四条完整证明、全部九个陈述内 let 值、全部四个实际归属定理类型，与精确源版本的内核及传递公理凭据一致。未发现关键缺口或静默前提变更。建议将本报告与已封存的首次成功对象证据合并资格验收；父实例须先完整读取本报告。资格范围仅为本模块的归一化独立同分布远频逐点界。

评审上下文：`/root/oq3_fg244_final_review`，全新独立非作者；规定派遣模型 `gpt-6.1-sol`、推理强度 `xhigh`。本报告是唯一写入文件。未启动子实例，未向其他聊天发消息，未执行服务器、Lean、公理检查、上传、Git、API、计划或 Goal，也未使用 math-ultra。

已读取 math-theorem 技能及四份完整参考文件、中文输出规则、工作区当前相关约束、SERVER/TEAM 的相关执行和归属说明、REGISTRY 当前权威字段及 streamlined-acceptance-current。当前唯一 OQ3 所有者为 `01a16c48-80ee-7520-a9d9-faeeb6d05c78`，协调5为 `01a17d3c-6dfd-7cc0-94ed-35d758a423a5`；明确人类恢复文件及 REGISTRY 对它的 SHA256 `2b69e1eb2251724f2236bd8176623e7445a794dbb12a4f17a346885469fba480` 已匹配。本评审没有执行权限，不将历史暂停条款误读为本次暂停，也不推断租约本身就是运行证据。

## 完整阅读与冻结一致性

先完整读取 `u22fg-frozen-declaration.lean.txt` 的 70/70 LF，再完整读取最终源 155/155 LF、8035 字节及四条证明，完整读取实际类型 84/84 LF、4414 字节，以及 47/47 LF 审计源。另完整读取 scope、receipt、audit-record、build-history、两份失败源快照、qualified/server dependency binding、own-firstO binding、primary-api、transport recovery；不存在未读的新陈述、证明、局部数学断言或实际类型。

确定性比较确认最终源以及 attempt01、attempt02 的四个完整声明，在每个 `:= by` 之前均与冻结声明逐字一致。检查包含所有变量、类型类、概率假设、量词次序、严格下界、闭上界、积分表达式、结论及 Q/S/rho 的全部值。三版之间只有证明修复，没有数学冻结变更。最终源、冻结、实际类型、审计源与 scope 均为严格可解码 UTF-8、LF、无 BOM、无 CR。

| 核心工件 | SHA256 | 字节 / LF |
| --- | --- | --- |
| 最终 `u22fg-source.lean` | `43bcd522e1271ae8589336ab94e2a4683b9db02a52a893946cb36f18661ed72a` | 8035 / 155 |
| `u22fg-frozen-declaration.lean.txt` | `f335e2f33cfb810086b75c344daea00b95fa6bad7a27f78cebf5094c24dad53c` | 3899 / 70 |
| `u22fg-actual-types.txt` | `1d7035493fba09fa11ce5b2ca404fa5772093a68834638d4650202ce70b7653d` | 4414 / 84 |
| `u22fg-Audit.lean` | `9a6a777072924efcb86c6ce45950ece0af089f65561789a3cfa28fe458ce7392` | 2215 / 47 |
| `two-hundred-forty-fourth-unit-scope.md` | `319e4745cea3a62503a8d0ffce9466ff2641a9fc3e64ffbfc5c351acdaa90717` | 1831 / 28 |
| `u22fg-receipt.json` | `7c00084f1086cee2e3b93bedffe74d736f53b4d5bd840889f15b0ac8d3b5bb0b` | 10549 / 351 |
| `u22fg-audit-record.json` | `261698acbccba66a0149e0e056fa1498bce689aacda536c2a2dfe7cd89e6316c` | 3246 / 106 |
| `u22fg-build-history.json` | `ad8fb21713aeeaf68a11f52532244a9180371992f79b813c4be5428f93ef7e0d` | 6795 / 245 |

以下陈述哈希取从 `theorem` 到 `:= by` 之前的完整 UTF-8 文本；证明哈希取 `:= by` 后首行到证明末行的原缩进文本，去除末尾 LF 和空白行，不加终止 LF。它们补充整体源哈希，不替代整体源绑定。

| 声明简称及最终源位置 | 陈述 SHA256 | 完整证明 SHA256 | 陈述 let |
| --- | --- | --- | --- |
| real_cutoff_bound，8–52；证明28–52 | `a8d9fc7830e5b0bc6dc452157fc45bd8d3a0c33b5e1e7cc87abee008e22cbb8f` | `6c4eeec70776fb5e03b81883fc35e87f2e778824cd9b0ad962babf2fa1dad1ca` | 3 |
| uniform_real_cutoff，55–88；证明76–88 | `0322a264be601ff7e1f997fbe4e381ec48db636914ab68dc2ad92398b82e4b27` | `7c041cbc55d93d4469f254c970cb86e18ec50d036eb2aaa1083ce776fe83fc35` | 3 |
| exists_above_cubic_log，91–121；证明96–121 | `2cb65ebc7030d809419bf3f5a9abd67c2dad5c3d00ea4616e1495004a4ae09a6` | `79a476e7c302203a4880f6b024668b8e03ac30177ecdb46f3047f29de98039ee` | 0 |
| uniform_log_cubic，124–152；证明145–152 | `a7b180a4bd7dd460be034f878b96f74e36f24dd5284aed93966664fc27a0070a` | `3f7146429e52b59e0d7b41f44a94b298af0b3dc7703fba12caa72df5646704fe` | 3 |

总计四个公开定理、四个实际归属声明、四个实际定理、零定义 VALUE、零新增私有或生成声明，九个陈述 let。没有把证明局部 `eps` 或 `letI` 计作公开定义。实际类型输出次序与源次序略异，名字和集合均精确对应。

## 合格依赖及历史证据复用

完整读取 CE164 的冻结63 LF、全部三个公开接口与全部51 LF/3 TYPE，以及 CF165 的冻结40 LF、全部三个公开接口与全部66 LF/10 TYPE，包括七个生成定理。129 LF/6586字节 CE 源和73 LF/3397字节 CF 源也已完整读取，用于确认接口所在文本和来源；已有完整旧证明复核、内核与全归属公理验收按精确版本复用，没有重新进行旧证明资格审判或运行旧检查。

合格清单 `publication-u22-cc-ci/docs/oq3-u22-iid-fourier-decay/manifest.json` 的本地 SHA256 为 `b4a06e846af79e63dac603e20d487742ce43658fc2176f97b1857838450a0f97`，与当前依赖绑定一致。CE/CF 两行中的源、冻结 scope、receipt、完整独立 review 哈希逐项核对通过；本地草稿源和实际类型与发布副本相同。旧 receipt 中历史 `PENDING_FRESH_COMPLETE_REVIEW` 标签由同源清单中已经合格的独立最终 review 补齐，不能单靠旧标签推断未合格或已合格。

| 依赖工件 | CE164 SHA256 | CF165 SHA256 |
| --- | --- | --- |
| 源 | `9dcb00097adb684a0cce97eaabd3189f750745498d291c8e4709d0b66a04e870` | `acf5eb8fd8399bde118d6174b38a9b93552ecad96cf6c7a8885dfc65eefcb931` |
| 冻结 scope | `01307f5390947ed9c5ea1ae6cbee03d67387f6cb6a990f085c949282f52dd072` | `dd96704818973c23345e9c13714d2db36e77c356fe418476380692f4638e0ffc` |
| 全实际类型 | `1ee903f3ef0b741b006e49b620b4ab1b7c9ff8141dfea0d2a5d0f7abbcc7232b` | `f380107dbc75e5e2192481b358d02f647a91d3be34fe2f9ab8466c97f8fb715f` |
| receipt | `28e6883f70e18fb1295cd1ad61364bf0ea04bc905a34cf28bb25283e9fec4a3c` | `ccedab6107a6b291b50dcb87056d0a81c8cdbf21d23e803e07baf5640b79182b` |
| 独立完整 review | `d6f40e8eb7500eed72b0bca9bef3a1675321d87057b5a354907a337e7fda1395` | `b1c009a83d394b666369640d9828b7de970c6b92ad4f74eb4576cbcb6aca5938` |
| 审计源，匹配各旧 receipt.audit | `3f64ae3d6b3e27a19ba8b31e1e43e5ab9542402eab938638ad2a10bfe2de0073` | `adac876cc7f04af8863ffa9cdc38c0725344b1c0256c537718c3d07ced017a31` |

CE 首完整成功为 attempt02、原全归属审计 RC0；CF 为 attempt03、原全归属审计 RC0。两个独立 build-history 与各 receipt.build_history 深度内容相同，实际类型和审计源均匹配各凭据；没有旧机器重跑。七个 CF 生成类型全为通用零/幂等式消除引理，其公理也在白名单内，不含隐藏的归一化和误差结论。

旧 receipt 没有自身首次对象哈希字段。当前 server-dependency-binding 中 CE 现存保留对象为 `51263983ac15422499c3ba9f611d270ab13c4c0710c0099fba7a1f54ad863794`，mtime `2026-10-23T19:07:33.611302+00:00`；CF 为 `d0fc3058ce1a00385b59ea145f5a97658eb5c031c089203bf4808bcb11f5ad94`，mtime `2026-10-23T19:18:31.409482+00:00`。这些是当前保留对象观测，`exactFirstOriginalO=null`，不倒填为旧 receipt 当年封存的首次哈希。相关旧独立报告的对象观测可作为自身历史陈述保留，两种证据标签不混同。

## 四条证明的逐步审查

以下仅为说明，记 `a=(n:ℝ)`、`r=√(xi²+eta²)`、`α=1+beta/2-d*beta`，不新增源定义或前提。

`normalized_iid_pair_weak_cramer_real_cutoff_bound`，源8–52：CORRECT。`hn` 给 a>0；`hR` 与严格远频条件给 r>0，包含 R=0 的情形。由 beta≥0，幂函数在正底数上的指数 -beta 非正；r≤a^d 因而给 `(a^d)^(-beta)≤r^(-beta)`，方向正确。`hpower` 使用正底数的实幂乘法、加法法则，证明 `a^α=a^(1+beta/2)*(a^d)^(-beta)`；没有把任意实 d 强制为自然数。乘以非负 `a^(1+beta/2)` 后得到系数下界，再乘非正 -c 反向，得到 CE 真正特征积分指数不大于 `-c*a^α`。CE 的实际概率律界与 exp 单调性传递后，返回显式预算正性与真正的 `exp(-c*a^α)` 上界。hN、hpositive、hdecay、hpower、hcoefficient、hnegative 和调用 CE 的 h 均已检查。

这里所消费的 CE 接口正是实际独立样本乘积测度的归一化和特征函数界。Q 是 n 个相同 pair law 的积，S 是 `(sqrt a)^(-1) • sum_i z_i`，rho 是 Q 经 S 的推前。独立性来自这些实际独立抽样，并未额外要求同一 pair 内两坐标独立。目标积分是 rho 上的复指数积分，采用欧氏半径，不是 pair 的最大范数，也不是假定一个代理特征函数误差。概率性、所需因子化及 Fourier 核可积性由合格 CE 及其旧依赖证据提供，没有把总化积分的非可积默认值当分析证明。

`normalized_iid_pair_uniform_real_cutoff_far_frequency_decay`，源55–88：CORRECT。先用 CF 的 `eventually_real_power_mul_stretched_exponential_lt`，只以 α,c,p,epsilon 和它们的标量正性取 N，再构造 max 1 N，之后才引入 n、任意 law、概率性、hWC、xi、eta 和两个截断条件。因此 N 在所有概率律和频率之前；可以覆盖随 n 变化、但共用同一 beta/c/R/d 的任何律族。临时 IsProbabilityMeasure 实例忠实使用 hlaw。第一定理给实际积分范数界；对任意实 p，非负底数的 `a^p` 非负，故左乘保持不等式，再接 CF 的严格小于 epsilon。没有偷偷要求 p≥0，也没有以所需归一化和衰减作为前提。halpha、N/hN、hn1、hCF、hbound、letI 与量词选择点均完整检查。

`exists_weak_cramer_real_cutoff_above_cubic_log`，源91–121：CORRECT。取 `eps=(1-(5/2)*beta)/2`，严格 beta<2/5 给 eps>0，且 beta<1。故 eps*beta≤eps；令 d=3+eps，则 d>3，且 `1+beta/2-d*beta=2*eps-eps*beta≥eps>0`。源内 linarith/nlinarith 所编码的正性与此一致，并未加入额外前提。合格主库接口 `isLittleO_log_rpow_atTop heps` 位于全局命名空间，给 `log x=o(x^eps)`；其 `tendsto_div_nhds_zero` 以及自然数嵌入复合给 `log a/a^eps→0`。取最终商<1的 N，再取 max 1 N，a>0 保证分母 `a^eps>0`，可以推出 `log a≤a^eps`。乘非负 a³，使用 `Real.rpow_natCast` 的反向等式，经 congrArg 乘相同 a^eps，再经 `Real.rpow_add` 的反向等式，得到真实 `a³ log a≤a^(3+eps)`。eps、heps、hsmall、hbudget、htR、ht、N/hN、hn1/hnR、hlog 及末尾完整等式链均有依据。

该证明没有删去 log，也没有以纯 a³ 截断冒充原始截断。`primary-api.txt` 是绑定到 mathlib `807d3836b165983210ee2ecf3cd28f239436949c` 的主库摘录，所列原源 SHA256 `f736afe5ee0e392168895c13ce258c142fdc5d3b45ecb5d3dd12af9299a8ee42` 为该绑定记录所载；本轮未访问服务器重算底层 mathlib 文件哈希。摘录中实际小 o 接口、正指数条件及商极限方法足以核对本次调用，最终精确源成功凭据也覆盖该解析结果。

`normalized_iid_pair_uniform_log_cubic_far_frequency_decay`，源124–152：CORRECT。先由第三定理取得同一 beta 的 d、正预算和截断阈值 N0，再由第二定理取得标量衰减阈值 N1。取 max N0 N1 后才引入任意 law 与频率。n 达到两个阈值，真实上界 `r≤a³ log a` 与第三定理的 `a³ log a≤a^d` 传递成第二定理需要的闭上界；严格远频下界原样传递。Q、S、rho 和 Fourier 相位保持完全相同，并无换律、换样本或缩放常数。hd 虽非最后调用必需，已在第三定理证明，非额外假定。全部 N0/hN0/hcut、N1/hN1/hFn、max 选择及传递调用已审查。

依赖方向为 CE 真正乘积律界 → FG第一条 → FG第二条（另用 CF 标量渐近）；主库 log 小 o → FG第三条；第二及第三条 → FG第四条。没有从第四条、原 OQ3 根结论或假定的 CF error 反向证明自己的循环。

## 边界、全部实际类型与安全门

- n=0 被第一条 hn≥1 或其余阈值 N≥1 排除，所有用于实幂等式和除法的底数在使用时已正。n=1 时 log1=0，第四条严格远频 r>sqrt1*R≥0 与 r≤0 不相容，因而该频率域为空；没有漏掉退化情况。第三条 n=1 时若进入阈值结论，0≤1正确。
- beta=0 是辅助定理允许的边界：α=1，第一/第二条不依赖 d 的正负；第三条取 eps=1/2、d=7/2，预算=1。原充分修复仍保留严格0<beta<2/5，辅助结果在0成立不更改原根假设。beta=2/5 未被第三/第四条涵盖，也未声称端点或最优性。
- 第一/第二条允许任意实 d，包括负 d，只要显式预算为正；a>0 保证 a^d>0，不需要暗中增加 d≥0。可能出现空远频域不影响条件命题。p 为任意实数，xi/eta 为任意实频率，坐标轴与零频均按显式不等式处理。
- beta≥0、c>0、R≥0、epsilon>0 保持字面前提。strict lower / closed upper 未改变。所有概率律与 hWC 常数按原量词共用，没有偷偷要求密度、无原子、矩、零均值、单位协方差或 law 的特殊构造。
- 全84 LF实际类型逐项匹配完整冻结声明；第一条实际类型16–18、第二条44–46、第四条71–73保留三组完整 Q/S/rho let，共九个，第三条零个。第一个结论还保留显式 α>0 的合取，不是只输出该已有假设而丢弃积分界。
- `u22fg-Audit.lean` 按环境实际 module owner 枚举全部归属，核对四个冻结 theorem、拒绝新增 axiom，并对每个实际名字 collectAxioms。输出为4 DECL /4 TYPE /4 KIND theorem /0 VALUE；每个传递公理集合均为 `[propext, Classical.choice, Quot.sound]`，没有漏查私有或生成归属。
- 最终源禁止词静态扫描命中0：sorry、admit、axiom、unsafe、native_decide、implemented_by；没有削弱证明设置。普通有限命题的 `by decide : 0<1` 不等于 native_decide。审计的 pp 选项只影响完整打印，不改变内核可信边界。

## 机器凭据、失败分母与传输恢复

项目本地钉死工具链文件为 `leanprover/lean4:v4.36.0-rc1`；依赖绑定及当前规则为 mathlib `807d3836b165983210ee2ecf3cd28f239436949c`、shared-v34。当前 receipt 绑定最终源/冻结/scope/实际类型/审计源的哈希逐项本地验证通过，独立 build-history 与 receipt 内历史内容一致。复用记录的服务器 CPU36–39,44–47、c12-heavy.lock、`-M8192 -j4`、phase40，不采用旧14–17记录作为当前资源授权。

| 原生尝试 | 完整源 SHA256 | 字节 / LF | 原始退出及时间 |
| --- | --- | --- | --- |
| 001 | `ff27fe74fdc08e9756a2032f9001759c749f39b455d07ab6f26426c7ae80c9d6` | 7928 / 153 | RC1，5.45066386833787s |
| 002 | `a4d577d1ceba948c50df563755a2ccd74669fd646507a1121e4d9fe1e3aafc1a` | 7958 / 154 | RC1，5.333109198138118s |
| 003，首次成功 | `43bcd522e1271ae8589336ab94e2a4683b9db02a52a893946cb36f18661ed72a` | 8035 / 155 | RC0，5.322255589067936s |

两份失败源完整保留且其四个声明不变。交接记录的001失败是错误 `Real.isLittleO_log_rpow_atTop` 命名空间和实幂重写；002仅剩在已定义相等目标上额外重写 `Real.rpow_natCast`。最终版本使用全局接口与显式 congrArg/trans 等式链修复证明。没有成功源重放，也不把旧失败改成通过。

首次原对象 SHA256 `db7cd62dab71c634a94159e51e06c2b23f6ec67921f44e0b55be5a9b13332a8d`，306376字节。对同一个原对象的全实际归属审计 RC0、5.812112417072058s，四个实际类型和全部传递公理已核对。own-firstO binding 将该对象链接到 accepted-source-view，记录 new_own_firstO_links=1、old_entry_changes=0、shared_cache_writes=0、binary_copies=0。对象哈希是当前FG自己的首次成功凭据，区别于上述CE/CF旧对象历史空字段。

原003原生日志封存 SHA256 `d898f6dc4fb1b2d9cdd706e26dab03204d1639bdec5be45d310361a704f65517` /858字节；原全归属审计日志 SHA256 `ce1a578397e8b42d28522fa420e0034381685aa9891845935fe4e5ce9277cc40` /4666字节。001/002失败日志分别为 `ec654f10afe23df2d836ad280ad11865f115bf27a7b0cad8e316a9bdd44d7f74` /1429字节、`e146c34ce08c591b95c98460038b8f4c89d69692c0da7179009e23db84d252db` /1280字节。交接说明记录的两条非致命提示保留。本轮完整读取的是这些精确凭据、历史和类型文本，没有重新取服务器原日志/对象；上述二进制和日志哈希是所复用原检查凭据的值，未声称在本机重算这些不存在的载荷。

传输恢复文件完整记载 put session76514 已 completed/transferred1；exec18915 在操作开始前失败，`execOperationMayHaveStarted=false`、`remoteMayStillBeRunning=false`。随后已观察精确最终源 SHA、仅两条旧原生历史、无对象、锁FREE、noUncertainWrite=true，再开始真正 native003。这次传输中断不计作第四条Lean尝试、证明失败或内核通过，不能按不明在飞请求重放。

## 原始来源、范围及资格结论

只读完整规定来源：`C:/game/shao/current/oq3/proofs/r2/report.md` 的1–158及493–523行；`repair01.md` 全226 LF；`verdict.md` 全58 LF。相应本地 SHA256 为 report `572e74aa9c12e2771f5543a5709a2807666eeea0a4076e7a3263e5c7bcf87f55`，repair `9d2e554838aa15b645aaf74a42468d423fed606aa91c1181d0dddf4e87c57cfd`，verdict `fd0a5732845aa96ab1725e6d1e52676502092e49d2c00225ce1fde26ac06f3b5`。未写入原来源或历史目录。

原报告139–156和518–519的真正截断是 n³log n，原CE/CF及旧DF的 n³ 界必须区别记录。本次FG正确提供真实对数截断的归一化IID远频逐点衰减桥；它是用一个严格大于3且仍有正预算的实指数覆盖 log 损失，未声称直接得到原报告式(5)完全相同的最强指数。它足以推出该截断下任意固定实多项式权的统一逐点小量。

严格0<beta<2/5仍是原充分修复的范围；联合非格点反例保留，p54修复与 v_corr 约定不变。外部均匀律结论按repair/verdict的修正归于 Song 的 uniform-in-law weak-Cramér Edgeworth 输入，不将原report的旧对角归属叙述重新认证为最终归属。本模块没有重新证明 Song 全部外部定理，也不作新颖性、优先性或历史首次认证。

本报告范围内，规范倾斜样本的同E/同law/同rho实际输运、加权远区与中区积分、六阶全窗口、Fourier反演/Hermite、平滑/振荡、外部远区/B–D/原根仍OPEN。FH新消费者在别处的机器通过不扩展本报告的资格结论。正确的有限或辅助界不等于原OQ3充分修复根已形式化完成。

资格建议：`QUALIFY_FG244_EXACT_SOURCE_WITH_REUSED_FIRST_NATIVE_AND_ALL_OWNED_AXIOMS`。本报告提供所需全新独立完整源到陈述/证明/全实际类型审查；父实例应完整读取全文并绑定本报告最终哈希，复用既有精确原对象/内核/AX，而不为本次上下文变化重跑已经成功的检查。当前FG receipt保留的待新鲜审查标签属于其写入时状态，不在本评审中修改。

## 补充工件字节绑定与角色释放

| 完整读取工件 | 本地 SHA256 |
| --- | --- |
| `u22fg-qualified-dependency-binding.json` | `817b1495003b9cf840c5427bb2b681425663d2e5f41f4054076cf792c57f4015` |
| `u22fg-server-dependency-binding.json` | `f6914712e8a0c18a4b2da92eefc909bd02ee0c6d4c6a26cc3a4b8b4583a6a707` |
| `u22fg-own-firstO-view-binding.json` | `a9b9c8fe5c4ee2f0ddba05c2a52a3311d91d6fda01dbb4fdd75abb2d45a2beb4` |
| `u22fg-primary-api.txt` | `8ab883625d9da5d9b0fad80ad0f138978993a53ef6d96ee04452c26498f887f1` |
| `u22fg-transport-before-attempt03-recovery.json` | `698a5c5013d186b05952975a608b752dadd28a056ba0a05038dabeef9b043cec` |
| `u22fg-header-parts.json` | `26e55c766afab390156b8f0d817cf85e419ba805f4e22aa8afc9d379f60dbf6c` |

所有上列本地可得源/冻结/类型/receipt/旧review/原来源report哈希均实际重算；本报告仅修改自己的唯一允许路径。规定配置 `gpt-6.1-sol/xhigh`；独立实际模型/强度计费证明未暴露，actual_model_attestation=null，actual_effort_attestation=null。input_tokens=null，cached_input_tokens=null，output_tokens=null，reasoning_subset_tokens=null；没有杜撰token或订阅百分比分摊。

COMPLETED_STOPPED
sole_review_authority_released=true
writer=0; child=0; heavy=0; inflight=0; pending=0; uncertain=0
父实例完整读取本报告是下一资格交接动作；本上下文不继续写任何其他文件，不保留服务器、执行、出版或分线所有权。
