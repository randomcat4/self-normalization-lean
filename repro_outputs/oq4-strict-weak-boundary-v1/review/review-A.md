# A 独立完整最终审稿

STATUS: CORRECT

审稿者 context223，fresh gpt-6.1-sol / xhigh，未参与本批数学推导、冻结或实现。只写本审稿目录。完整阅读最终源码的全部231行证明、冻结的五个声明及两个透明值、实际所属22声明的全部显式展开类型，以及两个非定理常量的完整值。没有新增 Lean/parser/build/nativewalk，也没有读取或重哈希任何对象二进制。

## 精确对象和范围

- 模块：`Shao.OQ4.RademacherStrictWeakBoundary`。
- 最终 `attempt002/Source.lean`：`2e18c7e784bd1b27a9b3e41eaa2a16f736f30ff0ecb1dd45d05d525e53b4a485`，10770字节、231 LF、UTF-8无BOM且无CR。
- 冻结接口：`498ae44f2b80a8a19e515f8fc1f14ab096847cc1cce8ab28e095f13edf7dcc4b`；lead冻结：`57df706d4a8646d79786bfd641aa71c28ffcd576a15e7cc26e4418bea5308773`。独立纯文本切片比较验证五头完整类型及两定义值逐字相同，没有额外顶层声明或假设。
- Combined：`72b57ec7ff340fb4f39aa6a2dccf7d772c4c4876ffe34f9fb618a7c00126dfdc`。服务器实际编译源码逐字等于该文件，并且逐字等于 Source 加审计后缀。
- 数学推导 `strict-weak-boundary-math-v1/proof.md`：`15f676f2fbe43e24c28bbdbae6333a5929d0515389244309a32eff3e7b0c9c47`，完整阅读；原来源 `spectrum01.md`：`b65f9e0c2f9b40a28d092491b479bd20d0b8ee8a9ac940c3c4760cfff7d2670b`，完整阅读，实际本批对应§2/4。

本批只证明固定 Rademacher 律的一般尺度严格／闭边界商核心。没有证明或认证临界有理／无理分类、criticalRatio、后续原空间搬运，也没有新颖性或一般分布结论。所有原研究根组保持 OPEN。

## 从来源到陈述及完整证明

`ratio` 的分子经 S5→S4→S3→S2透明别名精确等于同一有限 Rademacher 乘积律的 `closedStrip` 实概率，闭事件监测零前缀。分母 `strictP` 精确等于同一乘积律上监测1至n的 `strictEvent` 实概率。已读这些实际值及 S5 `definition_bridges`，没有把谱主项当成概率。定义使用全定义实数除法；本批仅在共同正尾解释通常的商和log。

1. **boundary_gap，19–46行。** 整数分支从h≥0得整数z≥0，再用toNat保持相同实数，故floor=ceil=z，闭修正1、严格修正0。非整数分支由floor≤h排除相等，得到floor<h<floor+1，ceil=floor+1，差为0。二值结论精确。负h没有被暗中纳入；例如h=-1/2不满足该恒等式，显式非负域不可删。
2. **boundary_main，50–174行。** h→∞给最终h≥2，并构造m=floor h的合法cell；没有要求任意前缀满足cell。弱 `S4_EVENTUAL` 与一般严格 `strict_S4_EVENTUAL` 的全部输入正是冻结三个尺度条件。具体调用两次均使用相同 `CanonicalBrownian.B/law/isBrownianReal`，而不是两个独立可自由选择的分母。已经完整读实际消费的弱 `S4Outputs`、`TimeLegal`、`ProbabilityLegal`、`LogIdentities`、`S4_EVENTUAL` 的展开类型／值，严格S4完整展开类型、delta/correction/Q完整值，以及CanonicalBrownian Sample/law/B完整值、概率实例和IsBrownianReal完整类型。
3. **共同尾，86–119行。** 弱输出的K_time≤K_pos与TimeLegal提供n≥1，ProbabilityLegal提供实际弱概率和该同一Brownian分母正性；严格输出提供实际严格概率正性。h≥2、两概率正性、商正性及log分解均在交尾上成立。n=0、负h、零概率前缀未被错误约消；非整数事件相同也没有被错写成所有前缀商等于1。
4. **log相减，120–142行。** 从弱log误差减严格log误差，使用正尾的两次log_div和boundary_gap，Brownian项严格相消，剩余正是π²/4·(n/h³)·integerIndicator。符号和乘法结合次序吻合冻结目标。公共头无需携带Brownian前提，因为内部用了已有合格具体见证；没有假设所求比值渐近。
5. **指数与加法误差，143–174行。** exp连续及正尾exp(logR)=R给归一化商趋1。第三尺度仅最终上界M>0和J∈{0,1}即给A≤π²M/4，故exp A统一有界；精确因式分解和夹逼给加法误差趋0。没有使用n/h³存在极限，也没有使用n序列StrictMono。
6. **boundary_tendsto_iff，177–228行。** 设t=(n/h³)J、a=π²/4>0。从加法误差先得到exp(at)与R有同一极限；最终t≥0保证exp(at)≥1，故先推出L≥1，随后才在L>0处使用log连续性并除以非零π²。反向从L≥1及t的极限得到at→logL，exp连续和加法误差闭合R→L。包括L≤0的排除，没有在0处误用log。

数学推导中其他候选推论虽已读作背景，但不计入本批认证。旧依赖证明资格按现有合格记录复用，未重审整套Brownian构造或旧S4证明。旧源七项与v73成功收据源映射匹配，GeneralStrictS4另绑定已合格context217/PR266的精确源和首对象stat。

## 全部实际所属及传递公理

实际owner由原成功审计的无命名空间过滤 `environmentDifference = moduleOwnership = stage2` 确定，独立验证三者及owned行完全相同且无重名。实际22 = 5公开 + 17生成 + 0显式private；类型为20 theorem + 2 definition。不是从文字描述复制计数。

已完整读22个类型的原未省略显式文本和2个完整定义值；包括外观属于旧命名空间但本次实际生成的 `Shao.OQ4.RademacherGeneralStrictS4.delta.eq_1`。其余生成类型是floor+1非零证书、数码／乘积／幂非零的simp证书、indicator方程证书；全部逐项记录在receipt的allOwnedCoverage。没有遗漏private/生成实例或隐藏新假设。完整新证明通过生产源码阅读覆盖，巨型生成定理证明项不打印；其type/value依赖在同次成功native JSON上递归核验。

独立在服务器只读同次 `audit-native.json`，验证compact投影逐项相同；从每个实际owner分别遍历typeRefs和valueRefs，并与每个原collectAxioms结果及保存的per-root-axioms逐项一致。62398个closure节点全可达、无缺失边；728个项目依赖声明覆盖31个项目模块。所有节点无unsafe/partial，opaque有可用值，没有新增项目axiom。全部实际owner的公理只在 `propext, Classical.choice, Quot.sound` 白名单内。

## 成功内核与精确绑定

复用原作者成功kernel PID880405，退出0、reaped、未超时，19.50795133970678秒。Lean v4.36.0-rc1，固定mathlib `807d3836b165983210ee2ecf3cd28f239436949c`，-M8192/-j4，trust1025、autoImplicit=false、skipKernelTC=false。执行收据SHA256：`5403ba96ee4fd9a6d40212246bf7c940a09c48ea4eeb1ce78e64727694755b0a`。保留attempt001失败；只认证attempt002最终bytes。

首成功对象原已记录SHA256 `53e01ae91121c8e4e55f262afef4b9addd349213024591a9906467c93a1b73a7`；本审稿只stat，dev64947/inode5112450/size605688/mtime_ns1792829561372923682完全吻合。全部321 runtime-view预存stat项、108唯一路径及101实际项目导入均与原检查绑定且当前未变；包括GeneralStrictS4原首对象inode4981026和CanonicalBrownian合格对象inode3805604。mtime_ns全程Python整数，未经JavaScript数值转换。

19项compact文件的本地和服务器字节数／哈希均独立核对。原saved audit SHA256 `d225562be869fc7646801622b84d7b0d58b49c00d3b49f7223b64ea3a1bb9bcb`。详细只读结果见 `server-A-readonly-verification.json`，本地freeze/format/interface绑定见 `local-A-evidence-verification.json`。本次新Lean0、parser0、nativewalk0、旧对象内容读取／重哈希0、旧producer重跑0。

JUSTIFICATION: 冻结一般尺度命题忠实表达来源§2/4的固定Rademacher边界机制；全部证明、实际展开接口、共同合法尾及全owner传递公理均正确且精确绑定同次成功内核／首对象。A审稿至此固化；后续B仅可消费此合格A，不重写或重审A。
