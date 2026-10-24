# B 原空间字面临界边界商及算术分类：独立完整终审

STATUS: CORRECT

审稿者 context225，gpt-6.1-sol / xhigh，独立于B作者lead；未参与B数学推导、冻结或实现。A已独立完整合格并固化，报告 `6a60e205f28db98511b3eaac1e9ec7129bd551395eea9f122333fb5bebbea1dd`、收据 `211002bb7219bf3a401e842fa9a527f34c0ad9a1db373f6921c19dcffd4184ad` 保持原字节。本次只审B增量、实际接口消费及来源绑定，不重审A或其他旧证明。

## 精确版本与范围

模块 `Shao.OQ4.RademacherOriginalStrictWeakCriticalArithmetic`；最终 `attempt002/Source.lean` 为 `770bfea8edee48773cd2a86c35ff71ca1df543b112752412fdbabdfdba9c0424`，7511字节、158 LF、UTF-8无BOM且无CR。全部158行生产源码及所有新证明已完整阅读。

冻结接口 `dafea24c4a616259e70a0f753431d4e959c55c1550cc96992fd65b981d3366e4`，lead冻结 `1c9076e4621282fc4331a502dcc89ca87e102ee4af9378b41c39d4cd42a26072`。独立纯文本切片验证五个完整头与sourceRatio定义值逐字一致，1定义、4定理、无额外顶层头或前提。Combined `1485eef515ecf5d9ea0f955dc6f66f992127c2c8630d1177c7188634e279aac1` 精确等于Source加17129字节审计后缀；服务器实际编译文件与之逐字相同。

本批将A的固定Rademacher严格／闭临界概率商，搬运到任意原样本空间上、字面阈值 `c·(n:ℝ)^(-1/6)` 的两实际自标准化事件。保留 `IsProbabilityMeasure μ`、正编号变量的 `iIndepFun` 与对Rademacher律的 `IdentDistrib`，不添加逐点±1、逐点可测性、矩条件或Brownian假设。ΩX具有任意宇宙uX，没有共同样本空间或耦合约束。

来源仍是已在A完整阅读并绑定的 `spectrum01.md` §3/4及数学稿§8；有理／无理c³分类明确是来源上的新增推论，不是原文逐字结论，不声称新颖性、一般增量律或一般OQ4关闭。所有原研究根组保持OPEN。

## 完整来源到陈述及证明

1. **sourceRatio，12–16行。** 完整透明值为μ对 `OriginalIIDWindow.sourceEvent` 与 `RademacherOriginalStrictBoundary.sourceStrictEvent` 的实际实概率之商，两侧使用相同S5.x。已读x的完整值，确为c乘n的负六分之一次实幂；没有把阈值改到相邻格点。弱事件由实际最大绝对前缀和与x乘平方根能量比较，严格事件监测1至n的实际绝对前缀和。原sourcePath使用X(i+1)，与独立／同分布假设的编号一致。使用全定义实数除法，定义本身没有分母正性假设。
2. **source_probabilities，18–66行，零时间。** n=0时sourceMaximum为0，sourceEnergy为空和0，所以弱事件逐点为univ，μ.real=1，不依赖x(c,0)的特殊值。旧 `source_strict_pullback` 的完整第二结论给原严格零时间事件univ，故概率也是1。S5.zero_time对任意c给p(0,S5.height c 0)=1；S5.height/root与CP对应别名精确转换得到所需p。StrictCube.zero_time对所有实h给strictP(0,h)=1。两项概率等式因此明确覆盖n=0，没有在零时间使用x=h/√n、约消n或把负h的闭事件误当univ。
3. **source_probabilities，正时间。** n≠0给n≥1，S5.positive_time的完整PositiveTime值包含x(c,n)=S5.height(c,n)/√(S5.N n)。该命题所需条件只有c>0和n≥1。S5.height透明地等于CP.height；N经S5→S4→S3→S2透明别名等于(n:ℝ)，因此 `exact hx0` 是真正的定义相等转换。已读该N别名链；attempt001的局部simp未展开嵌套S4.N是实现失败，最终改用定义相等未改变命题或数学条件。用root_spec的非负性和c>0得到高度≥0，精确满足已合格 `OriginalStrictWeakBoundary.source_probabilities` 的全部前提，后者在任意uX、同一AE-iid/IdentDistrib假设下输出两实际概率。没有添加或从概率推送推出逐点假设。
4. **sourceRatio_eq，68–78行。** 把上述对全部n的两概率等式代入实数除法，精确等于A.criticalRatio。这里不要求分母正性，覆盖两概率同时为零的有限前缀。旧OriginalStrictWeakBoundary的精确源码 `05bfce60b2236c421b3acd538d49bc62dd1418457af101b6ba71494ffabd4135` 已由独立223收据 `80188b76b3f5706817b200a7155620561a35c2c543ba8dbf0da60459b53d15d8` 及lead接受 `adf1d393a8bdd01a35a0e68bb84322d62dd94dd294a8c5d590de66561741c028` 合格，本次仅消费其完整类型和既有证明资格。
5. **original_main，80–118行。** 从全n商等式经funext得到两个商函数相同。A.critical_main的共同正尾通过两概率等式搬运，得到实际原弱概率、原严格概率及原商正性；三个临界log／归一化商／加法误差极限通过同一个函数等式精确搬运。没有对0/0前缀使用常规除法解释，也没有重新引入Brownian分母、加强第三尺度或改变q、J。
6. **original_arithmetic，120–155行。** 有理分支用同一个全函数等式完整搬运A的两点Cluster及不存在整列实极限；Cluster是已合格真实StrictMono子列定义。无理分支保留每个n≥1的两原概率精确相等，使用A中已证明的有限概率等式并代入source_probabilities；没有将低阈值的两零概率误写成商1。商最终1、整列趋1、Cluster单点也全部由全函数等式搬运。原冻结的两个蕴含及所有量词完整保留。

## 实际所属、完整类型／值及旧接口

独立在同次成功saved native JSON核定 `environmentDifference = moduleOwnership = stage2 = owned.names`，无重名、不按命名空间过滤。实际6 = 5公开 + 1生成 + 0显式private；种类1 definition + 5 theorem。生成头 `Shao.OQ4.RademacherS5Assembly.root.eq_1` 虽显示旧命名空间，实际module owner是本B，已纳入完整类型审阅和逐owner公理审计；其类型准确为S5.root n=CP.root n。

完整阅读所有6个实际owner的原始未省略显式展开类型和sourceRatio完整值；所有binder、宇宙、实例、函数与命题上下文均覆盖，无摘要替代。全部新证明按生产源码完整阅读；生成定理proof-term绑定同次nativeJSON及type/value闭包。

实际消费的41个项目接口全部覆盖：22项本次完整阅读，19项类型和非定理值与本context审A时已完整阅读的原始文本逐字相同，确定性比较后复用阅读，不声称重复逐字阅读。完整明细见 `B-direct-interface-full-coverage.json`。尤其完整读实际source_probabilities前提、S5.PositiveTime的全部4793字符值、S5.zero_time完整类型、严格零时间／pullback接口、字面x与原事件／能量／路径值。10个直接项目模块中7个旧库源码与v74成功源映射匹配，其余3个为已合格A、OriginalStrictWeakBoundary及其核心StrictWeakBoundary；全部资格与对象记录绑定，旧proof不重审。

独立只读同次savedJSON，从每个实际owner分别递归遍历typeRefs及valueRefs，逐项匹配原collectAxioms与per-root-axioms。62600个闭包节点全部可达、无缺边；909个项目依赖声明覆盖41个项目模块。所有节点无unsafe/partial，opaque值可用，无新增项目axiom；每个owner传递公理只在 `propext, Classical.choice, Quot.sound` 白名单内。

## 首成功内核、原对象与输出目录来源

复用attempt002首成功kernel PID891846，退出0、reaped、未超时，18.995830776169896秒。固定Lean v4.36.0-rc1、mathlib `807d3836b165983210ee2ecf3cd28f239436949c`，-M8192/-j4、trust1025、autoImplicit=false、skipKernelTC=false。执行收据 `93c05d7cafd2a7950caf7d2f6822e9778ef45f3f49cbe4e9169f0f19577600c1` 与实际argv、child/worker记录和Source/Combined哈希一致。首成功stdout仅有本B的PASS行，数字与独立导出库存一致，stderr空。

首成功对象原已记录SHA256 `f5ff73cbaaa91103885cbae4958feda2d6ada55720672e547e07aa53a8a789a5`；本审稿只stat，dev64947/inode5125730/size180872/mtime_ns1792832835243862689精确相同。113个runtime-view对象与106实际项目导入均匹配编译前保存stat；直接依赖A首对象inode5125382及旧OriginalStrictWeakBoundary首对象inode5124820也只stat绑定。全部mtime_ns使用Python整数，未经JavaScript Number。

本次审计后缀在attempt001与attempt002逐字相同，其字面outputDir确实仍指向本单元attempt001。审稿独立验证以下来源链，未重跑gate或修改成功字节：

- 最终实际编译源码等于attempt002 Combined，后缀内的目标module/public清单是B，字面写出目录是attempt001。
- provenance列出的audit-native.json、raw-expressions.json及owned-interface.txt，三项origin、attempt002投影副本和登记SHA256均逐字一致；原nativeJSON为 `6d32ea3ea19f63edc068da876b112888eb97e0b42a26eb22d42fb8321e25f32b`，实际module、owner、类型／值及递归图均与本B相符。
- 原attempt001失败日志为局部hx0类型不匹配，并在审计落盘语句之前因sorryAx拒绝；该次rc1/reaped、没有成功对象，也没有PASS行。保留失败源码／Combined／日志及简账，不将其视为认证。
- 实际文件时间关系为：先次失败stdout `1792832337833239357`；最终compiled source `1792832816111915641`；成功child-start `1792832816643914168`；origin audit `1792832834979863420`；origin raw／interface `1792832834983863409`；首对象 `1792832835243862689`；成功process receipt `1792832835639861593`。三项原审计输出均在第二次实际运行区间内、先于首对象，不是用旧失败结果冒充本次成功。

20项compact文件本地／服务器字节与哈希均独立核验，manifest `7a43a524db5f710f5e04517ad3ca88236832481fab33052314f947c334b56bad`；compact投影逐项等于上述同次原nativeJSON。详见 `server-B-readonly-verification.json`、`local-B-evidence-verification.json` 及本目录B旧依赖资格记录。原compiled源码、Combined、首对象未改，审计未重跑。

JUSTIFICATION: 字面临界阈值下原AE-iid空间两实际自标准化概率的全n等式、共同正尾及三极限、完整有理／无理算术分类均正确；零前缀和低阈值0/0处理完整。全部实际类型／值、每owner传递公理及这次特殊输出目录的来源链精确绑定首成功内核／原对象，无关键缺口。本次新Lean/parser/build/nativewalk均0，旧二进制读取／哈希0、旧producer重跑0；所有原根OPEN。
