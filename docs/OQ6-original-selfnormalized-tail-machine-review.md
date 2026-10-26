# Unit202 精确源码、首原始对象与全实际所有权最终独立审阅

STATUS: CORRECT

QUALIFIED: true

范围：仅 `Shao.OQ6.OriginalSelfNormalizedTail.original_selfnormalized_tail` 的原样本严格上尾4exp组件。

本报告把同一独立上下文已完成的完整 SOURCE_CORRECT 与新提供的实际机器证据组合。源码仍为 SHA256 `cfa791fd240ee560b2a876ea69a64e46c7c84735c935e1380446025e69a9e61a`，3989B、79LF；首次成功生成的原始 O 为 SHA256 `1bbfe0d3c074f66d956598045e392b776bccf127508122d58e553d507d7eda84`，188680B、mtime_ns `1792995157698608053`。未发现源码、冻结类型、数学证明、实际声明或递归公理之间的缺口。

实际模块所有权清单独立导出为1个常量：1 theorem、0 non-theorem、0 generated descendants、0 foreign actual owner。所有实际TYPE共90行，全部完整读取并与冻结声明逐项核对；没有应读取而缺失的非定理FULLVALUE。递归公理精确为propext、Classical.choice、Quot.sound。

## 精确 SOURCE 复用与作者分离

本审阅仍是此前独立完整审阅 unit202 的同一上下文；没有接手作者身份或修改证明。只在新的 `machine-source01-01/` 子目录写入工件。此前顶层 SOURCE报告、覆盖、绑定验证、manifest、DONE/CHECKPOINT/RELEASE0和RUNTIME-ACK等文件均逐一重新散列，保持原封存字节。父级 SOURCE intake hash `b84d3154daf2d3c7f7e4e960cb08b3ecdfb7391435858b04e57e8c060520cd60` 与旧报告、覆盖及冻结绑定一致。

原独立SOURCE报告完整覆盖了p51到声明忠实性、完整687B头、6别名、1局部概率实例、14局部命题、8组source-visible闭包、13组继承/结构闭包和17组匿名命题组合，消费14个actual TYPE与9个definition FULLVALUE。其证明关键连接已完成：201的逐点向量比较经188/199/198实际定义得到A×B包含于F⁻¹D；任意集合矩形质量、有限测度单调性和保测映射给ab≤2e；a≥0及b≥1/2给a≤4e。没有新增数学条件、能量除法或概率除法。

本次仅核对旧SOURCE资格仍绑定同一源码，并补齐新机器证据。没有重复旧producer完整证明审阅、旧kernel或leaf AX。既存Pi头文件的末尾规范LF封装说明及第一次本地校验失败记录继续封存；本次实际编译已接受同一源码，没有由此引入数学变化。

## 首次成功内核与同首对象审计

完整阅读了两次当前receipt/config语义投影，并确认它与保存的成功读取传输结果在JSON语义上完全相同。原始大型receipt/config和原始日志留在服务器，未下载到协作工作区。以下是实际命令结果的证据审阅，我没有另行运行检查。

| 证据 | 首次 author-kernel-01 | owned-object-audit-01 |
|---|---|---|
|实际 Lean退出码|0|0|
|实际耗时|5.87911101616919秒|5.196090472862124秒|
|receipt SHA256|71a15461d544ab2a84507f621a02128548cf7663a74b129c6b43bc8c7115216a|f4c3ddb35121ff94e0b03ad8e5a48970d222e20c1d6a451e7603b987bc6d6872|
|config SHA256|e6a39d92ff43ca149fe9c648725150ca6d0ad70c7835b02856fdd5f7b5f19170|69091b673cd0d8a4c6f87f3d2d58c0d8f9ace514ee8dae9d9b89d6c69ca2000a|
|当前receipt保护记录数|12847|12859|
|strict-wrapper success|false，原样保留|false，原样保留|

两次实际检查均自然结束，timedOut=false、cleanupEvents为空、ownershipIssue和postError均为null、所有受管检查进程结束。config记录与receipt before一致，before/after完全一致；源码和首原始O的hash、大小、mtime均在各绑定中保持相同。native准备和实际资源起点的objectBefore均为null，证明该记录是此精确源首次生成的对象；audit输入随后只import这个原始对象，命令没有`-o`，未重编写源对象。

两次实际命令均在CPU52–55、原lane资源阶段C12_OQ56_35下，以-M8192、-j4执行。config投影保留80GiB项目预算、180GiB聚合watchdog、200GiB硬限制与外部0–23保护。mathlib为钉死 `807d3836b165983210ee2ecf3cd28f239436949c`；精确SOURCE/primary资格所用Lean为 `leanprover/lean4:v4.36.0-rc1`。同一分支/HEAD保留在两个receipt投影中，没有源/依赖/Git身份切换。最终投影记录本lane ownLean为空和旧producer/leaf检查0次；这是保存的实际观察时点，不把ACTIVE租约或本地审阅状态当作实时服务器活动。

## 警告、包装返回和释放的真实含义

首native实际stdout完整361B，SHA256 `99e3a92d4ac472f52cd5a2248e513141d8cad22d159970183d233e9408fd650f`。唯一源码警告位于35:2，建议Prop目标使用`let`代替`letI`，属于证明无关性相关的样式建议。原代码保持不动，没有为清理警告重编译。

两次stderr都是既存mathlib本地修改提示，134B、SHA256 `11ec49f9906e54894a8ffa4551c841fd9873cf63f295722c88755032b40c3cbf`，全文已读并重新核对字节散列。native源错误为0。两次strict-wrapper success仍为false，外层传输/包装结果exit_code=1、success=false也保留；它们与实际Lean退出码0是不同字段。本结论依据完整的自然RC0、无错误、原对象及全类型/公理证据，不把外层包装结果改写成true。

`FIRSTEMPTY=false`同样保留。`native01-manual-AUTHORSTOP.json`不是中断运行的证明：其actualLeanExit=0、allNativeOwnedEnded=true，并明确锁定原源/首O、禁止警告清理重编译。它记录自然结束后的源码停止与原对象保存边界。其hash `7bd10dfea94ab055ec67161fad9d38f31a0f2732e255e0a2eafb1cae913154f6` 与服务器绑定一致。

## 所有权发现和完整输出可核对性

已完整读实际2745B、62LF audit输入，SHA256 `6e135404f2c743bd937d4b9482b15532595be2957b388c47526218fe4294ade1`，与实际audit config完全一致。输入通过anchor的 `env.getModuleIdxFor?` 找到模块，然后遍历ALL `env.constants.toList`，以实际模块索引相等筛选；没有namespace/name前缀过滤。对每个实际owner输出完整分段名字、constantKind、bodyExpressionPresent、levelParams和完整TYPE；defn/opaque另输出FULLVALUE，并对每个owner调用递归 `Lean.collectAxioms`，遇白名单外公理直接throwError。

实际raw JSON只有一个owner。我独立解析其name/components、kind、universe、body存在性及公理，而非接受summary的描述计数；再把所有raw JSON、完整TYPE、需要时的VALUE和最终COUNT逐字重建为stdout。重建结果精确为6744B，SHA256 `bf932784f2e1c5f281428fdb4f96da9d11518cc876752c12df5852a3495cc25d`，同时匹配metadata、receipt summary和server binding，且不含省略号或遗漏输出。COUNT行精确为1，和实际entries数量相同。

因此1 owner并不是只看公开theorem名而人为限定的清单。没有遗漏private/generated/foreign常量；这三类在本实际模块的数量为0，而不是未检查。0个non-theorem意味着本次没有待补读的FULLVALUE；6个源码局部别名、局部实例、点态lambda及算术证明没有额外形成模块所有者，已有完整SOURCE覆盖仍适用。

## 实际90行TYPE与冻结声明的逐项语义比对

实际唯一名字是 `Shao.OQ6.OriginalSelfNormalizedTail.original_selfnormalized_tail`，components依次为Shao/OQ6/OriginalSelfNormalizedTail/original_selfnormalized_tail，均是str段，无隐藏数字段。constantKind为thmInfo，isTheorem=true，bodyExpressionPresent=true，唯一levelParam为u_1。这与源中的一个theorem、任意宇宙Ω:Type*一致，不是axiomInfo或无body占位。

实际完整TYPE hash为 `3d7d9a3e5f03be6db28f7b6e8d34182b156cf67a0e852b3566a1c2b21d711169`。完整类型载于OWNED-COVERAGE；独立逐项解释如下：

| 实际TYPE部分 | 对应冻结含义与核对结果 |
|---|---|
|`∀ (n : Nat) {Ω : Type u_1}`|所有自然数n，任意宇宙Ω；没有n>0、n≥4、非空样本或标准Borel条件。|
|`[mΩ : MeasurableSpace Ω] (μ : Measure Ω) [hμ : IsProbabilityMeasure μ]`|可测空间和原概率法则精确保留，实例与μ绑定相同。|
|`(g : Ω → Real) (hg : Measurable g)`|函数域、值域和可测性精确，未改为只a.e.条件或更强连续性。|
|`hg2 : MemLp ... g (2 : ENNReal) μ`及完整Real norm实例展开|正是声明的L²；长类型中的norm/topology实例只是标准Real结构展开，没有L⁴或额外可积假设。|
|`hgmean` integral g=0|原μ下的完整Bochner积分，o为积分内绑定变量，等号方向和值精确。|
|`hgsecond` integral `(g o)^(2:Nat)`=1|平方二阶矩条件精确，没有归一化别的随机变量或改变幂类型。|
|`(t : Real) (ht : 1≤t)`|完整阈值前提精确，未只证明某个固定t或缩小端点。|
|目标sampleLaw实质量及pi measurable-space展开|原样本法则与Fin n→Ω事件域精确，没有替换为配对法则、条件法则或另一种测度。|
|Set.ofPred实际事件|严格`t*(sqrt(sampleEnergy)+4*sqrt((n:Real))) < abs(sampleSum)`；乘法括号、4、sqrt/cast和严格性均吻合。|
|上界|实数4乘exp，指数为负的`t^(2:Nat)`除以实数2；无阈值或常数改动。|

全部隐式/显式plication、作用域和宇宙都与冻结头匹配。实际展开的OfNat/Real norm证明字段没有新增数学数据。源码所用M/P/A/B/D/F、唯一hMProbability、hAB中的p/hp/i局部范围、14局部Prop及所有闭包和匿名组合，均由同一精确源的已接受完整SOURCE报告覆盖；本次native0确认这些exact应用和推理已被接受。没有源到TYPE的弱化，也没有额外未冻结假设。

## 递归公理和最终范围

唯一实际常量的递归AX完整列表为propext、Classical.choice、Quot.sound，各出现于1个actual owner。audit对所有实际owners执行了收集和白名单拒绝，完整输出和COUNT也已核对；没有sorryAx、新axiom或其他白名单外依赖。实际theorem有body，SOURCE禁止项扫描为0。本单元已满足精确源码的完整独立源到陈述/证明审阅、实际首kernel和同首对象全owned TYPE/递归AX要求，故最终判为CORRECT、QUALIFIED。

资格仍只限原样本严格上尾4exp组件。W/V特化、t=√y n^(1/4)代入、低能量付款、G_y并事件、完整S11以及C2/C12/OQ56根目标保持OPEN。原C1 immutablev85 complete、OQ3 PAUSED_BY_USER；p51对SZ2016(92)/JSW2003Lemma6.4的归因、p54修复和124非前置均保留。未新增JSW全文核对或新颖性主张。

本机器阶段本地确定性证据检查87项全部PASS，无失败检查。SOURCE历史失败账原封存保留。服务器/Lean/AX/上传/Git/API/network/children调用0，source和所有旧工件写入0。配置gpt-6.1-sol/xhigh；实际model/effort和input/cachedInput/output/reasoningSubset四类用量均不可独立观测，保持null。
