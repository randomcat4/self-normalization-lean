# 单元186 repair-01：记号前缀与证据映射续审

本轮结论为 `CORRECT_PREFIX_ONLY_REPAIR_SOURCE_REVIEW`。这是同一独立上下文对实际受影响范围的续审，结合旧完整数学/证明审阅使用；`qualified=false`，新源码的原生内核及全实际所属声明证据仍待到达，实际owner数量未知。未重审未变186证明，未重审或重跑已合格185。

新源码SHA256为 `07520a5e75c82565c542a3596f87755153234aece93f86f1a5517cedb13249ce`，5524字节、101 LF、无CR/BOM、单个终结LF；旧源码SHA256为 `920a18830fe17b36684a3c4f27787db74b85800edf968b0556675102ae370515`，5516字节。父级前缀修订SHA256为 `4a426be47a24c6ddd5a02b018f1109f68aed76b551316309b6c44cd3f8ca62ea`。全部作者源、旧审阅报告、旧映射纠正项和失败证据均按原字节保留。

## 首轮原生失败及先前审阅遗漏

native01确为已知失败：实际RC1，用时4.856679240241647秒，无对象、无超时、所属进程组全部结束，源与5318条保护记录保持相同。receipt SHA256为 `d785cf5665f23083c11b114255f07b6ad246221ba0138a51d829943fb2108835`。这不是未知在途请求，也不是部分通过。

已完整读取受影响诊断。首项为第13行105列 `expected token`；旧源该行零起始Unicode码点105恰为 `ℝ≥0∞` 最后的 `∞`，第21行138列的位置也与该行 `by` 的零起始位置一致。794字节的完整诊断文本可独立重构native01 stdout，SHA256与摘要中的 `af697fea7f9cd07f4174de7f073180d756f43f8607e143885fc7eb12fd491d15` 一致。

旧完整源码审阅对全局前缀的覆盖漏掉了本模块必须开启ENNReal记号的义务。native01定位了这一实际解析环境缺口；本续审明确纠正该遗漏，不改写旧报告，也不以旧source-only结论推断旧源可编译。旧源本身禁止词扫描为0；后续目标中的 `sorry.ofLp` 与 `declaration uses sorry` 是首个解析错误后的恢复占位级联，不能当作源中新增sorry，也不能当作任何定理通过。未使用的simp参数和既有mathlib工作区变更警告保持原记录。

## 实际记号主源与环境

本轮从工作区已有只读证据定位到 `next-source/p53-label-law-real-basic.json#/full_source` 中的完整 `Mathlib/Basic/ENNReal/Basic.lean`，源SHA256为 `f7fe64f0d1865209e4d2be2fd98e3bc5edf9af508dd665f0311e6396f8d513a2`，32272字节。独立验证嵌入全文哈希、字节及其与 `unit100/source-current.json#/official11/Basic/ENNReal/Basic/complete_source` 的完整相等；后者明确绑定Mathlib `807d3836b165983210ee2ecf3cd28f239436949c`。没有进行网络或服务器读取。

已读取实际主源的相关完整声明与环境：第104行 `def ENNReal := WithTop ℝ≥0`，第107行 `scoped[ENNReal] notation "ℝ≥0∞" => ENNReal`，第112行也将 `∞` 记号登记在ENNReal作用域中。这里不是依据调用示例猜测类型记号的归属。实际WithLp完整主源第8行公开导入该Basic模块，第44行明确 `open scoped ENNReal`，第49–53行才以 `p : ℝ≥0∞` 定义真实构造器和投影。

修复在本模块第11行、列构造器第13行之前开启同一既有记号作用域，满足该源级解析义务。导入文件自己使用的局部open并不替当前模块开启该记号。新增语句没有定义新数据、函数、局部实例、helper或数学前提；它也没有把列构造器改成另一种空间。所有后续实际elaboration类型、实例和生成项仍需由新原生/全owner证据核对。

## 精确源码差异与未变证明的复用

独立逐字比较确认唯一差异是第11行：

```diff
-open scoped BigOperators
+open scoped BigOperators ENNReal
```

在旧源零起始字节229处插入恰好8个ASCII字节 ` ENNReal`，不增行。新完整前缀与已冻结修订逐字相同；前缀后的整个尾段逐字相同，尾段SHA256为 `ed65ab936197fae14c12fe7420566c7813b3a9bf9a8f7b946b45dcc7a45e9fdc`。

已分别核对全部9声明的完整头、参数、结果类型、4个rawValue、完整声明字节、完整证明体和声明SHA：全部保持原值与原冻结意义。每个声明的字符和UTF-8字节边界恰平移8、所有行号不变；新声明映射全部字节span与源一致，完整prefix/声明/后缀拼接精确重构新源。不是仅比较人工写出的diff。

新 `source-local-scopes.json` 的4个普通Prop初始化、4个显式证明索引记录、11个嵌入表达式及完整局部时间顺序均与旧材料相同，只绑定新source和修订后的全局prefix。新 `interface-calls.json` 的全部33条记录亦逐项相同。原9个头/4值、5个证明及53个上下文/200个词法事件的完整独立覆盖由旧报告SHA256 `7af98fd1546099d22f2801df4ca05eca43d32ac2bc521dfc21dfc907775202c1` 和旧coverage继承；本轮只补实际漏项与重定位，不重复整段数学审阅。

## 独立映射纠正项的精确重定位

作者repair元数据沿用原第9条85–70的历史倒置范围，没有擅自改写作者旧记录。旧独立纠正项SHA256为 `c0e9286765628434da5c50120a2ed77bab0d30452123e4d383a5c7f29722d803`；本轮在新增 `evidence-mapping-rebase.json` 中把相同源码表达式绑定到新source。

正确行号仍为85–86，新完整调用区域的零起始UTF-8半开字节区间为 `[4709,4807)`；区域全文与旧纠正项完全相同，区域SHA256仍为 `fe1b1afda0b12ef49f2577669472baaea5103bb9fef41c877bee94d7f0e39bc4`。第86行表达式 `column n D` 的精确字节区间为 `[4790,4800)`，完整预期类型仍为 `Fin n → EuclideanSpace ℝ (Fin n)`。

完整producer调用、其完整合取Prop类型、初始化时可见的n、D、W、q、hW、hD、hq，以及hbase尚不可见/完成后仅在本定理内可见的规则均原样继承。所有前置全局声明都已完成，没有自引用、前向引用或跨定理hbase泄漏。这项新source绑定补足repair映射的实际覆盖；不需要作者重写元数据、改源或重复185检查。

## 结论边界与后续资格

69条直接及递归本地引用记录的哈希/字节核对全部一致，包括修复作者manifest/DONE/RELEASE0及旧独立报告/清单/释放。该数量只是引用记录数。原p44固定有限实矩阵点态范围不变：真实欧氏整行作用、矩阵平方能量、非负权重的开方界、全部实q≥2的有限立方体矩根和真实radMeasure可积性/积分矩根；n=0、零权重、零能量、非对称与非零对角均保留。没有新增183/184依赖。

本轮不把前缀修复的source-only通过说成native02成功。实际所属声明数量、全部实际TYPE、非定理FULLVALUE、私有/生成项和递归AX均待后续同一独立上下文收到精确证据后核对；白名单仅 `propext`、`Classical.choice`、`Quot.sound`。不能以9个源码声明代替实际owner数。

185合格证据直接复用，旧186的未变数学证明直接继承。随机鬼样本/交换法则、Jensen/Fubini、实际随机行尾、标量二阶混沌、DC/root仍未闭合，p51/p54修正及Shao–Zhou外部归属不变。C2/C12/OQ56仍OPEN，OQ3仍PAUSED_BY_USER。

本轮审阅者仅写指定新子目录；Lean/server/network/Git/upload/cache/children/locks均为0。请求配置gpt-6.1-sol/xhigh，实际模型/effort及input、cachedInput、output、reasoningSubset不可见，均记null。完成后在自然边界释放，等待父级提供精确新机器证据再激活同一上下文。
