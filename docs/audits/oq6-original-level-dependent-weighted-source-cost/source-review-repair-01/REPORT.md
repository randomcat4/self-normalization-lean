# Unit250：三个冻结修复的独立审查

STATUS: CORRECT

JUSTIFICATION: 新源精确等于旧完整已读源码加freeze-02授权的三个替换。坐标对映射现有明确的 `Fin n → Ω` 定义域；两处支配证明分别以 `add_le_add le_rfl` 保持目标中真实共同左前缀。直接受影响局部上下文、所有局部完整类型和新源坐标均已核对，没有新增前提、fact、instance或模型选择。旧完整SOURCE覆盖按不变字节区间复用，和本次delta阅读联合覆盖新365LF。

此为affected-SOURCE裁决；`sourceAccepted=true` 仅指可以进入指定服务器新源检查，`qualified=false`。本角色未运行任何Lean/lake/PP/AX，也未访问server/network、上传或Git/API。新源kernel、首次成功O的全部actual TYPE、required VALUE及递归AX仍PENDING，不以源码数量替代机器所属集合。

## 精确范围与证据复用

- 新源 `author-repair-01/OriginalLevelDependentWeightedSourceCost.lean`：SHA256 `9eab174ed67833ed40df18ea889fb60a98e0c49401d4955872560e15bc4ebe6f`，19238B、365LF、0CR、严格UTF-8。
- 旧源：`17ab15bf0299531a33ba9710cbb8e43c61d59de6d306aeb5e900378b2a799c2a`，19166B、363LF。既有363LF完整proof/source-to-statement阅读及p51/p54完整阅读复用，不另起重复全审。
- 原冻结声明：`a26f0a109e8f06fd03c4326ecd868ed882ae40f84a927c172b67e567ac8166de`。修复freeze-02：`dd409f67c9713400edad5ffec1c71a9b6afc5d3ac3b65163bb4597e4ece260bf`；坐标澄清：`217b674eb7e22afa4420f59e58e1f38642609d20f52aab7d6439b72a237d341e`。
- 旧独审SOURCE MANIFEST `9e2b6996cd3dfc28d75b3a11431c48f8ec7f818d012f933fba6c1932cf5710fd`、COVERAGE `05e0da2be7ce6e5dfc8863d42a9e72fca0860359343bda20841df73525c2cfab`、失败阶段MANIFEST `d21a0206e27593ef52455cd67d5c7bded4881cf4f2491d0ef11cad84e0a00e50` 及全部旧字节保持只读。原native01仍为旧源RC1/三个实际错误/noO，未转写为新源结果。
- 实际读取了修复freeze/clarification、author DELTA/STATIC/MANIFEST/release、输入绑定及新源218–285和301–360行；完整直接受影响fact hEdgeM236–240、hFullDom324–327、hDeleteDom328–333均逐行核对。

## 三个实际delta

1. 旧238行变成新238–240行。类型标注为 `Measurable (fun ζ : Fin n → Ω => (ζ j, ζ k'))`，其两坐标来自原measurable_pi_apply，构成Ω×Ω值映射，随后与原 `hr : Measurable (fun t : Ω×Ω => r t.1 t.2)` 组合。`e ζ j k'` 与组合结果由原定义化简一致。标注仅消除定义域推断歧义；没有假设坐标独立，没有给r新增可测性假设，对j=k'也有效。hEraseM、pair/row可测性后续沿原fact类型消费，不发生接口扩张。
2. 旧325行变成新327行。原 `hBdom ζ : B ζ<=BA ζ` 乘非负z²后，`add_le_add le_rfl` 把相同 `z*|D1 ζ|` 放在两侧左边，与fullTest/sourceFull展开完全对应，再乘同一正full指数。hFullDom完整类型不变；没有交换预算、不改变系数。
3. 旧331行变成新333行。原 `hBdiffdom ζ i` 乘非负z后，`add_le_add le_rfl` 保持同一真实绝对D删除差为左前缀，再按未变步骤乘非负cap和相同partial指数。真正预算删除差仍来自既有共同确定项消去；没有改成两个预算的分别上界。

以上三处在SOURCE层面针对原三个formal错误，数学与目标次序相符；是否成功elaborate并被kernel接受仍由新源实际native结果决定。

## 无损联合覆盖与实际清单

独立由freeze的before/after字符串正向精确重建新源、逆向精确重建旧源，两方向均字节相同。四个不变字节区间已分别派生并hash绑定，长度为11996、5095、273、1572B；三个变化块及映射写在 `UNION-COVERAGE.json` 与独立检查中。联合覆盖不是把新365行伪称重新全文读过：不变区间沿用旧完整审稿，实际变化块及完整受影响上下文本轮阅读。

独立核对新清单：118命名绑定=50let（16结果telescope+34proof）+68have，118完整signature与旧源逐一相同，118完整新源block及hash/新行坐标匹配。公共17参数组实际binder/type文本不变。变量binder-marker按新源重导为131，额外唯一站点是新240行标注里的lambda；它不是逻辑前提、local fact或machine owner。hDeleteM的新区间307–314及嵌套hAbsD309–311、hAbsB312–313的外层i和先前局部fact作用域保持。

本轮40个唯一输入文件绑定全部实际匹配；40=作者包39集合再加parent repair-intake文件。初次检查把新增的坐标元数据 `columnCodepoint1` 也参与整对象相等，故公共参数元数据比较false；原诊断保留，v2改为比较实际binder/type/source字段后17组完全相同。冻结完整头本身在两次检查中一直字节精确，不存在声明改变。

## 范围和后续

p51 S10/S13/S14的当前层级z预算、原h/μ/g/r、原n、D的n-1分母、能量的原(n-2)^2删除归一化、同一full/partial指数、cap与正积分I均不变。p54对条件p矩过强变化率的修复继续保留，外部概率引擎继续归属Shao–Zhou。未声称unit249的fixed clipping1三次费用、physical-tail、CDF、externalSZ、eventual-window、DC或fullOQ56闭合。

本独立上下文保持可续审，等待lead提供此9eab174e精确新源的首次成功原始O及native/sameO机器材料；随后完整阅读所有actual owner的unelided TYPE、所有必需非theorem VALUE和每owner递归AX，并核对冻结statement。此前qualified=false。本轮请求模型gpt-6.1-sol/xhigh；实际模型/effort及input、cachedInput、output、reasoningSubset不可见，全部null。
