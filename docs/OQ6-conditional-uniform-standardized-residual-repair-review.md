# 单元 181 repair01 独立补充源审

STATUS: CORRECT_SOURCE_REVIEW_PENDING_SERVER

精确补审对象为 `2dd4569985df4b849ec4f1cc1e0320754a9d2fcec1db9ef994dd007c6fc4ddb4`，26670 字节、573 LF。本次复用我在同一独立审稿上下文完成的原 `952b979f…` 全部 570 行源到声明/证明审查及完整冻结/作用域覆盖，仅对受影响 hWVarId 作独立补审。没有发现新的数学缺口。`qualified=false`：新源码的实际服务器 kernel/O/module-owner TYPE/FULLVALUE/递归 AX 尚未交给本审核对。

已完整读取 repair01 的 RELEASE、artifact-manifest、proof-delta.json、proof-delta.patch、mapping-delta.json、mathematics.md；父级 parent-repair01-intake 的绑定、结论及行政检查清单已解析，未将其通过数作为正确性背书。另完整读取原 kernel01 的本地诊断投影，确认它是 217:12 重写匹配失败、自然 exit1、没有对象；不是证明通过或未确定的在途检查。旧失败与旧审稿证据保持原字节。

新旧源码独立逐字节比较：仅原 217–219 三行替换成新 217–222 六行，增加 103 字节和 3 LF。9811 字节前缀和 16582 字节后缀均完全相同；逆替换精确还原旧 952b979f… 源。声明、原假设、25 个数据的类型/值/顺序、阈值选择、固定常数、量词和选项全部保持。197 项完整数学字段、36 个额外 Prop、16 内部绑定组、11 次生产者应用的类型/值和词法上下文经独立比较保持相同。原完整审稿发现的覆盖补充继续有效，后段源位置统一加 3；没有用修复重写旧报告或重复审查生产者。

已重新完整读新源码 165–240 行、hWVarId 全部 209–224 行和它从 imports/namespace、全部原输入、固定 g/r/M/W2/Cenv/RhoBound、hThreshold/N0/hN0Spec 直到 hWVarInt 的完整真实环境。此处 R、lam 尚未引入。hwSq : Integrable (fun o : Ω => w o²) μ 与 hw1 : Integrable w μ 都已在 171–175 行证明；μ 的概率实例已由原输入提供，故常函数可积。M=∫w²、W1=∫w 的值及 hWVarInt : Integrable (fun o => (w o−W1)²) μ 没有变化。后续 226–230 行仍从平方积分非负及 hWVarId 推出 W1²≤M。

唯一修复是把 `integral_add` 的原隐含两个函数显式给出：

```lean
f := fun o : Ω => w o ^ 2 - 2 * W1 * w o
g := fun _o : Ω => W1 ^ 2
```

它们分别具有完整类型 Ω→ℝ；o/_o 各自在对应 lambda 内绑定，W1,w,μ,Ω 均已存在。f/g 是定理的命名参数，不是新局部数据别名。f 的可积性正由原 `hwSq.sub (hw1.const_mul (2 * W1)))` 支付，g 的可积性正由原 `integrable_const (W1 ^ 2)` 支付。与旧失败中已展开的函数相减应用相比，差别仅为定义性展开后的 lambda 句法，未新增数学函数信息、假设或库结论。

实例化后的实际数学等式是

\[
\int\bigl[(w^2-2W_1w)+W_1^2\bigr]\,d\mu
=\int(w^2-2W_1w)\,d\mu+\int W_1^2\,d\mu.
\]

对两份已可积函数使用积分加法合法。后续原 `integral_sub hwSq (hw1.const_mul (2 * W1))` 与 `integral_const_mul` 给第一项 M−2W1∫w；概率常数积分给第二项 W1²；W1=∫w 后以环恒等式得到 M−W1²。前一步以 `integral_congr_ae`/ring 展开 (w−W1)² 也保持原字节。因此受影响承重结论仍完整成立，没有把不可积总化积分当矩、没有引入未来前提，也没有改变统一残差界的其他证明范围。

新 source-map 在 ITEM045 及四个以完整 hWVarId 为位置的 inline 项 ITEM133/135/136/137 中包含新的完整源块；内部 hWVarId binder 组的相应 proof block 也随之更新。其余代码块按精确位置平移。独立审稿原有的 ITEM001/002 第14行、ITEM124/125 源头、10 个局部顺序修正、三个合并绑定组的第二处出现，以及 ITEM176 导入接口族标识继续沿用，按行映射接到新源码；不得把重新生成的 map 当作已经自动修复这些旧索引细节。

本补审结论只支付修复的数学/源范围。下一步须核对父级提供的同一新源码 kernel02 和同对象实际整个模块所属枚举、完整 TYPE/非定理 FULLVALUE（若有）/逐所属递归 AX。实际模型、强度和输入/缓存输入/输出/推理子集用量未暴露，保持 null；请求仍为 gpt-6.1-sol/xhigh。本审无 Lean/服务器/网络/Git/上传/cache/工具链/子代理操作，写入仅限当前 repair01-and-server-evidence 目录。OQ56/C2/C12 OPEN，OQ3 单独 PAUSED_BY_USER。
