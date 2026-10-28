# 必要派生类型、投影和作用域

本文与 `ORDINARY-LET-CONTEXT.json` 的完整普通 let 上下文合读；这里的 P、G、Hsource、V0、D1、D2z、Ssafe、physical、clipped 以及所有事件均指冻结的同一个局部定义。全部源码字节切片在 `LOCAL-DECLARATIONS.json`、`BINDING-SCOPES.json`、`PRODUCER-CONTRACTS.json` 中原样嵌入。

P 的完整定义为 `sampleLaw n μ`，定义上为 `Measure.pi (fun _ : Fin n => μ)`。原 μ 的概率测度实例给 `instP : IsProbabilityMeasure P`，因此 `measure_ne_top P Hsourceᶜ : P Hsourceᶜ ≠ ∞`。此结论只保证有限测度；不增加任何集合可测性假设。

`hFrontier` 的完整 ∀/eventually/核前提/let/结论类型逐字来自 P54 的公开头，已放进绑定清单。它的参数调用 `hFrontier C a t0 M hC ha ht0 hM` 返回 `∀ᶠ n in atTop, 4≤n ∧ ...`；filter 绑定 n 与 hn。`hn.1 : 4≤n`，`hn.2` 接收 r、w、全部原 canonical 和包络假设，再接收 512、rho、z、h512、hrho、hz、hzWindow。该返回的四个分量为原 Hsource 可测、完整 hOldOn、原两种零分母并的包含和 `hHfee : P.real Hsourceᶜ ≤ payment`。

`hOldOn x hx` 的十四个拆解绑定均在 hOn 的局部 x、hx 作用域内。七个前部字段分别是 V>0、投影能量≥1/2、当前 z 的分子≤V/8、分子<V/4、当前 z²|rawdelta|≤1/32、|rawdelta|≤1/32、rawdelta>−1/8。其后五个固定 y=1 裁剪字段保留完整类型但不用于当前 z 的推导；最后两个字段为真实分母正和原始偏差因式分解。

`hCurrentClip` 的四个分量是：1+D2z≥1/2、|D2z|≤当前预算、|D2z|≤|rawdelta|，以及 V>0 时当前裁剪分母正。只取第三分量作为 `hContract`。`sq_nonneg z : 0≤z²`，故 `mul_le_mul_of_nonneg_left hContract (sq_nonneg z)` 的完整派生类型是 `z²*|D2z x|≤z²*|centeredDelta n g r x|`。与 hRawScaled 传递给 `hScaled : z²*|D2z x|≤1/32`。

`hRawLower : −1/8<centeredDelta n g r x` 经线性算术给 `hLower : −1/2≤centeredDelta n g r x`。`hx.1 : x∈G` 定义上是 `x∈projectionGood n g z`。literal 比较按实际实参返回五分量：D2z=rawdelta、当前裁剪分母正、真实分母正、两个分母相等、clipped=physical。相应完整投影类型为：

~~~lean
hLiteral.1 : clippedCenteredDelta n g r 512 rho z x = centeredDelta n g r x
hLiteral.2.1 : 0 < projectionV n g x * Real.sqrt (1 + clippedCenteredDelta n g r 512 rho z x)
hLiteral.2.2.1 : 0 < Real.sqrt (centeredSq n g r x)
hLiteral.2.2.2.1 : projectionV n g x * Real.sqrt (1 + clippedCenteredDelta n g r 512 rho z x) = Real.sqrt (centeredSq n g r x)
hLiteral.2.2.2.2 : clippedCenteredStatistic n g r 512 rho z x = (if Real.sqrt (centeredSq n g r x) = 0 then 0 else (projectionW n g x + residualStatisticD n r x) / Real.sqrt (centeredSq n g r x))
~~~

`hOn x hx` 的七分量及后面 hxOn 的同名类型均完整写在静态类型清单中。源码使用的关键投影如下：

~~~lean
hxOn.1 : 0 < V0 x
hxOn.2.1 : z * |D1 x| ≤ V0 x / 8
hxOn.2.2.1 : z ^ 2 * |D2z x| ≤ (1 / 32 : ℝ)
hxOn.2.2.2.1 : 0 < Real.sqrt (centeredSq n g r x)
hxOn.2.2.2.2.1 : Real.sqrt (centeredSq n g r x) = V0 x * Real.sqrt (1 + centeredDelta n g r x)
hxOn.2.2.2.2.2.1 : D2z x = centeredDelta n g r x
hxOn.2.2.2.2.2.2 : clipped x = physical x
~~~

Hsource 到 Ssafe 的最后义务是 `z²*|D2z x|≤1/8`，只使用上述 1/32 界。hUnionSubset 三个证明分支的绑定类型分别是 `hxSafe : x∉Ssafe`、`hxClip : clipped x≠physical x`、`hxPhysical : Real.sqrt(centeredSq n g r x)=0`；它们分别与 hSafeSubset、hOn 最后一项、hOn 第四项矛盾。不要求三个事件互斥。

hRemainderSubset 内假定 `hxSafe : x∈Ssafe`。分支 `hxE2 : x∈E2` 经 change 得完整类型 `(1/4:ℝ)<z²*|D2z x|`，与 `hxSafe.2.2 : z²*|D2z x|≤1/8` 矛盾。另一分支 `hxZ0 : V0 x=0` 与 `hxSafe.1 : 0<V0 x` 矛盾。没有对边界等号作零测度假设。

四事件并在 Lean 中按左结合解释为 `((E2∪Z0)∪Eclip)∪Zphysical`。四分支分别将 E2、Z0 先送入 Ssafe 补，再送入 Hsource 补；Eclip 和 Zphysical 由 hUnionSubset 直接送入 Hsource 补。各分支只有点集包含，没有概率求和。

三次 measureReal_mono 的完整派生类型分别为 `P.real Ssafeᶜ≤P.real Hsourceᶜ`、`P.real(E2∪Z0∪Eclip∪Zphysical)≤P.real Hsourceᶜ`、`P.real Eclip≤P.real Hsourceᶜ`。每次用有限 P 给右集合的非无穷证明，随后与同一 `hHfee` 传递。这三条最终类型都以同一个 payment 为右端。

最外层 refine 的待证类型是冻结 cg 后的完整全称命题；filter 中第一个 refine 的待证部分是冻结的全部 r/w/rho/z 全称命题。顺序 intro 17 个普通 let 后，最终 exact 的十二个分量依次为 Hsource 可测、physical 可测、clipped 可测、Eclip 可测、Hsource⊆Ssafe、完整 hOn、三事件并包含、E2/Z0 包含、Hsource 补付款、Ssafe 补付款、四事件并付款、Eclip 付款。

本清单只描述完整源码中的显式绑定与作者静态类型；不声称获得编译器生成项的实际类型、proof term 或递归公理集。独立审查和新源码服务器内核/全实际所属审计仍为未完成门。
