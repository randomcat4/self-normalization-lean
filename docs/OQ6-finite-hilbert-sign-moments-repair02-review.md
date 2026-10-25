# 单元185修复02独立受影响范围续审

源码级状态：`REPAIR02_AFFECTED_SOURCE_REVIEW_COMPLETE_MACHINE_PENDING`，`qualified=false`。本报告绑定精确source SHA256 `33d2027bc54fc1800e422ba21f0ba1af40334333300cdc8ff9f60238d6ee13c3`，40494字节、812 LF。修复作者的精确RELEASE0为 `3a5673b345cf68e9211b9be57d5abe2d97bbd2ea9e00304bfdfb9f7f44bdc6a6`；原native01/02均失败且无对象，不宣称它们有部分机器通过。此处的MACHINE_PENDING只表示本文写作时尚未读到成功新门及全部owner元数据；最终机器裁决必须另有同source证据。

完整读本次repair-reasons、source-to-statement、1804字节完整diff、affected-scopes的三完整old/new声明和全部涉及类型/初始化体/控制binder/chronological scope、freeze-comparison、全部三条diagnostic-disposition，以及static-map-assembly-correction。静态映射曾把hbase/hsum/hprod的换行赋值符号误提取为类型一部分，已直接依新完整源码核对其真实类型分别为非负平方根积、严格正平方根和、严格正共轭乘积；没有把错误的初始expectedType当作actualTYPE。映射修复不改变source字节。

## 三个完整证明的续审

1. **pair_sign_mean，97–119行。** 完整private头继续使用修订05的显式Classical决策；e仍是修复后pairCount的逐坐标函数。hreg初始化中的s、r、r∈univ和局部产品j均在自己的真实scope内；e初始化不见自身，hreg初始化不见hreg。新次序先 `simp_rw [pow_add]`，再 `rw [Finset.prod_mul_distrib]`，最后才把幂函数作用于if，并分别化简两个端点产品。这保留了逐位置恒等式

   `∏j σj^(I[a=j]+I[b=j]) = (∏j σj^I[a=j]) * (∏j σj^I[b=j]) = σa*σb`。

   特别a=b时仍是两个相同因子相乘σa²，pairCount对同一位置的贡献仍是2，没有以集合去重替换重数。剩余全偶/非全偶分支分别将he转为同一定义的ht，只在各自分支内同时化简两侧0/1条件值，不需假定两个Decidable实例可归约相同。原整向量偶矩证明通过相同private头消费该结论，接口含义保持。

2. **finite_hilbert_sign_moment_bound，656–730行。** 完整读取该公开证明及所有局部事实。唯一改动是在hpow初始化的实幂桥与自然指数rewrite后删去已无目标的rfl；hpow类型、f完整值、hpcast、k/p/A/f顺序及其余根/平方根推导原字节不变。两个hceil分属hqp/hpq初始化；s分属hf/hpow，均无跨scope借用；hbase、hsum、hprod现在的静态字段与源码相符。公开q≥2仍推出p>0，能量只需非负，hroot继续允许零底数，无新增能量正性或维数假设。

3. **radMeasure_atomic，732–763行。** 完整读取任意可测矩形E/hE、原子公式、hLaw、hweight和末尾prod_sum。唯一变化把hLaw中的ring换为 `simp only [one_div, mul_comm]`。其实际代数目标的两个成员指示均是ENNReal：将1/2统一为2⁻¹，再按乘法交换律置为相同形式即可；不需要指示非零/正性，也不需要决定成员命题为真或假。nu、真实law、概率实例导出的SigmaFinite、矩形可测义务和修订06完整系数显参均保持。hLaw初始化只见此前hAtom等事实，不见自身；它的j离开初始化即出scope。最终公开积分桥以相同测度恒等式消费该private定理，任意实f可积性及归一化不变。

## 新完整主源与实际使用条件

已完整读331行 `Mathlib/Algebra/BigOperators/Group/Finset/Piecewise.lean` 主源包，包SHA256 `2bcbf79d7a7bd0d76e95e13cfb1888b9b115b82381b0998cce268f61c0431764`，真实库源SHA256 `ff5fbaab50a679c4533d56c668c7906a1356f78d140cb92f117c987b3e5f8b31`。完整环境为 `{ι M γ : Type*} {s : Finset ι}`、`namespace Finset`、`section CommMonoid`、`[CommMonoid M]`。其完整接口含：

```lean
@[to_additive (attr := simp)]
theorem prod_ite_eq [DecidableEq ι] (s : Finset ι) (a : ι) (b : ι → M) :
  (∏ x ∈ s, ite (a = x) (b x) 1) = ite (a ∈ s) (b a) 1

@[to_additive (attr := simp) /-- A sum taken over a conditional whose condition is an equality
test on the index and whose alternative is `0` has value either the term at that index or `0`.

The difference with `Finset.sum_ite_eq` is that the arguments to `Eq` are swapped. -/]
theorem prod_ite_eq' [DecidableEq ι] (s : Finset ι) (a : ι) (b : ι → M) :
  (∏ x ∈ s, ite (x = a) (b x) 1) = ite (a ∈ s) (b a) 1
```

两条Finset定理确实带simp；同文件后部Fintype同名定理只有to_additive属性，不能假称它们带simp。新hreg的有限积是Finset.univ上的真实Finset积，取ι=Fin n、M=ℝ，所需DecidableEq与CommMonoid均存在；a分别取t(r)两端点，属于univ。prod_mul_distrib在同一个CommMonoid实例上成立，不需非零或非负性。pow_add是ℝ幺半群上的自然指数加法，不是实幂指数桥。

one_div在ENNReal的总除法上无额外非零前提，mul_comm来自其交换乘法。实幂与自然幂的桥继续使用前次已完整核过的实际Real.rpow/Powℝℝ定义、rpow_eq_pow和rpow_natCast；本轮没有新实例。

## 不变范围与边界

父级静态intake SHA256 `eb9260638904bf0c0a6fb1d1668cd2753cff71b57eadd4dc4bd53950060c8f7b` 绑定16工件、34头/15值、16未变proof、三完整old/new声明及精确diffspan/prefix/suffix。该源区间完整性证据复用，不重跑旧检查。34个有效头、15个有效值、23个局部let、四个双射函数、两个uncurry函数、修订06已有系数、prefix03与suffix均和repair01精确相同；仅三个proof体改变。其余已完整读过的证明与API覆盖复用原review加repair01补充，不再次重审。

修订05的pairCount外括号完整保留，旧scope误读的更正仍有效。k=0时空积等于1，pairCount全0；n=0时若有r则t(r)会给出Fin0端点，该分支不存在，不偷偷添加n>0/k>0。d=0和能量0在公开界的非负实幂/平方根合法域中；q仍是任意实数≥2、常数先固定为2、无维数因子。

本次源码级续审没有发现新的数学前提缺口；是否实际闭合全部proof仍以精确新门为准。实际module-index全部owner数量UNKNOWN，TYPE、所有非定理FULLVALUE及逐name递归AX未在本文中取得。不得用34源码声明或490历史词法条目充当实际owner/binder数量。

源范围继续仅p44§1(3)固定向量Hilbert符号矩及同一真实radMeasure积分版本；p51 S18的Shao–Zhou Lemma6.1外部归属、p54条件p矩与严格好事件修正保留，无183/184数学依赖，无根闭合/新颖性主张。C2/C12/OQ56 OPEN，OQ3 PAUSED_BY_USER。

本审阅只写repair02-and-server-evidence；source和旧review均未改，Lean/server/network/Git/upload/cache/children/locks均0。
