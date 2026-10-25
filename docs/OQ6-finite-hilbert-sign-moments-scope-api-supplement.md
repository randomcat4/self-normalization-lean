# 独立作用域与API补充

绑定候选SHA256：`f5a30c5f0466413355b5deaacf5075d9f73bba9b2dff1d0b81905cbdf3a33fd6`。本文件是独立源码级阅读，不是Lean展开TYPE。

## 两次凹函数割线dot调用

主源为 `Mathlib/Analysis/Convex/Deriv.lean`，完整片段在 `next-source/oq6-finite-hilbert-sign-moments-185/convex-tangent-integral-scalar-complete-primary-source.json` 的 `files[3].ranges[0]`（850–930）；完整环境为 `section MirrorImage` 内 `namespace ConcaveOn`：

```lean
variable {S : Set ℝ} {f : ℝ → ℝ} {x y f' : ℝ}

lemma slope_le_of_hasDerivAt (hfc : ConcaveOn ℝ S f)
    (hx : x ∈ S) (hy : y ∈ S) (hxy : x < y) (hf' : HasDerivAt f f' x) :
    slope f x y ≤ f' :=
  hfc.slope_le_of_hasDerivWithinAt_Ioi hx hy hxy hf'.hasDerivWithinAt

lemma le_slope_of_hasDerivAt (hfc : ConcaveOn ℝ S f)
    (hx : x ∈ S) (hy : y ∈ S) (hxy : x < y)
    (hf' : HasDerivAt f f' y) :
    f' ≤ slope f x y :=
  hfc.le_slope_of_hasDerivWithinAt_Iio hx hy hxy hf'.hasDerivWithinAt
```

两条接口不需要区间内处处可导。实际rpow_tangent的顶层环境是 `(x r : ℝ) (hx : 0 ≤ x) (hr : 0 < r) (hr1 : r ≤ 1)`；全局前缀与此前声明都保留冻结修订03。先有 `hc : ConcaveOn ℝ (Set.Ici 0) (fun t : ℝ => Real.rpow t r)`，由 `Real.concaveOn_rpow hr.le hr1`；再有 `hd : HasDerivAt (fun t : ℝ => Real.rpow t r) r 1`，由 `Real.hasDerivAt_rpow_const (x := 1) (p := r) (Or.inl one_ne_zero)` 和1的实幂化简。该导数定理的条件是x≠0或1≤p；实际用1≠0，未要求r≥1。

第514行的 `hc.le_slope_of_hasDerivAt hx (by norm_num) hlt hd` 在 `lt_trichotomy x 1` 的x<1分支，新增 `hlt : x < 1`。实参特化是 `S=Ici0`、`f(t)=t^r`、库x=本地x、库y=1、f'=r；条件依次是本地hx、0≤1、hlt、hd。结论为 `r ≤ slope f x 1`，用 `slope_def_field` 得 `r ≤ (1-x^r)/(1-x)`；`1-x>0` 后交叉相乘给切线界。hx允许x=0，此处不在0处求导。

第523行的 `hc.slope_le_of_hasDerivAt (by norm_num) hx hgt hd` 在x>1分支，新增 `hgt : 1 < x`。实参特化是库x=1、库y=本地x；条件依次是0≤1、本地hx、hgt、hd。结论为 `slope f 1 x ≤ r`，分母x-1>0，给 `(x^r-1) ≤ r(x-1)`。相等分支先 `subst x`，仅用1的实幂。三个分支互不借用分支变量。

## 有限测度缩放dot调用

主源为 `Mathlib/MeasureTheory/Function/L1Space/Integrable.lean`，完整声明和环境在 `inner-finite-measure-sum-focused-primary-source.json` 的files[2]。其环境含可测空间α、拓扑空间ε及 `ESeminormedAddMonoid ε`，声明为：

```lean
theorem Integrable.smul_measure {f : α → ε} (h : Integrable f μ)
    {c : ℝ≥0∞} (hc : c ≠ ∞) : Integrable f (c • μ)
```

实际第768行特化α为真实 `Shao.Path n = Fin n → ℝ`、ε为ℝ、μ为有限Dirac和、c为 `(2^n)⁻¹ : ENNReal`。hSum在第763行已由每个原子可积推出；hc在第753行由2^n≠0及 `ENNReal.inv_ne_top` 推出。没有对f增加全局可测性，也没有使用不存在的私有源接口。

## 实际局部作用域重建

我完整按源码的声明顺序、缩进、have初始化子证明、lambda/forall/求和/乘积和tactic分支读取作用域。未把作者map的宽泛同名候选集当作作用域等同。实际规则如下：

- 每个顶层声明只见此前声明和自己的完整 telescope；本模块无新增variable前提、局部instance或假设常量。
- `have h : P := by ...` 中h在其初始化子证明内不可递归使用；初始化中的intro、funext、obtain见证只在该子证明有效，h完成后才在外层可用。
- 第71行偶见证l/hl只在he分支；第93行not_forall给出的j/hj只在非全偶分支。每个配对词t和乘积r均由所在有限类型引入，未改变n,d,k。
- 第117/128/145/156/174/185行六个主事实的s、i、j、t、r及内层hpow/hps均按各自初始化scope分开。所有a均是固定的列范数函数；两条uncurry系数的s只来自对应点态证明，无选择或未来数据依赖。
- 第266行 `sum_nbij'` 的五项义务依次是toEven入支持、fromEven入allocation、左逆、右逆、被加项相同；每项新引入的ell/hell或m/hm、各自hhalf/hsum不可跨兄弟分支使用。第369行toNat/fromNat同理。第339/412行归纳前驱与IH仅在succ分支。
- 第443行ell/hell作用于整个单项比较，denEven/denHalf只依赖该ell；分母正性与hnum非负性在相应乘除比较之前已建立。
- 第535行B=0分支与B≠0分支分开。g=f/B只在后者定义；hBpos先于g。hf0及其s只在零分支。第590行hfg及其s只在hscale的逐项子证明。
- 第644–647行k,p,A,f顺序固定；hqp/hpq子证明中的hceil各自局部。hpowered只用hp.le/hA，hroot先验证非负底数及p>0；hs反证中的hlt/hsum/hprod只在该初始化中。
- 第721行E与hE是pi_eq提供的任意可测坐标矩形；hAtom/hLaw各自forall实例化，不把hE强化为所有集合可测。第761行x=signPath n s只在对应原子可积子证明；最后桥的f仅是其公开目标函数。

冻结计划中的旧按n归纳hTail/sFull、按有序词计数的alpha/m/permutation/labels和beta、h/hPrime求导族、逐点零能量族、额外constant-w族及pathSum点态j族确实未消费。实际改用完整标准多项式、凹性在1处的导数和定义反身性；修订02/04的四个总转换函数与两个uncurry函数均按精确冻结值出现。普通Prop/分支/IH变量不构成新增数学假设。

## hfilter静态binder误识别的精确处理

`actual-source-map.json` 中 `allBinders` 的215–223记录共用候选字节区间 `[12352,12467)`（SHA256 `f6460285b88f10719a2f45e1e8be850277fb2fcb66c9eeb45ed93e171ce3ba67`），实际是第257–258行：

```lean
∑ m ∈ (Finset.piAntidiag Finset.univ (2 * k)).filter
    (fun m : Fin n → ℕ => ∀ j : Fin n, Even (m j)), ...
```

外层只有一个受限求和索引 `m : Fin n → ℕ`；集合表达式不引入名为∈、(Finset.piAntidiag、Finset.univ、(2、*、k)).filter或(fun的binder。215-m应按该外层m理解，216–223是过度切分造成的伪条目（223-m重复吸收了内层lambda token）。内层filter lambda的m由224-m的独立区间 `[12420,12438)` 标识，类型为 `Fin n → ℕ`，只作用于其forall j偶性谓词；它遮蔽外层同名m，但不改变后续被加项中的外层m。225-j仅在谓词，226-j仅在被加项乘积。

这使map的490条成为含过度记录的词法索引，不能宣称是实际binder数量。其他已读实际scope的数学有效性由完整实际源码及上述消歧建立；本补充不写作者原JSON，不借伪计数充当机器元数据。实际生成owner及其TYPE仍须由服务器取得。

## 其他接口与实例消歧

62条显式主源记录覆盖实际调用的有限产品/展开/重索引、实内积、rpow、ceil、阶乘及测度接口；88条基础记录只按预期契约使用。`two_mul`的源第74行是自然数指数上的重写，虽然作者预期表只写ℝ；其自然数实例为 `∀ l : ℕ, 2*l=l+l`。Fintype的DecidableEq/Fintype实例由Fin/Bool及classical提供；multinomial的环是ℝ；原子矩形计算的半权、prod_sum和指标函数在ENNReal上，其交换半环/带零交换幺半群条件成立。

生成接口已按完整原声明/tag/环境阅读：prod_bool→sum_bool、prod_prod_type→sum_prod_type、prod_nbij'→sum_nbij'、prod_const→sum_const。特别是Set.mulIndicator_apply→Set.indicator_apply同时将One变Zero及else1变else0；实际用于常函数1的指示函数，结果为if成员则1否则0。没有误用Finsupp的同名接口。

有限路径可测空间是实坐标乘积，Fin n有限，具有可测单点；每个实函数原子值的扩展范数有限。公开law_isProbabilityMeasure提供边缘SigmaFinite。这里没有要求全局f可测、没有Dirac积分缺失条件、没有无穷系数引起的积分歧义。
