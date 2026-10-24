# 单元160、162、164独立完整终审

结论：**CORRECT**。五个实际所属定理（四个公开源定理和一个生成化简定理）的原文语义、完整形式类型、证明、所消费接口和递归公理覆盖均通过独立审查；未发现关键缺口。此为独立终审结论，尚需父实例核对本报告及封印后另行记录资格认定。它不关闭C2或完整稀有后缀概率链。

## 角色、范围与读取证据

审阅者与作者分离，使用父实例明确配置的 gpt-6.1-sol / xhigh 新上下文；运行ACK与检查点已实际落盘。后端模型/努力级别及分项用量没有独立遥测，报告相应字段为null，不把原始token量或订阅百分比分摊当成精确费用。使用math-theorem独立验缝和中文输出规范，不启用math-ultra、Goal、调度或附加实例。

只写本终审目录；正式源、回执、旧接受证据和服务器均只读。160/162成稿但尚未封存时，父实例明确追加164，本上下文记录实际追加运行ACK后完整审阅。完整读过三个最终Lean源、全部冻结上下文和头、完整9072+3199+4275字节实际类型、三个空定义值导出、OwnedAudit源码/所属映射/回执/finisher、所有原核验命令和日志及失败差分。审计日志中已读完整类型导出的块由确定性脚本逐字重构，其余警告与退出标记也完整阅读。没有运行任何Lean或公理审计，没有回放成功门。

原文只读绑定：supplement.tex SHA256 b99f2ac4d2f39dd39772d98a5702b7a923c2f10f8730a08fc1b4cd6bba4742bd，读取5058–5063和5094–5147，重点5107–5111、5123–5147；main.tex SHA256 beb00f718487e36de433175c97f1d500cb48e7a92ce5bd5ad5d62bb132122d06，读取145–170、175–244。原文使用实际自归一化能量和弱乘法越界，包括全零样本；C1、C2原根的量词和本轮辅助范围据此区分。

当前REGISTRY为v85，原C1 COMPLETE，C2/C12 OPEN，OQ3 PAUSED_BY_USER。C12只有CPU14–17/单重命令/c12-heavy.lock的既有配额。本审阅只读，不占用Lean执行许可。

## 冻结、精确字节与实际所属范围

| 单元 | 模块 | 实际/公开定理 | 实际完整类型字节 | 私有/生成/全局值 |
|---|---|---:|---:|---:|
| 160 | Shao.C2.AuxiliarySourceGaussian | 2/2 | 9072 | 0/0/0 |
| 162 | Shao.C2.AuxiliaryCenteredProductLaw | 1/1 | 3199 | 0/0/0 |
| 164 | Shao.C2.AuxiliaryMarkedDeletion | 2/1 | 4275 | 0/1/0 |

合计由实际所属映射与源码声明导出：3模块、4公开源定理、5实际所属定理、1生成定理、0私有源定理/非定理值，16546完整类型字节与0定义值字节。冻结前记录implementationStarted=false；最终源去除证明体后连同导入、上下文和完整头逐字等于冻结。162两次尝试的头亦相同。未更改数学前提。

### 单元160精确绑定

- 源：`2d5ba73634a034eb61ea95939325786042988dc489f06dad4bf65587d49f8a74`
- 对象：`401939f6b667f2bbaf065ec162b1762ea09aa6cf00c8e4e8c29ef489640b8ef5`
- 回执：`6ea092d97c26b51696c071d44ccfd5e8332269bc038aaaea8e891b7b4adc17d0`
- 冻结：`94c3cbe379cbdd8fffc482b954e42b22b0e5db2ce2b9c650949f6ea8f54baff3`

完整冻结内容：
```lean
import Shao.C2.AuxiliarySourceEvent
import Shao.Probability.GaussianTail

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
namespace Shao.C2.AuxiliarySourceGaussian
open MeasureTheory ProbabilityTheory

theorem auxiliary_rare_threshold_gaussian_geometry
    (x : ℝ) (hx : 1 ≤ x) :
    let a : ℝ := Real.sqrt (9 * x ^ 2 / 4 - 1)
    let y : ℝ := a - 1 / (100 * (1 + x))
    x ≤ y ∧ y ≤ 3 * x / 2 ∧
      (3 * x / 2) ^ 2 - y ^ 2 ≤ 2 := by

theorem auxiliary_rare_threshold_gaussian_tail
    (x : ℝ) (hx : 1 ≤ x) :
    let y : ℝ := Real.sqrt (9 * x ^ 2 / 4 - 1) - 1 / (100 * (1 + x))
    Shao.standardNormalTail y ≤ 12 * Shao.standardNormalTail (3 * x / 2) := by

end Shao.C2.AuxiliarySourceGaussian
```

### 单元162精确绑定

- 源：`e33534bddfb3299850fcc1f3d21c2c3cb8271422a81b2a359d7a4dbfdd19801e`
- 对象：`3a14fb7e48a79e51a9cc2767574593836467ed3a6096edabd7ef979c0e91f5bb`
- 回执：`8dda63424f2dac7bdd49953402f808b01b5d05223899a379be5136c1d9f1f7ca`
- 冻结：`8a88ee0a9d4e8ebeaac337a73ac009a2c0f8cbec7919df34dbb3c83a5b34a006`

完整冻结内容：
```lean
import Shao.C2.AuxiliaryOwnC1Budget
import Shao.Probability.FiniteIID

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
namespace Shao.C2.AuxiliaryCenteredProductLaw
open MeasureTheory ProbabilityTheory

theorem auxiliary_centered_product_law_and_endpoint
    (rho : Measure ℝ) [IsProbabilityMeasure rho] (n : ℕ) (mu : ℝ) :
    let chi : Measure ℝ := Measure.map (fun z : ℝ => z - mu) rho
    let P : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => rho)
    let Pc : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => chi)
    Measure.map (fun v : Shao.Path n => (fun i => v i - mu)) P = Pc ∧
      ∀ y : ℝ,
        P.real {v : Shao.Path n |
          y * Real.sqrt (Shao.energy (fun i => v i - mu)) ≤
            |Shao.prefixSum (fun i => v i - mu) n|} =
        Pc.real {w : Shao.Path n | y * Real.sqrt (Shao.energy w) ≤
          |Shao.prefixSum w n|} := by

end Shao.C2.AuxiliaryCenteredProductLaw
```

### 单元164精确绑定

- 源：`d41692110c947b26f92f6bd2f9511a0c1f25a20e0a470d59dcd19b770cc196e5`
- 对象：`e5b27b3e0a19791a148e8db4f210c9f2b7ba7df343e692fe65ff9f046ed3bd01`
- 回执：`b248dfe2fa310cba34c975f90315f12d4a91880a0fb5c6a0db099c16eeaffc9b`
- 冻结：`4340b780200936caede6c070bac3c1cd0620862e55687c16c595caaf62ea3a0b`

完整冻结内容：
```lean
import Shao.C2.AuxiliarySourceGaussian

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
namespace Shao.C2.AuxiliaryMarkedDeletion

theorem auxiliary_marked_terminal_deletion
    {n : ℕ} (w : Shao.Path n) (v x : ℝ) (hx : 1 ≤ x)
    (hFull : 0 < v ^ 2 + Shao.energy w)
    (hCross : (3 / 2 : ℝ) * x * Real.sqrt (v ^ 2 + Shao.energy w) ≤
      |v + Shao.prefixSum w n|) :
    0 < Shao.energy w ∧
      Real.sqrt ((9 / 4) * x ^ 2 - 1) * Real.sqrt (Shao.energy w) ≤
        |Shao.prefixSum w n| := by

end Shao.C2.AuxiliaryMarkedDeletion
```

第一轮服务器只读观测的87项哈希全部匹配：当前目标源、原成功尝试源、输出对象及实际导入对象、完整回执列出的证据和冻结、全部声明相关旧C12源码/对象、实际接受公共源码/对象、钉住Lean收集器和owner接口源码。分支为author/c12-auxiliary-centered-v71，HEAD aef587dd277f159314297cef02b352057d7102ec。Lean为4.36.0-rc1，mathlib为807d3836b165983210ee2ecf3cd28f239436949c；实际mathlib解析到共享只读shared-v34包视图。终态再只读核对并封印，不回放既有成功门。

## 逐实际所属定理审查

### Shao.C2.AuxiliarySourceGaussian.auxiliary_rare_threshold_gaussian_geometry

源位置：10–45行。判定：**CORRECT**。

**精确语义。** 对每个实数x≥1，令a=√(9x²/4−1)、δ=1/[100(1+x)]、y=a−δ，则x≤y≤3x/2，且(3x/2)²−y²≤2。没有概率、矩或额外阈值前提。

**原文对应。** 与supplement5059的v_x和5123的y_x完全相同；(9/4)*x²与9*x²/4只是实数域中的代数重排。结论给出5135–5136所需的统一平方差界，并加强原文1≤y≤2x；不代替后续概率不等式。

**实际类型。** 完整pp.all实际类型保留唯一x:Real及hx:1≤x，两层let为原a和y，结论是x≤y ∧ (y≤3x/2 ∧ ((3x/2)²−y²≤2))。所有数字除法及乘法均为实数；没有隐藏类型类、局部公理或加强前提。

**完整证明审查。**

1. x≥1给出x≥0、x²≥1和9x²/4−1≥0；Real.sqrt_nonneg及Real.sq_sqrt分别给a≥0和a²=9x²/4−1。后者的非负根式条件在调用前支付。

2. D=100(1+x)>0，故δ≥0，且δD=1。由100δ+100xδ=1和δ≥0、x≥0，分别得到xδ≤1/100和δ≤1/100。div_mul_cancel₀的分母非零由正性给出。

3. 比较平方时两侧都非负。a²−(11x/10)²=(26/25)x²−1≥1/25，故11x/10≤a；又a²=(3x/2)²−1≤(3x/2)²，故a≤3x/2。两个sq_le_sq₀调用均使用正确方向及非负前提。

4. y=a−δ≥11x/10−1/100≥x（x≥1）；δ≥0也给y≤a≤3x/2。弱不等式在x=1同样成立，无极限或严格边界漏洞。

5. 精确展开平方差为1+2aδ−δ²。将a≤3x/2乘以非负2δ，得到2aδ≤3xδ≤3/100，因此平方差≤103/100≤2。源中hCross、hdX和sq_nonneg delta支付的正是这些步骤。

**消费接口。** Real.sqrt_nonneg；Real.sq_sqrt with explicit nonnegative radicand；sq_le_sq₀ with both sides nonnegative；div_mul_cancel₀ with positive denominator；mul_le_mul_of_nonneg_right。

**边界。** x=1包含；D=200>0、a=√(5/4)、δ=1/200，比较均有余量；x可任意大，无紧性、渐近或数值枚举假设；没有除以x、y、能量或概率；唯一变量分母D严格为正。

**所属与公理。** 实际模块owner为Shao.C2.AuxiliarySourceGaussian，kind=theorem；递归公理恰为propext、Classical.choice、Quot.sound。完整导出已逐字阅读：
```text
TARGET_DECL Shao.C2.AuxiliarySourceGaussian.auxiliary_rare_threshold_gaussian_geometry KIND theorem AXIOMS [propext,
 Classical.choice,
 Quot.sound]
ACTUAL_TYPE ∀ (x : Real)
  (hx : @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) x),
  have a : Real :=
    Real.sqrt
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
        (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
            (@OfNat.ofNat.{0} Real (nat_lit 9)
              (@instOfNatAtLeastTwo.{0} Real (nat_lit 9) Real.instNatCast
                (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))))))
            (@HPow.hPow.{0, 0, 0} Real Nat Real
              (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid))) x
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
          (@OfNat.ofNat.{0} Real (nat_lit 4)
            (@instOfNatAtLeastTwo.{0} Real (nat_lit 4) Real.instNatCast
              (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))))
        (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)));
  have y : Real :=
    @HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) a
      (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
        (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (@OfNat.ofNat.{0} Real (nat_lit 100)
            (@instOfNatAtLeastTwo.{0} Real (nat_lit 100) Real.instNatCast
              (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 99) (instOfNatNat (nat_lit 99)))
                (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 98) (instOfNatNat (nat_lit 98)))))))
          (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
            (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) x)));
  And (@LE.le.{0} Real Real.instLE x y)
    (And
      (@LE.le.{0} Real Real.instLE y
        (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
            (@OfNat.ofNat.{0} Real (nat_lit 3)
              (@instOfNatAtLeastTwo.{0} Real (nat_lit 3) Real.instNatCast
                (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
            x)
          (@OfNat.ofNat.{0} Real (nat_lit 2)
            (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
              (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))))
      (@LE.le.{0} Real Real.instLE
        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
          (@HPow.hPow.{0, 0, 0} Real Nat Real
            (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
            (@HDiv.hDiv.{0, 0, 0} Real Real Real
              (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                (@OfNat.ofNat.{0} Real (nat_lit 3)
                  (@instOfNatAtLeastTwo.{0} Real (nat_lit 3) Real.instNatCast
                    (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                      (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
                x)
              (@OfNat.ofNat.{0} Real (nat_lit 2)
                (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                  (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                    (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))))
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@HPow.hPow.{0, 0, 0} Real Nat Real
            (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid))) y
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
        (@OfNat.ofNat.{0} Real (nat_lit 2)
          (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
            (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
              (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))))
```

### Shao.C2.AuxiliarySourceGaussian.auxiliary_rare_threshold_gaussian_tail

源位置：47–89行。判定：**CORRECT**。

**精确语义。** 对每个实数x≥1，原阈值y=√(9x²/4−1)−1/[100(1+x)]满足实际标准正态尾概率Ψ(y)≤12Ψ(3x/2)。常数12与x无关。

**原文对应。** 直接证明supplement5135–5136的Mills比较。Shao.standardNormalTail为实际gaussianReal 0 1在Ioi上的测度取实数值，与原文Ψ=1−Φ一致；既有GaussianTail接受证据复用，不把待证的高斯比较假设成输入。

**实际类型。** 完整实际类型只量化x:Real与hx:1≤x；let y正是源阈值，结论为Shao.standardNormalTail y≤12*Shao.standardNormalTail(3*x/2)。没有抽象tail函数、外部oracle、概率上界前提或只对有限x的结论。

**完整证明审查。**

1. 设u=3x/2。前一新定理给x≤y≤u及u²−y²≤2；由x≥1得y≥0、u≥0，所以接受接口standardNormalTail_ratio_bound u y hu hy的两个实数非负条件均成立。

2. 1+y>0且1+u≥0，故R=(1+u)/(1+y)≥0。交叉乘正分母，把R≤2约化为1+3x/2≤2(1+y)，由y≥x和x≥0成立。这里没有零分母或负数除法翻向问题。

3. 原生Real.exp_bound_div_one_sub_of_interval在1/2满足0≤1/2<1时给exp(1/2)≤1/(1−1/2)=2。exp_add给exp1=exp(1/2)²，结合exp(1/2)>0得exp1≤4。这不是未证明的exp1≤4数值断言。

4. u²−y²≤2给(u²−y²)/2≤1，指数单调性得exp((u²−y²)/2)≤exp1≤4。指数单调性无额外正指数条件；真实指数本身恒正。

5. 接受的实际Mills比值接口给Ψ(y)≤(4/3)R exp((u²−y²)/2) Ψ(u)。R、指数、Ψ(u)及4/3均非负；源中hRatio0、hTail0和exp正性足以合法地逐因子放大。

6. 于是右端≤(4/3)*2*4*Ψ(u)=(32/3)Ψ(u)≤12Ψ(u)，最后一步使用Ψ(u)≥0。convert/ring只统一同一实际接口的代数表达；原无用ring及sequencing警告保留，不影响已闭合证明。

**消费接口。** new geometry theorem at exact same x/hx；Shao.standardNormalTail actual definition；Shao.standardNormalTail_ratio_bound(u,y,0≤u,0≤y)；Shao.standardNormalTail_basic.2.2.1 u positivity；Real.exp_bound_div_one_sub_of_interval；Real.exp_add；Real.exp_le_exp；Real.exp_pos。

**边界。** x=1由相同非严格比较覆盖；y≥x≥1保证所有分母正；未要求除以Ψ(u)；尾值非负已明确支付乘法方向；平方差只需上界，未偷偷加入未声明的绝对差界或渐近范围；12为充分统一常数，不声称最优。

**所属与公理。** 实际模块owner为Shao.C2.AuxiliarySourceGaussian，kind=theorem；递归公理恰为propext、Classical.choice、Quot.sound。完整导出已逐字阅读：
```text
TARGET_DECL Shao.C2.AuxiliarySourceGaussian.auxiliary_rare_threshold_gaussian_tail KIND theorem AXIOMS [propext,
 Classical.choice,
 Quot.sound]
ACTUAL_TYPE ∀ (x : Real)
  (hx : @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) x),
  have y : Real :=
    @HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
      (Real.sqrt
        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
          (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
              (@OfNat.ofNat.{0} Real (nat_lit 9)
                (@instOfNatAtLeastTwo.{0} Real (nat_lit 9) Real.instNatCast
                  (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
                    (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))))))
              (@HPow.hPow.{0, 0, 0} Real Nat Real
                (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid))) x
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
            (@OfNat.ofNat.{0} Real (nat_lit 4)
              (@instOfNatAtLeastTwo.{0} Real (nat_lit 4) Real.instNatCast
                (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))))
          (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))))
      (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
        (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (@OfNat.ofNat.{0} Real (nat_lit 100)
            (@instOfNatAtLeastTwo.{0} Real (nat_lit 100) Real.instNatCast
              (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 99) (instOfNatNat (nat_lit 99)))
                (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 98) (instOfNatNat (nat_lit 98)))))))
          (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
            (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) x)));
  @LE.le.{0} Real Real.instLE (Shao.standardNormalTail y)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@OfNat.ofNat.{0} Real (nat_lit 12)
        (@instOfNatAtLeastTwo.{0} Real (nat_lit 12) Real.instNatCast
          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 11) (instOfNatNat (nat_lit 11)))
            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10)))))))
      (Shao.standardNormalTail
        (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
            (@OfNat.ofNat.{0} Real (nat_lit 3)
              (@instOfNatAtLeastTwo.{0} Real (nat_lit 3) Real.instNatCast
                (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
            x)
          (@OfNat.ofNat.{0} Real (nat_lit 2)
            (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
              (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))))))
```

### Shao.C2.AuxiliaryCenteredProductLaw.auxiliary_centered_product_law_and_endpoint

源位置：10–52行。判定：**CORRECT**。

**精确语义。** 任意实数概率测度rho、任意n:Nat及mu:Real，chi=map(z↦z−mu)rho，P=pi rho、Pc=pi chi。真实逐坐标平移T(v)i=v_i−mu满足map T P=Pc；并对所有实数y，P.real{y√energy(Tv)≤|prefixSum(Tv,n)|}=Pc.real{y√energy(w)≤|prefixSum(w,n)|}。

**原文对应。** 对应supplement5107–5111/5123–5138中心律及其端点事件的真实分布传输。mu是任意平移参数，取mu=mu_s时即可消费；本单元不证明mu是期望，不证明中心矩界，不调用尚未核验的161。能量始终为实际中心坐标平方和，未换成方差或期望能量。

**实际类型。** 完整实际类型含rho:Measure Real、唯一概率类型类IsProbabilityMeasure rho、n:Nat和mu:Real；三层let为实际map/pi/pi；结论为测度精确相等与forall y:Real的Measure.real事件精确相等。Path n是Fin n→Real；prefixSum w n是全部n项和。无n>0、可积性、矩、方差、对称、无原子或尾概率条件。

**完整证明审查。**

1. 平移z↦z−mu可测；X_i(v)=v_i−mu由平移与可测坐标投影复合而可测。chi和P的概率实例合法：rho为概率，map与有限pi保概率；虽然当前map实例也有非可测回退分支，本证明明确给出了平移可测性，所有后续map公式使用真正的推前分支。

2. 原生iIndepFun_pi对每个可测平移函数给出P上的真实坐标独立性，精确地实例化为i↦(v↦v_i−mu)。要求的Fin n有限性与各rho概率性均具备；没有只假定同分布就偷用独立性。

3. 每个i的边缘律由Measure.map_map hShift (measurable_pi_apply i)的反向等式分解为平移推前后的坐标边缘；measurePreserving_eval的map_eq把边缘替换成rho，结果正是chi。IdentDistrib结构的两项AE可测性和第三项map等式均完整供应；map_id将右侧id推前化为chi。

4. 接受的FiniteIID.iid_samplePath_map_eq_pi hX hIndep hLaw要求源概率P、目标概率chi及每项可测、独立、同律，以上全部已支付。其samplePath X在定义上就是T，输出的pi chi就是Pc，得到的是measure等式，不是只对某个统计量的近似同律。

5. 目标集合A={w| y√energy w≤|prefixSum w n|}对任意实数y可测：measurable_energyWall y与continuous_prefixSum n的绝对值可测，measurableSet_le保留弱不等式。没有借助边界零测性或分布连续性。

6. Measurable.of_eval hX给真实路径映射T可测；对map T P=Pc取q↦q A，用Measure.map_apply hCenter hA得到P(T⁻¹A)=Pc(A)。T⁻¹A按定义正是左边中心化原路径事件，最后congrArg ENNReal.toReal给出目标真实概率等式；没有用toReal的逆向注入性或非法无穷减法。两侧本来都是概率测度，语义上确为有限概率。

**消费接口。** Shao.Path n = Fin n→Real；Shao.energy actual squared coordinate sum；Shao.prefixSum at n actual full sum；Shao.Probability.iid_samplePath_map_eq_pi and samplePath；Shao.measurable_energyWall y；Shao.continuous_prefixSum n；native iIndepFun_pi；native measurePreserving_eval；native IdentDistrib structure；Measure.map_map；Measure.map_id；Measure.map_apply；Measurable.of_eval。

**边界。** n=0：所有坐标要求为空，空乘积在唯一空路径上为概率1；energy和fullsum均0，forall y的弱事件为全空间，传输仍精确；零能量：0≤|0|的等号事件保留，没有除以sqrt energy或移除全零样本；rho可有原子，mu任意，y可负/零/正；可测集合传输完全不使用端点零测性；中心化可生成零方差律；声明允许，且不借此声称C1输入合法；所有等号边界使用≤，不是严格事件的AE替代。

**所属与公理。** 实际模块owner为Shao.C2.AuxiliaryCenteredProductLaw，kind=theorem；递归公理恰为propext、Classical.choice、Quot.sound。完整导出已逐字阅读：
```text
TARGET_DECL Shao.C2.AuxiliaryCenteredProductLaw.auxiliary_centered_product_law_and_endpoint KIND theorem AXIOMS [propext,
 Classical.choice,
 Quot.sound]
ACTUAL_TYPE ∀ (rho : @MeasureTheory.Measure.{0} Real Real.measurableSpace)
  [@MeasureTheory.IsProbabilityMeasure.{0} Real Real.measurableSpace rho] (n : Nat) (mu : Real),
  have chi : @MeasureTheory.Measure.{0} Real Real.measurableSpace :=
    @MeasureTheory.Measure.map.{0, 0} Real Real Real.measurableSpace Real.measurableSpace
      (fun (z : Real) => @HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) z mu) rho;
  have P :
    @MeasureTheory.Measure.{0} (Shao.Path n)
      (@MeasurableSpace.pi.{0, 0} (Fin n) (fun (a : Fin n) => Real) fun (a : Fin n) => Real.measurableSpace) :=
    @MeasureTheory.Measure.pi.{0, 0} (Fin n) (fun (a : Fin n) => Real) (Fin.fintype n)
      (fun (a : Fin n) => Real.measurableSpace) fun (x : Fin n) => rho;
  have Pc :
    @MeasureTheory.Measure.{0} (Shao.Path n)
      (@MeasurableSpace.pi.{0, 0} (Fin n) (fun (a : Fin n) => Real) fun (a : Fin n) => Real.measurableSpace) :=
    @MeasureTheory.Measure.pi.{0, 0} (Fin n) (fun (a : Fin n) => Real) (Fin.fintype n)
      (fun (a : Fin n) => Real.measurableSpace) fun (x : Fin n) => chi;
  And
    (@Eq.{1}
      (@MeasureTheory.Measure.{0} ((i : Fin n) → Real)
        (@MeasurableSpace.pi.{0, 0} (Fin n) (fun (i : Fin n) => Real) fun (a : Fin n) => Real.measurableSpace))
      (@MeasureTheory.Measure.map.{0, 0} (Shao.Path n) ((i : Fin n) → Real)
        (@MeasurableSpace.pi.{0, 0} (Fin n) (fun (a : Fin n) => Real) fun (a : Fin n) => Real.measurableSpace)
        (@MeasurableSpace.pi.{0, 0} (Fin n) (fun (i : Fin n) => Real) fun (a : Fin n) => Real.measurableSpace)
        (fun (v : Shao.Path n) (i : Fin n) =>
          @HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) (v i) mu)
        P)
      Pc)
    (∀ (y : Real),
      @Eq.{1} Real
        (@MeasureTheory.Measure.real.{0} (Shao.Path n)
          (@MeasurableSpace.pi.{0, 0} (Fin n) (fun (a : Fin n) => Real) fun (a : Fin n) => Real.measurableSpace) P
          (@Set.ofPred.{0} (Shao.Path n) fun (v : Shao.Path n) =>
            @LE.le.{0} Real Real.instLE
              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) y
                (Real.sqrt
                  (@Shao.energy n fun (i : Fin n) =>
                    @HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) (v i) mu)))
              (@abs.{0} Real Real.lattice Real.instAddGroup
                (@Shao.prefixSum n
                  (fun (i : Fin n) => @HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) (v i) mu)
                  n))))
        (@MeasureTheory.Measure.real.{0} (Shao.Path n)
          (@MeasurableSpace.pi.{0, 0} (Fin n) (fun (a : Fin n) => Real) fun (a : Fin n) => Real.measurableSpace) Pc
          (@Set.ofPred.{0} (Shao.Path n) fun (w : Shao.Path n) =>
            @LE.le.{0} Real Real.instLE
              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) y (Real.sqrt (@Shao.energy n w)))
              (@abs.{0} Real Real.lattice Real.instAddGroup (@Shao.prefixSum n w n)))))
```

### Shao.C2.AuxiliaryMarkedDeletion.auxiliary_marked_terminal_deletion

源位置：8–49行。判定：**CORRECT**。

**精确语义。** 任意n:Nat、真实剩余路径w:Path n、任意实数v和x≥1，若完整原能量F=v²+energy w>0，且(3/2)x√F≤|v+prefixSum w n|，则剩余真实能量T=energy w>0，并有√((9/4)x²−1)√T≤|prefixSum w n|。

**原文对应。** 逐点对应supplement5141–5147删除标记坐标v后T′、d′的真实弱事件包含。v与w正是一个标记值及剩余路径，完整能量和完整和明确写成v²+T与v+d；不需要给任意抽象T,d外加“零能量蕴含零和”公理。仅形式化这一有限路径原语，不占用既有residual候选作者的加权记录或网格数学范围。

**实际类型。** 完整pp.all实际类型保持{n:Nat}、w:Path n、v x:Real、hx:1≤x、hFull:0<v²+energy w和同一弱完整端点hCross；结论是实际剩余energy严格正与原v_x阈值的弱剩余端点。没有n>0、v符号、iid、矩、概率、原子性或额外能量/和联系前提。

**完整证明审查。**

1. FinitePath.energy_nonneg给T≥0。若T不正则T=0，接受接口prefixSum_eq_zero_of_energy_eq_zero直接给实际d=0。F>0在T=0时给v≠0、|v|>0；sqrt(v²)=|v|对任意v成立。

2. T=d=0后，hCross变成(3/2)x|v|≤|v|。将hx:1≤x乘以非负|v|，再用|v|>0，得到(3/2)|v|≤|v|的矛盾。因此T>0是从真实有限路径推出来的，而不是声明中偷偷加入的零能量条件。

3. x≥1给((9/4)x²−1)≥0。完整hCross左侧的(3/2)、x、sqrt F均非负，故pow_le_pow_left₀可合法平方，Real.sq_sqrt hFull.le与sq_abs给(9/4)x²F≤(v+d)²。没有对带符号和直接平方保序。

4. 精确二阶Cauchy恒等式：(v²+T)(T+d²)−T(v+d)²=(vd−T)²≥0。故T(v+d)²≤F(T+d²)，只使用真实T和d，不用iid、随机变量或经验方差。

5. 把已平方hCross乘以T≥0，连上Cauchy不等式，得到(9/4)x²TF≤F(T+d²)。mul_le_mul_iff_of_pos_right hFull取消的因子恰是已证明严格正的完整能量F，未取消可能为零的v、d、x或抽象剩余能量。

6. 取消后得到((9/4)x²−1)T≤d²。两个sqrt因子和|d|都非负；sq_le_sq₀加上被开方量非负与T≥0，把该平方不等式恢复为要求的弱阈值事件。所有≤边界保留。

**消费接口。** Shao.energy_nonneg actual energy；Shao.prefixSum_eq_zero_of_energy_eq_zero actual path and fullsum；Real.sqrt_sq_eq_abs valid for every sign of v；pow_le_pow_left₀ with nonnegative left side；mul_le_mul_of_nonneg_left with T≥0；mul_le_mul_iff_of_pos_right with F>0；Real.sq_sqrt with both radicands nonnegative；sq_le_sq₀ with both sides nonnegative；unit160 exact imported source/object; no unit160 proof replay。

**边界。** n=0时T=d=0，因此hFull与hCross不能同时成立；泛化定理为正确的条件蕴含，未声称存在该事件；x=1仍有3x/2>1；无严格阈值偷换；v可正、负或0；sqrt(v²)=|v|覆盖全部符号；F>0是原文完整事件的T_t>0，若去掉该条件全零样本会击穿T>0结论；本证明保留该必要原文条件；剩余T=0情况被真实路径接口证明不可能，所有非零情况下的等号端点均保留。

**所属与公理。** 实际模块owner为Shao.C2.AuxiliaryMarkedDeletion，kind=theorem；递归公理恰为propext、Classical.choice、Quot.sound。完整导出已逐字阅读：
```text
TARGET_DECL Shao.C2.AuxiliaryMarkedDeletion.auxiliary_marked_terminal_deletion KIND theorem AXIOMS [propext,
 Classical.choice,
 Quot.sound]
ACTUAL_TYPE ∀ {n : Nat} (w : Shao.Path n) (v x : Real)
  (hx : @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) x)
  (hFull :
    @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
      (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
        (@HPow.hPow.{0, 0, 0} Real Nat Real
          (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid))) v
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@Shao.energy n w)))
  (hCross :
    @LE.le.{0} Real Real.instLE
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
            (@OfNat.ofNat.{0} Real (nat_lit 3)
              (@instOfNatAtLeastTwo.{0} Real (nat_lit 3) Real.instNatCast
                (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
            (@OfNat.ofNat.{0} Real (nat_lit 2)
              (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))))
          x)
        (Real.sqrt
          (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
            (@HPow.hPow.{0, 0, 0} Real Nat Real
              (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid))) v
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
            (@Shao.energy n w))))
      (@abs.{0} Real Real.lattice Real.instAddGroup
        (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) v (@Shao.prefixSum n w n)))),
  And
    (@LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
      (@Shao.energy n w))
    (@LE.le.{0} Real Real.instLE
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Real.sqrt
          (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
              (@HDiv.hDiv.{0, 0, 0} Real Real Real
                (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                (@OfNat.ofNat.{0} Real (nat_lit 9)
                  (@instOfNatAtLeastTwo.{0} Real (nat_lit 9) Real.instNatCast
                    (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
                      (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))))))
                (@OfNat.ofNat.{0} Real (nat_lit 4)
                  (@instOfNatAtLeastTwo.{0} Real (nat_lit 4) Real.instNatCast
                    (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                      (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))))
              (@HPow.hPow.{0, 0, 0} Real Nat Real
                (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid))) x
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
            (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))))
        (Real.sqrt (@Shao.energy n w)))
      (@abs.{0} Real Real.lattice Real.instAddGroup (@Shao.prefixSum n w n)))
```

### Shao.C2.AuxiliaryMarkedDeletion.auxiliary_marked_terminal_deletion._simp_1_1

源位置：25–25行。判定：**CORRECT**。

**精确语义。** 对任意宇宙层级类型α及Preorder α、任意x:α，命题x<x等于False。它是主定理零能量反证中simp产生的标准重写定理。

**原文对应。** 源25行simp only中使用lt_self_iff_false，把假设0<0重写为False；生成项只承担这个逻辑化简，不新增概率或原文数学前提。

**实际类型。** 完整实际类型为∀{α:Type u_2}[Preorder α](x:α), Eq Prop (x<x) False。该式不是False本身，不是任意α上的无条件矛盾，也不暗含LinearOrder或实数特殊性。

**完整证明审查。**

1. 已读取原生Order.Basic在Preorder作用域中的完整lt_self_iff_false：其证明为⟨lt_irrefl x, False.elim⟩，故x<x↔False对全部所量化对象成立。

2. simp把该双向命题经命题外延性propext转成命题相等，以便改写主反证的hFull。该生成证明义务的逻辑内容和源中的实际使用均完整核对。

3. 原实际owner递归公理集合只含propext，与上述构造一致；不从生成名称猜测证明正确，也不把它漏计成公开头之外的零声明。

**消费接口。** Preorder strict order irreflexivity；lt_self_iff_false under Preorder；propext transforms iff to Prop equality。

**边界。** 任意α和宇宙层级；不依赖非空实例，因为显式量化x；主证明的实数0实例没有特殊额外前提；它属于生成定理，不是私有源定理或全局定义值。

**所属与公理。** 实际模块owner为Shao.C2.AuxiliaryMarkedDeletion，kind=theorem；递归公理恰为propext。完整导出已逐字阅读：
```text
TARGET_DECL Shao.C2.AuxiliaryMarkedDeletion.auxiliary_marked_terminal_deletion._simp_1_1 KIND theorem AXIOMS [propext]
ACTUAL_TYPE ∀ {α : Type u_2} [inst : Preorder.{u_2} α] (x : α),
  @Eq.{1} Prop (@LT.lt.{u_2} α (@Preorder.toLT.{u_2} α inst) x x) False
```

## 实际接口和旧证据的复用

接受公共映射SHA256 e4f13313c11ef8b2b03c1b4b5ede0068a7400a7f5f96c065b738b88719f9d4f9中选取FinitePath、GaussianTail、MeasurablePath、FiniteIID，并绑定TruncationIntegrals的实际旧依赖。公共库本地只读源、C12当前源/导入对象与已接受integration-bearing-v83源/原对象均精确匹配。GaussianTail的真正尾定义及完整ratio/basic签名、FiniteIID完整联合律接口及其概率类型类、MeasurablePath真实energyWall/continuous_prefixSum和FinitePath的Path/energy/fullsum定义均已读。旧证明不因本次消费重审或重跑。

160导入已接受AuxiliarySourceEvent作为上下文，独立证明标量界；其9*x²/4与旧(9/4)*x²为同一实数代数式。162导入已接受AuxiliaryOwnC1Budget作为上下文，使用其传递导入的真实路径可测接口。164导入本轮160的精确源码/对象，仅消费真实energy非负及零能量下prefixSum为零等旧公共接口；其x阈值与160/原文一致。161/163及待核验C1概率消费模块均未导入。旧源/证明证据在精确源与对象绑定后复用。

原生接口额外读到完整侧条件：exp_bound在[0,1)给exp(t)≤1/(1−t)；iIndepFun_pi在有限索引及各边缘概率下，对每个AE可测函数给真实乘积空间独立性；measurePreserving_eval要求各边缘为概率并给投影真实边缘；map_map要求两个函数可测；map_apply要求函数可测和目标集合可测；IdentDistrib结构含两侧AE可测性与推前等式。sq_le_sq₀要求两侧非负；Real.sq_sqrt要求被开方量非负。这些实际条件在所有新证明的使用处均已支付。所有10份所读mathlib文件均逐字等于钉住Git对象；共享目录的历史local-changes警告保留，不凭警告猜测这些接口发生变化。

150–159五份既有独立审阅的parent-acceptance均为QUALIFIED，已核对各封印报告哈希；本轮只检查精确依赖源/对象与新消费接口、交互。158/159接受SHA674872c472c907628c5f6e9ad3439fc633349e135b10e381380c2e760d8647b6，156/157接受SHA348d90bec438d7c8a42261982fd057fd7acb185574a489b6838e67272321ca89，其余逐项列于JSON，不重复旧数学验收。

## 内核、递归公理与失败账

完整阅读的OwnedAudit不是只查公开名字：遍历env.constants.toList，用env.getModuleIdxFor?及header.moduleNames判定实际模块owner，对每一个目标owner调用Lean.collectAxioms，再逐项检查标准白名单。publicNames只核对公开定理覆盖，未用于缩小整体owner审计。实际导入后2+1+2个owner全部是这五个定理，包含164的一个生成化简定理，没有遗漏私有、生成声明、实例或全局定义。pp.all完整类型导出无省略符、未解决元变量或sorryAx；定义值导出确实为空。

已完整读取既有合格证据中的钉住Lean CollectAxioms源码，SHA256 b39bd22253a76816ee6d24284e69674d0b491be343fd71f9ee9376833d1485f6，并与当前工具链逐字绑定。collect遍历定义、定理和opaque常量的类型及值，递归追踪依赖、收集axiomInfo；导入项使用已预计算的传递公理集合，privateEnv可见所需证明体。Environment.getModuleIdxFor?读取const2ModIdx，钉住Environment源码SHA256 e7b97a029388b84c3f69c58e8df9e30064415e34a863781e1843e8c6c15e0e8f及实际接口也已完整核对。

收集器会检查定理/定义/opaque的类型和证明/值，递归追踪依赖；导入声明可用序列化时预先计算的传递公理集合，使用privateEnv访问所需证明体。不能把“使用导入集合”误读为“没有传递检查”。三个原审计实际均AUDIT_EXIT=0，五个owner的公理均只含白名单，164的生成项仅用propext。未新增axiom、unsafe、sorry、admit或native_decide。

160的attempt001是唯一尝试，KERNEL_EXIT=0；完整原命令使用CPU14–17、c12-heavy.lock、-M8192 -j4。无用ring和不可达sequencing警告原样保留。162的attempt001 KERNEL_EXIT=1，精确失败为多余rfl导致No goals to be solved，以及把measurable_prefixSum当作具有abs字段；失败源SHA d8d82c5c36e1c8da94d77901d4049844d6e329992d3408388119b369aa4204a8。attempt002仅移除该rfl，并用continuous_prefixSum n的abs.measurable支付同一集合可测性；冻结头不变，KERNEL_EXIT=0、全1owner审计PASS。两条letI风格警告保留。失败不是数学反例；第二稿完整证明仍由本次独立审查确认。

164的唯一attempt001 KERNEL_EXIT=0，完整命令与同一配额一致；全2owner原审计PASS，无失败或证明/风格警告，仅保留原共享mathlib advisory。新增28项只读服务器哈希全部匹配，复用本轮160精确源/对象，未回放任何旧成功门。

三个finisher均已完整阅读，只用于理解证据溯源，未执行。它们验证源快照、对象与实际导入对象相等，提取完整实际类型及空值，校验退出标记和owner数量；回执历史PENDING状态原样保留，独立结论在本新目录单独表达。

本次只读查询修正共六类，完整保存在query-mistakes.json与原观测文件：错误REGISTRY字段投影、泛名搜索过宽、sq_le_sq₀的声明关键字、两个sqrt猜测路径、map实例的命名拼写，以及一次过宽历史字段预览。均未触发Lean、服务器写入或改变任何数学声明；后续通过精确路径/签名读取修正。

## 交付、限制与父实例资格认定

数学判定为CORRECT；现有精确源版本的内核和全所属递归公理证据通过且可复用。运行轨迹、逐owner完整审阅、冻结、失败账、初始与终态哈希观测、确定性覆盖检查、最后释放封印共同组成可核验工件。父实例还需完成其资格认定并在独立父属文件记录；不得直接修改本次已封印报告。

160只支付原y_x的几何和高斯尾比较，162只支付真实乘积律和端点概率传输，164只支付真实标记坐标删除的逐点弱事件包含。161/163未核验且不在依赖中，原C1概率输入的消费、原raw事件推送、低能量并集与完整rare suffix、加权记录/网格范围仍不由这三个单元独立结案。C2/C12保持OPEN。没有新颖性、最优常数或原根完成的附加主张。
