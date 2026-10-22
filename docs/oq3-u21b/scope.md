# U21b 冻结候选：实际抛物线律的仿射标准化与一致弱Cramér传递

状态：FROZEN_FOR_INDEPENDENT_STATEMENT_REVIEW。原A完整326行CORRECT终票全读后PR161发布；U20e完整335行CORRECT终票全读后PR163发布。当前163branch d4a9ffc332fe8247b121dc3298c322c52ac1d26b clean，无本单元Lean源/probe/Audit/newbranch。root v39§7原C尚缺矩阵标准化和完整稳定性，本节点直接补频率/平移/常数传递；不把同sourceP的局部逆当一般C替代。

来源：R2 report.md38–60的谱假设(2)、§2中Y=Delta^(-1/2)(W-m)后“线性标准化不改变weak-Cramér指数”，以及343–373§5(20)–(22)后协方差标准化只按(2)改变常数；R2 SHA572e74aa9c12e2771f5543a5709a2807666eeea0a4076e7a3263e5c7bcf87f55。当前PR159已实现实际紧倾斜族未标准化WC，待root；本单元先给独立通用仿射传递，不依赖159/161/163叶。下一完整C消费者须将A绑定实际协方差逆平方根（或明确证明等价的白化），由实际谱(2)消去本TYPE显式L/U频率比较，不能把这些输入当输出或据本节点宣称C闭合。

模块Shao.OQ3.AffineWeakCramer，namespace Shao.OQ3，0公开定义/2完整公开THM。精确imports：

```lean
import Shao.OQ3.JointNonlattice
import Mathlib.Data.Matrix.Mul
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
```

open MeasureTheory，open scoped Matrix BigOperators，noncomputable section。完整TYPE如下：

```lean
theorem affine_parabola_characteristic_factor (mu : Measure ℝ)
    (A : Matrix (Fin 2) (Fin 2) ℝ) (b : Fin 2 → ℝ) (xi eta : ℝ) :
    let Y : ℝ → (Fin 2 → ℝ) := fun x => A *ᵥ (![x, x ^ 2] - b)
    let nu : Measure (Fin 2 → ℝ) := mu.map Y
    let xiA : ℝ := xi * A 0 0 + eta * A 1 0
    let etaA : ℝ := xi * A 0 1 + eta * A 1 1
    let phi : ℂ := ∫ y : Fin 2 → ℝ,
      Complex.exp (((xi * y 0 + eta * y 1 : ℝ) : ℂ) * Complex.I) ∂nu
    phi = Complex.exp (((-(xiA * b 0 + etaA * b 1) : ℝ) : ℂ) * Complex.I) *
      jointCharacteristic mu xiA etaA ∧
      ‖phi‖ = ‖jointCharacteristic mu xiA etaA‖

theorem uniform_weakCramer_of_affine_frequency_bounds
    {ι : Type*} (K : Set ι) (mu : ι → Measure ℝ)
    (hprob : ∀ p ∈ K, IsProbabilityMeasure (mu p))
    (A : ι → Matrix (Fin 2) (Fin 2) ℝ) (b : ι → (Fin 2 → ℝ))
    (L U beta c R : ℝ) (hL : 0 < L) (hU : 0 < U) (hbeta : 0 ≤ beta)
    (hc : 0 < c) (hR : 0 ≤ R)
    (hfreq : ∀ p ∈ K, ∀ xi eta : ℝ,
      L * Real.sqrt (xi ^ 2 + eta ^ 2) ≤
          Real.sqrt ((xi * A p 0 0 + eta * A p 1 0) ^ 2 +
            (xi * A p 0 1 + eta * A p 1 1) ^ 2) ∧
        Real.sqrt ((xi * A p 0 0 + eta * A p 1 0) ^ 2 +
            (xi * A p 0 1 + eta * A p 1 1) ^ 2) ≤
          U * Real.sqrt (xi ^ 2 + eta ^ 2))
    (hWC : ∀ p ∈ K, ∀ xi eta : ℝ, R < Real.sqrt (xi ^ 2 + eta ^ 2) →
      ‖jointCharacteristic (mu p) xi eta‖ ≤
        1 - c * Real.rpow (Real.sqrt (xi ^ 2 + eta ^ 2)) (-beta)) :
    let Y : ι → ℝ → (Fin 2 → ℝ) := fun p x => A p *ᵥ (![x, x ^ 2] - b p)
    let nu : ι → Measure (Fin 2 → ℝ) := fun p => (mu p).map (Y p)
    let Phi : ι → ℝ → ℝ → ℂ := fun p xi eta =>
      ∫ y : Fin 2 → ℝ,
        Complex.exp (((xi * y 0 + eta * y 1 : ℝ) : ℂ) * Complex.I) ∂nu p
    let cA : ℝ := c * Real.rpow U (-beta)
    let RA : ℝ := R / L
    0 < cA ∧ 0 ≤ RA ∧
      ∀ p ∈ K, IsProbabilityMeasure (nu p) ∧
        ∀ xi eta : ℝ, RA < Real.sqrt (xi ^ 2 + eta ^ 2) →
          ‖Phi p xi eta‖ ≤
            1 - cA * Real.rpow (Real.sqrt (xi ^ 2 + eta ^ 2)) (-beta)
```

真实对象门：Y是实际同一个实样本x的(X,X²)先平移再乘同矩阵A，nu是实际Measure.map像测度，Phi是这个真实二维向量律的特征积分，不是自由复杂数族／另选概率律。第一个THM允许任意mu且不假设概率，因Y连续可测、相位连续可测及原库integral_map/固定常数积分线性给无条件实际积分身份；模等式来自实相位exp范数1。不能以概率的全定义积分为0绕过可测门。第二THM明确对K内所有mu p要求真概率，并输出实际像律nu p真概率；无须对p联合可测，因不对p积分。

坐标门：u=(xi,eta)作用于AY，原始频率应是Aᵀu，即(xi*A00+eta*A10,xi*A01+eta*A11)，不能漏转置或用A u。平移只贡献exp(-i[(Aᵀu)·b])，保留完整复因子和范数身份。所有半径字面为sqrt(xi²+eta²)的二维Euclidean值，不是Fin2函数空间的默认max范数。

常数/边界门：L/U/c>0、R≥0、beta≥0是显式调用者条件；频率双界也是显式uniform contract，未称已从协方差生产。RA=R/L≥0。在RA<rho时rho>0且L*rho>R，所以下界给rho(Aᵀu)>R≥0；上界和-beta≤0用真实Real.rpow_le_rpow_of_nonpos给(U*rho)^(-beta)≤rho(Aᵀu)^(-beta)，再Real.mul_rpow得到精确cA=c*U^(-beta)>0。不在零频率/零L/零U上非法约分或取负幂，不需beta严格正，保留beta=0边界。K可空、中心b任意、A/p不要求连续；uniform常数在p/频率之外固定，无n依赖。没有beta上界或最优性声称；原B的0<beta<2/5可合法实例化此更一般传递。

承重/剩余：本节点消除原R2§2/§5实际中心化仿射像律的精确特征因子、转置频率、保持指数且给统一radius/c的门；直接消费者是159紧倾斜族WC之后的标准化以及原C/B组合。尚未将A命名或证明为实际Delta^-1/2，未生产谱(2)、均值逆/全族矩/Edgeworth/远域概率；必须后续实际绑定这些对象，不能把hfreq隐藏成已消去前提。所有原根账仍OPEN；原A161等待root正式验收，C本节点非最终完整根。

环境：小Shao-only DFS由JointNonlattice得到5正式接受源（AtomProjection/FiniteConstraints/JointNonlattice/SourceStarter/SummableAtoms），hash取已通过RootA74/v39正式字典，canonical5 bc48253cce1ae61632e2f1c21945b41c6f7839c681075d8b9814140e54e3587f，candidate-cache JSON SHA23b224201d8975c529022f788c3556798548943598f46e752d1b3089b10c3864。Mathlib闭图复用已实际通过的旧roots：JointNonlattice旧接受链，Matrix.Mul在接受实际Matrix.mulVec链，Bochner.Basic在已接受integral_div链，Pow.Real为159直接passedseed。新单元只定向核5项目对象+3显式Mathlib对象共8路径全存在；不重扫全Mathlib图或声称有一份新全图计数。沿普通Lake/own单Shao-root，不需额外U20c view；不copy对象/cache/改pins/重复smoke。独立声明审查应核真实公开API和这个复用证据，不凭作者标签推数学。

执行：完整CORRECT声明终票hash核且整份lead读完后才从已接受v39 59a531正常新建owned feat/oq3-affine-weak-cramer；不依赖159/161/163叶，不merge/reset/rebase/retarget或改11关键旧frozenheads。全Lean仅serverCPU14–17/native8192MiB/j4/autoImplicit=false/单heavy；首完整成功不重跑，实际module-owner全部TYPE/所有private+generated/传递公理Audit，随后完整独立proof终票整份lead读完才接受/commit/精确PR。禁sorry/admit/newaxiom/unsafe/native_decide/implemented_by/设置弱化，白名单propext/Classical.choice/Quot.sound；root独占shared/cache/pins/integration。外部CPU0–9/80GiB不动，不新agent/chat/goal，复用sole reviewer lease1。
