# U21a 冻结候选：紧倾斜族的平方模缺口与弱 Cramér 传递

状态：FROZEN_FOR_INDEPENDENT_DECLARATION_REVIEW。前一U20b完整208行CORRECT终票已全部读完、接受并精确发布PR153后，才冻结本scope73。尚无本单元Lean源、probe、Audit或新分支。

来源：current/oq3/proofs/r2/report.md343–369，SHA256 572e74aa9c12e2771f5543a5709a2807666eeea0a4076e7a3263e5c7bcf87f55。原目标C的有界倾斜稳定性，特别是(20)/(22)和统一常数m²c/2。原(21)是来源的一条证明路线，本目标直接要求实际平方模缺口和真实特征函数界；可从已验收真实测度下界的更强模界推导，不将未证明的cosine恒等式作为输入。

生产模块：Shao.OQ3.CompactTiltWeakCramer；仅 namespace Shao.OQ3，0公开定义、1公开完整定理。精确imports：

```lean
import Shao.OQ3.CharacteristicMeasureDomination
import Mathlib.Analysis.SpecialFunctions.Pow.Real
```

open MeasureTheory，open scoped ENNReal NNReal，noncomputable section。完整公开TYPE冻结如下，禁止缺合取或改量词：

```lean
theorem exists_compact_tilted_weakCramer_bound (mu : Measure ℝ)
    [IsProbabilityMeasure mu] (M : ℝ) (hM : 0 ≤ M)
    (hb : ∀ᵐ x ∂mu, |x| ≤ M) (K : Set (ℝ × ℝ)) (hK : IsCompact K)
    (u0 v0 beta c R : ℝ) (hc : 0 < c)
    (hWC : ∀ xi eta : ℝ, R < Real.sqrt (xi ^ 2 + eta ^ 2) →
      ‖jointCharacteristic (mu.tilted (fun x => u0 * x + v0 * x ^ 2)) xi eta‖ ≤
        1 - c * Real.rpow (Real.sqrt (xi ^ 2 + eta ^ 2)) (-beta)) :
    let mu0 : Measure ℝ := mu.tilted (fun x => u0 * x + v0 * x ^ 2)
    ∃ m : ℝ, 0 < m ∧ m ≤ 1 ∧ 0 < m ^ 2 * c / 2 ∧
      ∀ p ∈ K,
        (ENNReal.ofReal m • mu0 ≤
          mu.tilted (fun x => p.1 * x + p.2 * x ^ 2)) ∧
        (∀ xi eta : ℝ,
          m ^ 2 * (1 - ‖jointCharacteristic mu0 xi eta‖ ^ 2) ≤
            1 - ‖jointCharacteristic
              (mu.tilted (fun x => p.1 * x + p.2 * x ^ 2)) xi eta‖ ^ 2) ∧
        ∀ xi eta : ℝ, R < Real.sqrt (xi ^ 2 + eta ^ 2) →
          ‖jointCharacteristic
            (mu.tilted (fun x => p.1 * x + p.2 * x ^ 2)) xi eta‖ ≤
              1 - (m ^ 2 * c / 2) *
                Real.rpow (Real.sqrt (xi ^ 2 + eta ^ 2)) (-beta)
```

量词/语义门：固定一个真实概率mu及同一紧K；M、u0/v0、beta/c/R固定于全部p和频率之外；单个m在全部p和频率之外、0<m≤1。mu0及每个倾斜均为mu真实quadratic tilt，真实exp可积/正配分须由有界mu生产。不得把概率实例或测度下界当新caller输入。hWC是sourceC正确的单点弱Cramér输入，输出是统一同指数、同截断R的族界和精确正新常数m²c/2；不得把整个族的目标界放进前提。

sqrt(xi²+eta²)为真实二维欧氏频率范数，不偷换成Prod的max范数。Real.rpow基数非负；在源beta>0、R>0时即通常||u||^-beta。本代数传递对任意实beta/R成立，因此不额外要求它们正；应用原根时保留原beta/R正性，也不声称beta非正是原弱Cramér条件。theta0不必属于K，K允许空，定理更一般且不妨碍原用途。m≤1通过min选择，与输出同一个测度下界一致，不能混用两个不同m。

承重/剩余：消除原C当前缺失的actual特征函数平方模缺口(22)与标准统一弱Cramér常数；直接供根B的实际倾斜族WC部分和原C组装。矩阵标准化的统一范数比较/频率变换及原B Edgeworth/格胞/远区概率链另需证明。共享canonical全局率接口仍由root实现验收，不是本单元依赖；根A适配稍后。原A/B/C/D均保持OPEN，任何根关闭由完整适配及根验收决定。

已做一次候选静态physical/public import图：15个旧已验收Shao/2418Mathlib物理，public2402内部+189external，无source/olean缺失；canonical15=2b038a74d11a67ef91fcaceaf4dd5c3fa88de4757967e5e2d9d555851cf02bb5。15源与root v37收据元数据全部一致，不重复图/稳定缓存/pins/smoke。没有本scope Lean执行。独立声明审查须自行核实来源及真实API适用，不依作者路线自认证。

执行/验收门：声明最终报告hash核实且整份读完后才允许正常新建owned分支（适合已接受root checkpoint，本单元无148/151/152/153依赖），实现完整TYPE。所有Lean只在指定服务器CPU14–17、native8192MiB/j4/autoImplicit=false，首次完整成功后不重复。实际module-owner全常量TYPE/公理审计，白名单propext/Classical.choice/Quot.sound；再由同唯一独立审查员完整proof审查并整份读最终报告后才接受/commit/PR。root独占shared定义/cache/pins/integration/merge/rebase/retarget，保留153/152/151/148/146/144冻结heads，外部CPU0–9/80GiB不动。
