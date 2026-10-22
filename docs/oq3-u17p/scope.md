# OQ3-U17p：未来质量选择之前的真实有限前缀律

冻结v1，DECLARATION_REVIEW_PENDING，未批准／未实施。拟 Shao/OQ3/FinitePrefixLaw.lean；imports 精确为 Shao.OQ3.FiniteStageMeasure、Shao.OQ3.PositiveRate；namespace Shao.OQ3，open MeasureTheory Filter，open scoped Matrix Topology BigOperators，noncomputable section，保留两层end。一完整公开定义、两个完整公开目标；定义不另计target，合取不拆分增加节点。

原始目标→R1 113–145的实际有限阶段律与486–550的先见证后未来质量递归。原件SHA3473d34ff20bd0d334b9ef3ea3c3ee167fba4d5cc3a742849820ce54d639e662。剩余关键义务→AdaptiveTailBudget要求对每个合法positivepast生产真实hW，而非先假定一个最终r存在。本模块消除→实际阶段律仅依赖前缀的公开精确身份，以及固定p/q后统一半径下每个正前缀的实际概率／均值／支撑／单点正性门。直接消费者→同一个prefixMass消费O已接受实际26见证；真正U18a提供hcont后，为所有合法前缀生产hW，再用原transfer传至一个固定最终律。P本身不需要hcont，也不宣称hW或diagonal完成。

```lean
def prefixMass (ell : ℝ) (p : Fin 4 → ℝ) (J : ℕ) (u : Fin J → ℝ) : AtomicIndex → ℝ :=
  finiteMass ell p (fun j => if hj : j < J then u ⟨j, hj⟩ else 0) J
```

```lean
theorem finiteMass_eq_prefixMass (ell : ℝ) (p : Fin 4 → ℝ) (J : ℕ)
    (u : Fin J → ℝ) (r : ℕ → ℝ) (hpref : ∀ i : Fin J, r i.val = u i) :
    finiteMass ell p r J = prefixMass ell p J u
```

```lean
theorem exists_source_prefix_radius (p : Fin 4 → ℝ) (q : ℝ)
    (hp : ∀ i, 0 < p i)
    (hc : (constraintMatrix sourceEll) *ᵥ p = constraintTarget q) :
    ∃ eps : ℝ, 0 < eps ∧ ∀ (J : ℕ) (u : Fin J → ℝ),
      (∀ i, 0 < u i) → (∑ i, u i) < eps →
      (∀ i : AtomicIndex, 0 ≤ prefixMass sourceEll p J u i) ∧
      HasSum (prefixMass sourceEll p J u) 1 ∧
      (∫ x : ℝ, normalValue x ∂atomicMeasure (prefixMass sourceEll p J u)) = q ∧
      (∫ x : ℝ, x ∂atomicMeasure (prefixMass sourceEll p J u)) = q / 4 ∧
      (∀ᵐ x ∂atomicMeasure (prefixMass sourceEll p J u),
        x ∈ Set.range (fun i : Fin 4 ⊕ Fin J =>
          stageAtom (fun j : Fin J => addedAtom j.val) i)) ∧
      (∀ i : Fin 4 ⊕ Fin J, 0 < (atomicMeasure (prefixMass sourceEll p J u)).real
        {stageAtom (fun j : Fin J => addedAtom j.val) i})
```

公开定义给真实canonical零延拓有限原子权重：它完全取决于给定ell/p/J/u，不读未来r。第一个目标必须实际证明finiteBase／addedMoment及所有AtomicIndex的精确函数相等；不能把前缀相等当成不同函数的定义相等，也不能调用其他模块不可公开调用的private helper。其ell/p/r不加正性／可和性／未来tail假设，因为该身份是有限前缀的纯代数事实。

第二目标固定实际sourceEll、正p及真实矩阵约束，eps在所有J/u之前。给定任意J（含0）与严格正u、真实有限和小于eps后，输出同一prefixMass的逐点非负和真正HasSum1（据此消费已接受atomicMeasure概率定理），实际EY/EX，AE真实stage范围及每个实际stage原子的真实单点正质量。不得手工输入finiteBase正性／均值／probability／Summable或把真实积分改成有限形式总和冒充。此有限模型目标不需qwindow作为额外假设；未来O消费者仍从固定source starter保留其1<q<103/100。

未来r在此无须被选择；prefix零延拓非负但不处处严格正，不能将只对strictpositive无限序列公开的family接口不加论证地用于它。所有所需半径必须由真正可公开消费的定理取得；不依赖SourceTransferBudgets隐藏在proof内的radius。定义／两个目标均是后续hW所需实际对象与门，不把任意手工满足这些门的w当作本模块结果。仍须将来真正生产同一prefixMass的hcont才能获得无条件26/hW。

声明审查先仅提取并盲译完整DEF body和两个完整TYPE，持久化新报告，之后才scope/R1/actual库与来源／数学／API；机械最后。候选只读闭包11:55:37UTC按多modifier含public meta import重建：7Shao/2384Mathlib物理，public2346Shao/Mathlib+189外部停止叶=2535；源/olean缺0。全部7源码恰已接受O的58项前置子集，canonical相对路径Shao/...lean键、sort_keys=True且separators=(',',':')的compactSHA4219e7cb2734f96de45a8029c06bc5a7cb443c5db41d75699e6c135821f5115b。外部叶内部不声称递归；作者candidatecache/扫描器/实现/未来笔记不能作为reviewer数学依据。

O完整210行独立CORRECT终票已lead全文读后接受，PR131 OPEN精确head7f27bc0a58ec3516f7c490e2054b5031ff1c38b7/baseN91b79f92/6files1commit已核附chat。O旧source/scope/票/receipt不改。其完整hcont仍显式输入。O整票读后12:02:47UTC freshU18a两root及原51项仍缺，root唯一cachewriter；lane继续此独立有限模型承重工作，不下载或重建公共cache。

独立reviewer仅写新声明report及remote副本，不写源/scope/shared/旧票/cache、不Lean/#check/probe/rebuild/spawn/commit/pub/完整rawlog下载。作者整份声明final全文读前不写本模块Lean源/probe。目标及Audit全部在指定server，CPU14–17、native-M8192-j4、-DautoImplicit=false、lane一heavy，无ulimit-v/心跳或语义放宽；不动外部CPU0–9/10CPU/80GiB。传递白名单仅propext/Classical.choice/Quot.sound；禁止sorry/admit/newaxiom/unsafe/native_decide/implemented_by。

仍OPEN→实际hcont/条件Levy和无条件15/19、forallprefix hW、最终单律diagonal、generalKL/global minimizer、literalPhi、原24 exactζ及根A/B/C/D。p/q/eps固定先于未来r/J/n；beta<2/5只为充分修复，不主张最弱／最优／新颖性。不以本有限模型门替代完整原26或根闭合。
