# OQ3-U17b：真实样本能量比和远区紧集几何

冻结v1，DECLARATION_REVIEW_QUEUED_AFTER_U16J_FULL_FINAL；未批准/未实施。拟 Shao/OQ3/SourceEnergyGeometry.lean。imports Shao.OQ3.SampleBoundary、Mathlib.Topology.Order.Compact；namespace Shao.OQ3，open MeasureTheory，open scoped BigOperators，noncomputable section。两个完整公开定义、三个完整公开目标。数学独立于U17a和J，只使用既有样本几何；等J完整终票由lead全文读完后才能派唯一reviewer声明门，批准前不写本Lean源或Lean probe。

来源 current/oq3/proofs/r1/report.md SHA3473d34ff20bd0d334b9ef3ea3c3ee167fba4d5cc3a742849820ce54d639e662，164–172能量支持/边界比、386–391负层与远区控制、400–408真实样本曲边事件。此处只证明确定性几何与真实远区参数紧性，不含概率指数界、有限覆盖、KL数据处理、任意rho的唯一全局最小、完整17/19/LLT/hW或根结论。

```lean
def sourceEnergyRatio (q : ℝ) (n : ℕ) (z : Shao.Path n) : ℝ :=
  Real.sqrt (Shao.energy z / ((n : ℝ) * q))

def sourceFarEnergySet (q H delta : ℝ) : Set ℝ :=
  {R | 0 ≤ R ∧ 1 ≤ q * R ^ 2 ∧ q * R ^ 2 ≤ 1 + H ∧
    delta ≤ q * (R - 1) ^ 2}

theorem sourceFarEnergySet_isCompact (q H delta : ℝ) (hq : 0 < q) (hH : 0 < H) :
    IsCompact (sourceFarEnergySet q H delta)

theorem sourceTail_normalDeviation_energy_lower (q : ℝ) (hq : 0 < q)
    (n : ℕ) (hn : 0 < n) (z : Shao.Path n) (htail : z ∈ sourceTail q n) :
    -((n : ℝ) * q * (sourceEnergyRatio q n z - 1) ^ 2) ≤ normalDeviation q z

theorem sourceTail_far_energy_mem (q H delta : ℝ) (hq : 0 < q)
    (hH : 0 < H) (hdelta : 0 < delta) (n : ℕ) (hn : 0 < n)
    (z : Shao.Path n) (henergy : ∀ i : Fin n, 1 ≤ (z i) ^ 2 ∧ (z i) ^ 2 ≤ 1 + H)
    (htail : z ∈ sourceTail q n) (hfar : normalDeviation q z ≤ -delta * (n : ℝ)) :
    sourceEnergyRatio q n z ∈ sourceFarEnergySet q H delta ∧
      0 < sourceEnergyRatio q n z ∧ sourceEnergyRatio q n z ≠ 1
```

定义均总化在任意实q/自然n上，但所有除法取消和几何目标都显式假设q>0/n>0；不声称n=0时有该几何。far集合要求非负R，保留所有能量端点与delta界等号；可能空集，紧性目标不得暗加非空性。hH在紧性中只给统一sqrt上界有意义；delta任意实数，紧性不假设delta正。

第一目标：集合是四个连续实多项式弱不等式的闭集交。q>0和qR²≤1+H给0≤R≤sqrt((1+H)/q)；于是它是闭集与该Icc的交，或直接用IsCompact.of_isClosed_subset。空集和R=0的包含判定不作伪非空推断。实际库Compact模块及所需olean必须只读核对；缺cache先报root，不下载。

第二目标：令N=(n:ℝ)>0，E=energy z≥0，R=sourceEnergyRatio≥0。先证Nq>0、E/(Nq)≥0及R²=E/(Nq)，再给NqR²=E。曲边阈值T=sqrt q/4*sqrt(NE)非负，U=NqR/4非负；平方恒等式T²=NEq/16=U²，在非负域sq_le_sq₀或sq_eq_sq₀推出T=U。htail给sum≥U。actual normalDeviation=8sum-E-Nq ≥ 2NqR-NqR²-Nq= -Nq(R-1)²。该一侧关系必须从正sourceTail分支推导，不能仅平方而引入负尾。

第三目标：有限逐坐标1≤xi²≤1+H，真实energy有限和给N≤E≤N(1+H)。N>0除后1≤qR²≤1+H，第一定义给R≥0，E≥N>0再给R>0。第二目标加hfar和N>0严格取消N得到delta≤q(R-1)²。故属于实际远区集合；delta>0使R=1不可能。无需均值/概率/有限stage/原子正质量假设；不把这个泛化几何目标计成源根已闭。

审查顺序：两个实际DEF完整体、三个完整type独立翻译并持久化优先；再原源与scope，再可行性和真实库API/cache；机械hash/pins最后。实施后完整proof审查另行进行，不能用本声明门替代。标准axiom白名单propext/Classical.choice/Quot.sound，禁止sorry/admit/new axiom/unsafe/native_decide/implemented_by。继续保持p/q/eps/P先于r/J/n及beta<2/5仅充分修复，根A/B/C/D全OPEN。
