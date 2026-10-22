# U17b SourceEnergyGeometry 完整独立proof/source/TYPE审查

STATUS: CORRECT

唯一reviewer lease1，只拥有本新报告与授权run/proof-review.md，不独占代码库、不回退他人。先仅读actual两个DEF完整体/三个公开完整类型并独立翻译持久化，再source/scope/proof/actual全部TYPE，机械证据最后。声明审查上下文已存在，不能用旧票或作者绿色预期替代本轮证明审查。不Lean/probe/build/rebuild/spawn/写cache/sourceedit/下载原始全日志，不启动重型进程或干预CPU0–9的外部任务。

actual source SHA256=`3cad1d1f12583690a6acbffc749110ace2b2786831f706049583cb755ac2253a`，5141bytes/119行。

## 1. actual完整公开定义体与类型（先读）

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

## 2. 独立盲译（先落盘）

sourceEnergyRatio 对任意实q、自然n和真实路径z:Fin n→ℝ，取实际平方和energy除以(n:ℝ)*q的标准实平方根。定义本身含q0/负q/n0下的标准总化语义，不自动具有比率平方恒等式；证明取消/开根门必须来自目标另给的正性。

sourceFarEnergySet(q,H,delta)是实R的集合，要求R≥0、1≤qR²≤1+H、delta≤q(R−1)²。参数在定义内不要求正、集合不要求非空，也未无条件排除R1。两个定义都没有概率输入或均值替换。

第一actual定理对任意实q/H/delta，假设q>0与H>0，断言上述完整F紧；delta允许任意正负0，空集也包括，不准加非空/离1距离正的隐含门。

第二actual定理给q>0、自然n>0和任何真实路径z，只要求z∈actual sourceTail q n，断言真实normalDeviation q z≥−nq(sourceEnergyRatio−1)²。没有逐坐标energy界、概率/均值/AE/有限原子假设，必须由真实正尾几何与q/n正域推出。

第三actual定理给q/H/delta均正、自然n>0、路径逐坐标1≤z_i²≤1+H、actual sourceTail成员及normalDeviation≤−delta*n；结论同一个实际energy ratio属于F，且严格>0和≠1。逐坐标条件是真全Fin n，不是未经提升的AE；不能从定义无条件读出严格R/非1。

当前只忠实翻译actual两个完整body与三完整type，尚未看proof/private/generated/receipt或Audit绿灯。根A/B/C/D、source3/generalKL/globalfar/full17/19/LLT/hW仍OPEN。

## 3. 冻结匹配与真实来源（盲译之后）

本票盲译先持久化SHA256=`655ebb104c129e1f7a6131f91c102f7cfc7f0f21120f9fd5d54d9126b4795f14`，3332bytes/46行。此后才读scope48/真实R1与actual全部proof。两个完整actual DEF body及三个完整publictypes对scope Lean fence去白空格逐字匹配 **PASS**；原2imports SampleBoundary/Mathlib.Topology.Order.Compact保持，未改签名/假设或以隐藏实例改变其数学含义。

真实R1原件 `C:/game/shao/current/oq3/proofs/r1/report.md` SHA256=`3473d34ff20bd0d334b9ef3ea3c3ee167fba4d5cc3a742849820ce54d639e662`。164–172给实际能量支持与边界能量比，384–391是负层/远区概率控制的背景需求，400–408的曲边身份/正尾符号给本单元几何来源。B当前只证明确定性样本能量比/远区参数紧性，不把compact set自身当成有限cover或概率far界，也不声称一般KL/DPI/源全局最优。

actual `Shao.Basic.FinitePath:18,31,50–51`：Path n=Fin n→ℝ；energy=Σ_i z_i²，energy_nonneg来自有限平方和，无variance/期望替换。actual SampleBoundary:19–27的normalDeviation=Σ_i normalValue(z_i)−Nq，normalValue=8x−x²，sourceTail={energy>0且sqrtq/4*sqrt(N energy)≤Σ_i z_i}；其公开29–32给精确M=8ΣX−E−Nq。tangentDeviation q的中心是Nq/4，B不将之换成本新energy ratio R或用作额外概率中心。

## 4. 全部119行证明/private/locals独立核查

1–7原2imports/namespace/open/noncomputable；9–14两个完整publicdefs已实际读体；16–23唯一authored private theorem；25–47紧性publicproof；49–79路径下界；81–116远区成员；118–119闭作用域。所有行/locals已读。实际生成owned项下一阶段需逐个actualTYPE核，不从作者报数或表面源码假定它们只是无害算术。

### 4.1 private energy_ratio_sq（16–23）

hq>0、hn>0先经real cast给N>0与Nq>0；Shao.energy_nonneg z给E≥0。只有此后22用Real.sq_sqrt(div_nonneg E_nonneg hnq.le)得到R²=E/(Nq)，23 field_simp取消的是先正后非零的Nq，真结论NqR²=E。private没有htail/坐标界/概率假设，故三个public消费时不偷用更强语义；n0/q0时虽def总化，但这条恒等式明确不声称成立。

### 4.2 sourceFarEnergySet_isCompact（27–47）

27–36四个实际弱不等式集合分别由isClosed_le(常数/identity/连续多项式)得闭；37–38有限交按定义的right-nested conjunction得到完整F闭，没有漏掉delta约束或能量下界。所有delta实数都适用。

39以H>0/q>0给U=(1+H)/q>0，40用真实isCompact_Icc[0,sqrtU]及of_isClosed_subset，后者**不需非空**。41–44从R∈F取R≥0和qR²≤1+H，在正q下le_div_iff₀转换得到R²≤U。45–47明确R≥0、sqrtU≥0后平方序比较，Real.sq_sqrt hU.le合法，得到R≤sqrtU。没有假设F有元素、没有用delta>0、没有要求q接近1或额外R>0才能有界；空集/任何负delta/0delta都正确。H正足够给全局上界，未提升全实R空间为紧。

### 4.3 sourceTail_normalDeviation_energy_lower（52–79）

52 N>0，53消费同一q/n/z的private energy_ratio_sq；54–55 E≥0、R≥0。56–59定义真实T=sqrtq/4*sqrt(NE)、U=NqR/4，并先建立T/U≥0。60–64以q≥0和NE≥0后的实际sqrt平方公式算得T²=NqE/16，65–69用原NqR²=E及ring算出U²=NqE/16；没有在非正根域做sq_sqrt或将Nq误变N²q²因子。

70由**两底数非负**后的sq_eq_sq₀推出T=U，排除平方身份±号歧义。71 hTU ▸ htail.2是原正尾阈值T≤ΣX的真实代入，不是从平方事件凭空选择正S；htail.1的E>0在此较弱下界中未再使用合法，不能反过来声称只靠平方条件就是sourceTail。72改写actual normalDeviation_eq_sum_energy=M=8ΣX−E−Nq。74–78用he与U完整体的精确环等式
−Nq(R−1)²=8U−E−Nq，79用ΣX≥U与**正系数8**给所需下界。未乘负数翻错方向，未作q≈1、n大、概率均值或坐标energy界假设。

这条恒等/不等式只从真实正尾分支出发，允许任意正q、任意正自然n和路径。E=0在htail下不可能，但proof也不需先除E或R；退化分母唯一Nq已正，没有除R或R−1。

### 4.4 sourceTail_far_energy_mem（87–116）

87–90先N>0/Nq>0、N(1+H)>0，再同q/n/z的he。91–99逐坐标**全Fin n**的henergy直接Finset.sum_le_sum，真实card Fin n=n与sum_const给N≤E≤N(1+H)。没有AE→全路径的未证明提升，也没有把样本能量替成给定均值。

100–105用真实he与上述能量界，乘法序等价只取消正N，得1≤qR²≤1+H。hupper是正量事实，虽代数推导不必额外需要，其使用不引入新假设。106消费第二目标同q/n/z/htail的hgeom。107–109合hgeom与hfar，先推出N*delta≤N*q(R−1)²，再用正N的mul_le_mul_iff_right₀取消；弱far不等号等号保留。没有除delta、R−1或任何可能为零量。

110–111由N≤E与N>0得E>0、Nq>0给E/(Nq)>0，真正Real.sqrt_pos_of_pos推出R>0。112以hR.le、hlow/hhigh/hdeltaR构造完整F成员，再带真实hR；113–116假设R1时delta≤q*0²=0，hdelta>0矛盾，故R≠1。第一紧性目标没有偷用此hdelta正性，第二路径下界没有偷用逐坐标bounds。能量上下端点、far边界、delta分离等号均真实保留。

## 5. actual库语义/导入与边界核查

只读指定服务器实际库，未Lean/probe：

| 实际API源 | 真实门及此proof消费 |
|---|---|
| Topology/Order/Compact:51–56,77–79 | 公开isCompact_Icc与实数所具备ConditionallyCompleteLinearOrder/OrderTopology实例，紧的是闭区间而非全ℝ |
| Topology/Compactness/Compact:104–107 | IsCompact.of_isClosed_subset需compact外集/closed内集/subset，无Nonempty门，actual40–47完整给出 |
| Topology/Order/OrderClosed:443–446 | isClosed_le需两连续函数；四个实多项式/常数/identity连续后闭集合交，actual27–38匹配 |
| Analysis/Real/Sqrt:143–145,177,285–288 | sqrt_nonneg；sq_sqrt需被开方数≥0；sqrt_pos_of_pos需真正正数；private/主证明每处先建门 |
| Algebra/Order/GroupWithZero/Basic:748–759 | sq_eq_sq₀/sq_le_sq₀需两底数非负，actual70正根身份及45有界性分别给出 |
| 标准正乘/除序与取消、Finset.sum_le_sum/card Fin n/ring | 每处取消仅N/q/Nq均有严格正；sum来自真实逐坐标全称；没有不合法除R/k/delta |

没有额外Integrable/AE/Fubini/μ/probability假设在当前三个目标中缺失，因为当前都是确定性几何与实拓扑命题，不在本proof里做任何积分/概率比较。root/未来概率门仍须另证，不能从import概率模块推出已完成。原2defs的任意q/n总化保留，只有真实几何恒等/取消声明明确正q/n；n0不被误当归一化，无新Matrix/volume实例或KLcache需要。

数学阶段判定支持CORRECT：actual119行/唯一private/全部locals正确，源含2defs3public1private；接下来必须逐个核实际generated/所有owned TYPE，再最后核作者机械证据。此阶段未读receipt、build成功记录或Audit公理/计数/PASS。

## 6. 全部13项actual DECL/TYPE与生成辅助（机械绿灯之前）

数学阶段先持久化SHA256=`20e2794167b63e66aeb926bd2a8283f1407b7a1da02a8ffdce1b42c0f4b4cc57`，10440bytes/102行；随后只筛读真实Audit.log中全部DECL/TYPE与完整长续行，未读其AXIOMS/计数/PASS或作者receipt/build。实际输出如下，不下载raw全日志：

```text
DECL _private.Shao.OQ3.SourceEnergyGeometry.0.Shao.OQ3.energy_ratio_sq._simp_1_5
TYPE ∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀] {a : M₀} [IsReduced M₀] (n : ℕ), a ≠ 0 → (a ^ n = 0) = False
DECL Shao.OQ3.sourceTail_far_energy_mem
TYPE ∀ (q H delta : ℝ),
  0 < q →
    0 < H →
      0 < delta →
        ∀ (n : ℕ),
          0 < n →
            ∀ (z : Shao.Path n),
              (∀ (i : Fin n), 1 ≤ z i ^ 2 ∧ z i ^ 2 ≤ 1 + H) →
                z ∈ Shao.OQ3.sourceTail q n →
                  Shao.OQ3.normalDeviation q z ≤ -delta * ↑n →
                    Shao.OQ3.sourceEnergyRatio q n z ∈ Shao.OQ3.sourceFarEnergySet q H delta ∧
                      0 < Shao.OQ3.sourceEnergyRatio q n z ∧ Shao.OQ3.sourceEnergyRatio q n z ≠ 1
DECL _private.Shao.OQ3.SourceEnergyGeometry.0.Shao.OQ3.energy_ratio_sq._simp_1_1
TYPE ∀ {α : Type u_2} [inst : Zero α] [inst_1 : OfNat α 2] [NeZero 2], (2 = 0) = False
DECL _private.Shao.OQ3.SourceEnergyGeometry.0.Shao.OQ3.energy_ratio_sq._simp_1_4
TYPE ∀ {M₀ : Type u_1} [inst : Mul M₀] [inst_1 : Zero M₀] [NoZeroDivisors M₀] {a b : M₀},
  a ≠ 0 → b ≠ 0 → (a * b = 0) = False
DECL _private.Shao.OQ3.SourceEnergyGeometry.0.Shao.OQ3.energy_ratio_sq
TYPE ∀ (q : ℝ),
  0 < q → ∀ (n : ℕ), 0 < n → ∀ (z : Shao.Path n), ↑n * q * Shao.OQ3.sourceEnergyRatio q n z ^ 2 = Shao.energy z
DECL Shao.OQ3.sourceEnergyRatio
TYPE ℝ → (n : ℕ) → Shao.Path n → ℝ
DECL _private.Shao.OQ3.SourceEnergyGeometry.0.Shao.OQ3.energy_ratio_sq._simp_1_3
TYPE ∀ {α : Type u_2} [inst : Zero α] [inst_1 : OfNat α 4] [NeZero 4], (4 = 0) = False
DECL Shao.OQ3.sourceTail_normalDeviation_energy_lower
TYPE ∀ (q : ℝ),
  0 < q →
    ∀ (n : ℕ),
      0 < n →
        ∀ z ∈ Shao.OQ3.sourceTail q n,
          -(↑n * q * (Shao.OQ3.sourceEnergyRatio q n z - 1) ^ 2) ≤ Shao.OQ3.normalDeviation q z
DECL _private.Shao.OQ3.SourceEnergyGeometry.0.Shao.OQ3.energy_ratio_sq._simp_1_7
TYPE ∀ {R : Type u_1} [inst : AddMonoidWithOne R] [CharZero R] (n : ℕ), (↑n + 1 = 0) = False
DECL Shao.OQ3.sourceFarEnergySet
TYPE ℝ → ℝ → ℝ → Set ℝ
DECL _private.Shao.OQ3.SourceEnergyGeometry.0.Shao.OQ3.energy_ratio_sq._simp_1_2
TYPE ∀ {α : Type u_2} [inst : Zero α] [inst_1 : OfNat α 3] [NeZero 3], (3 = 0) = False
DECL _private.Shao.OQ3.SourceEnergyGeometry.0.Shao.OQ3.energy_ratio_sq._simp_1_6
TYPE ∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] {a : G₀} (n : ℤ), a ≠ 0 → (a ^ n = 0) = False
DECL Shao.OQ3.sourceFarEnergySet_isCompact
TYPE ∀ (q H delta : ℝ), 0 < q → 0 < H → IsCompact (Shao.OQ3.sourceFarEnergySet q H delta)
```

按实际出现顺序逐项判定（不是只看计数）：

1. `energy_ratio_sq._simp_1_5`：MonoidWithZero且IsReduced时非零a的任意自然幂非零，包括n0；不是在任意有零因子的环无条件断言。实际库Algebra/GroupWithZero/Basic:251声明IsReduced context，258的pow_ne_zero由eq_zero_of_pow_eq_zero的逆否给同一结论；n0时a≠0已排除全体平凡零结构的问题。将非零命题写成 `(a^n=0)=False` 是合法命题等式归一化，不是新数学前提。
2. public far_energy_mem：全部q/H/delta正、n>0、全Fin坐标energy门、实际sourceTail/hfar保留，输出同R成员且严格R正/非1，未弱化为另一集合或偷删hfar。
3. `_simp_1_1`：只有Zero/OfNat2和**显式NeZero2**就推出(2=0)=False；它不宣称任意特征中2非零，也不把OfNat等同自然cast而漏掉条件。
4. `_simp_1_4`：在NoZeroDivisors下两个非零因子乘积非零，实际库Algebra/GroupWithZero/Basic:84–85与Defs:304对应；无额外交换/乘法单位或正性依赖。a/b非零门实际用于field_simp分母，不可用此类型取消可能0的因子。
5. private energy_ratio_sq：actual完整TYPE明确q>0与n>0，非所有总化q/n；同路径真实energy/Nq关系完全匹配第4.1节。
6. def sourceEnergyRatio：一个实q、依赖自然n和Path n到ℝ，同实际完整body；body已在第1/4节读过，未仅从TYPE猜测分母/平方根。
7. `_simp_1_3`：如第3项但数4，**显式NeZero4**，没有特征遗漏。
8. public sourceTail_normalDeviation_energy_lower：其`∀ z ∈ sourceTail`是标准∀z, membership→结论的打印形式，q/n正门和精确−Nq(R−1)²保留，未暗添坐标界/概率前提。
9. `_simp_1_7`：AddMonoidWithOne/CharZero下自然cast n+1非零，实际Algebra/CharZero/Defs:79–80 `Nat.cast_add_one_ne_zero` 对应；CharZero意味着自然cast单射，故真n+1≠0，不需实数序。不可误读成任意实变量x+1非零。
10. def sourceFarEnergySet：三个实参数到Setℝ，与完整四合取body对应；未隐式增加正delta/非空或R非1。
11. `_simp_1_2`：如第3项但数3，**显式NeZero3**；合法归一化，不假定所有环特征0。
12. `_simp_1_6`：GroupWithZero下非零a的任意整数幂非零，含负幂和0；实际Algebra/GroupWithZero/Units/Basic:411–413逐自然/负后继情况由pow_ne_zero与inv_ne_zero证明。a≠0明确必要，没有非法0负幂取消。
13. public sourceFarEnergySet_isCompact：q/H正但delta全实，不含Nonempty/正delta/额外有界前提，保留最初scope完整量词。

七个generated实际均为private energy_ratio_sq的simp命题归一化辅助，已经逐条按真实类型及对应标准代数结构独立检查，非作者所说“generated”就默认通过。未执行Lean/#print或新checker；其实际内核产物/公理覆盖最后核。总计13actualTYPE=2defs+3publictheorem+1authoredprivate+7generatedtheorem，每个完整type已读；无另漏定义eq helper的假设。数学+全部actual TYPE阶段支持CORRECT，尚未读作者receipt/机械绿灯。

## 7. 最后机械证据、冻结绑定与版本

actual全部TYPE阶段已先持久化SHA256=`6a1a21e1b580105e5769a81bfd1ed7296541d02443067e60ac2317c2173a4594`，16576bytes/171行；此后才读作者receipt、Audit源/AXIOMS/gate、既有build03及真实源码/12闭包/pins/hash。没有用作者叙述或形式成功替代此前数学判断。

### 7.1 真实文件与三端hash

run=`/root/rivermind-data/shao-lean-20261021/runs/oq3/u17b-20261021`，worktree=`/root/rivermind-data/shao-lean-20261021/workspaces/lead-oq3`。

| 实际对象 | 实际SHA256 | 字节/行 | 独立核查 |
|---|---|---|---|
| SourceEnergyGeometry.lean（localdraft/worktree/run快照） | `3cad1d1f12583690a6acbffc749110ace2b2786831f706049583cb755ac2253a` | 5141/119 | 三端同、两个DEF完整body/三types与冻结scope匹配 |
| scope.md / local forty-eighth-unit-scope.md | `7d1b62f0a8f93e99fb86398b7af6313dce03ecc69acae17abcb8626976b159e0` | 3995/38 | 两端同冻结scope |
| statement-review.md / local u17b-statement-review.md | `86ab5a9e8dbfa5ff403f34c06b5b6e873f4f8c75f78dc2a6116ecf05abaf2fd5` | 16981/142 | 两端同lead接受的声明票 |
| receipt.json / local U17b-receipt.json | `2e843e6694b8107710a1132ed3c4dd630242af075772d3b6c3754efb91f7bbf8` | 4820/71 | 两端同，最后才读/逐项核真产物 |
| Audit.lean / local U17b-Audit.lean | `08304794f1ecb0f7bc5f453d56cdf4eff9c5fd1ac59d8e0d34b2d524a316062a` | 1763/40 | 两端同，全文读覆盖逻辑 |
| Audit.log | `8fcb40aa45138c23524dc618261f71a64198fe921e46078f2b890512b91d4f9d` | 3201/61 | 全13TYPE先读、最后读公理/gate |
| build-03.log | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` | 0/0 | 实际空文件，历史exit0由既有receipt记录，未重跑 |
| prerequisite-hashes.json / local u17b-prerequisite-hashes.json | `3a0b935c631f9637c7b7dbded909e53aaf0483466124db8411cecf0645f7c2cc` | 1236/14 | 两端同，12项实际重hash匹配 |

源LF/CR0、无尾空格，禁止项扫描sorry/admit/axiom/unsafe/native_decide/implemented_by或跳kernel选项为空；源显式仅2def+3publictheorem+1private，原两imports。实际目标olean已存在400936bytes，只读stat，无新检查。关机前成功build03/Audit沿用其已保存产物，本轮没有重跑，旧build01/02说明不作独立数学证据。

### 7.2 Audit真实覆盖与每项公理

Audit全文先核3target均为theorem及两defs均为defnInfo，再环境枚举选5个公开stems的所有子名以及整个 `_private.Shao.OQ3.SourceEnergyGeometry` 前缀；拒绝新axiom，`Lean.collectAxioms`逐项传递递归，只准propext/Classical.choice/Quot.sound。该selector不是泛扫任意publicnamespace，但本票完整source确认无额外非stems publichelper，因此当前覆盖完整；private前缀包含7个实际生成simp theorem，未只查3目标漏掉辅助。

各声明实际axioms（完整名称见第6节）：

| actual owned项目 | 实际传递axioms |
|---|---|
| energy_ratio_sq._simp_1_1 | propext |
| energy_ratio_sq._simp_1_2 | propext |
| energy_ratio_sq._simp_1_3 | propext |
| energy_ratio_sq._simp_1_4 | propext |
| energy_ratio_sq._simp_1_5 | propext |
| energy_ratio_sq._simp_1_6 | propext, Classical.choice, Quot.sound |
| energy_ratio_sq._simp_1_7 | propext |
| private energy_ratio_sq | propext, Classical.choice, Quot.sound |
| def sourceEnergyRatio | propext, Classical.choice, Quot.sound |
| def sourceFarEnergySet | propext, Classical.choice, Quot.sound |
| public sourceFarEnergySet_isCompact | propext, Classical.choice, Quot.sound |
| public sourceTail_normalDeviation_energy_lower | propext, Classical.choice, Quot.sound |
| public sourceTail_far_energy_mem | propext, Classical.choice, Quot.sound |

实际gate为 `U17B_FROZEN_THEOREMS 3`、`U17B_ALL_THEOREMS 11`、`U17B_ALL_DECLARATIONS 13`、`U17B_AXIOM_GATE PASS`。故13owned=2defs+3public+1private+7generatedtheorem，完整13TYPE已独立逐项检查，defs实际完整body已先读；没有漏掉额外def.eq helper，也没有靠计数推断数学。作者历史receipt status/nonclaims正确标U17b，pending independent/no commitPR at author-check time保留历史含义，不是本终票之后的当前状态。

### 7.3 实际12项项目前置闭包

从actual原两imports递归重新枚举源码，集合恰12，**12/12每项实际SHA重算**同时等于run prerequisite-hashes.json与receipt字段，所有前置olean真实存在。没有U17a/J新模块进入B实际import图：

| 实际项目源 | 实际SHA256 |
|---|---|
| Shao/Basic/FinitePath.lean | `898262898f9c088e2d10e6238e411b4397387b21b1b71a2b545c5edef936e1bb` |
| Shao/OQ3/AtomProjection.lean | `0d369052c7f87122765612efdeaca5d9ac71abca861e7785c86d1f9edcc74d22` |
| Shao/OQ3/AtomicMeasure.lean | `59ddc48fb7b395f362939e58cbd9d7911685a6ed6e6574142e8a6d4ab3ee0c39` |
| Shao/OQ3/FiniteConstraints.lean | `800d9db8cb6749a31ecfe611409de92b10ea8bb2aef955bfd825ede7324f0ef0` |
| Shao/OQ3/FiniteNormalSpan.lean | `0374da4860edf8af8bbbb9172e4e93bfe9b6c37ac57672b85a4f58392475b7de` |
| Shao/OQ3/FiniteStageMeasure.lean | `1a32fb904e6ee9d2b0b48d92c4ebb3568452bb02500ce52a1a03eb01ae0256b1` |
| Shao/OQ3/InverseTilt.lean | `c7e7d19e8b70481b663bec1fd12ea9301d73313faaf35997e85aa9ba99f21811` |
| Shao/OQ3/ResonanceArithmetic.lean | `cd21a264d637bab30fed765bdc25ed09bb4ff56f6efb9c88ee09be4ca6e1648b` |
| Shao/OQ3/SampleBoundary.lean | `7660e23b71ce28ab43a4ad1d8df1862cf8a507b6bb9b41255e961f0bee0b93e2` |
| Shao/OQ3/SourceStarter.lean | `0e2a081619976f88149707c2ef9311dc909003e61d3d0f7c4e21e6c3dbbc5a6d` |
| Shao/OQ3/SummableAtoms.lean | `0ea4c64fe9ef9b45fbf44d24312771a1dbfbcc5de8448564e3e87bdf17c7178b` |
| Shao/Probability/FiniteIID.lean | `d1b565489199d55af70a27c31a0f803a2b7433e78c9197a361b3c10c0598845b` |

这些冻结源的承重语义见第3–5节，实际SampleBoundary/FinitePath仍使用真实有限平方和与正sourceTail；不以导入了概率模块就声称本目标给真实概率far界。未重做任何旧成功target/Audit。

### 7.4 固定库/环境与分支历史

实际Mathlib HEAD=`807d3836b165983210ee2ecf3cd28f239436949c`；toolchain=`leanprover/lean4:v4.36.0-rc1`。lean-toolchain SHA256=`d581a24b57a4ae9e0b2132ca8ac7cc3ac336a9fc2751fe6b29414e2d434d54c4`（29bytes），lake-manifest.json SHA256=`40e8e3385f2b0c8ae56fa9de6947301472379cb62eeb83247944827c38b8af6e`（3541bytes/117行）。

下列消费库源实际字节逐项同HEAD git对象，且其既有olean实际存在；包括7个generated类型的标准代数依据，不仅确认顶层Compact缓存：

| 库源（Mathlib前缀省略） | 实际SHA256 |
|---|---|
| Topology/Order/Compact.lean | `e3d3e63921f09661fc6178857a0a72f28c27d41f7810f66607f24ac5919c7001` |
| Topology/Compactness/Compact.lean | `cdc05494e34ec5d4163211223acf44d4c980629cac5542a52ca6d7360d80754e` |
| Topology/Order/OrderClosed.lean | `011a07d8a57515c2a6bf066bf4ef24ff22eeffcc4d6115afd9ff22f5d45ded9e` |
| Analysis/Real/Sqrt.lean | `1f19e1d6722b2f51c2cd676d0b28ede856c7915ac815b597cef4b3919040c204` |
| Algebra/Order/GroupWithZero/Basic.lean | `28c0432242f3766a643689abd852cbf92fee391d314f76815e6977e64854103c` |
| Algebra/GroupWithZero/Basic.lean | `ecd1e404d5269d81c7042acbb921a03dc078726935ac37120f4f3f17a9777d90` |
| Algebra/GroupWithZero/Units/Basic.lean | `1e7324f9db0a7a93972e83d49fee90d9503d27bca407912a7ad30191430d302f` |
| Algebra/CharZero/Defs.lean | `4df0a05b9b2993687b26b3baec8a128f0ac2953980f78fe0ba533ad60dc3c276` |

真实读取时branch=`feat/oq3-source-energy-geometry`，HEAD=`83416bf5a82c1e2baddd8ad0d8050f41d3893f63`，status仅 `?? Shao/OQ3/SourceEnergyGeometry.lean`。receipt中branch=`feat/oq3-energy-bernoulli-mgf`、head998120143278fa0badc4380c2fd11c7162d4f31f是作者检查时的历史基线；lead已预告先发布A再切B，现实际B源/12pins/库版本逐项未变，所以**分支推进本身不构成冻结失配**。本票绑定冻结source/依赖/pins；稍后B发布的exact commit仍由lead独立核。未改或重写历史receipt。

所有远端操作经指定共享broker，host key SHA256=`+IZMFu9Xx6FSAhvQhtvZ3MpV70v2d+XNWcequAbsp+c`；未改连接、读凭据、kill/干预其他任务。遵守noLean，未使用ulimit或启动heavy，因此CPU14–17/本线一heavy以及CPU0–9外部任务限制无任何新检查占用；无cache写入。

## 8. 最终完整独立裁决

JUSTIFICATION: **CORRECT。** actual两DEF完整body与三public完整types先独立盲译持久化，与冻结scope精确匹配；实际119行/private/全部locals及库语义正确。紧集由四闭约束与真实紧Icc上界得到，任意delta/空集正确；正q/n之后真实energy ratio平方恒等式、两正根平方比较T=U、原sourceTail正分支和8系数得到精确路径下界；全Fin真实平方和与正N取消给远区成员/R>0/R≠1，所有能量/弱不等式端点保留。全部13actualTYPE包括7generated逐项独立核过，其代数结构/非零门完整，未遗漏隐藏定义辅助。最后源码三端、12实际依赖、库pins/真实已有构建与Audit/传递白名单一致；未发现数学/source映射/类型/机械绑定缺口。

作者门和独立终判有严格顺序区分，成功日志没有替代数学。源定义的q0/n0总化没有被当作合法归一化；actualproof所有取消/开根都在明确正域。只有本单元真实确定性样本几何/远区参数紧性完成，不推导有限cover、真实iid概率far界、MGF测试/KL/RN/DPI/Legendre优化、source3一般唯一全局最小、完整17/19/LLT、hW/WC或根闭合，无最弱/最优/新颖性主张。根 **A/B/C/D、source3/generalKL/globalfar/full17/19/LLT/hW仍OPEN**。

本轮只写本新local终票及授权run/proof-review.md，未修改source/scope/receipt/旧票/shared/cache，不spawn/Lean/probe/build/rebuild/commit、下载raw完整日志或读取作者futurecandidate/notes。报告上传后两端hash另核，等待lead全文读取才进入B发布。
