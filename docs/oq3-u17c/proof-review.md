# U17c FarEnergyExponentialCover 完整独立proof/source/TYPE审查

STATUS: CORRECT

唯一reviewer lease1，只有本新local报告与授权run/proof-review.md写入权，不独占代码库/不回退别人。actual完整publictype先独立翻译持久化，再scope/source/proof/private/generated/API，全actualTYPE之后才作者receipt/机械。先前声明批准是上下文，不替代actual证明审查。不spawn/Lean/probe/build/rebuild/cachewrite/sourceedit或下载raw全log，不读作者future/candidate/实施notes。

actual source SHA256=`40ee1824e49f2bf38e653edfa38363774e27a7d58c3c9e1c2b97245cfc86803d`，4543bytes/108行。零公开定义、一完整target。

## 1. actual完整公开类型（先读）

```lean
theorem exists_source_far_energy_exponential_cover (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (hb : ∀ᵐ x ∂mu, |x| ≤ 4 + Real.sqrt 10) (q H ell delta : ℝ)
    (hq0 : 1 < q) (hq1 : q < 103 / 100) (hH0 : 50 < H) (hH1 : H < 51)
    (hell : 0 ≤ ell) (hgap : ell * q < 7 / 200) (hdelta : 0 < delta)
    (henergy : ∀ᵐ x ∂mu, 1 ≤ x ^ 2 ∧ x ^ 2 ≤ 1 + H)
    (hsecond : (∫ x : ℝ, x ^ 2 ∂mu) = q) :
    ∃ c : ℝ, 0 < c ∧ ∃ T : Finset ℝ,
      (∀ t ∈ T, Integrable (fun x : ℝ => Real.exp (t * (x ^ 2 - q))) mu ∧
        0 < (∫ x : ℝ, Real.exp (t * (x ^ 2 - q)) ∂mu)) ∧
      ∀ R ∈ sourceFarEnergySet q H delta, ∃ t ∈ T,
        ell * q * (R - 1) ^ 2 + c < t * (q * R ^ 2 - q) -
          Real.log (∫ x : ℝ, Real.exp (t * (x ^ 2 - q)) ∂mu)
```

## 2. 独立盲译（先落盘）

固定真实实概率μ，AE |x|≤4+sqrt10，固定实q/H/ell/delta，要求1<q<103/100、50<H<51、ell≥0、ell*q<7/200、delta>0；同一μ另有AE 1≤x²≤1+H和真实二阶矩∫x²=q。结论先存在共同实c>0，再有有限实测试集合T。T中全部t的真实exp(t(x²−q))可积且真实积分Z_mu(t)>0；随后对实际sourceFarEnergySet q H delta中全部R，存在同一个T中的某t给严格不等式ell*q*(R−1)²+c < t*(qR²−q)−logZ_mu(t)。

c/T位于全R外，可依赖固定μ/参数；t是真有限实数、可任意符号，不是无穷参数。不能只给随R变动的一族c或无限测试集。R能量端点p0/p1和far弱不等式边界包含；空far集合也仍需某正c但T可空。实际概率、二阶矩中心、测试能量偏移与惩罚系数都保持同一q，不能把purebinaryD直接当actualKL或换成另一个law的normalizer。

本类型没有样本n/iid事件、概率far界或Legendre最优输出。此阶段未读actualproof、generated或receipt/Audit绿灯，暂不判定。根A/B/C/D、source3/generalKL/真实far概率/full17/19/LLT/hW均OPEN。

## 3. 冻结公开类型、来源与承重前置

盲译阶段先落盘SHA256=`f370b5e53dd575f8d753ee24725323f8d2b2b643c8041af5418b7e6f776cedd1`，2691bytes/32行。此后读scope49/真实R1与actual108行proof。actual唯一完整publictype对冻结fence去白空格逐字匹配 **PASS**，原2imports恰EnergyBernoulliMGF/SourceEnergyGeometry，没有新增隐含假设、改q/μ中心或额外导入改变接口。冻结scope SHA256=`ea2fe343d95821eedf377ccb0a36d9fdd5f32187165076395cf5b9060e527bc5`，声明票159行SHA=`9b07e6d51cfc9d92e5e93e4d29b8dfdbe3c592a3fd77d2c3c91299f470ecb78f`仅作先前接受上下文。

真实R1 `C:/game/shao/current/oq3/proofs/r1/report.md` SHA256=`3473d34ff20bd0d334b9ef3ea3c3ee167fba4d5cc3a742849820ce54d639e662`。164–188给能量支持/边界比与纯binaryD来源，224–237三段充分gap及384–391远区控制背景。此实现仅把已接受充分二元熵界转为同μ的有限指数cover；不把它叫实际KL/DPI、源唯一全局最小或真实样本far概率估计。7/200是实际U14b的refined充分界，不称为103/3000的数值弱化。

实际承重语义已按接受的完整proof及其公开接口核：SourceBinaryEntropyGap.source_gap给可行p闭区间、z=(q−1)/H内部、R正非1时严格binaryD>(7/200)(R−1)²；A第一公开给包含p0/p1的有限theta/正Btheta/严格测试，A第二给所有实t同μ的真Integrable/正Z与实际logMGF比较（真可积/AE凸弦/正B先于log）；B的F实际是R≥0、1≤qR²≤1+H、delta≤q(R−1)²，真实紧性覆盖任意delta/空集。本proof未引用未审后续D或新的概率tail producer，实际依赖hash最后另核。

## 4. 全部108行actualproof/locals的独立审查

1–6原2imports/namespace/open/noncomputable；8–19唯一公开类型；20–105完整proof；107–108闭作用域。无authoredprivate/defs，全locals与公开proof逐行已读。实际7generated项不凭作者数目/名字默认通过，下一阶段读全actualTYPE再逐项分析。

### 4.1 共同参数与全实t的真实积分门（20–31）

20 classical只提供Finsetℝ的经典选择/DecidableEq，不改证明语义。21–22由q>1/H>50先给q>0/H>0。23–26定义g=7/200−ell*q，原hgap严格给g>0；c=delta*g/(4q)>0在任何R、theta、T之前建立，正delta/g/q均明示。没有逐点c_R后用紧性无根据改成统一c。

27 Z(t)是真实Bochner exp积分。28–31对**任意实t**用A第二实际公开目标、同μ/hb/q/H/henergy/hsecond得到真Integrable与Zt>0。没有small-tilt门、t非负或概率族更换，未用不可积Bochner=0/log0总化。该全t事实先于有限cover，稍后T中所有测试都能合法返回normalizer条件，不能只保证先前逐R挑中的t。

### 4.2 逐R真实测试并保留2c余量（32–81）

32–34在共同c之后对任意R∈actualF建立∃实t实际测试>ell*qW+2c，W=(R−1)²。

- 35–40由F中R≥0，若非R>0则R0，与1≤qR²矛盾。41–46由F的delta≤q(R−1)²和delta>0排R1。这些门实际构造，不从“far”命名直接读出严格性。
- 47–52定义p=(qR²−1)/H、z=(q−1)/H。H正后从F能量界推出p≥0/p≤1，q>1给z>0、q<103/100/H>50给z<1。p允许0/1，未非法收紧。没有把z是概率参数作为未证明前提。
- 53–59先将F的delta≤qW乘非负g，得delta*g≤qWg；55–57的4*c*q=delta*g只取消已正q。58用正q的乘法序等价合法取消q，从hm/hceq得到4c≤gW。nlinarith只做此多项式推导，没有除W或R−1。
- 60–61按实际gap所有完整输入hq0/hq1/hH0/hH1/hRpos/hRne/hp0/hp1消费同q/H/R的binaryD界。62–63建立ell*q*W≥0（hell含0、q正、平方非负），该事实虽然推导hL也可不用，实际为更强可见门，无错误新假设。
- 64–67由4c≤(7/200−ellq)W、strict actualgap、c>0真实推出L=ellqW+2c<binaryD p z。精确身份(7/200)W=ellqW+gW；2c<4c保证严格余量，未把非严格比较错误变严格，也没有仅逐R正gap无统一分离。
- 68–69 A第一目标给有限实theta、正二点Btheta与L<theta*p−logBtheta。p闭端点有限见证已经在A完整proof中通过，未以±∞代替。htheta虽后续未显式再次消费，它的内容真实返回；后面的A第二目标本身也已真证normalizer正，不依赖Real.log全实单调。
- 70–74取t=theta/H；71先前H>0⇒H≠0后field_simp得tH=theta，72–74纯实环等式theta*p=t(qR²−1)；该环形式不取消未知符号分母。t不限定符号，不除theta或p。
- 75–78同μ/hb/q/H/t/henergy/hsecond的A第二actuallog比较，Zt definitionally为真实积分，z definitionally为同二阶矩比；先htH再把两个真实B匹配。79–81结合严格htest与logZt上界，得到精确 `ellqW+2c < t(qR²−q)−logZt`：减log上界方向正确，能量偏移恒等式t(qR²−q)+t(q−1)=t(qR²−1)。没有将试验值称为Legendre最优或与一般KL相等。

### 4.3 开cover、真实有限T及全量化输出（82–105）

82–83定义U_t={R | c < t(qR²−q)−logZt−ellq(R−1)²}。84–86用actual isOpen_lt和fun_prop：固定t时logZt仅是实常数，余式是R上的连续多项式。没有在此调用未经证明的t↦Z连续、积分交换/DCT/Fubini，Zt真正性由hactual全t给出但其R连续性并不需要关于t的极限。

87–93用hpoint给留2c余量的测试，再由c>0降到严格c阈值形成真实cover K⊆⋃_(t:ℝ)U_t。实际Set.mem_iUnion构造t，并非给出无限集合就假装已有有限cover。

94–95以B真实 `sourceFarEnergySet_isCompact q H delta hq hH` 和全t开集/真实cover消费actual `IsCompact.elim_finite_subcover`，得T:Finsetℝ和K⊆⋃t∈T U_t。该定理对任意索引、空K都成立，无Countableℝ或NonemptyK被悄添，故K可能空时T可为空，不发生取点失败。

96输出原c/hc与这个同T，尚未对R再选择常数。97–98对全t∈T直接返回早已对任意实t建立的hactual t；成员假设ht未使用是合法更强事实，绝非T中的真实可积/正Z被漏掉。99–105对任意R∈K，由有限双iUnion membership真实提取t/htT/htR，再把严格c<F_t(R)实代数还原冻结不等式。c/T都在全R外，未逐R更换集合或裕量，也未漏有限T membership。

边界p0/p1、R远区等号、ell0由原类型/上述严格门完整保留；q/H近边界都在严格给定区间内，唯一取消q/H先正。delta严格正允许构造c且排R1。K空时相同c>0且cover vacuous合法；没有从Finset存在反推有R或T非空。不存在n/n0、真实样本事件或某一J的概率归一化在此被暗中声称。当前proof仍是标量有限覆盖。

## 5. actual固定API/继承语义

- actual Topology/Compactness/Compact:207–212的IsCompact.elim_finite_subcover消费任意ι:Type、全索引开集、真实s⊆⋃iUi后给Finsetι，原类型无Nonempty/Countable门；本proof取ι=ℝ，实际使用与库完全一致。
- actual Topology/Order/OrderClosed:584–587的isOpen_lt从两Continuous函数给严格开集，固定Zt/logZt是R常数；不需关于t的积分类连续或新cache。
- actualA两个公开类型/B紧性完整类型/U14b实际strict sourcegap及纯binaryD定义均在本proof中以同μ/q/H参数消费；A的真实normalizer/可积/任意signedt与B空集紧性来自接受的完整proof而非作者未经审查绿色陈述。其源码/传递闭包机械绑定最后核。
- 正实乘除序（mul_le_mul_iff_right₀ hq等）、Set.mem_iUnion双层有限union/Finsetℝ classical/实多项式ring和nlinarith都只在原已给正性门使用，没有0除或错误量词搬移。

数学阶段判定：actual108行公开proof及全部locals正确，0authoredprivate/0defs；generated真实类型下一阶段单独核，不能只查唯一target。此阶段尚未读receipt/build或Audit公理/计数/PASS。根A/B/C/D、source3/generalKL/真实far概率/full17/19/LLT/hW仍OPEN。

## 6. 全部8项actual DECL/TYPE长续行与generated逐项审查

数学阶段先持久化SHA256=`66f14a3424b9f5430fbcf671bb0c0f881df8f647098f5f4e93a921eaed7f595e`，10571bytes/84行。随后仅筛读真实Audit.log的全部DECL/TYPE和完整长续行，不先读AXIOMS/计数/PASS或receipt/build。下列完整摘录不是raw全日志下载：

```text
DECL Shao.OQ3.exists_source_far_energy_exponential_cover._simp_1_7
TYPE ∀ {R : Type u_1} [inst : AddMonoidWithOne R] [CharZero R] (n : ℕ), (↑n + 1 = 0) = False
DECL Shao.OQ3.exists_source_far_energy_exponential_cover._simp_1_3
TYPE ∀ {α : Type u_2} [inst : Zero α] [inst_1 : OfNat α 4] [NeZero 4], (4 = 0) = False
DECL Shao.OQ3.exists_source_far_energy_exponential_cover._simp_1_1
TYPE ∀ {α : Type u_2} [inst : Zero α] [inst_1 : OfNat α 2] [NeZero 2], (2 = 0) = False
DECL Shao.OQ3.exists_source_far_energy_exponential_cover._simp_1_4
TYPE ∀ {M₀ : Type u_1} [inst : Mul M₀] [inst_1 : Zero M₀] [NoZeroDivisors M₀] {a b : M₀},
  a ≠ 0 → b ≠ 0 → (a * b = 0) = False
DECL Shao.OQ3.exists_source_far_energy_exponential_cover._simp_1_2
TYPE ∀ {α : Type u_2} [inst : Zero α] [inst_1 : OfNat α 3] [NeZero 3], (3 = 0) = False
DECL Shao.OQ3.exists_source_far_energy_exponential_cover._simp_1_5
TYPE ∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀] {a : M₀} [IsReduced M₀] (n : ℕ), a ≠ 0 → (a ^ n = 0) = False
DECL Shao.OQ3.exists_source_far_energy_exponential_cover
TYPE ∀ (mu : MeasureTheory.Measure ℝ) [MeasureTheory.IsProbabilityMeasure mu],
  (∀ᵐ (x : ℝ) ∂mu, |x| ≤ 4 + √10) →
    ∀ (q H ell delta : ℝ),
      1 < q →
        q < 103 / 100 →
          50 < H →
            H < 51 →
              0 ≤ ell →
                ell * q < 7 / 200 →
                  0 < delta →
                    (∀ᵐ (x : ℝ) ∂mu, 1 ≤ x ^ 2 ∧ x ^ 2 ≤ 1 + H) →
                      ∫ (x : ℝ), x ^ 2 ∂mu = q →
                        ∃ c,
                          0 < c ∧
                            ∃ T,
                              (∀ t ∈ T,
                                  MeasureTheory.Integrable (fun x => Real.exp (t * (x ^ 2 - q))) mu ∧
                                    0 < ∫ (x : ℝ), Real.exp (t * (x ^ 2 - q)) ∂mu) ∧
                                ∀ R ∈ Shao.OQ3.sourceFarEnergySet q H delta,
                                  ∃ t ∈ T,
                                    ell * q * (R - 1) ^ 2 + c <
                                      t * (q * R ^ 2 - q) - Real.log (∫ (x : ℝ), Real.exp (t * (x ^ 2 - q)) ∂mu)
DECL Shao.OQ3.exists_source_far_energy_exponential_cover._simp_1_6
TYPE ∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] {a : G₀} (n : ℤ), a ≠ 0 → (a ^ n = 0) = False
```

逐actual项核查，而非用“generated”总标签跳过：

1. `_simp_1_7`：AddMonoidWithOne/CharZero下**自然cast**n+1非零，实际Algebra/CharZero/Defs:79–80 Nat.cast_add_one_ne_zero从自然succ非零得到。它不声称任意实x+1非零，CharZero是明确所需门。
2. `_simp_1_3`：数4的OfNat/Zero且显式NeZero4给(4=0)=False；不偷断任意特征中4非零。
3. `_simp_1_1`：数2同理，显式NeZero2已给，不需要把α默认为实数才能真。
4. `_simp_1_4`：NoZeroDivisors加a/b各非零给乘积非零，actual Algebra/GroupWithZero/Basic:84–85 mul_ne_zero内容对应。没有遗漏相乘量非零条件或隐含交换律。
5. `_simp_1_2`：数3同第2/3项，NeZero3明确；不是由OfNat自身推出非零。
6. `_simp_1_5`：MonoidWithZero/IsReduced下非零a任意自然幂非零，actual Algebra/GroupWithZero/Basic:251–258的IsReduced context与pow_ne_zero覆盖；n0时a≠0也排掉全平凡零结构问题。没有在任意有nilpotent的环无条件取消幂。
7. 唯一public实际TYPE：原同μ/hb、qH范围/ell非负/strict gap/delta正、AEenergy/真二阶矩完整；∃c正→∃同T→T中全部真可积/正Z∧全farR∃t∈T严格margin的顺序不变。prettyprint省略可推断的T类型，实际先读的完整source明确Finsetℝ，全长续行无隐藏弱化或新假设。惩罚ell*q、能量偏移qR²−q、同μZt均保留。
8. `_simp_1_6`：GroupWithZero中非零a的任意**整数**幂非零，actual Units/Basic:411–413按自然/负后继分别由pow_ne_zero/inv_ne_zero证明；n0/负幂都合法，前提a≠0必要且明示。

上述命题等式`(P)=False`是非零事实的propext归一化，无新增数学前提。7generated均在唯一public目标stem下，实际源没有authoredprivate；所有actual8TYPE已读并按各自泛型结构/标准库语义检查，不只查唯一目标或假设只有3helper。当前数学+类型判定支持CORRECT，下一阶段才核Audit是否覆盖真实全部stems/private前缀及其公理/计数、作者receipt/机械。

## 7. 最后真实机械/冻结/依赖/版本核对

全actualTYPE阶段已先持久化报告SHA256=`dae9c326ad4c42f527860e29dc1e39da7c5aab95da19b7179b8d771178235bc6`，15418bytes/142行；此后才读作者receipt/Audit源、真实AXIOMS/计数/PASS、既有build02、实际源码三端与16闭包/pins。作者叙述和成功日志没有成为前述数学判定的前提。

### 7.1 实际文件绑定

run=`/root/rivermind-data/shao-lean-20261021/runs/oq3/u17c-20261021`，worktree=`/root/rivermind-data/shao-lean-20261021/workspaces/lead-oq3`。

| 实际对象 | SHA256 | 字节/行 | 核查事实 |
|---|---|---|---|
| FarEnergyExponentialCover.lean（localdraft/worktree/run快照） | `40ee1824e49f2bf38e653edfa38363774e27a7d58c3c9e1c2b97245cfc86803d` | 4543/108 | 三端同，唯一完整publictype与scope白空格匹配 |
| scope.md / local forty-ninth-unit-scope.md | `ea2fe343d95821eedf377ccb0a36d9fdd5f32187165076395cf5b9060e527bc5` | 4447/32 | 两端同冻结scope |
| statement-review.md / local u17c-statement-review.md | `9b07e6d51cfc9d92e5e93e4d29b8dfdbe3c592a3fd77d2c3c91299f470ecb78f` | 18221/159 | 两端同已接受声明票 |
| receipt.json / local U17c-receipt.json | `b4dbbc2eae733a0da44ad16349d495d35966cc89f55ce904d3f3306a5544b409` | 5348/75 | 两端同，最后读并按实际产物核 |
| Audit.lean / local U17c-Audit.lean | `6caa244e99fd692c436ee0f2c892fda02f53f9e135839d8e3438ba6737cb7eb5` | 1634/38 | 两端同，全文核覆盖 |
| Audit.log | `c6b870243307d6598979aab332f0131697b106aaed41af2f5f66f3a7cff3d485` | 2710/50 | 全8TYPE先读，公理/gate最后读 |
| build-02.log | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` | 0/0 | 实际空文件，历史exit0由已有receipt记录，未重跑 |
| prerequisite-hashes.json / local u17c-prerequisite-hashes.json | `8ecaef08a1baf1301d83a48c910776f0f1d1bf54faa44f667b38bb4513a9477a` | 1667/18 | 两端同，16实际hash逐项匹配 |

实际source CR0、无尾空格；禁止项sorry/admit/axiom/unsafe/native_decide/implemented_by与跳kernel选项扫描为空；显式源声明只有唯一public theorem，原两imports未改。实际目标olean存在718312bytes，仅只读stat。build01修复史是receipt历史说明，不替代本轮独立proof；未重复成功target/Audit或读取下载原始失败全日志。

### 7.2 Audit全覆盖与actual公理

actual Audit全文先核唯一target存在且isTheorem，随后环境常量枚举选该publicstem下**所有生成子名**和整个 `_private.Shao.OQ3.FarEnergyExponentialCover` 前缀；逐项拒绝新axiom、调用 `Lean.collectAxioms` 检查全部传递公理只准propext/Classical.choice/Quot.sound。selector不是任意publicnamespace通配，但完整source确实仅唯一target，没有额外publichelper可被漏选；authoredprivate为0，private前缀也检查为空。

actual8项公理：

| actual项目（publicstem简写） | 实际传递axioms |
|---|---|
| _simp_1_1 | propext |
| _simp_1_2 | propext |
| _simp_1_3 | propext |
| _simp_1_4 | propext |
| _simp_1_5 | propext |
| _simp_1_6 | propext, Classical.choice, Quot.sound |
| _simp_1_7 | propext |
| exists_source_far_energy_exponential_cover | propext, Classical.choice, Quot.sound |

实际log计数 `U17C_FROZEN_THEOREMS 1`、`U17C_ALL_THEOREMS 8`、`U17C_ALL_DECLARATIONS 8`、`U17C_AXIOM_GATE PASS`。因此8owned全theorem=1public+7generated，0authoredprivate/0defs；第6节所有完整actualTYPE已独立核，不因形式PASS就默认辅助正确。真实传递白名单与内核产物只是数学/source独立检查之后的额外形式证据。

receipt身份/nonclaims正确标U17c，作者门pending independent/no commitPR at author-check time是作者检查时的历史状态，非本终票完成后的实时状态；本票不改作者收据。receipt记录成功target/Audit命令为CPU14–17、原生 `lean -M8192 -j4`，未使用ulimit-v；这是历史命令事实，本次review没有新执行或占用heavy，不干预CPU0–9外部任务。

### 7.3 实际16项闭包/pins

从actual原两imports递归重新枚举Shao源，集合恰16；**16/16实际源重算hash**同时匹配run prerequisite-hashes.json和receipt imported_project_sources_sha256，全部既有前置olean存在。A/B根源与接受终票绑定不变，无未来D或概率尾链依赖混入：

| 实际项目源 | 实际SHA256 |
|---|---|
| Shao/Basic/FinitePath.lean | `898262898f9c088e2d10e6238e411b4397387b21b1b71a2b545c5edef936e1bb` |
| Shao/OQ3/AtomProjection.lean | `0d369052c7f87122765612efdeaca5d9ac71abca861e7785c86d1f9edcc74d22` |
| Shao/OQ3/AtomicMeasure.lean | `59ddc48fb7b395f362939e58cbd9d7911685a6ed6e6574142e8a6d4ab3ee0c39` |
| Shao/OQ3/BinaryEntropyBounds.lean | `291cc2afc5e632ad8326b5d98ceb619b959a41bc8d49120d2a52bd1a0b213228` |
| Shao/OQ3/EnergyBernoulliMGF.lean | `e3bb038b2b92fac9a5341b26d437eeba046a5fd954a753fe80a7058ce32432ad` |
| Shao/OQ3/FiniteConstraints.lean | `800d9db8cb6749a31ecfe611409de92b10ea8bb2aef955bfd825ede7324f0ef0` |
| Shao/OQ3/FiniteNormalSpan.lean | `0374da4860edf8af8bbbb9172e4e93bfe9b6c37ac57672b85a4f58392475b7de` |
| Shao/OQ3/FiniteStageMeasure.lean | `1a32fb904e6ee9d2b0b48d92c4ebb3568452bb02500ce52a1a03eb01ae0256b1` |
| Shao/OQ3/InverseTilt.lean | `c7e7d19e8b70481b663bec1fd12ea9301d73313faaf35997e85aa9ba99f21811` |
| Shao/OQ3/ResonanceArithmetic.lean | `cd21a264d637bab30fed765bdc25ed09bb4ff56f6efb9c88ee09be4ca6e1648b` |
| Shao/OQ3/SampleBoundary.lean | `7660e23b71ce28ab43a4ad1d8df1862cf8a507b6bb9b41255e961f0bee0b93e2` |
| Shao/OQ3/SourceBinaryEntropyGap.lean | `f5696cc1c953b3079f0c2987a239b3d0c0003292bb3018052c80d4f1fa9254c9` |
| Shao/OQ3/SourceEnergyGeometry.lean | `3cad1d1f12583690a6acbffc749110ace2b2786831f706049583cb755ac2253a` |
| Shao/OQ3/SourceStarter.lean | `0e2a081619976f88149707c2ef9311dc909003e61d3d0f7c4e21e6c3dbbc5a6d` |
| Shao/OQ3/SummableAtoms.lean | `0ea4c64fe9ef9b45fbf44d24312771a1dbfbcc5de8448564e3e87bdf17c7178b` |
| Shao/Probability/FiniteIID.lean | `d1b565489199d55af70a27c31a0f803a2b7433e78c9197a361b3c10c0598845b` |

actual Mathlib HEAD=`807d3836b165983210ee2ecf3cd28f239436949c`，toolchain=`leanprover/lean4:v4.36.0-rc1`。lean-toolchain SHA256=`d581a24b57a4ae9e0b2132ca8ac7cc3ac336a9fc2751fe6b29414e2d434d54c4`（29bytes），lake-manifest.json SHA256=`40e8e3385f2b0c8ae56fa9de6947301472379cb62eeb83247944827c38b8af6e`（3541bytes/117行）。

消费库源码逐项同真实HEAD git对象字节一致，所对应现成olean存在（涵盖有限cover/开集与generated代数，不把库工作树改动掩盖在版本字符串后）：

| 库源（Mathlib前缀省略） | 实际SHA256 |
|---|---|
| Topology/Compactness/Compact.lean | `cdc05494e34ec5d4163211223acf44d4c980629cac5542a52ca6d7360d80754e` |
| Topology/Order/OrderClosed.lean | `011a07d8a57515c2a6bf066bf4ef24ff22eeffcc4d6115afd9ff22f5d45ded9e` |
| Algebra/GroupWithZero/Basic.lean | `ecd1e404d5269d81c7042acbb921a03dc078726935ac37120f4f3f17a9777d90` |
| Algebra/GroupWithZero/Units/Basic.lean | `1e7324f9db0a7a93972e83d49fee90d9503d27bca407912a7ad30191430d302f` |
| Algebra/CharZero/Defs.lean | `4df0a05b9b2993687b26b3baec8a128f0ac2953980f78fe0ba533ad60dc3c276` |
| Analysis/SpecialFunctions/Log/Basic.lean | `0c2f73c5a7d1a27efc9e44d02ead60112bfe10e3cfbba2407ad3dbcd1c363a97` |
| MeasureTheory/Integral/Bochner/Basic.lean | `66837a733a5514a0fd824591ac10d43063c5a5cd94c9bdbbf80025686c16c670` |

真实当前branch=`feat/oq3-far-energy-exponential-cover`，HEAD=`f2b851f4ec58229cdcd1fc7951249b9e3e02af7a`，status仅 `?? Shao/OQ3/FarEnergyExponentialCover.lean`，与作者门基线一致。本票绑定本冻结分支source/前置/pins；root另批整合旧源至main或关闭已集成PR，不改变当前C源或成为重审旧成功目标的理由。发布exact commit/PR由lead另核，不在此直接commit。

共享broker只读正常，host key SHA256=`+IZMFu9Xx6FSAhvQhtvZ3MpV70v2d+XNWcequAbsp+c`；未改连接、读取凭据或写cache。未新Lean/probe/build/rebuild/spawn/kill，也未下载任何raw全日志。

## 8. 最终完整独立裁决

JUSTIFICATION: **CORRECT。** actual完整publictype先独立盲译落盘且与冻结scope一致；实际108行全部proof/locals与真实库/承重语义已核：同μ/真实矩/AE能量门先给所有实t的真可积和正Z，strict gap和delta严格分离先于全部R构造共同c；能量可行/R正非1及p0/p1门完整。有限theta→t=theta/H先正H再取消，Bernoulli测试转真实logZ的符号/系数精确；固定t的R连续开集与真实紧性给同Finset T，无可数性/非空或t↦积分连续的额外隐藏门。返回全T真normalizer条件和同c/T在全R外的严格cover。全部8actualTYPE/7generated逐项结构/非零门正确；最后源码三端、16真实闭包、库pins/实际已保存产物/全部传递公理白名单匹配，未发现数学/source/类型/机械绑定缺口。

作者形式门与本完整独立判定分开，绿色审计没有替代数学；不把标量覆盖称Legendre最优或actualKL身份。真实完成的是**同μ有限实指数cover**，没有真实iid/加权事件积分比较或概率far界，更没有source3一般唯一全局鞍点、generalKL/RN/DPI、完整17/19/LLT/hW/WC或根闭合，无最弱/最优/新颖性主张。sourceEll若未来专化仍是log(31/30)<1/30，不是1/30，本proof消费的是一般ell及显式strictellq gap。根 **A/B/C/D、source3/generalKL/真实far概率/full17/19/LLT/hW均OPEN**。

本轮只写拥有的新local终票及授权run/proof-review.md；未改source/scope/receipt/旧票/shared/cache，不spawn/Lean/probe/build/rebuild/commit/rawlogdownload或读作者future/candidate/实施notes。上传后另核两端SHA，lead全文读取后才进入C发布。
