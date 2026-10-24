# 单元158–159：来源参数、实际居中弱事件与自身 C1 预算的独立完整复核

STATUS: CORRECT

统一结论针对冻结的 `Shao.C2.AuxiliarySourceParameters` 与 `Shao.C2.AuxiliaryOwnC1Budget`：合计5条公开源定理、14条生成定理、19个实际所属、60328字节完整实际类型、0全局定义值。前半复核单元158，后半复核父实例在封存前明确追加的单元159；这次追加未另开模型上下文。所有实际所属、全部源证明、生成命题的完整类型及证明义务、实际消费接口、论文来源及现存服务器内核与传递公理证据均已复核，未发现关键数学或语义缺口。审阅者不是作者，未改形式源码，未运行 Lean、公理审计或任何旧成功检查。父实例仍负责最终资格确认、后续集成和发表。

单元158证明：来源时间条件与显式充分秩条件支付小参数条件和实际均值漂移界，再把每条具有足够真实原始能量的路径上的来源弱端点事件送到真实居中路径上的弱端点事件。单元159进一步支付实际居中分布的数据、自身归一化截断矩预算及其≤rhoStar/2的充分秩条件。二者都没有证明实际 C1 概率调用、乘积事件传输或完整稀有后缀估计。当前注册表 v85 的原始 C1 已完成；C2/C12 仍开放。本报告不沿用历史审阅中已过时的“原始 C1 开放”表述。以下截至“单元159追加复核”标题的“本单元”特指158。

## 独立性、冻结与证据边界

审阅上下文：全新 `gpt-6.1-sol`，推理力度 `xhigh`，角色为唯一最终独立审阅者。写入范围仅为 `drafts/c12-lane/auxiliary-source-parameters-final-review-v1/`。没有子代理、额外聊天、Goal、计划任务、服务器写入、缓存改动或发表操作。令牌输入、缓存输入、输出及其中推理子集均无可用计量，因此在机器报告和释放文件中分别记为 null。

作者 `RELEASE.json` 记载作者写入权和执行权已释放、无在途任务。已验证其来源、对象、收据和冻结哈希与实物一致。审阅期间只读进程观察没有发现本目标模块的 Lean/lake 重任务。C12 的 CPU14–17、单一 c12-heavy.lock、-M8192 -j4 限额与收据相符；审阅没有取得或占用重执行锁。

关键字节绑定如下：

| 工件 | SHA256 |
|---|---|
| AuxiliarySourceParameters.lean | f9407e08fe5c02a20930e533f1db1d390a985b089256524493b5b8aa214baf4e |
| 产出及当前导入对象 | 7901360029879f251d1d3b1a07900966e28254ee3791bef701ed44bb2a025cf1 |
| receipt.json | 464eb29dcc2c54afcf37a49552355342a9c8070b583d882442440e1e34d39645 |
| frozen.lean.txt | 8b120bc5a1f7bbff80b25aa63c34ae63ee2d4bcacfb4717a7efc9e4f8895f063 |
| actual-owned-types.txt，21181字节 | 33758a9c43b0f28e7fa078a26fdb3d0ebd037389246ed5ad82d09ebcc23a20ad |
| actual-definition-values.txt，0字节 | e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855 |

已完整读取6430字节最终源码、1796字节冻结声明、source-and-proof.md、freeze-record.json、freeze-comparison.json、receipt.json、RELEASE.json、owned-audit.json、OwnedAudit.lean 和 finish-receipt.py。冻结文件包含唯一导入、选项、命名空间及两条完整声明。剥除两段证明后与冻结文件逐字节相同。无新私有声明、全局定义或生成声明；局部 c、d 和五个结论中的 let 均不是新增全局值。

已完整阅读两段实际展开类型。它们是实数上的命题、自然数 n、字面原生 `Measure.tilted`、字面真实积分均值以及 `Fin n → ℝ` 路径；没有被替换成代理分布、方差能量、概率断言或参数化的未支付漂移假设。机器报告逐所属声明保留完整类型块及其哈希，便于父实例确定覆盖范围。

## 来源与原题范围

只读原稿 `C:/game/shao/current/c12/supplement.tex` 的 SHA256 为 b99f2ac4d2f39dd39772d98a5702b7a923c2f10f8730a08fc1b4cd6bba4742bd；`main.tex` 的 SHA256 为 beb00f718487e36de433175c97f1d500cb48e7a92ce5bd5ad5d62bb132122d06。二者均未改动。

完整阅读 main.tex149–245：原始样本是均值零、有限正二阶矩的 iid 实随机变量；高阶矩要求为2<p≤3；最大值从正前缀起算；所有 crossing 是弱乘法事件，含全零样本；严格生存是其字面补集。原始 C1 与 C2 的分母、区间 I_n 和双侧最大值不能由本单元的有限路径蕴含替代。

补充稿4682–4697将此处辅助分布的规范化写为 EX=0、EX²=1、β=E|X|³。5046–5067定义 v_x=√(9x²/4−1)。本单元的第二条定理正使用这些真实对象。有限三阶矩前提施加在辅助预处理分布 nu 上，并没有替换或强化原始 C2 的有限二阶矩样本律。

完整阅读5094–5111及5123–5130，并读到相邻5113–5139以界定后续缺口。5094–5101在 st≤Lx² 下使用真实能量倾斜，要求 |μ_s|≤2sβ 和足够小的 √l|μ_s|；5103规定 sβ²≤1/128；5123–5130在 T_l≥l/8 上使用 y_x=v_x−1/[100(1+x)]，要求弱事件居中传输。第一条定理支付所需的数值条件，第二条接到真实 μ_s 和真实路径事件。居中方差、三阶矩界的旧接口本已存在；它们到自身 C1 合法预算和概率估计的应用仍未包含在本单元。

来源充分秩的解释也正确。4984定义 H=Kβ²(1+x)^6、m=⌈H⌉；5094的 l=t 或 t−1，且后文采用 l≥t/2。若已知来源 l≥Kβ²(1+x)^6/2，固定 L 后一次选择 K≥8000000(1+L)²，就可推出本单元的秩界。来源 s≥0、l≤t、st≤Lx² 又给 sl≤Lx²。这是明确记录的后续确定性实例化，不是本单元已经形式化了 t、l、m 的全部关系；也没有把待证漂移界当作新前提。K 可以在 L 后选择，常数没有偷依赖 n、x、nu。

## 所属声明一：auxiliary_rare_parameter_payment

源码9–91，实际种类 theorem，公开源声明，传递公理恰为 propext、Classical.choice、Quot.sound。冻结声明为：

```lean
theorem auxiliary_rare_parameter_payment
    (beta L s : ℝ) (hBeta : 1 ≤ beta) (hL : 0 ≤ L) (hs : 0 ≤ s)
    (n : ℕ) (x : ℝ) (hx : 1 ≤ x)
    (hTime : s * (n : ℝ) ≤ L * x ^ 2)
    (hRank : 4000000 * (1 + L) ^ 2 * beta ^ 2 * (1 + x) ^ 6 ≤ (n : ℝ)) :
    0 < n ∧ 4 * x ^ 2 ≤ (n : ℝ) ∧ s * beta ^ 2 ≤ 1 / 128 ∧
      Real.sqrt (n : ℝ) * (2 * s * beta) ≤ 1 / (1000 * (1 + x))
```

语义：它对所有满足列出条件的实数 β,L,s,x 和自然数 n 成立；无渐近量词、随机性、额外整数下限或隐藏均值条件。结果中的 n>0 是结论而非前提。1/128 与1/[1000(1+x)]都是实数除法，4和4000000的系数未改变。

完整证明逐步复核如下。

1. 16–22置 c=1+L、d=1+x。由 L≥0、x≥1、β≥1 得 c≥1>0、d≥2>0、β>0、x≥0。`change` 只把 hRank 中定义性相同的1+L和1+x换成 c,d，没有改变前提。
2. 23–29从 `(2000 c β d³)²=4000000 c²β²d⁶≤n` 推出 `2000 c β d³≤√n`。两个平方根比较对象都已非负；`sq_le_sq₀` 的 `.1` 是从平方不等式到原不等式，方向正确。`Real.sq_sqrt` 使用 Nat.cast_nonneg n，因此没有对负数平方根作非法消去。
3. 30–31的左边严格正，故 √n>0，`Real.sqrt_pos.mp` 得实数 n>0。最后 `Nat.cast_pos.mp` 正确返回自然数 n>0，不是把实数取整。
4. 32–42由 c≥1、β≥1 得 c²≥1、β²≥1及 c²β²≥1。`mul_le_mul` 的两个非负侧条件分别是0≤1和0≤c²。x²≤d⁶也成立；独立核对可由 d=1+x≥1、0≤x≤d，得 x²≤d²≤d⁶；源码用展开多项式和 x³至x⁶非负支付同一事实。将它乘以非负 d⁶，得 x²≤c²β²d⁶。
5. 43–50乘以正4，再把4放大到4000000。被乘因子 c²β²d⁶非负，最终由 hRank 得4x²≤n；没有反向放大错误。
6. 51–61中 L≤(1+L)²=c²，因为差为1+L+L²≥0。结合 x²≤d⁶、x²≥0、c²≥0，得 Lx²≤c²d⁶。乘非负128β²后，用128≤4000000和 c²β²d⁶≥0，得到128β²Lx²≤n。乘法重排由 ring/nlinarith 完成，系数和 β 次数均正确。
7. 62–71把 hTime 乘以128β²≥0，重排为 `(128sβ²)n≤128β²Lx²≤n`。68–70仅消去此前证明严格正的实数 n。原生 `mul_le_mul_iff_of_pos_right hNpos` 是 `b*n≤c*n ↔ b≤c`，其中 c=1；`one_mul` 对齐右侧。因此128sβ²≤1，除以正128得 sβ²≤1/128。这里不需要 s>0，也没有消去 s、β 或 L。
8. 72–79为漂移主步骤。设 D=√n(2sβ)。恒等式 `c d² (1000dD)=(2000cβd³)(s√n)` 正确，因为两边均为2000csβd³√n。根秩界乘以 s√n≥0后得左边≤√n(s√n)=s(√n)²=sn。s=0 时保持合法，未除以 s。
9. 80–86由 L≤c、x²≤d²，乘法的侧条件 x²≥0、c≥0，得 Lx²≤cd²。因此 `cd²(1000dD)≤sn≤Lx²≤cd²`。`cd²>0` 由 c>0,d>0保证。`mul_le_mul_iff_of_pos_left` 消去的是左侧正因子 cd²，右侧以 mul_one 对齐，得1000dD≤1。
10. 87–90使用1000(1+x)>0。`le_div_iff₀` 的 `.2` 将 `D*1000(1+x)≤1` 转回所需 D≤1/[1000(1+x)]。与1000dD只差交换律。没有以非严格非负条件进行除法；最终四个合取按冻结顺序返回。

第一条定理因此有完整代数证明。较大的充分常数并非必要最优常数；本单元没有声称最优性或研究新颖性。

## 所属声明二：auxiliary_source_mean_and_weak_event

源码93–129，实际种类 theorem，公开源声明，传递公理同样恰为 propext、Classical.choice、Quot.sound。冻结的全部前提和结论为：

```lean
theorem auxiliary_source_mean_and_weak_event
    (nu : Measure ℝ) [IsProbabilityMeasure nu]
    (h2 : Integrable (fun z : ℝ => z ^ 2) nu)
    (h3 : Integrable (fun z : ℝ => |z| ^ 3) nu)
    (hmean : (∫ z : ℝ, z ∂nu) = 0)
    (hnorm : (∫ z : ℝ, z ^ 2 ∂nu) = 1)
    (L s : ℝ) (hL : 0 ≤ L) (hs : 0 ≤ s)
    (n : ℕ) (x : ℝ) (hx : 1 ≤ x)
    (hTime : s * (n : ℝ) ≤ L * x ^ 2)
    (hRank : 4000000 * (1 + L) ^ 2 * (∫ z : ℝ, |z| ^ 3 ∂nu) ^ 2 *
      (1 + x) ^ 6 ≤ (n : ℝ)) :
    let beta : ℝ := ∫ z : ℝ, |z| ^ 3 ∂nu
    let rho : Measure ℝ := nu.tilted (fun z => -s * z ^ 2)
    let mu : ℝ := ∫ z : ℝ, z ∂rho
    let a : ℝ := Real.sqrt ((9 / 4) * x ^ 2 - 1)
    let y : ℝ := a - 1 / (100 * (1 + x))
    0 < n ∧ 4 * x ^ 2 ≤ (n : ℝ) ∧ s * beta ^ 2 ≤ 1 / 128 ∧
      Real.sqrt (n : ℝ) * |mu| ≤ 1 / (1000 * (1 + x)) ∧
      ∀ v : Shao.Path n, (n : ℝ) / 8 ≤ Shao.energy v →
        a * Real.sqrt (Shao.energy v) ≤ |Shao.prefixSum v n| →
        y * Real.sqrt (Shao.energy (fun i => v i - mu)) ≤
          |Shao.prefixSum (fun i => v i - mu) n|
```

实际类型中的五个 let 都是这些明确对象的定义性绑定。没有对外全称量化一个任意 rho 或 mu，没有把 |mu| 改为任意上界符号，也没有遗漏真实积分或能量的测度/路径参数。外层 IsProbabilityMeasure、h2、h3、hmean、hnorm 均保留。h2/h3 的显式可积性使积分不是利用不可积时取零的约定来伪造矩条件。

完整证明逐步复核如下。

1. 115行展开五个结论 let。它们与旧接口的同名局部定义在定义性相等意义下相同；nu、s 和路径长度 n 未被替换。
2. 116–117消费单元152的 `auxiliary_absolute_third_moment_ge_one nu h2 h3 hnorm`。该接口要求概率测度、平方及三阶绝对矩可积、平方积分为1，结论正是1≤真实 β。本单元逐项具备这些条件，无需先假设 β≥1。
3. 118–119消费本模块第一条定理。实际 hRank 已经使用同一真实三阶绝对矩，因此与 let beta 定义性相等。参数 L,s,n,x、时间界和秩界均不变，产出 hn、hN4、hSmall、hBound。
4. 120–122消费单元152的 `auxiliary_energy_tilt_small_parameter`，传入原 nu、h2、h3、hmean、hnorm、s、hs及刚支付的 hSmall。该接口的十项合取依次为倾斜概率性、id可积、居中id可积、居中积分零、居中平方可积、居中绝对三次方可积、真实均值上界、方差下界、方差上界、居中三阶矩上界。模式匹配第七项 hMean 正是 `|mu|≤2*s*beta`；没有把方差或其他合取误当成均值界。
5. 123–124将 hMean 乘以非负 √n，得到 `√n|mu|≤√n(2sβ)`，再与 hBound 传递，支付 `√n|mu|≤1/[1000(1+x)]`。这里没有额外漂移前提；hMean 的 rho 是字面原生倾斜 rho，mu 是它的真实积分均值。
6. 125–128返回前四项后，对任意真实有限路径 v、原始能量条件及弱 crossing，调用单元157的 `auxiliary_centered_source_weak_event v mu x hx hN4 hEnergy hDrift hCross`。调用参数一一对应，其阈值为同一 a,y，能量为同一 `Shao.energy v`，居中坐标恰为 `v i - mu`，终点和恰为 n处 `prefixSum`。旧接口不额外要求随机路径、iid样本、正中心能量或概率事件；所以全称逐路径结论完整，并无从确定性蕴含跳到概率结论。

本条定理只提取旧小参数定理的均值界并接到事件接口，其余九项即使未公开返回也不构成缺失前提。它仍未公开或证明合法 C1 预算，因此报告没有把旧方差/三阶矩界自动解释为已完成 C1 调用。

## 实际被消费接口与旧证据复用

直接导入 `Shao.C2.AuxiliarySourceEvent`，其消费所需的 AuxiliaryEnergyCentered 沿现有导入链到达。已阅读三个消费接口的完整源声明及各自完整实际展开类型，源接口与展开类型相符。没有重审旧证明，也没有重跑旧成功检查。四份旧父级接受记录均为 QUALIFIED；机器校验其报告/验证/观察/释放文件哈希未变。

| 接口及本轮用途 | 精确源/对象绑定 |
|---|---|
| 单元152 auxiliary_absolute_third_moment_ge_one，支付真实 β≥1 | AuxiliaryEnergyCentered.lean 465e3efe00bab80dea7207acb6da86198d6c28a4551908d035c51446aba8fd38；对象102b9e26587ecd4db4acd77030a6603afc6e776a4a13d754462e8ebb2882d505 |
| 单元152 auxiliary_energy_tilt_small_parameter，提取真实倾斜均值界 | 同一精确模块；完整类型导出19628字节、859e12ac5283cddf42f8eabf00e92bcfbfa35a0a2966d4c6a7e0822ac6313382 |
| 单元157 auxiliary_centered_source_weak_event，完成真实弱事件居中蕴含 | AuxiliarySourceEvent.lean bf101dd5ed9a8438da6203ca0397e11aa7dc11c32bd735e50ed1e983795b152b；对象617fe62ee8130d7d616360f845f72fffe99481d06ccdddba3dda71b1d26d406c；完整类型导出10728字节、2776700762f5c126d5345095b89a6e577808791ab5cdb833f59cfc933c53869f |

新消费交互的符号和顺序已经逐项检查：旧均值定理的方差是 rho 下 id 的真实方差；新单元只拿均值界而不改变它的积分对象。旧事件定理的 mu 可以是任意实数，新单元选择真实均值，强于其需要；hRank4和hDrift由第一条支付。`Path n=Fin n→ℝ`，`prefixSum` 是取索引值小于给定秩的真实坐标和，n处是全部坐标和；`energy` 是全部坐标平方和，居中能量不是 n乘方差。

receipt 的11个项目依赖源文件与11个当前导入对象已绑定到既有合格证据，包括能量倾斜/矩/居中/Laplace、乘积低能量、高斯支付、居中事件、来源事件和三个公共定义模块。当前仅复用其精确源/对象及合格证明证据，不授予新增范围。

原生库接口已直接只读确认：GroupWithZero/Defs.lean296–307的两个带正因子 iff 及别名；GroupWithZero/Basic.lean758–759的平方比较和1128–1129的正除法；Analysis/Real/Sqrt.lean的平方根非负、平方还原和正性。选中三个 mathlib 源文件均与钉住807d3836b165983210ee2ecf3cd28f239436949c的 Git 原始字节一致。编译日志提示共享 mathlib 工作区有本地变更；本轮不改它，所需接口已按实物、钉住源码及现有合格对象核对，没有依赖该提示来猜测正确性。

## 边界与反例攻击

| 情形 | 独立核对 |
|---|---|
| n=0 | 秩左边≥4000000·1·1·2⁶=256000000>0，故不可满足 hRank；源码先严格证明实数n>0再消去，未预设结论。 |
| x=1 | d=2>0；a=√(5/4)，y=a−1/200。单元157允许 hx 等号且已支付4≤n，所有分母正；没有用 x>1。 |
| β=1 | 平方比较只要求β≥1，根秩左边仍正；无除以β−1或严格矩间隙，完整覆盖。 |
| s=0 | hScale乘以s√n=0合法，漂移界成为0≤正数；第二条的旧均值界强迫mu=0，居中传输仍成立。 |
| L=0 | n>0与0≤s、sn≤0强迫s=0；消去因子为c=1而不是L，无除零。 |
| hRank或hTime取等号 | 全链使用≤，平方根、正乘消去和正除法均保留等号；未把弱结论偷偷改成严格结论。 |
| 原始能量=n/8 | hEnergy是≤，按单元157弱边界直接传递；n>0确保原始能量严格正，但本单元没有对其作除法。 |
| 弱 crossing 取等号 | hCross和输出均为≤，实际接口没有排除等号；不存在误用严格补集。 |
| 居中能量为0 | 结论仍是乘法事件，左右都是0，合法；无以居中能量作分母。 |
| mu为负、原坐标重复或全部相同 | 始终使用|mu|和|prefixSum|，任意Fin n路径均覆盖；无需正mu、坐标不同、连续分布或非格点。 |
| 原始全零路径 | 由于n>0且原始能量要求≥n/8，它不在此局部前提中；没有声称消除了原始根定理中全零弱事件义务。 |

这些是完整一般证明中的边界检查，并非用有限数值测试替代证明。没有为救证明改变或补充冻结前提。

## 原始执行、失败保留与传递公理

服务器 pinned Lean 为 leanprover/lean4:v4.36.0-rc1，mathlib 为807d3836b165983210ee2ecf3cd28f239436949c，包视图解析为 shared-v34/packages。分支 author/c12-auxiliary-centered-v71，HEAD aef587dd277f159314297cef02b352057d7102ec。作者 attempt002 的目标源码与当前工作树及本地冻结完成源码均相同；产出 .olean 与当前 `.lake/build/lib/lean/Shao/C2/AuxiliarySourceParameters.olean` 相同。内核原始退出码0；审计原始退出码0。此次审阅只读验证并复用，不声称自己重新执行了检查。

attempt001的6408字节完整失败源码、原命令和1144字节失败日志已阅读，永久保留。它在69行误用 `mul_le_mul_right hNpos`，在85行误用 `mul_le_mul_left`，因它们不是所需的 iff 而无法投影 `.mp`。attempt002仅把这两处替换为带严格正因子的 native iff 别名；确定性差异核对显示只有这两行证明表达式变化，全部导入、上下文及两条声明不变。失败退出码1未被抹除。成功日志165字节含KERNEL_EXIT=0。原始审计日志21406字节被完整核算：21181字节两段类型块，0字节定义值，以及225字节的警告/总数/成功标记，合起来与实物逐字节一致。

OwnedAudit.lean不是只按公开名前缀筛选：它遍历环境全部常量，以 `env.getModuleIdxFor?` 和模块索引确定真实所属，故私有及生成名也在筛选范围。它对每个所属调用 `Lean.collectAxioms`，逐一拒绝白名单之外公理，记录完整实际类型和定义值；并检查两公开名实际种类为theorem。实物 map 的两个实际所属名与两条源码公开声明完全相同，种类都是theorem，故不是靠硬编码公开数2漏掉其他对象。由实物推导计数：1模块、2公开源定理、2实际所属、2实际定理、0私有、0生成、0非定理值。

已完整阅读钉住 Lean 安装中的 Lean/Util/CollectAxioms.lean，6654字节，SHA256 b39bd22253a76816ee6d24284e69674d0b491be343fd71f9ee9376833d1485f6。它从 kernel checked 环境访问定理/定义/不透明项的类型和本体，递归访问所用常量；导入模块通过导出时预计算的公理闭包复用，局部缓存只防止重复和递归循环。故本审计是传递公理闭包而非仅直接名字清单。每个本单元实际所属的闭包恰为 propext、Classical.choice、Quot.sound，没有 sorryAx 或新增公理。形式源也无 sorry、admit、axiom、unsafe、native_decide。

## 只读查询失误与最终交接

截至单元158阶段有三处已保留的只读查询问题，均不影响源码或执行结果：(1)首次观察脚本不兼容旧观察中的 expected/actual 字段，9条预期哈希读为null并产生false；原文件保留，后续只补核这9项，全部匹配；(2)PowerShell ConvertFrom-Json因旧报告同时有STATUS/status而拒绝解析，改用Python读取，无旧文件改动；(3)首次猜测CollectAxioms位于/root/.elan而文件不存在，随后读取activate.sh中的ELAN_HOME定位到项目独立toolchains/elan并完整读取。没有把这些查询失误当成证明失败或成功，未重播任何内核/公理命令。

最终只读观察重新核对已选中的精确源、对象、原始证据和原生接口哈希。`validation.json` 从实际源/所有权图推导覆盖、检查全部旧父级接受哈希、源码冻结、类型块、空值、两个证明差异及本报告的一致性；这些确定性检查不替代本报告中的逐步数学审阅。最后 writer-release.json封存目录并释放本审阅上下文的写入和执行范围，标明零在途；封存后不再修改报告。

单元158结论：两条冻结定理均 CORRECT。其下一依赖159在父实例明确授权下追加到本同一审阅上下文，复核如下。

## 单元159追加复核：范围、冻结与精确工件

STATUS: CORRECT

追加目标是辅助居中律的自身 C1 预算，来源为同一补充稿5103–5111。作者在本报告封存前明确交付并释放单元159，审阅仍仅写同一审阅目录。完整读取8619字节最终源、2530字节冻结声明、39147字节17个完整实际类型、0字节定义值、全部作者说明/审计代码/收据/释放/冻结比较及预执行格式修正记录。两次失败源快照及三次原始命令和内核日志均完整读取；第三次源与本地及工作树相同。

| 单元159工件 | SHA256 |
|---|---|
| AuxiliaryOwnC1Budget.lean | 9a79ae9ff5b8a5d3e97d49ed6affa896075c99b9ed603018bd7318c80c1c74a2 |
| 产出及当前导入对象 | ba2a981ab9cfcfede91de9b19016097bc3a3787e3261108e5242fb060edd152c |
| receipt.json | be9be65a41f3a94f9f044934a137b36cd9803f702aeb9c2e5a9d7f2b0ffb372d |
| frozen.lean.txt | 3d8d8d7a1d32897db1390d75b0ea95dd4e3364809f20a0cd502c8884efc18e43 |
| actual-owned-types.txt | aa1f818d2077ee3889ce9eea91b343eab9697969f3a5e8eb86a850aeb371ef61 |
| owned-audit.json | 5fd5f40b971ef11287a62e12dd626364e4f8bf050182247d7f6d10881787819b |

三个头在三次尝试中都与冻结文件完全一致。真实所属 map 为3条公开源定理加14条生成 `_simp_1_*` 定理；0私有源定理，0定义/其他种类。所有真实所属而非仅公开名字均进入公理审计。

## 单元159声明一：auxiliary_normalized_cubic_budget

完整冻结头及完整实际展开类型均已阅读；JSON保留完整头、完整源证明及完整类型。该声明对任意实数上测度 chi 成立，不要求其为概率测度：给定平方和绝对三次方可积、真实平方积分≥1/2、β≥0及真实三阶矩≤12β、自然数n>0、y≥0，定义 sigma=√(∫z²dchi) 和 eta=map(z/(sigma√n))chi，结论为字面 `Shao.truncationBudget eta n y ≤ 48β(1+y)³/√n`。无抽象预算占位，也不先假设归一化律的预算。

完整证明的独立推导：令 t=√n>0，t²=n，m2=∫z²dchi≥1/2。sigma>0且sigma²=m2。因为sigma非负而sigma²≥1/2，sigma≥1/2；于是sigma³=m2·sigma≥(1/2)(1/2)=1/4。这是有意使用较松的充分常数，并非错误地声称sqrt(1/2)=1/2。源码 hSigmaCube 的 `mul_le_mul hSecond hSigmaHalf` 的侧条件分别为1/2非负和m2非负，方向正确。

令c=(1+y)/(sigma t)≥0。对于任意z，字面F(cz)=(cz)²min(|cz|,1)≤(cz)²|cz|=|cz|³=c³|z|³。平方因子非负保证乘 min≤abs 合法；最后一步用c≥0，不能漏掉绝对值的符号。F(cz)的可积性来自既有 `integrable_truncationF_mul chi h2 c`，右侧可积来自h3常数乘法，故 `integral_mono` 的两侧可积条件都具备。得到∫F(cz)dchi≤c³∫|z|³dchi≤12βc³。

归一化映射z↦z/(sigma√n)可测；被积函数z↦F((1+y)z)连续，来源是明确 `continuous_truncationF.comp`。用 `integral_map` 得真正预算等于n∫F(cz)dchi；其中(1+y)·[z/(sigma√n)]=c z是同一个实数恒等式。没有用积分换元来偷换测度，也没有假设不连续F的可测性。最终typed hCont精确限定函数自变量和参数y，修复了早期函数推断失败。

将上述积分界乘n>0，再用t²=n、sigma>0、t>0得到n·12βc³=12β(1+y)³/(sigma³t)。源码两处field_simp的消去因子只有已严格正的sigma、t及其乘积/幂，未除以β、y、积分值为零的量。最后由sigma³≥1/4且48β(1+y)³≥0，有12β(1+y)³≤48β(1+y)³sigma³。乘法消去t后，正分母不等式给所需48β(1+y)³/t。`div_le_iff₀` 使用sigma³t>0而非仅非负。全部代数恒等式、合取外 let 和实数除法均与实际类型相同。

此证明对于任意chi合法，因为换元只需可测性而积分比较两侧显式可积；没有隐含概率性或有限总质量。β=0时若前提可满足则上界为0，整个推理仍不除以β；n=0明确排除。即使chi退化/非对称/有原子，也不影响积分论证。

## 单元159声明二：auxiliary_centered_law_and_own_budget

完整冻结头和实际类型均保留nu的概率性、平方/三阶绝对矩可积、均值0、二阶矩1、s≥0、sβ²≤1/128及n>0。结论的六个let是字面β、原生rho=nu.tilted(−sz²)、实际mu=∫zdrho、chi=map(z−mu)rho、sigmaSq=∫z²dchi以及eta=map(z/(√sigmaSq√n))chi。

结论十项按顺序为：chi概率性；chi下id可积；chi真实均值0；chi下平方可积；chi下绝对三次方可积；sigmaSq等于rho下id的真实方差；sigmaSq≥1/2；sigmaSq≤2；chi三阶绝对矩≤12β；对所有y≥0的自身截断预算上界。实际展开类型中的And嵌套顺序与源码一一相符，没有返回nu的方差或错用rho的原始二阶矩。

证明先消费既有合格单元152的完整小参数接口，模式匹配得到真实rho概率性、居中可积/零均值/平方与三次方可积、rho方差上下界、居中三阶矩界。小参数前提与同一真实β定义性相同。把rho概率性设置为局部实例后，由可测仿射映射推得chi概率性。`integrable_map_measure`的方向`.2`将rho下g(z−mu)可积送到chi下g可积：分别对g=id、g(z)=z²和g(z)=|z|³使用，恰好消费hCentered、hSquare、hCube。目标g均连续，因此AE强可测条件由真实函数提供；映射z−mu可测。

对均值应用integral_map得到∫z dchi=∫(z−mu)drho=0；对平方应用同一换元得到sigmaSq=∫(z−mu)²drho。原生 `variance_eq_integral` 对可测id的表达式为Var[id;rho]=∫(id−rho[id])²drho，且mu=rho[id]，故反向等式正好是所需hVar。没有把总方差、条件方差或任意中心常数混淆。虽然声明没有另写Var[id;chi]=sigmaSq，chi均值0已确保sigmaSq是其真实中心二阶矩；本结论准确返回的是自身平方积分与rho方差的相等式。

对三阶矩换元后使用原hThird，得到chi第三绝对矩≤12β。β≥0通过旧矩下界1≤β支付；hVar将旧[1/2,2]传到sigmaSq。然后对每个y≥0调用本模块第一条，参数测度就是chi，其h2/h3/hSecond/hThird均刚刚证明，sigma及eta与自身真实二阶矩的定义性匹配。没有用nu的单位方差替代居中chi的自身sigmaSq。

这支付了来源5103–5111所需的真实居中律数据和预算上界。它还没有调用C1概率定理，也没有生成一个任意样本族或iid乘积。反射律的概率应用仍属于下一消费者；第一条任意chi的通用界可供其使用，但本报告不把它包装成反射概率估计已完成。

## 单元159声明三：auxiliary_own_budget_rank_payment

冻结与实际类型均要求β≥0、rhoStar>0、x≥0、0≤y≤2x、n>0以及n≥(768/rhoStar)²β²(1+x)^6；结论是48β(1+y)³/√n≤rhoStar/2。常数768、48、384和平方/六次方均逐项核对。

令d=1+x≥1、t=√n>0、w=(768/rhoStar)βd³≥0。hRank重写为w²≤t²，两个对象非负，所以同一平方比较给w≤t。乘正rhoStar并以rhoStar≠0消去768/rhoStar，得768βd³≤rhoStar t，除以正2得到384βd³≤(rhoStar/2)t。源码field_simp此处不需要β或d非零，只需要已经给定的rhoStar>0。

由0≤y≤2x得0≤1+y≤2(1+x)=2d，三次方单调性给(1+y)³≤8d³。乘48β≥0得48β(1+y)³≤384βd³≤(rhoStar/2)t；最后t>0允许除法，结论成立。x=0时y=0，β=0时w=0，所有≤和等号端点保留；不要求β≥1或x≥1，故这是合法的更一般代数接口。rhoStar=0和n=0明确不在声明中，不能将其代入分母。

来源l≥Kβ²(1+x)^6/2时，一次选择K≥2(768/rhoStar)²即可实例化本秩界。与158的K≥8000000(1+L)²同时要求只需取两者最大值，常数依赖只在已固定的L、rhoStar上；没有改变原来源的选参次序。来源y∈[1,2x]是此声明0≤y≤2x的子范围。

## 单元159全部14个生成所属的证明义务

已完整读取所有17段实际类型；其中14个生成名分为第一条和第三条各7个。同后缀在两组的语义相同，但JSON逐个保留各自真实类型块、哈希、公理列表和审阅结论，未因同形而少计。它们是field_simp/norm_num简化中的命题等式，形式为 `(P = False)`，不是新数学假设或数值近似。对其完整类型进行独立一般推导，配合来源所在源证明和原始内核/全所属审计，不仅凭编译通过放行。

| 生成所属（两个公开前缀均分别覆盖） | 完整类型的数学内容及证明 |
|---|---|
| auxiliary_normalized_cubic_budget._simp_1_1；auxiliary_own_budget_rank_payment._simp_1_1 | 任意带Zero/OfNat2/NeZero2的类型，命题2=0等于False。NeZero实例就是2≠0；由其否定得到(2=0)↔False，再由propext得到命题等式。无需假设该类型是实数。 |
| auxiliary_normalized_cubic_budget._simp_1_2；auxiliary_own_budget_rank_payment._simp_1_2 | 同上但numeral3；只消费NeZero3，完整覆盖所有量词和类型类实例。 |
| auxiliary_normalized_cubic_budget._simp_1_3；auxiliary_own_budget_rank_payment._simp_1_3 | 同上但numeral4；只消费NeZero4，没有默认为CharZero。 |
| auxiliary_normalized_cubic_budget._simp_1_4；auxiliary_own_budget_rank_payment._simp_1_4 | 任意Mul/Zero/NoZeroDivisors类型，a≠0且b≠0推出(a*b=0)=False。若ab=0，则无零因子条件给a=0或b=0，分别矛盾；再用命题外延。没有交换律或消去律的隐藏要求。 |
| auxiliary_normalized_cubic_budget._simp_1_5；auxiliary_own_budget_rank_payment._simp_1_5 | 任意MonoidWithZero及IsReduced，a≠0则对任意自然数k，(a^k=0)=False。若某次幂零则a为幂零元，IsReduced使a=0，与前提矛盾；k=0也包含。该生成类型带有实际IsReduced实例，未把无零因子或k>0作为未写假设。 |
| auxiliary_normalized_cubic_budget._simp_1_6；auxiliary_own_budget_rank_payment._simp_1_6 | 任意GroupWithZero，a≠0则对任意整数k，(a^k=0)=False。非零元为可逆元，其正/零/负整数次幂均非零；零指数是1，负指数为非零逆元的自然幂。完整覆盖整数指数，未误读为仅自然幂。两项闭包为三项白名单。 |
| auxiliary_normalized_cubic_budget._simp_1_7；auxiliary_own_budget_rank_payment._simp_1_7 | 任意AddMonoidWithOne及CharZero、自然数k，((k:R)+1=0)=False。左侧为(k+1:R)，CharZero使Nat.cast单射，故等于0将推出k+1=0而不可能；无需给R加有序结构。 |

除两项整数幂生成定理外，其余12项公理闭包仅为propext；三条公开源定理的闭包为完整三项白名单。没有生成的值、实例定义、私有定理或其他实际所属遗漏。

## 单元159实际消费接口与接受证据

除158已经复核的152接口外，本单元新增消费 `Shao.truncationBudget`、`Shao.integrable_truncationF_mul`、`Shao.truncationF`和`Shao.continuous_truncationF`。已阅读其精确定义/完整源声明和本轮应用处：F是z²min(|z|,1)，budget是n∫F((1+y)z)deta，可积接口只要求原chi平方可积，对任意实数比例c有效；连续性接口确实针对同一F。对这些既有公共模块不重审旧证明。

接受映射 `coordination/root-cache-exports/c12-accepted-v83-original-brownian-comparison-20261025.json`，SHA256 e4f13313c11ef8b2b03c1b4b5ede0068a7400a7f5f96c065b738b88719f9d4f9，给出精确已接受绑定：

| 公共模块 | 源SHA256 | 对象SHA256 |
|---|---|---|
| Shao.Basic.TruncationBudget | 70cf7e33d458b847ea94cfa5bd8dce59a9dc3cb0ef632140a0f55fca8ded71bd | e5e28c3aaed49b4ac35bed42a6433c154d625e205f5a1c4f868176933eac07d5 |
| Shao.Probability.TruncationIntegrals | d7432b7c579c6e6e0d9980af322437941f59f8f670bebd2dd4770f6cfcf1e234 | 3badf67e4cf9f6f299f3618a072aed6582eb26a81d5c95a22190e3339b123c7e |

本地只读库、当前C12源、当前导入对象以及已接受integration-bearing-v83源/对象按该映射绑定。所有新增接口消费的是这些确切对象，而非重建或缓存猜测。

原生Bochner Basic中的integral_map要求映射AE可测和目标函数在map测度下AE强可测，结论正是map积分拉回；integral_mono要求两侧可积及逐点序；integral_const_mul使常数提出。Integrable.lean中的integrable_map_measure是目标可积与复合函数可积的双向等价；Variance.lean157–159的variance_eq_integral是实际中心积分公式。所需三个mathlib文件均与钉住Git源码一致。全部侧条件在本轮源证明中明确满足，不存在只因最终数值界合理就忽略函数/测度接口的情形。

## 单元159原始尝试、公理审计及边界

attempt001因F连续性不能由fun_prop自动发现，以及一处field_simp后多余ring而退出1；attempt002显式给了连续性，但函数参数未被正确确定，integral_map重写失败，退出1；attempt003以明确类型的hCont修复函数推断并通过，退出0。两次失败的原始源、命令、日志均保留，所有头不变。成功日志保留ring_nf建议、无效/未执行tactic和letI风格警告，不能把其中“The ring tactic failed...”建议文字误报为本次内核失败；原日志KERNEL_EXIT=0且没有Lean error。另有作者预执行Python占位替换语法错误，独立pre-execution-format-correction.json明确记录它发生在任何Lean之前，本轮不把它计算为内核尝试。

原始审计39374字节由39147字节17段完整类型、0字节值与227字节警告/汇总/成功标记精确组成，AUDIT_EXIT=0。OwnedAudit选取方法和已复核的native递归闭包算法与158相同，实际模块名及公开名单改为本模块三条，遍历结果17条均theorem。白名单以外公理无一出现。禁止的sorry/admit/axiom/unsafe/native_decide均未出现在形式源码中。

除前述边界外，明确检查：平方积分=1/2时sigma仍正且所用松界成立；β=0不被消去；rhoStar>0使768/rhoStar和最终rhoStar/2合法；y=0、x=0、y=2x及秩等号均保留弱不等式；n=1在一般预算头中合法，所需t=1>0；s=0由旧实际小参数数据直接覆盖；中心mu正负和原子分布均可。第二条真实chi数据不是原nu数据的重新命名；规范化中使用其实际sigmaSq。单元158到159的相互作用只需要158支付hn、hSmall，而159自身预算还要求其明确给出的rhoStar秩界；没有暗称158固定常数自动适用于任意rhoStar。

本轮追加接口查询曾在rg中包含不存在的猜测路径Probability/Truncation.lean；已根据实际TruncationIntegrals导入改读Basic/TruncationBudget.lean，未改任何被审文件。首次原生定位使用theorem搜索未找到以lemma声明的variance_eq_integral/integral_mono，后续按真实lemma名称补读。一次本地报告验证因Windows路径键使用反斜杠而出现KeyError，仅在内存归一化路径键后通过；原始只读观察保留。未重放服务器执行或丢弃证据。

## 统一最终判定与下一依赖

单元158–159均CORRECT。合计2模块、5公开源定理、14生成定理、19实际定理所属、0私有源定理、0全局定义值；完整实际类型共60328字节。统一验证和最后只读观察绑定两个原始成功对象、全部目标/依赖源及所需旧合格对象、原始失败与成功记录、冻结版本和公共接受映射；无内核/审计成功重放。封存后报告不可修改。

下一来源依赖是实际C1概率消费者：在真实居中律及其反射上使用已接受完整C1接口，把刚支付的自身预算送入相应最大事件界，随后完成真实端点/乘积概率传输和剩余稀有后缀组装。原始C1保持已完成，C2/C12保持开放；本报告不对未审的新消费者作预先结论。父实例可按本报告精确字节资格确认并继续，本审阅上下文在writer-release.json最后封存后释放，零在途。
