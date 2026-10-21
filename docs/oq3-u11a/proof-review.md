# U11a 完整独立声明、来源与证明审查

## 第一阶段：实际公开签名盲译

本节在读取本次实际证明、私有State/辅助、scope解释、R1或作者receipt/Audit之前落盘。本次只从AdaptiveTailBudget.lean提取三个实际公开签名；零公开定义。实测源SHA256=`86df6ca9eb9aa21b7eff614c9cfdef5be96b4bbd5d192fcb8c5e0ce97c8006bf`，192行。前序声明审查上下文已存在，本次仍从实际签名独立重译。未读作者API或其他notes。

1. eps>0，且F对每个逐项严格正、有限总质量<eps的长度J前缀给严格正预算。存在同一条全正实序列r，真实Summable、总和严格<eps，并对所有J，其整个未来尾`Σ'k r(J+k)`严格小于F在同一最终r前J项上的值。无F连续性、统一正下界或固定前缀假设。

2. 再给逐项严格正的任意固定a(J)，则存在同一条满足上述条件的r，其每个完整未来尾同时严格小于F(J,实际前缀)和a(J)。没有给每个J分别选择r。

3. hW明确保证每个合法有限前缀有自然数见证；hcap明确保证该前缀的每个W见证给正预算。结论先给全域chooseN(J,past)，在全部合法前缀上满足W，再给同一全正可和且总质量<eps的r，其全部未来尾受cap(J,实际前缀,chooseN(J,实际前缀))严格控制。非法前缀不要求W，chooseN不保证单调或增长。该目标保留hW/hcap输入，不声称实际LLT见证已经建立。

待核证明事项：私有状态和递归须先保证当前有限前缀合法再用hF；Fin.snoc必须一致生成最终r前缀；每项严格正、真实几何可和、J=0及所有无限shift-tail和strict总mass必须实际证明；最后完整核对所有私有/生成TYPE和真实机械产物。当前尚无本次完整裁决。

## 第二阶段：冻结scope与真实R1

盲译落盘后读取冻结scope与真实R1 113–135、484–550。scope实测SHA256=`1c4faf77bf27b05d6e9e7fd3b37242b5e68352a39f700d8fbc279fe21480fe9f`，既有声明审查SHA256=`86f4ff2a541b9306856d2e16d017e58c1874feb7a9d8c0d7d5be42a448759e04`；实际三个完整公开签名与scope按空白规范化独立比较3/3相同，无量词或前提变化。

真实R1 SHA256=`3473d34ff20bd0d334b9ef3ea3c3ee167fba4d5cc3a742849820ce54d639e662`。122–135的源正索引r₁,…在阶段J保留前J项，Lean零索引的Fin J前缀对应r₀,…,r_{J−1}，完整未来尾应从r_J开始，恰为J+k。486–497先在有限模型选n_J，521–529才提出未来尾预算；当前第三签名准确保留见证与预算的显式条件接口。531–537的可数兼容性对应前两个目标，当前单元不把source的LLT、TV或常数连续性段落当成已由这些签名证明。J=0合法空前缀控制全部质量，属于与实际finiteBase零阶段一致的加强。根A/B/C/D仍OPEN。

## 第三阶段：全部实际证明与固定库独立审查

本阶段在读取作者receipt/Audit之前完成。完整192行源码含一个私有状态结构、两个私有递归/推进定义、一个私有一致性定理和三个公开目标。代码只导入SummableAtoms；三个项目承重源在机械阶段核冻结hash。本单元不调用旧概率、LLT或对角定理来代替所需递归论证。

| 实现行 | 独立逐步检查 |
| --- | --- |
| 15–21 | TailBudgetState B F J同时保存真实Fin J前缀、逐项正、正cap、cap≤F(J,past)/2及“前缀和＋cap≤B”。不是仅存一个预期预算而缺少合法性不变量；没有把待证未来r放进状态假设。 |
| 23–33 | advanceTailBudget对任意合法状态用Fin.snoc追加s.cap/2；lastCases穷尽新末项和旧castSucc索引。旧值保持s.past，新值严格正由cap_pos/2得到。 |
| 34–41 | 实际有限和展开为旧和＋cap/2；s.reserve、cap>0及hB:B<eps先给新前缀和<eps。随后才调用hF(J+1,past,hp,hmass)，完全不依赖尚未建立的最终r或总和。 |
| 42–53 | 新cap取min(旧cap/2,F新前缀/2)，两项已严格正；min同时给cap≤F/2和减半界。旧reserve加新项后仍可用另一半cap支付新cap，因此新reserve真实保持。 |
| 55–61 | tailBudgetTrace以给定s0开始按自然数递归调用同一推进函数，得到一个一致状态轨道；每步J类型精确是Fin J，未独立重选历史前缀。 |
| 63–78 | tailBudgetTrace_past以J归纳，J=0空Fin消去；后继用lastCases：末项正是第J步cap/2，旧castSucc位置由归纳假设保持原先第i步cap/2。Fin.val_last/castSucc的值一致，给所有状态的每个历史值准确对应最终序列。 |
| 86–99 | 初始空前缀逐项正真空成立，空和0<eps由heps给，先合法使用hF0。B=min(eps/2,F0/2)>0、B<eps；s0.cap=B、reserve空和＋B≤B、预算界均真实。没有为初始化凭空假设F0正。 |
| 100–104 | tr是同一轨道，b_J为其cap，r_J=b_J/2，严格正由状态cap_pos。hstep直接展开推进定义得b_{J+1}≤b_J/2。 |
| 105–116 | 对每个J固定后以k归纳，精确得到b_{J+k}≤b_J(1/2)^k，再除2得到r_{J+k}≤(b_J/2)(1/2)^k。Nat.add_assoc处理实际shift，起点k=0无索引遗漏；nlinarith仅处理乘常数1/2的线性比较。 |
| 117–120 | 比较级数是真正公比1/2实数几何级数，abs(1/2)<1已证明。每条shift-tail非负并有逐项majorant，用实际Summable.of_nonneg_of_le建立每个尾的Summable，不靠tsum总化分支。 |
| 121–127 | 两条级数已各自Summable后才使用tsum_le_tsum；用实际几何和及tsum_mul_left把majorant总和精确算为b_J。因此是整个无限尾≤b_J，不是仅下一项或有限尾界。 |
| 128–130 | funext配合私有一致性定理证明(tr J).past恰等于fun i=>r i.val；实际F因此只消费同一最终r的前J项。 |
| 131–135 | htail0给全质量≤b0=B，B<eps给严格总质量；hsr0且Nat.zero_add给真实Summable r。初始预算预留使极限≤仍推出所需严格<。 |
| 136–144 | 状态cap_pos为b_J>0、cap_le_budget为b_J≤F(J,past)/2，替换真实前缀后得b_J<F(J,实际前缀)；与整个shift-tail≤b_J连用给每个严格尾界。该严格性不要求无穷比较处严格，也不漏J=0。 |
| 154–159 | 用min(F(J,past),a_J)作新预算，hF合法门与ha共同给其严格正。一次调用首目标给同一r，两个min≤侧分别给严格界；a不用可和或单调。 |
| 175–185 | chooseN在合法前缀处从hW选证人、非法处为0。hn在任意J/past的合法门下用choose_spec，反分支由合法证据矛盾排除，故覆盖全部合法前缀而非只最终r的前缀。 |
| 186–189 | 先将chooseN及全合法域性质hn交付，再以cap(J,past,chooseN J past)作F。只在合法门下用hn给W、hcap给正预算，然后首目标产生r；hW/hcap未消失或被偷换成无条件结论。 |

全部局部辅助past/hp/hsum/hmass/hf/c/hc/hr/past0/hp0/hm0/hf0/B/hBpos/hB/s0/tr/b/r/hr/hstep/hgeom/hbound/hsgeom/hsr/htail/hpast/hb0/ht/hb/hbudget、各归纳假设及chooseN/hn均已覆盖。私有结构的字段、构造器、消去/递归器和其他自动生成项还将由实际机械TYPE全量核对。

### 实际固定库语义

在作者机械证据前，只读指定服务器固定Mathlib/Lean源核对如下；没有运行任何成功目标的新构建。

| 实际库文件与SHA256 | 消费的实际定义/结论 |
| --- | --- |
| Mathlib/Data/Fin/Tuple/Basic.lean `e7b680bb3181fff915623cfa82d2e52424d423e5d5762578f3fe218533d8af48` | 522–524行snoc按i.val<n保留旧项，否则给新末项；533–535行snoc_castSucc与546行snoc_last准确证明两种取值。 |
| Lean Init/Data/Fin/Lemmas.lean `bb624cf249804c6b843c2abd54620a45f7864930016a3642992b06ebaf7529aa` | 1043–1045行lastCases覆盖末项与每个旧castSucc索引，真实dependent motive不会漏Fin(J+1)元素。 |
| Mathlib/Algebra/BigOperators/Fin.lean `b68854ca28f56de8a58284ae90ae2fc07887b75c720ad6e3a81fd58e6340da50` | 82–86行prod_univ_castSucc的to_additive为sum_univ_castSucc，准确分成旧索引和＋末项。 |
| Mathlib/Topology/Algebra/InfiniteSum/ENNReal.lean `88ef56c969006630d0066b7af2c74e75dd060608f3c42f0ef288ad1c6da908cc` | 532–537行Summable.of_nonneg_of_le对实数f/g明确要求0≤g、g≤f以及Summable f，实际代码全部给出。 |
| Mathlib/Topology/Algebra/InfiniteSum/Order.lean `526aed3d15913b1d7ad9de9f28fc26ac9ab023942b0d80cbc72323a293817b01` | 132–135行Multipliable.tprod_le_tprod的to_additive为Summable.tsum_le_tsum，明确需要点态界与两边Summable。 |
| Mathlib/Analysis/SpecificLimits/Normed.lean `eee44dfd62feb67bdf3ccc6cf57e8e101f38a7408dbb9c6347e0978ce2010d41` | 493–497行实几何级数在abs(r)<1时真实可和且tsum=(1−r)⁻¹，公比1/2满足门。 |
| Mathlib/Topology/Algebra/InfiniteSum/Ring.lean `bba1f8897f3b78060d4893ee3b47f8edf6f533d2adca7909305d0a42ee50c087` | 113–118行tsum_mul_left把实数标量提出，配合前述已证Summable的几何和准确得b_J。 |

### 边界、量词与范围

J=0为真空正前缀，初始hF合法门真实由heps建立；尾0+k为全部r。每个J的尾包含r_J，且所有k≥0无穷项均被同一几何级数控制。所有r_J严格正，同时r总质量严格<eps，任意已有前缀也因此可合法使用下游正预算；本实现的递归证明更早已通过reserve证明了这项合法性，无循环。

F可以在合法前缀间任意不规则，状态只需当前F值正即可，没有偷用连续性或统一正下界。chooseN可依赖W/hW/eps及整个合法有限前缀，但不能读取未来r；其全合法前缀性质在最终r存在之前证明。其自然数值不宣称单调或趋于无穷，实际有限模型见证和cap正性仍由明确hW/hcap提供。

本阶段独立数学裁决：CORRECT。此时尚未读取本单元作者receipt/Audit或实际机械日志。没有实际LLT、TV、常数连续性、最终固定律误差发散或对角闭合的新增结论，根A/B/C/D均OPEN。

## 第四阶段：最后的实际机械核验与44项TYPE

独立数学判断落盘后才读取本地U11a-receipt.json/U11aAudit.lean及真实服务器同名run产物。通过共享server.py只读读取，返回exit0、stderr为空，host key SHA256=`+IZMFu9Xx6FSAhvQhtvZ3MpV70v2d+XNWcequAbsp+c`。未重新构建、执行Audit或下载日志。

真实worktree=`/root/rivermind-data/shao-lean-20261021/workspaces/lead-oq3`；分支`feat/oq3-adaptive-tail`，HEAD=`81298fef5ed7de6b9b7146d5b086b2b39513d5bf`；实际git状态仅`?? Shao/OQ3/AdaptiveTailBudget.lean`。实际源SHA256=`86df6ca9eb9aa21b7eff614c9cfdef5be96b4bbd5d192fcb8c5e0ce97c8006bf`，与已完整审查的本地冻结192行源相同。独立扫描无sorry/admit/axiom/unsafe/native_decide，无CR或尾空白。

实际run=`/root/rivermind-data/shao-lean-20261021/runs/oq3/u11a-20261021`，本地receipt/Audit与真实run文件hash一致：

| 实际产物 | 字节数 | SHA256及检查 |
| --- | --- | --- |
| receipt.json | 2948 | `05b05b71607673636c98ced3f28d8b58d1282f884e41698a939e786de1da36f8`；记录build/Audit均exit0 |
| build-02.log | 0 | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`；实读为空，无警告/错误文本 |
| Audit.lean | 1552 | `199ab3bc4fa0b685b553ad87c8610f8db21d6bf21ac13100a33ec099b36694b9`；实际枚举所有三个公开前缀及模块私有前缀 |
| Audit.log | 22914 | `697aaa51fbec86fcc17f0022f2e6876651271eb72c9aeab5cbb0abccd94ecc3f`；全部DECL/TYPE/AXIOMS实际读取 |

receipt绑定的成功build命令为`lake env lean -o .lake/build/lib/lean/Shao/OQ3/AdaptiveTailBudget.olean Shao/OQ3/AdaptiveTailBudget.lean`，Audit命令为`lake env lean /root/rivermind-data/shao-lean-20261021/runs/oq3/u11a-20261021/Audit.lean`。本次核验的是这些真实已有成功产物及其冻结源绑定，没有虚称独立重跑。

Audit实读逻辑要求三个目标存在且为theorem；枚举其全部名字前缀及`_private.Shao.OQ3.AdaptiveTailBudget`，拒绝项目axiom，并对每项Lean.collectAxioms检查传递白名单。实际日志与独立DECL计数均为44，末尾3冻结目标/24定理/44声明及AXIOM_GATE PASS。

下表按实际日志顺序逐项记录全部44个TYPE，非仅按目标数推测。公开项省略Shao.OQ3前缀；其余全有私有前缀`_private.Shao.OQ3.AdaptiveTailBudget.0.Shao.OQ3`。表中S表示TailBudgetState B F J，p/c为其past/cap，p⁺=Fin.snoc p(c/2)；“轨道共同参数”精确是eps/B、hB:B<eps、F、只对正且总和<eps前缀保证F>0的hF、s0:TailBudgetState B F 0。

| # | 实际声明 | 实际TYPE独立检查 |
| --- | --- | --- |
| 1 | TailBudgetState.past_pos | ∀S/i:Fin J，0<p_i，真实字段投影 |
| 2 | TailBudgetState.noConfusionType | Sort u及两套B/F/J参数和两个状态→Sort u，标准异参数构造器不混淆类型 |
| 3 | advanceTailBudget._proof_7 | ∀B/F/J/S，min(c/2,F(J+1,p⁺)/2)≤F(J+1,p⁺)/2，真实min右侧界 |
| 4 | TailBudgetState.cap | ∀B/F/J，S→ℝ，预算字段 |
| 5 | exists_positive_mass_with_adaptive_tail_caps | 实际eps>0和hF合法门→同一全正Summable r、Σ'r<eps、∀J完整shift-tail<F(J,实际前缀)，与盲译相同 |
| 6 | tailBudgetTrace._sunfold | 轨道共同参数→(J:ℕ)→TailBudgetState B F J，智能展开辅助无额外条件 |
| 7 | TailBudgetState.mk | 给past、past_pos、cap、cap_pos、cap≤F(J,past)/2、前缀和＋cap≤B→S，六字段齐全 |
| 8 | TailBudgetState.recOn | 给S及对六个字段的构造器分支→motive S，motive:S→Sort u，标准依赖消去 |
| 9 | advanceTailBudget._proof_5 | hF及S、p⁺逐项正、Σp⁺<eps→0<F(J+1,p⁺)，调用合法门明确保留 |
| 10 | tailBudgetTrace_past | 轨道共同参数、∀J/i，(tr J).past i=(tr i.val).cap/2，真实历史一致性 |
| 11 | TailBudgetState.past | ∀B/F/J，S→Fin J→ℝ，前缀字段 |
| 12 | TailBudgetState._sizeOf_inst | ∀B/F/J，SizeOf S，结构生成实例 |
| 13 | tailBudgetTrace._f | 轨道共同参数→(x:ℕ)→Nat.below x→TailBudgetState B F x，自然数递归生成辅助 |
| 14 | tailBudgetTrace.eq_2 | 轨道共同参数、∀J，tr(J.succ)=advanceTailBudget(...)(tr J)，后继方程 |
| 15 | TailBudgetState.rec | 对六字段构造器分支及S→motive S，motive:S→Sort u，标准递归器 |
| 16 | advanceTailBudget._proof_1 | `(1+1).AtLeastTwo`，实数分母2所需数值类型类证明 |
| 17 | advanceTailBudget._proof_8 | S及Σp⁺=Σp+c/2→Σp⁺+min(c/2,F(J+1,p⁺)/2)≤B，真实reserve保持 |
| 18 | TailBudgetState.mk.inj | 两个同参数mk状态相等→past=past'∧cap=cap'，不增加未证不等式 |
| 19 | advanceTailBudget | eps/B、B<eps、F/hF、S_J→S_{J+1}，与实际私有推进定义相同 |
| 20 | TailBudgetState.reserve | ∀S，Σpast+cap≤B，真实reserve投影 |
| 21 | advanceTailBudget._proof_4 | eps/B、B<eps、F/S、Σp⁺=Σp+c/2→Σp⁺<eps，先合法再调用hF的核心辅助 |
| 22 | TailBudgetState.casesOn | S及对全部六字段的构造器分支→motive S，标准cases消去器 |
| 23 | TailBudgetState.cap_pos | ∀S，0<cap，真实字段 |
| 24 | exists_witness_first_positive_mass_with_tail_caps | eps>0、全合法前缀hW、合法前缀W见证hcap→先∃chooseN及全合法域W性质，再∃同一全正可和r及严格总质量/全部cap尾界；量词与盲译相同 |
| 25 | TailBudgetState.noConfusion | 两套状态参数相等及状态HEq→相应noConfusionType；标准结构不混淆消去 |
| 26 | advanceTailBudget._proof_6 | S及0<F(J+1,p⁺)→0<min(c/2,F(J+1,p⁺)/2)，消费状态cap_pos |
| 27 | tailBudgetTrace.match_1 | (motive:ℕ→Sort u)→x→(Unit→motive0)→(∀J,motive J.succ)→motive x，零/后继匹配器 |
| 28 | advanceTailBudget.eq_1 | 私有推进等于past=p⁺、cap=min(c/2,F新/2)且含已证四个Prop字段的状态；实际定义展开方程 |
| 29 | TailBudgetState.ctorIdx | ∀B/F/J，S→ℕ，结构构造器索引 |
| 30 | advanceTailBudget._proof_2 | ∀S/i:Fin(J+1)，0<p⁺_i，实际追加正性 |
| 31 | tailBudgetTrace.eq_1 | 轨道共同参数→tr0=s0，初始化方程 |
| 32 | exists_positive_mass_with_adaptive_and_fixed_tail_caps | eps>0、hF、∀J a_J>0→同一全正可和r、strict总质量、∀J未来尾同时<F与<a_J，与盲译相同 |
| 33 | TailBudgetState | ℝ→((J:ℕ)→(Fin J→ℝ)→ℝ)→ℕ→Type，真实状态类型 |
| 34 | TailBudgetState._sizeOf_1 | ∀B/F/J，S→ℕ，结构size函数 |
| 35 | TailBudgetState.mk.noConfusion | 两个mk相等及(过去HEq→cap相等→P)→P，P:Sort u，标准构造器消去 |
| 36 | advanceTailBudget._proof_3 | ∀S，Σp⁺=Σp+c/2，实际有限和展开 |
| 37 | TailBudgetState.mk.congr_simp | past/past'相等、cap/cap'相等及原结构证据→两套相应mk相等，Prop字段按相等运输 |
| 38 | tailBudgetTrace._unsafe_rec | 与轨道完全相同的共同参数及返回状态类型；固定Lean自动生成的运行时递归辅助，详见下文 |
| 39 | tailBudgetTrace | 轨道共同参数→(J:ℕ)→TailBudgetState B F J，实际结构递归主定义 |
| 40 | TailBudgetState.mk._flat_ctor | 与mk相同六字段参数→S，标准平坦构造辅助 |
| 41 | TailBudgetState.mk.injEq | 两个同参数mk的相等命题等于(past=past'∧cap=cap')命题，proof字段不引入额外数据 |
| 42 | TailBudgetState.cap_le_budget | ∀S，cap≤F(J,past)/2，真实字段投影 |
| 43 | TailBudgetState.mk.sizeOf_spec | mk状态的sizeOf=1+sizeOf cap+sizeOf cap_pos+sizeOf cap_le_budget+sizeOf reserve，结构生成计算性质 |
| 44 | tailBudgetTrace.congr_simp | eps=eps'、相同B/F及s0=s0'→∀J两个运输后的轨道状态相等，标准递归定义congruence |

44项传递公理全部仅为propext/Classical.choice/Quot.sound的子集；实际match_1为[]，数值AtLeastTwo辅助只含[propext]，其余为三项白名单。无项目axiom或遗漏模块私有声明。没有把结构递归器的Type误作新增数学假设，也没有只看公开三个目标。

特别只读核固定Lean编译器源码，确认自动生成`_unsafe_rec`的真实含义：Lean/Compiler/Old.lean SHA256=`72b18cd03391e07468fd747cb7f23245f768227efc6003bf33193c3768683de3`，43–53行明确为常规递归自动生成该名字的运行时辅助；Lean/Elab/PreDefinition/Structural/Main.lean SHA256=`8a86ae2d1bae7f1b6c3e52a86f20e3460eecf0dbb7f7a891a16f89971d36be29`，191–210行显示先加入类型正确的结构递归主定义，再生成辅助与展开信息。它不是作者新增unsafe证明、公理或native_decide入口；当前源没有unsafe关键字，三个目标和全部辅助均有真实内核成功产物及传递公理检查。该观察只解释已实读生成项，不忽略或隐去它。

真实三个承重项目源逐份核hash如下，与已审冻结版本一致：

| 实际项目源 | SHA256 |
| --- | --- |
| Shao/OQ3/FiniteConstraints.lean（U1） | `800d9db8cb6749a31ecfe611409de92b10ea8bb2aef955bfd825ede7324f0ef0` |
| Shao/OQ3/SourceStarter.lean（U2） | `0e2a081619976f88149707c2ef9311dc909003e61d3d0f7c4e21e6c3dbbc5a6d` |
| Shao/OQ3/SummableAtoms.lean（U3a） | `0ea4c64fe9ef9b45fbf44d24312771a1dbfbcc5de8448564e3e87bdf17c7178b` |

真实lean-toolchain=`leanprover/lean4:v4.36.0-rc1`，实际Lean版本4.36.0-rc1、commit=`c9afcddf514a6772bd4d649f7cfc04eff0b9f15e`，Lake=`5.0.0-src+c9afcdd`，真实lake-manifest中的mathlib rev=`807d3836b165983210ee2ecf3cd28f239436949c`。这些均为本次实际只读返回值，未重复旧目标门。

## 最终独立裁决

STATUS: CORRECT

JUSTIFICATION: 实际三个公开签名与冻结scope/真实来源一致，完整192行证明、私有状态与递归、有限前缀一致性、真实几何可和及每个无限shift-tail都已独立核实。所有hF调用先有合法前缀门，严格正/总质量/尾预算包括J=0，min固定预算与chooseN全合法前缀的先选择接口均无关键缺口。最后读取的真实服务器冻结源、三项目依赖、pins、build/Audit成功记录和全部44实际TYPE及传递公理准确绑定本单元，支持本单元LEAN_FULLY_CHECKED。作者receipt的AWAITING_INDEPENDENT_PROOF_REVIEW是作者门时历史状态；完整独立裁决由本报告给出，未以该作者门替代数学或来源判断。

仅本单元通过；没有重跑全项目构建或执行commit/PR/merge。hW实际LLT见证、实际TV与常数连续性预算构造、样本量增长/单调、最终固定律的尾渐近及对角闭合均不在本单元已证范围。所有根A/B/C/D保持OPEN。
