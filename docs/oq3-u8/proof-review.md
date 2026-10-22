# U8 最终独立声明、来源与证明审查

## 第一阶段：实际定义与八导出签名盲译

本节在本次读取最终证明、私有辅助、scope/R1、既有声明报告、receipt/Audit或作者笔记前落盘。只读取实际 `FiniteNormalSpan.lean` 的导入、两个定义及八个公开签名；实测源SHA256=`0374da4860edf8af8bbbb9172e4e93bfe9b6c37ac57672b85a4f58392475b7de`，158行。此前声明审查上下文存在，本次从实际导出重新核对；未读作者global-rate-frontier、API或notes。

实际HasNormalLattice(μ,h)要求h>0且存在同一任意实offset，使μ-AE x有整数k满足Y(x)=offset+hk。实际IsMaximalNormalLattice还要求所有符合该定义的候选h'都≤h；不是只在零平移网格中比较。

八目标的独立数学翻译：

1. 每个J及活跃stageAtom的Y值都精确等于dyadicMesh(J)乘整数。
2. Y(addedAtom J)−Y(baseAtom2)=dyadicMesh(J+1)。
3. 任意μ若AE位于有限stage值域，则HasNormalLattice(μ,meshJ)，不要求概率。
4. 任意候选平移格距h，若x/y实际单点实质量严格正且Y(x)−Y(y)>0，则h不超过该正差。
5. AE有限stage支撑及全部活跃点实际正质量下，meshJ为最大法向格距。
6. π_J=atomicMeasure(finiteMass)在finiteBase全旧质量正、整条r正的门下有最大格距meshJ；无需矩或概率门。
7. P_J=originalMeasure(ℓ,finiteMass)另在矩阵非奇异、旧矩方程及同样严格正门下有相同最大格距。
8. 存在同一p>0、q∈(1,103/100)、eps>0与source旧矩方程，使后来任意正可和、总量<eps的完整r，对所有J同时给π_J/P_J最大格距meshJ。参数存在量词在r/J前。

本节尚未读证明。后续须核任意offset在实际正点的AE提升、整数差符号/绝对值、J=0和J+1最新活跃索引、π/P真实质量与AE支撑、共同参数，以及全部私有/生成声明；未作LLT或联合非格点提升。

## 第二阶段：冻结、真实来源与固定库

盲译先落盘后，才读取scope解释及真实只读R1 113–119、396–406。scope实测SHA256=`fb35d6d762e70ee479b05d636bca2a2f7b22d70f605fed611e3cff81a378b2d6`，既有声明报告SHA256=`6df91b8e4d0a23e63986586b10d26c02a8c325f86744a131d0992a470889a850`，真实R1 SHA256=`3473d34ff20bd0d334b9ef3ea3c3ee167fba4d5cc3a742849820ce54d639e662`。独立空白规范化比较实际两定义体与八签名，10/10完全一致，无条件或量词变动。

R1 113–119的源新增编号从1起，实际addedAtom(J)的法向值为6+mesh(J+1)；阶段FinJ保留实际新增0,…,J−1，对应源1,…,J。R1 396–398要求实际有限π_J的最大法向格距h_J，不只是一个可容纳的网格；实际两个定义允许任意offset，目标恰覆盖该更强最大性。400–406的层相位与统计量代数恒等式不在本单元输出，不将八目标扩大成LLT或后续层结论。

完整数学审查阶段通过指定服务器只读核对固定库：manifest mathlib revision=`807d3836b165983210ee2ecf3cd28f239436949c`；实际 `Mathlib/Algebra/Order/Group/Unbundled/Int.lean` SHA256=`4516aaa27a817733996036b73fd7b4303a3e41b9b6da018f342a4fff0e791457`，80–81行 `Int.one_le_abs {z:ℤ} (h₀:z≠0) : 1≤|z|` 的唯一门正是整数非零，与实际调用一致。该读取不涉及本单元receipt、Audit或机械日志，没有运行Lean。

## 第三阶段：158 行完整证明与全部局部辅助

完整读取固定哈希源1–158行后，在本单元receipt/Audit/build日志前形成独立数学判断：CORRECT，无关键缺口。未读作者global-rate-frontier或其他API/notes。

| 源行 | 精确逐步检查 |
| --- | --- |
| 19–24 | HasNormalLattice保留正h和同一任意offset的AE整数取值。IsMaximal同时要求自身存在以及所有候选平移格距h'≤h，没有先固定候选offset或仅比较一族零offset网格。 |
| 29–34 | 从已审U6c的实际stage缩放整数定理取同一整数k，展开mesh为(2^J)⁻¹后乘法消去。2^J对所有自然数J均严格正、非零，field_simp的消去合法，包含J=0，不是假定任意分母非零。 |
| 36–39 | 使用真实新增法向公式及旧baseAtom2的法向值6，精确减去6得到mesh(J+1)，源偏移不变。 |
| 45–48 | 明确证明meshJ>0，选offset=0；对μ-AE的stage值域逐点取真实索引，再使用前项整数证人。没有假定概率或正权，这一步只给网格存在。 |
| 50–60（唯一顶层私有数学引理） | 对任意谓词A及μ-AE A，若某实际正质量点x不满足A，则singleton{x}包含于异常集，μ{x}=0进而μ.real{x}=0，与hx矛盾。此泛型引理可用于“存在整数”的谓词，不要求选好同一整数或AE谓词外的点也满足它。 |
| 67–72 | 解包任意hspan获得h>0、该候选自己的任意offset和AE整数存在式。在两个实际正点分别调用私有引理取kx/ky，精确实数cast后相减给 `Yx−Yy=h·↑(kx−ky)`，offset完全消除。 |
| 73–78 | 若整数差0，则正差hdiff被heq迫使为0，矛盾。因而实际 `Int.one_le_abs` 非零门满足；exact_mod_cast只把精确整数绝对值下界移至实数，未用近似或取整。 |
| 79–83 | 实现采用绝对值路线：由h>0乘1≤|整数差|，再用abs_mul和h正性化为|Yx−Yy|；最终hdiff>0去绝对值。无需偷加“整数差为正”假设，符号和反向整数差均被正确处理，输出h≤正差。 |
| 91–102 | 先保留自身网格存在，再对任意候选h/offset证明上界。J=0使用活跃旧点base1/base2，hpos真实给两singleton正质量；Y值7/6，差精确1=mesh0。未构造Fin0新增点或依赖不存在的末项。 |
| 103–112 | J=succ N时，实际代码局部名J=N；以 `⟨N,Nat.lt_succ_self N⟩:Fin(N+1)` 取最新活跃addedAtom(N)，并取旧base2，两点正质量都由hpos给出。新增差为mesh(N+1)>0；通用任意offset上界精确得候选h≤本阶段mesh，不遗漏源最新编号N+1。 |
| 118–129 | finiteMass_nonneg由旧权重正、r正降为非负；U3c给实际π_J的AE有限值域。对每个活跃点，actual atomicMeasure_real_singleton把真实实轴单点质量写为finiteMass：旧侧hp正，新侧j.isLt使截断值=r_j>0。无需HasSum1或r可和，泛型有限π可未归一化，但最大格距结论不依赖总质量。 |
| 137–138 | P_J另消费U3c的actual originalMeasure有限AE支撑和finite_original_atom_pos，其hM/hc/hp/hr门均传入。依赖定理内部的真实总质量1、指数可积与Z_J>0保障P_J正单点，未把π_J权重直接当P_J质量。 |
| 148–155 | 一次取U3c同一p/q/eps，先给存在见证，再引入整条r与任意J；同一hfamily给该J的hpJ。π_J/P_J两结论共享同一r/hc/source矩阵非奇异性和hpJ，没有分阶段重选q或eps。 |

全部局部辅助hk、hsub、hnull、hzero、hreal、hh、offset、hae、hkx、hky、heq、hne、hlarge、hx/hy、hd、hdiff、hle、hw、hfamily、hstages、hpJ均已审查。源外生成声明必须在最后机械阶段逐项TYPE核对，不能仅按公开目标数推断其内容。

### 数学边界与源范围

任意offset的最大性确由两个实际正singleton提升后相减取得，没有把“全部原子集合落在某网格”当成“某测度的所有支撑点实际正”。zero μ虽满足任意正h的网格存在，但hpos不成立，所以没有对零测度错误地推出最大值。一般μ不需概率，正实单点门已经足够；实际源族仍由U3c维持π_J/P_J真概率。

dyadicMesh正性与严格整数离散界用于每个实际阶段。J=0的旧点差1足够最大性；J=N+1的最新新增差mesh(N+1)是真实正质量见证，未来零延拓点不被使用。π_J与P_J允许任意实ℓ，P的正指数保留所有活跃点，ℓ=0无退化问题。

当前只处理有限Y分布的最大法向格距；未把有限阶段称为严格联合非格点，未更换既有固定极限P以消费U6d，也未证明LLT、相位返回、层相位/统计量恒等式、尾渐近、曲边界常数、尖点、产品TV或对角。根A/B/C/D保持OPEN。

本阶段独立数学裁决：CORRECT。此时尚未读取本单元receipt/Audit或机械产物。

## 第四阶段：真实机械绑定及全部十八项 TYPE

独立数学判断落盘后才读取本地U8-receipt.json和U8Audit.lean，实测SHA256分别为 `954b5ffa363b411649089cc15d095de32a526c74594f28f176a722734a7ab408`、`6d06f1c7240fe494e3068829b0dd1541b0e0003ce917125d909bc76a0471e663`。实际目标源无sorry/admit/新axiom/unsafe/native_decide，无CR或尾空白。

已完整审查Audit源：逐一确认八冻结目标存在且为theorem，遍历十个公共源名前缀与模块私有前缀，拒绝项目新增公理，对每项用Lean.collectAxioms核查全部传递依赖，仅允许propext、Classical.choice、Quot.sound；打印实际TYPE与总计数。两个定义的真实存在和类型及所有额外声明也由下述真实日志逐一核对，不只信目标数。

经共享tools/server.py实际只读核对指定worktree源/八份导入、Git/pins及服务器runs/oq3/u8-20261021的receipt.json、Audit.lean、Audit.log、build-01.log，远端exit0、stderr为空。没有运行目标构建或Audit重跑，没有下载日志、写cache/源码、撤销他人文件或作commit/PR。

实际worktree=`/root/rivermind-data/shao-lean-20261021/workspaces/lead-oq3`，branch=`feat/oq3-normal-span`，HEAD=`a0c2b01ce52840df6161af1329019d362d7a60cb`，与作者凭据基线一致。

| 真实远端源 | 实测 SHA256 |
| --- | --- |
| FiniteNormalSpan.lean | `0374da4860edf8af8bbbb9172e4e93bfe9b6c37ac57672b85a4f58392475b7de` |
| U1 FiniteConstraints.lean | `800d9db8cb6749a31ecfe611409de92b10ea8bb2aef955bfd825ede7324f0ef0` |
| U2 SourceStarter.lean | `0e2a081619976f88149707c2ef9311dc909003e61d3d0f7c4e21e6c3dbbc5a6d` |
| U3a SummableAtoms.lean | `0ea4c64fe9ef9b45fbf44d24312771a1dbfbcc5de8448564e3e87bdf17c7178b` |
| U3b AtomicMeasure.lean | `59ddc48fb7b395f362939e58cbd9d7911685a6ed6e6574142e8a6d4ab3ee0c39` |
| U4 InverseTilt.lean | `c7e7d19e8b70481b663bec1fd12ea9301d73313faaf35997e85aa9ba99f21811` |
| U3c FiniteStageMeasure.lean | `1a32fb904e6ee9d2b0b48d92c4ebb3568452bb02500ce52a1a03eb01ae0256b1` |
| U6a AtomProjection.lean | `0d369052c7f87122765612efdeaca5d9ac71abca861e7785c86d1f9edcc74d22` |
| U6c ResonanceArithmetic.lean | `cd21a264d637bab30fed765bdc25ed09bb4ff56f6efb9c88ee09be4ca6e1648b` |

全部与已完整独立CORRECT的前序源及receipt绑定相同，U4正确使用已审LF版本。此依赖链没有U7或U5a依赖，没有借其结论消除有限零质量门。

真实receipt.json为3410字节，SHA256=`954b5ffa363b411649089cc15d095de32a526c74594f28f176a722734a7ab408`，与本地回执相同且内容已完整读取。回执记录原目标命令 `lake env lean -o .lake/build/lib/lean/Shao/OQ3/FiniteNormalSpan.olean Shao/OQ3/FiniteNormalSpan.lean` exit0；真实build-01.log为0字节，SHA256=`e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`。原Audit命令记录exit0；真实Audit.lean为2220字节，SHA256=`6d06f1c7240fe494e3068829b0dd1541b0e0003ce917125d909bc76a0471e663`，与已完整读本地脚本相同。真实Audit.log为5343字节，SHA256=`5340e08c220d7faf535eb01be6344ef2407182402ead0f18f36e4498a1e73bf7`，与回执相同，日志已完整读取。

公开十声明的实际TYPE逐项核对如下，全部门/量词同时与实际源码及scope比较：

| 声明（省略Shao.OQ3） | 真实 TYPE 检查 |
| --- | --- |
| HasNormalLattice | `Measure ℝ → ℝ → Prop`，对应实际正h/任意offset/AE整数定义。 |
| IsMaximalNormalLattice | `Measure ℝ → ℝ → Prop`，对应自身格点存在及全部候选跨度上界。 |
| stageAtom_normalValue_lattice | ∀J和Fin4⊕FinJ活跃i，∃整数k，实际Y(stageAtom i)=meshJ·k。 |
| addedAtom_normal_difference | ∀J，实际Y(addedJ)−Y(base2)=mesh(J+1)。 |
| normal_lattice_of_stage_range | 对任意μ/J，只以实际AE有限值域给HasNormalLattice(μ,meshJ)。 |
| normal_lattice_span_le_of_positive_atoms | hspan、两个实际正singleton及正Y差的全部门保留；输出h≤该差。 |
| stage_normal_span_maximal | 实际AE值域与∀活跃i真实单点正质量给最大meshJ。 |
| finite_atomic_normal_span_maximal | finiteBase全旧正、r全正给实际π_J最大格距，不添加概率门。 |
| finite_original_normal_span_maximal | 同一严格正门加hM/hc，输出实际P_J最大格距。 |
| exists_source_finite_maximal_normal_family | 先∃同一p/q/eps，再∀合格完整r/∀J，同时给真实π_J/P_J最大格距，全部对象/括号/量词一致。 |

额外八个theorem实际TYPE也全部逐项读取，绝非只有三个helper。其中一个私有引理为 `_private.Shao.OQ3.FiniteNormalSpan.0.Shao.OQ3.holds_at_positive_atom`，完整TYPE是 `∀μ (A:ℝ→Prop), (μ-AE x,A x) → ∀x, 0<μ.real{x} → A x`，其50–60行完整源证明已审，适用于真实整数存在谓词。

另外七个生成声明均位于 `Shao.OQ3.stageAtom_normalValue_lattice` 前缀下，实际类型和数学内容如下：

| 生成后缀 | 实际 TYPE 与内容 |
| --- | --- |
| `_simp_1_1` | 任意带Zero/OfNat2及NeZero2的类型中，命题 `(2=0)=False`；非零门明确。 |
| `_simp_1_2` | 同样对OfNat3及NeZero3，`(3=0)=False`。 |
| `_simp_1_3` | 同样对OfNat4及NeZero4，`(4=0)=False`。 |
| `_simp_1_4` | 任意带Mul/Zero/NoZeroDivisors的类型，a≠0、b≠0蕴含 `(a*b=0)=False`；没有无条件排除零因子。 |
| `_simp_1_5` | 任意MonoidWithZero且IsReduced的类型，∀n:ℕ，a≠0蕴含 `(a^n=0)=False`；包含n=0，所需非零/约化条件完整。 |
| `_simp_1_6` | 任意GroupWithZero，∀n:ℤ，a≠0蕴含 `(a^n=0)=False`；负指数也有完整非零门。 |
| `_simp_1_7` | 任意AddMonoidWithOne且CharZero类型，∀n:ℕ，`(↑n+1=0)=False`；自然数cast及特征零条件明确。 |

这些是34行field_simp生成的通用非零化简事实，分别由NeZero、无零因子、约化幂、非零整数幂及特征零自然数嵌入保证；实际用于ℝ时条件均为标准实例，没有隐藏的格点/正质量/最大性新假设。私有加七生成共八项，连同八目标及两定义正好十八声明；无遗漏。所有项及传递依赖仅含标准白名单，部分生成项只依赖propext。

真实汇总为 `U8_FROZEN_THEOREMS 8`、`U8_ALL_THEOREMS 16`、`U8_ALL_DECLARATIONS 18`、`U8_AXIOM_GATE PASS`。实际pin=`leanprover/lean4:v4.36.0-rc1`，mathlib revision=`807d3836b165983210ee2ecf3cd28f239436949c`；同一服务器会话已实际探测Lean4.36.0-rc1（commit c9afcddf514a6772bd4d649f7cfc04eff0b9f15e）、Lake5.0.0-src+c9afcdd，本次pins未变。

STATUS: CORRECT

机械覆盖：LEAN_FULLY_CHECKED，仅指固定哈希U8两定义、八目标、一个私有及七生成theorem和全部传递依赖的既有真实成功构建/公理审计。本轮独立数学判断先于作者门与真实产物，再逐项核对十八TYPE和绑定；没有重编成功目标或根集成构建。

JUSTIFICATION: 冻结定义/八签名与真实源一致；任意offset的正原子AE提升、整数差非零与绝对值下界、J=0/后继最新索引、真实π_J/P_J质量/支撑、共同p/q/eps对全r/J均证明完整。八份承重源、十八实际TYPE、私有/全部七生成辅助、真实成功产物与传递公理门全部匹配，无关键缺口。未commit/PR；LLT、非格点提升、层代数/相位返回、尾渐近及对角未在本单元证明，根A/B/C/D保持OPEN。
