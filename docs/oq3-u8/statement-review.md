# U8 独立声明与来源审查

## 第一阶段：仅 Lean 代码块盲译冻结

本节在读取scope解释、真实R1或作者API/笔记前落盘。只读取 `fourteenth-unit-scope.md` 的Lean代码块，实测SHA256=`fb35d6d762e70ee479b05d636bca2a2f7b22d70f605fed611e3cff81a378b2d6`。两定义、八目标，尚无实现或本单元机械认证。

定义 `HasNormalLattice μ h` 要求h>0，且存在同一实offset，使μ几乎每个x的normalValue(x)都等于offset+h·k（整数k可随x变化）。这允许任意平移网格。`IsMaximalNormalLattice μ h` 还要求所有满足该条件的正格距h'都≤h，是已达到的最大格距，不只零平移格距上界。

八个目标独立翻译：

1. 任意J及活跃阶段索引i:Fin4⊕FinJ，实际stageAtom的normalValue为dyadicMesh(J)乘某整数。
2. 对任意自然数J，新增原子addedAtom(J)与旧baseAtom2的normalValue之差恰为dyadicMesh(J+1)。
3. 任意实线测度μ若AE落在对应有限stageAtom值域，则它具有正格距dyadicMesh(J)的normalValue平移格点性质；不要求概率。
4. 任意μ及候选格距h，若已有HasNormalLattice(μ,h)，且x、y两点有实际严格正单点实质量、normalValue(x)−normalValue(y)>0，则h≤该差。结论对候选的任意offset成立。
5. 若μ AE落在阶段有限值域且每个活跃点均有实际正单点质量，则dyadicMesh(J)是其normalValue分布的最大格距。
6. 对任意ℓ,p,r,J，若finiteBase全旧质量>0且整条r>0，则π_J=atomicMeasure(finiteMass)具有最大格距dyadicMesh(J)。此项不要求矩方程或概率归一化。
7. 对P_J=originalMeasure(ℓ,finiteMass)加矩阵非奇异与旧矩方程门，及上述严格正质量门，则同一最大格距成立。
8. 先存在同一p>0、q∈(1,103/100)、eps>0及source矩方程；其后每条正、可和、总量<eps的完整r，对所有J同时给π_J和P_J的normalValue最大格距dyadicMesh(J)。p/q/eps先于r与全部J。

盲译尚未核实最大性使用哪些实际正点、J=0与最后新增点的源索引偏移。它不陈述LLT或有限阶段联合非格点，也不改变既有固定极限P的含义。

## 第二阶段：真实来源及承重定义核对

盲译落盘后才读取scope解释、真实只读R1 113–119与396–406，以及已独立完整CORRECT的真实前序源。R1实测SHA256=`3473d34ff20bd0d334b9ef3ea3c3ee167fba4d5cc3a742849820ce54d639e662`，与冻结值一致。未读U8作者API/notes/frontier，未写实现或运行Lean。

实际读取的承重源哈希：U1 FiniteConstraints=`800d9db8cb6749a31ecfe611409de92b10ea8bb2aef955bfd825ede7324f0ef0`，U6c ResonanceArithmetic=`cd21a264d637bab30fed765bdc25ed09bb4ff56f6efb9c88ee09be4ca6e1648b`，U3b AtomicMeasure=`59ddc48fb7b395f362939e58cbd9d7911685a6ed6e6574142e8a6d4ab3ee0c39`，U3c FiniteStageMeasure=`1a32fb904e6ee9d2b0b48d92c4ebb3568452bb02500ce52a1a03eb01ae0256b1`，均与前序审查相同。实际dyadicMesh(J)=(2^J)⁻¹>0，Y(baseAtom)=[−9,7,6,12]，Y(addedAtom j)=6+dyadicMesh(j+1)。finiteMass的新增侧仍在j<J时r_j、否则0。

| R1锚点 | 精确语义对应 |
| --- | --- |
| 113–119 | 源新增点编号从1起，实际addedAtom(j)对应源j+1；阶段FinJ保留j=0,…,J−1，最新点是addedAtom(J−1)，其法向差正好为mesh(J)。 |
| 396 | 阶段所有Y值属于h_Jℤ，由U6c真实整数缩放定理与mesh逆幂定义给出，不只相位范数为1。 |
| 397–398 | “差群包含h_J”在实际测度上必须由真实正质量点取得；候选明确用hpos和通用两点上界排除任意平移的大格距，没有仅以零平移包含冒充最大性。 |
| 400–406 | 网格层相位θ、居中层网格和统计量代数恒等式不在当前八目标中；本审查不把最大法向格距升级为这些后续目标或LLT。 |

## 八目标的独立数学、正质量与边界核查

**网格存在与精确索引。** U6c `stageAtom_normalValue_scaled_integer`给每个活跃点的 `2^J Y(a)=k∈ℤ`。实幂2^J非零，合法乘其倒数得Y(a)=mesh(J)k；J=0亦成立。U1新增/旧法向公式直接给 `Y(addedAtom J)−Y(baseAtom2)=mesh(J+1)`，第二目标保留正确的J+1，没有偏移一项。

由AE有限值域，逐点取活跃索引并用第一目标，选择offset=0及mesh(J)>0，即给第三目标。该步骤不需概率或正权；即便μ为0，仅网格存在结论仍真。最大性另有正原子门，未对零测度断言存在最大格距。

**任意平移网格的两点上界。** 设hspan给h>0及同一offset的AE整数表示。若该表示在指定x点不成立，则singleton{x}包含在AE异常零集，迫使μ{x}=0和μ.real{x}=0，矛盾于hx。y点相同。因此取得实际整数k_x、k_y，且

```text
Y(x)−Y(y)=h·(k_x−k_y)。
```

offset完全抵消。hdiff>0与h>0使整数差严格正，故至少1；从而h≤Y(x)−Y(y)。整数符号/离散下界才是关键，不是仅知道差非零。此论证不需μ概率；实际单点正实质量门足以排除AE虚支撑。第四目标准确消费任意offset，未限定候选网格必须经过0。

**最大性及J=0。** 第三目标先给候选自身mesh(J)是合法正格距。对任意其他h'及其任意offset，分阶段取正差：

- J=0：活跃旧点baseAtom1与baseAtom2的Y值为7和6，hpos给两者实际单点正质量，差1=mesh(0)。通用两点上界给h'≤1。
- J=N+1：取最新活跃点addedAtom(N)（其活跃索引Sum.inr⟨N,N<N+1⟩）与旧baseAtom2。hpos同时给两点实际正质量，第二目标的正差为mesh(N+1)=mesh(J)，所以h'≤mesh(J)。

这与自身网格存在合成定义中的已达到最大性，证明第五目标。J=0无需构造不存在的新增点，也不把收敛极限点当自动正原子；旧baseAtom2的正质量是hpos明确提供的。格距不只是在一族零offset网格中最大。

**真实π_J与P_J，不能互换。** π_J版本虽不带矩方程/概率门仍成立：hp与hr给完整finiteMass非负，活跃旧侧质量为finiteBase_i>0，新侧由j.isLt等于r_j>0，未来0。fixedAtom单射及实际 `atomicMeasure_real_singleton` 在非负门下给这些实轴singleton的真实质量，不需要HasSum1。U3c已证π_J的AE有限值域，因此可用第五目标；无需r可和，因为截断只有有限质量。

P_J版本另外保留hM、hc，使有限四HasSum的第0坐标给真实质量1，U4归一化因子Z_J>0。U3c `finite_original_atom_pos`在这些准确门下给每个活跃点的实际P_J实质量>0，`originalMeasure_finiteMass_ae_range`给同一有限值域AE支撑。故P_J最大格距等同mesh(J)，不是把π_J的质量直接当成P_J质量。任意实ℓ（含0/负）指数仍处处正，在有限紧支撑上真实可积；不需额外ℓ≠0。

**同一source参数与实际概率性。** 第八目标可一次取U3c `exists_source_finite_and_limit_family`的同一p/q/eps，在引入后来整条r之前固定。每个合格r给全部J的旧有限权重正与同一hc，source矩阵非奇异性已有完整证明；hr全正，满足两个有限最大格距目标。对每个J的π_J/P_J概率性也由同一U3c前提和四矩继承，虽最终签名不重复列出概率字段，实际对象始终是这些真实源律。

所有r/J共用同一p/q/eps，不让q/eps依赖阶段或样本n，不把U6d固定极限P替换成P_J来做共振积分极限。有限未来零项只影响非活跃点，不影响所选正质量见证。有限法向格点是目标本身，不能套U6b的全无限正原子严格联合非格点结论。

STATUS: CORRECT

JUSTIFICATION: 两定义与八签名忠实表达真实有限Y分布的最大正格距；AE平移网格在实际正原子上的提升、offset消去、正整数差至少1、阶段最新点精确mesh差、J=0两旧点差1、真实π_J/P_J门及同一p/q/eps对全r/J均数学正确。可按原冻结接口实现，无需修改前提。本报告仅为独立声明/source gate，未实施或运行U8 Lean；LLT、相位返回、尾渐近、层统计代数、曲边界常数、尖点、产品TV和对角未在此证明，根A/B/C/D保持OPEN。
