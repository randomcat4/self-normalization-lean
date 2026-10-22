# U11b 独立声明与来源审查

## 第一阶段：只读 Lean 代码块后的盲译

本节在读取scope解释、指定R1或本次实际依赖源之前落盘。本次只提取seventeenth-unit-scope.md的Lean代码块：两个定义、七个完整目标签名。实测scope SHA256=`5006fc0c25fcc4d37194006a18cc31116e13665cd7933804ecae47bfdedc8bd7`。未读作者API或其他notes；尚无实现或U11b构建。

定义compensationTailConstant(ell)为固定原子特征界B=(4+sqrt10)²乘矩阵逆的全部16个系数绝对值之和，再加1。该常数仅依赖ell，不依赖p/r/J/n。定义atomicMassL1(w,v)=Σ'_{i:AtomicIndex}|w_i−v_i|，是同一离散索引的权重差绝对值和；对任意输入它是总化实数tsum，不能仅凭定义认定真实可和、度量或测度总变差。

七目标独立翻译：

1. 任意ell下该补偿常数严格正。
2. ell≥0、r非负且真实Summable时，每个特征分量k的完整无限新增矩减去前J项精确等于从J开始的整个shift-tail特征级数。
3. 同样前提下，每个shift-tail特征矩的绝对值≤B乘该完整未来质量尾和。
4. 同样前提下，任意p、每个旧基点索引i的极限补偿质量减有限阶段质量，恰为矩阵逆第i行乘特征尾向量后的负数。负号在整个有限k和外，逆系数索引为i k。
5. 对四个旧质量差求绝对值之和，≤(compensationTailConstant−1)乘完整未来质量尾。
6. 只需r非负且Summable，对任意ell/p/J，整个AtomicIndex上极限质量与有限阶段零延拓质量之差的绝对值函数有真实HasSum，其和等于四旧项绝对差之和＋整个未来质量尾。这里没有ell≥0门，不承诺任意ell下矩阵概率构造正确。
7. 加ell≥0后，整个atomicMassL1≤compensationTailConstant乘同一完整未来质量尾。

待核重点：实际inverse mulVec行列方向与整体负号、Fin J与shift J+j真实级数拆分、J=0、所有非负/可和门、目标6为何不需要hell、HasSum先排除tsum总化漏洞，以及权重L1与实际测度TV的范围界线。没有hM须仅为有限线性算子恒等式，不得由此推导奇异矩阵下的概率律性质。

## 第二阶段：真实来源与实际依赖定义

盲译落盘后才读取scope解释和真实R1 122–135、516–520。R1实测SHA256=`3473d34ff20bd0d334b9ef3ea3c3ee167fba4d5cc3a742849820ce54d639e662`。前段给阶段J的补偿向量`−M⁻¹Σ_{j≤J}r_jv(x_j)`和小总质量保持正性；后段(29)以固定有界线性补偿映射控制π与π_J的TV。当前候选准确只提取其权重误差输入，没有在目标中宣称测度TV桥已完成。

本次直接只读下列实际已审项目源，而非作者API说明：

| 实际源及SHA256 | 相关定义与核对 |
| --- | --- |
| U1 FiniteConstraints.lean `800d9db8cb6749a31ecfe611409de92b10ea8bb2aef955bfd825ede7324f0ef0` | 35–36行feature四分量；42–43行M(k,i)=第i旧基点的第k特征，行是特征、列是旧质量；50–55行addedMoment为真实有限新增特征和，compensatedBase=p−M⁻¹*ᵥaddedMoment。 |
| U3a SummableAtoms.lean `0ea4c64fe9ef9b45fbf44d24312771a1dbfbcc5de8448564e3e87bdf17c7178b` | 23行AtomicIndex=Fin4⊕ℕ；27–37行无限新增矩为真实tsum，limitingBase=p−M⁻¹*ᵥ无限新增矩，limitingMass=Sum.elim limitingBase r，finiteBase使用Fin J上的r i.val；39–78行给ell≥0时仅新增点的特征绝对值统一界B及真实Summable feature。 |
| U3c FiniteStageMeasure.lean `1a32fb904e6ee9d2b0b48d92c4ebb3568452bb02500ce52a1a03eb01ae0256b1` | 18–19行finiteMass在同一AtomicIndex上定义为Sum.elim finiteBase (if j<J then r_j else0)；不是把有限与无限质量放在不同索引域比较。 |

指定服务器固定Mathlib也只读核到Matrix/Mul.lean SHA256=`90df689a0a8508b82a2895aa6398152c8c1578abe6784b3a80f92d3874d91102`，719–729行mulVec及mulVec_apply_eq_sum准确给`(A*ᵥv)i=Σk A i k*v k`。因此候选逆矩阵的第i行、第k列方向正确；不是误用A k i或转置。

固定InfiniteSum/NatInt.lean SHA256=`4dc1dffbdb6a0b0157e8810b20dfc0051bedf7f449b6d1fa5b8a9a47fa47f645`，232–235行prod_mul_tprod_nat_add的to_additive给真正Summable下“range J前缀和＋shift尾和＝总和”；它有可和前提，shift写作j+J，与候选J+j由自然数加法交换一致。U3a 86–90行已有实际Fin.sum_univ_eq_sum_range对应Fin J与range J。

源正索引r₁,…在阶段J保留j≤J，实际Lean r₀,…,r_{J−1}为前缀。候选J+j从首个未保留的r_J开始，准确对应源Σ_{k>J}r_k，没有少一项。J=0是空前缀，finiteBase=p、finite新增侧全0，尾为全部r。

## 第三阶段：逐项目标可实现性与范围

记A=M(ell)⁻¹、B=(4+sqrt10)²、T_J=Σ'j r(J+j)、S_A=Σ_iΣ_k|A i k|。下列是独立声明审查的数学论证，不是尚不存在的Lean实现证明或构建成功。

| 目标 | 独立核对 |
| --- | --- |
| 1 compensationTailConstant_pos | B≥0，有限绝对值和S_A≥0，所以C=B S_A+1≥1>0；任意ell的总化逆矩阵元素都是真实有限实数。无需hM或ell≥0。 |
| 2 infiniteAddedMoment_sub_prefix | U3a的summable_addedFeature在ell≥0、r≥0、Summable r门下给每个完整feature级数真正可和。由有限range J与shift-tail拆分，再移项得到所写等式；不能对任意不可和tsum使用该移项。 |
| 3 addedMoment_tail_abs_le | 同一真实可和feature级数的shift-tail也可和，且r的shift-tail可和。每项绝对值= r(J+j)·|feature|≤B r(J+j)，使用非负r；先对真实级数取三角不等式，再求逐项界得≤B T_J。B只界新增点，不错误用于旧基点x=−1处可能很大的exp(9ell)。 |
| 4 limitingBase_sub_finiteBase_tail | 由实际定义，(p−A I)−(p−A P_J)=−A(I−P_J)；p严格抵消。目标2给(I−P_J)_k为真实尾矩，mulVec_apply_eq_sum给第i行Σk A i k·尾矩_k，整体负号准确。无需M可逆恒等式，只消费给定有限矩阵A的线性性。 |
| 5 limitingBase_finiteBase_l1_le | 对目标4取绝对值：每个旧项≤Σk|A i k|·|尾矩_k|≤B T_J Σk|A i k|。T_J≥0由r≥0保证，有限求和并交换实数乘法得≤B S_A T_J=(C−1)T_J。常数没有依赖p/r/J/n。 |
| 6 atomicMassL1_limiting_finite_hasSum | 在inl旧侧是四个任意实数绝对差，有限所以真实HasSum到其有限和；inr自然数侧逐项等于if j<J then0 else r_j（因为hr），该零延拓尾由Summable r真正可和，和为T_J。按Fin4⊕ℕ的HasSum.sum组合得到整个AtomicIndex的所写HasSum。这里不需要ell≥0，也不需要变换无限feature级数：limitingBase即使仅作为定义出的实向量也是有限四项，不导致该绝对误差级数总化。 |
| 7 atomicMassL1_limiting_finite_le | 先从目标6的HasSum.tsum_eq得到定义中tsum确为旧四项绝对差＋T_J，再用目标5得≤(C−1)T_J+T_J=C T_J。不能只展开atomicMassL1就宣称其是真实L1。 |

所有结论对r允许零项正确，不要求全严格正。r全0时全部尾和及质量误差均0；J=0时旧差为limitingBase−p、新侧为全部r，目标2前缀空和正确。目标6的ell任意、p任意不暗含基质量正或概率性；其弱前提足够，因为只有旧四项与真实可和r尾。

没有hM是正确的：所有新恒等式均为给定A的有限线性运算与真实特征级数拆分，不使用M A=I来恢复约束。已有四约束概率构造另有hM及p/q/eps/质量门，U1的compensated_stageMoment 68–71行和U3c的finiteMass_constraints 21–23行明确保留这些假设。当前结论不能替代它们，也不能推成奇异矩阵下概率族仍成立。

常数C只依赖固定ell及实际M⁻¹；ell≥0仅是调用统一新增feature界所用充分门。源族可以在固定sourceEll与同一p/q/eps下将本结论同时用于全部J及同一r；当前签名未重选这些参数，也没有在样本量n之后改变常数或律。

### 与测度总变差的界线

atomicMassL1的索引域是真实共同AtomicIndex，目标6真实证明绝对误差可和；它本身仍是权重层结论。这里没有π/P测度tvDist目标，不使用单点像的注入性来省略测度桥，不建立有限/概率门或归一化TV系数。将其用于R1(29)的测度版本须另行证明并明确TV约定；当前不声称(28)、测度版(29)、常数连续性、LLT或最终对角已经完成。

## 最终声明裁决

STATUS: CORRECT

JUSTIFICATION: 两定义、七目标签名准确提取固定线性补偿映射的权重尾控制。实际M⁻¹行列方向与整体负号正确，真正可和的feature级数支持prefix/shift拆分，常数固定且不依赖p/r/J/n。全AtomicIndex目标先给真实HasSum再取tsum；其无需ell≥0的弱前提由有限旧侧及零延拓r尾充分保证。J=0、源/Lean索引偏移与所有非负/可和门无关键缺口，且没有将权重L1冒充测度TV或奇异矩阵概率构造。

这是仅声明/source gate。尚无AtomicTailControl.lean实现、完整证明审查、U11b构建或Audit成功声明；未读作者API/其他notes，只新增本报告。所有根A/B/C/D保持OPEN。
