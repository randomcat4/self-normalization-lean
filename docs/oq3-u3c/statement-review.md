# U3c 独立声明与来源审查

## 第一阶段：仅 Lean 代码块的盲译冻结

本节在读取 scope 解释、真实 R1 或作者笔记前落盘，只读取 `eleventh-unit-scope.md` 的 Lean 代码块。实测 scope SHA256=`1693b5970255be976c08172fff0dab38afd4d9669f0a0774bba8bbd1f1d80d88`。尚无实现，本报告不声称目标 Lean 检查成功。

唯一新定义 `finiteMass(ℓ,p,r,J)` 使用与极限律相同的完整 AtomicIndex：旧侧是 finiteBase(ℓ,p,r,J)，新增自然数侧在 j<J 时为 r_j，在 j≥J 时为0。它是完整索引上的有限阶段零延拓，不是每个无限原子均有正质量。

八个实际候选签名的独立翻译如下。

1. 任意 ℓ、q、p、r、J，只要矩阵行列式非零且同一 p 满足完整矩阵约束，就有 finiteMass 的全部加权特征在完整索引上真实 HasSum 到同一 constraintTarget(q)。无需 r 可和/非负，因为实际有限截断。
2. 对固定 ℓ≥0 和四坐标严格正的 p，存在同一 eps>0，使每条非负、可和、总质量<eps 的 r，在所有自然数 J、所有旧索引 i 处 finiteBase 都严格正。eps 在 r/J/i 前固定，可能依赖 ℓ、p。
3. 若该阶段 finiteBase 非负且整条 r 非负，则完整索引 finiteMass 非负，包括未来零项。
4. 对任意参数，atomicMeasure(finiteMass) 几乎处处落在四旧点加前 J 个新增点的有限 stageAtom 值域。无正性/概率前提。
5. 同样无条件，originalMeasure(ℓ,finiteMass) 几乎处处落在同一有限值域。
6. 矩阵非奇异、p 的矩方程、该阶段有限旧权重非负和 r 非负的门下，原律 P_J 真为概率；恒等函数对 P_J 可积且均值0；P_J 有统一 AE 双侧绝对值界；以正对数权重 ℓY 再倾斜 P_J 精确返回该阶段 atomicMeasure。ℓ 在此不限符号。
7. 相同矩阵门下，若有限旧权重及整条 r 严格正，则每个活跃索引 `Fin 4⊕Fin J` 所对应的 P_J 实单点质量严格正。没有要求/推出所有完整无限索引均正。
8. 存在同一 p>0、q∈(1,103/100)、eps>0 及 sourceEll 矩阵方程，使后来每条正可和且总量<eps 的 r 同时满足：极限 limitingMass 全索引严格正、四特征真实 HasSum；并且对所有 J，finiteBase 全旧索引严格正，finiteMass 四特征真实 HasSum，P_J 真概率、恒等函数可积且均值0、P_J 的 AE 支撑在对应有限 stageAtom 值域。p/q/eps 先于全部 r 与 J；所有 J 使用同一 r 的不同截断。

盲译阶段尚未核对 finiteBase 与 stageWeight 的具体对应、j<J 与源编号的偏移、J=0，以及是否能为有限与极限同时选一统一半径。也没有从有限 P_J 的正活跃原子推断 U6b 所需全无限正质量或套用 U5a 的全索引严格正熵目标。

## 第二阶段：真实来源与现有定义核对

盲译落盘后才读取 scope 解释与真实只读 R1 113–145。R1 实测 SHA256=`3473d34ff20bd0d334b9ef3ea3c3ee167fba4d5cc3a742849820ce54d639e662`，与冻结值相同。未读取作者 notes/API/frontier；未读取或编写 U3c 实现。

实际 `SummableAtoms.lean` 36–37 定义

```text
finiteBase ℓ p r J = compensatedBase ℓ p
  (j:Fin J ↦ addedAtom j.val) (j:Fin J ↦ r j.val)。
```

`FiniteConstraints.lean` 53–62 中 compensatedBase 正是 p 减同一四特征矩阵逆乘前 J 个新增点的加权特征向量；stageWeight 的旧侧就是该 finiteBase，新侧就是 Fin J 上的 r。stageAtom 的旧侧是 baseAtom，新侧是这些 addedAtom。因此 finiteMass 在嵌入 `Fin 4⊕Fin J → AtomicIndex` 的活跃子集上与 stageWeight 完全相同，在其外为0；没有引入第二套点位置或质量。

| 真实 R1 锚点 | 候选的精确对应及范围 |
| --- | --- |
| 113–119 | 源 x_j 从 j=1 起，实际 addedAtom(k) 使用 mesh(k+1)。候选保留 k<J，等价源1≤j≤J，不丢首原子或额外加入未来原子。 |
| 122–126 | 同一 r 的前 J 项进入已有 compensatedBase，有限旧质量精确补偿该部分，future 项零延拓；没有把每阶段截断总质量当作新参数。 |
| 127–130 | 一个统一小总量半径保所有阶段旧质量正，并和已审极限族共享 p/q；完整有限四矩以真实 HasSum 在共同索引空间表达。 |
| 132–135 | p/q/eps 在整条后来 r 和所有 J 前固定；r 以后可递归选择，但 witness 之后选尾的对角过程不在此目标中实现。 |
| 137–140 | π_J 是 atomicMeasure(finiteMass)，P_J 是同一 finiteMass 的逆倾斜原律，继承真实 singleton 归一化与 Z_J>0，未把原无限 P 替换成 P_J 去消费 U6d 极限。 |
| 142–143 | P_J 的中心化、实际恒等函数可积及统一 AE 双侧界由明确概率/矩门推出；没有提前输出独立样本或 V_n 性质。 |
| 144–145 | 以 ℓY=8ℓx−ℓx² 再倾斜该同一 P_J 精确返回该 π_J。 |

## 八目标的独立数学与边界审查

**有限 HasSum 与有符号分支。** 对每一坐标 k，finiteMass 加权特征在完整索引上的非零支撑至多为四旧索引加0,…,J−1，故即使 r 有任意符号、不可和，其序列也真实 HasSum 到对应有限和。该和就是 U1 `compensated_stageMoment` 的分量；hM 与 hc 正好满足其两个条件。未将测度的 ofReal 截负解释成有符号矩；只有有符号代数/HasSum 目标不要求非负，真正概率结论另有明确非负门。

**统一有限半径。** 已审 U1 `exists_compensation_radius`（102–108）对全部有限 J 同时给正半径，消费新增点特征统一界。已审 U3a `addedAtom_feature_bound`（39–70）在 ℓ≥0 时给 B=(4+√10)²。对 hr≥0、Summable r，有

```text
Σ_(j<J) r_j ≤ Σ'_(j≥0) r_j < eps。
```

所以同一个 eps 直接对每个 Fin J 截断消费补偿半径，得到全部 finiteBase>0。eps 不依赖 J 或 r；不需要交换极限与正性，也不从“最终 J 正”推“所有 J 正”。该一般半径目标无 hM 是合理的：U1 的逆矩阵范数界对 Lean 中已定义的实矩阵逆（含奇异时的总化逆）仍有界，正性估计不需要矩恒等式；非奇异性只在准确四矩目标中使用。

**完整索引非负与有限 AE 支撑。** finiteMass_nonneg 的 Sum 两分支及 if 两分支分别消费 hp、hr 和0≥0。对任意参数的两个 AE range 目标也成立：旧侧 dirac 位于四旧点，激活新增侧 dirac 位于对应 Fin J 的 stageAtom 值域，未激活侧权重恰为0、ofReal(0)=0，不产生值域外质量。即使有负活跃权重，ofReal 截成0只会减少实际测度支撑。有限值域在实轴上可测；对完整 measure.sum 逐项验证即可。P_J 的有限支撑由 tilted 对 π_J 的绝对连续性继承，不依赖概率、Z 正或错误的“有界即有限”推断。

**真实有限 π_J/P_J。** 在 finite_original_properties 的非负门下，第一目标的第0坐标给 HasSum finiteMass 1，故 π_J 真为概率。四坐标是 `(1,x²−4x,x exp(−ℓY),x²)`，目标 `(1,0,0,q)`；U3b 给真实可积约束，U4 给逆指数真实可积、Z_J>0、P_J 真概率、恒等函数可积且 EP_J X=0、统一 AE 界和完整再倾斜恒等。对任意实 ℓ，有限支撑（亦有共同紧界）保证连续指数可积，所以此概率目标无需 ℓ≥0。π_J 的均值仍为q/4，由四矩相减得出；P_J 的0均值来自逆倾斜中心化特征，两者不交换。

**活跃原子的严格正性。** 将 i:Fin 4⊕Fin J 嵌入完整 AtomicIndex 后，stageAtom i=fixedAtom(embed i)，finiteMass(embed i) 对旧侧为正 finiteBase、对新侧为正 r_j。全索引 fixedAtom 单射确保真实 singleton 质量就是该权重，没有未来点碰撞或重数。hs=1 与非负门给 Z_J>0，实际 P_J singleton 为 `w_i exp(−ℓY_i)/Z_J>0`。结论只对活跃 i；任意未来 j≥J 的实际质量为0，不能升级到所有 AtomicIndex 严格正。

**J=0。** Fin 0 没有新索引；新增特征有限和为空为0，finiteBase=p−M⁻¹0=p。finiteMass 只保四旧点，所有未来新增质量0。HasSum 四矩还原 hc，概率/正性由对应 hp 门给出；AE finite range 就是四旧点值域。全体签名都含这个边界，没有额外假设 J>0。

**有限和极限同一组参数。** 已审 `exists_source_limit_family` 先给 p、q、epsL，满足 q 范围及 sourceEll 的矩方程，后对所有合格 r 给 limitingMass 全正与真实四 HasSum。对同一 p、固定 sourceEll≥0，统一有限半径给 epsF；取 `eps=min epsL epsF>0`。任何整条 r 的总和<eps 同时满足两半径门，故可在同一 p/q/r 下组合极限结论与全部 J 的有限结论。source 处非奇异性已有 `source_constraintMatrix_nonsingular`，不是新的自由前提。不存在每个 J 重选 p/q/eps，也不需要对每个 r 重选半径。合格 r 非空由已有 `exists_positive_small_summable` 保证。

**有限阶段格点及后续边界。** 源有限 stageAtom 的 Y 值在缩放2^J后均为整数，故沿 U6c 的非零共振频率整个有限支撑的相位为1。这与有限概率律的 CF 范数=1 相容，不能把有限 P_J 说成当前 U6b 意义的严格联合非格点。U6b 要求全无限指定原子质量正，而 finiteMass 的未来零项明确不满足；U5a 的熵/严格正率目标也要求全 w_i>0，不能直接套用它们。当前八签名均未作这些错误调用或输出有限阶段正 KL。

STATUS: CORRECT

JUSTIFICATION: 一定义、八声明忠实表达真实有限 π_J/P_J 与极限律共享参数的桥；同一 AtomicIndex 零延拓、源索引 k+1 偏移、J=0、真实有限四 HasSum、概率/中心化/再倾斜门、仅活跃原子正性和全 r/J 统一半径均数学正确。可按原冻结接口实现，无须修改前提。本报告仅为独立声明/source gate，尚无 U3c 实现或机械认证；定量 TV/尾控制、有限正 KL、全局鞍点唯一性、LLT、尾渐近和对角不在此单元，根 A/B/C/D 保持 OPEN。
