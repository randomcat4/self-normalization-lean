# U5a 独立声明与来源审查

## 第一阶段：只读 Lean 代码块的盲译冻结

本节在读取 scope 解释、真实 R1、导入定义或其他报告之前落盘。只读取 `tenth-unit-scope.md` 的 Lean 代码块，实测 SHA256 为 `1de636f4c3d8cbd7d4fafd715ab8af5fad0e65e5d3a138d239c69b51a91d6eeb`。没有读取 U5aAPI 或作者笔记。尚无实现，本报告不声称任何 U5a Lean 检查。

两个定义的独立翻译：`saddleRate ℓ q w = ℓq + log(inverseNormalizer ℓ w)`；`originalAtomEntropy ℓ w` 是全索引 `AtomicIndex` 上 `w_i log(w_i / originalMeasure(ℓ,w).real{fixedAtom i})` 的实数无限和。该和的分子是 w 权重，分母是 originalMeasure 的实际 singleton 质量；名称本身不能证明它是相对熵或可和，必须随后核查对象及 HasSum。

九个目标的精确含义如下。

1. 对任意 ℓ、w，`originalMeasure ℓ w` 几乎处处落在 `fixedAtom` 的值域内。无正性、归一化或矩前提。
2. 若 w_i≥0，且每一坐标约束的加权特征族真正 HasSum 到 `constraintTarget q`，则 `normalValue` 对 `atomicMeasure w` 可积，其积分等于 q。
3. 若 w_i≥0、HasSum w 1，且指定 i 的 w_i>0，则该点的实际对数质量比恰为 `ℓ normalValue(fixedAtom i)+log(inverseNormalizer ℓ w)`。
4. 若每个 w_i>0 且全部坐标约束真正 HasSum，则逐原子的加权对数比真正 HasSum 到 saddleRate。此项强于只写一个总化 tsum 等式。
5. 同样严格正质量及 HasSum 约束下，定义的熵 tsum 等于 saddleRate。
6. 增加 ℓ≠0 后，`exp(−ℓq) < inverseNormalizer ℓ w`。所有原子权重严格正，不能仅非负；其严格性有待核查原子上 normalValue 的非退化。
7. 相同前提下 saddleRate 严格正。
8. 相同前提下 originalAtomEntropy 严格正。
9. 存在同一组 p、q、eps，满足 p 的四坐标严格正、1<q<103/100、eps>0、固定参数 `sourceEll` 下矩阵方程；对每一条严格正、可和且总和<eps 的自然数尾质量 r，结论同时给 originalMeasure 为概率测度，x 真实可积且均值 0，实际熵等于 saddleRate，且两者均严格正。p/q/eps 的存在量词在 `∀r` 之前，不能依赖后来选定的 r。

盲译未从名称推断 π、P、normalValue 或 sourceEll 的具体含义。下一阶段须核查实际导入定义、π 的均值 q/4 与 P 的均值 0、离散熵两测度顺序、ℓ 非零的严格性，以及来源所承诺的范围。

## 第二阶段：实际定义、scope 与真实来源

盲译先落盘后，才完整读取 scope 解释及真实 R1 146–159。真实 R1 全文件 SHA256 为 `3473d34ff20bd0d334b9ef3ea3c3ee167fba4d5cc3a742849820ce54d639e662`（同一只读文件已在本轮 U6b 阶段实际核对）。没有读取 U5aAPI 或作者笔记。

实际读取 `FiniteConstraints.lean` 的定义、`SummableAtoms.lean` 的全索引/单射/支撑与 source family 接口，以及 `AtomicMeasure.lean`、`InverseTilt.lean` 和已完整独立 CORRECT 的 U4 报告。对象确为：

```text
Y(x)=normalValue x=8x−x²，AtomicIndex=Fin 4⊕ℕ；
π=Σ_i w_i δ_(fixedAtom i)；
Z=∫exp(−ℓY)dπ；
P=π.tilted(−ℓY)，P{a_i}=w_i exp(−ℓY(a_i))/Z。
```

实际 `fixedAtom` 单射；四个旧点为 −1、1、4+√10、2，新增点为 `4+sqrt(10−2^(−(j+1)))`。全部 |x|≤4+√10，双方的可数原子值域相同。π 的实际 singleton 质量由 `atomicMeasure_real_singleton` 给 w_i；P 的 singleton 公式与严格正性由 U4 的 `originalMeasure_real_singleton`、`originalMeasure_atom_pos` 给出。

| 真实来源 | 精确覆盖及保留范围 |
| --- | --- |
| R1 149–151 | π 的均值为 q/4，已有 `atomicMeasure_mean`，由第 3 矩减第 1 矩再除 4 得出。U5a 不将这个均值改成 0；其 `atomicMeasure_normalValue` 要求的是 EπY=q。有限 π_J 的相同均值未在本 scope 新证。 |
| R1 152–153 | 鞍点方程及全局性质不在本单元目标中；名字 saddleRate 不能视为已经证明鞍点存在、唯一或全局极小。 |
| R1 154–157 | `saddleRate` 的符号正是 ℓq+log Z。熵使用 π 权重乘 log(π/P)，不是 D(P∥π)，其实际分母为 P 的实轴单点质量。 |
| R1 158–159 | Y 非常量使严格 Jensen 成立，ℓ≠0 是显式门；正率和指数归一化等式具有正确符号。本单元只证明无限律这部分，不将其升级成尾渐近。 |

## 数学与边界可行性核查

**真实概率与 EπY=q。** hm 的第 0 坐标是 HasSum w 1；严格正 hw 蕴含非负，故 π 真为概率测度。实际四特征为 `(1, x²−4x, x exp(−ℓY), x²)`，目标为 `(1,0,0,q)`。恒等式 `Y=x²−2(x²−4x)` 将 hm 第 3 坐标减去两倍第 1 坐标，得到加权 Y 的真实 HasSum q；结合原子积分桥给 Integrable Y 和 EπY=q。不是由一个总化 tsum=q 倒推可积。

**P 的概率与均值。** U4 对任意实 ℓ、非负真实概率权重已给逆指数真实可积、Z>0、P 真概率。第三特征 `x exp(−ℓY)` 的零矩给 EPX=0；它与 EπX=q/4 是不同积分，scope 和最终族均保持两者区别。紧支撑对任意实 ℓ 保证指数与 Y 所需可积性，不需要偷偷加入 ℓ≥0。

**实际离散相对熵。** π、P 均集中于单射的同一可数原子族，π{a_i}=w_i>0，P{a_i}>0；所以求和没有重数、丢失连续部分、top 的 toReal 或零分母。逐点比值等于 `Z exp(ℓY(a_i))`，其正数对数为 `ℓY(a_i)+log Z`。hw/hs 及该项 hi 正是消去 w_i、取正对数所需的前提。原点之外的零质量区域不影响两离散概率律。

**HasSum 真可和。** 对每个 i，把加权对数比写成 `ℓ(w_iY(a_i))+(log Z)w_i`。这两条序列分别有真实 HasSum ℓq、log Z，所以目标的 HasSum 到 ℓq+log Z 成立，包含真实 Summable。也可由有界 Y 和 HasSum w 1 得加权绝对值可和。因此 `originalAtomEntropy_eq` 取 tsum 不落在不可和时默认 0 的分支；它是这一对实际离散概率律的有限 D(π∥P)。未要求建立任意测度上的通用 Radon–Nikodym KL 框架。

**严格 Jensen 的非退化和必要门。** 令 T=−ℓY，其均值为 −ℓq。指数严格凸，Y(−1)=−9、Y(1)=7，两个实际原子均有 w>0；ℓ≠0 使 T 在这两个正质量点的取值不同，故 T 不可能 AE 常量。两点至少一个不同于均值。严格切线缺陷 `exp(T)−exp(m)(1+T−m)` 处处非负且在该正质量原子严格正，所有项均真实可积，积分便严格正。这给 `exp(−ℓq)<Z`，并非只给弱 Jensen。Z>0 后由 log 严格递增得到 `−ℓq<log Z`，即 saddleRate>0；熵等式给 entropy>0。

若 ℓ=0，则 Z=1、P=π、率与熵都为 0，不能删 hell。若只保留非负质量，允许 Y 在有质量点上常量，严格 Jensen 不再自动成立；当前所有原子严格正足以排除此退化。hw 比数学上最弱门略强，但与源 family 一致，未造成错误声明。

**先固定的 source family。** 实际 `sourceEll=log(31/30)>0`，所以 hell 不需新的源假设。前序 `exists_source_limit_family` 已一次选择 p、q、eps，再对全部合格 r 给严格正全权重和四个 HasSum。U4 原律族、当前熵等式/严格性可消费同一 witness 与同一 r。最终声明存在量词在 ∀r 前，保留 q∈(1,1.03) 和 eps>0，未让 p/q/eps 随 r、J、n 变化。r 的正、可和、小总量门并非空集，前序还已有 `exists_positive_small_summable`。当前最后一条未新输出 π 的所有性质，但其已冻结前序接口确保对象对应，没有将 π=P 或令 P 均值变成 q/4。

STATUS: CORRECT

JUSTIFICATION: 两定义与九目标签名在实际定义下忠实落实 R1 146–159 中无限原律的 D(π∥P)=ℓq+log Z>0。实际单射原子、双方真实 singleton、Z>0、HasSum 真可和、ℓ≠0 与两个正质量异 Y 原子的严格性均有足够前提；均值 q/4 与 0、固定 p/q/eps 的量词顺序未混淆。此为独立声明/source 审查，尚无 U5a 实现或机械认证；有限阶段律、鞍点全局唯一性、协方差、LLT、尖点、对角与根 A/B/C/D 保持 OPEN。
