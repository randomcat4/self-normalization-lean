# U11d v2 独立声明与来源审查

## 第一阶段：明确范数实例下的盲译

本节在读取v2解释、v1对照、真实来源或固定Normed.lean之前落盘。只提取twentieth-unit-scope-v2.md的Lean代码块：一实际定义、五完整类型。v2实测SHA256=`4857b5da48d16c4f05c6b81fed92f7e9109ad8b94cd355e4c78ce0e8f7f28d8c`。本轮按指定新增Mathlib.Analysis.Matrix.Normed导入和`open scoped Matrix.Norms.Elementwise`理解矩阵范数：对于2×2实矩阵，范数为四个条目绝对值的最大值，即两层sup。该实例仍须在后续只读固定库中验证。本轮不读取作者实现、失败日志、API或receipt，不运行Lean目标。

定义correctedInverseScale(ell,q,mu)为`(ell sqrt R(mu))⁻¹`，R=真实normalVariance−(32ell/q)det真实parabolaCovariance。任意输入下此实数表达式总化；只有后续ell>0和R>0门支持正逆尺度与连续性。

1. 非负HasSum到1的w/v，对每个自然k，两真实原子k次幂矩积分差绝对值≤beta^k L1(w,v)，beta=4+sqrt10，k=0包括。
2. 任意合法参考概率w、eta>0，存在delta>0，使每个同样非负HasSum1的v且真实L1(v,w)<delta，同时满足四个实际协方差条目误差的最大值<eta，以及真实Var(Y)误差绝对值<eta。这里一个共同delta控制两种误差，明确采用最大元素范数。
3. 对固定sourceEll、1<q<103/100、非负w、四旧权重严格正和四约束真实HasSum，实际radicand R(w)>0。
4. ell>0、q>0、参考合法概率w及R(w)>0，任意eta>0有delta>0，对全部合法v且L1(v,w)<delta，同时R(v)>0及正域逆尺度误差<eta。sqrt与逆所需正/非零门不能由总化定义代替。
5. ell>0、q>0、p、非负参考r与J、hM/hc、有限旧质量非负及实际有限律R>0下，对eta>0先有cap>0，随后对全部非负真实可和s：其前J项逐项等于r，limit旧质量非负，且整个shift J+j尾<cap，则limit(s)的R>0且逆尺度与有限参考误差<eta。r本身不要求可和，cap在整个未来s之前；n不出现。

待核：明确范数实例是否确实可用、其定义是否为两层sup及与已有矩阵拓扑相容；v2对比v1是否只修复实例环境而无类型前提变化；真实可积矩、多项式连续性和前缀cap量词是否仍正确。当前尚无裁决。

## 第二阶段：v1/v2对照与历史说明

盲译落盘后读取v2解释及v1，只比较scope，不读取当前作者实现或失败日志。v1实测SHA256=`5ea11ed53acc78efda65d33bb9af8c7225913b0cea5be74c26a260eafa571d6e`；旧声明报告实测SHA256=`ee14fbd8450a45f3e80c42cbd2f3c1c6f4aa968e788f96f943d78c80eda17176`，两者均保持原样。

独立比较结果：两个版本的整个Lean代码块逐字符相同，即一完整定义体及五完整类型文本完全相同。v2仅在声明环境加入`Mathlib.Analysis.Matrix.Normed`、`open scoped Matrix.Norms.Elementwise`，并追加明确范数修复说明。未改数学前提/结论或量词；隐含范数实例从未指定改为明确指定，是实际接口修复，不能只用文本相同跳过重新审查。

旧声明票遗漏了“原声明环境没有矩阵Norm实例”这一接口门；其数学连续性论证不等于原签名已经可elaborate。首轮失败事实来自协调者通知及v2说明，本轮没有读取或重跑失败日志。旧票保留为历史，本票只为v2的明确实例环境作独立裁决，不追溯改写旧票或声称旧票已核该实例。

## 第三阶段：固定范数定义、作用域与拓扑相容

只通过指定服务器读取固定Mathlib源，命令返回exit0、stderr为空；没有Lean构建/检查目标，没有读作者实现/API/receipt。实际Analysis/Matrix/Normed.lean SHA256=`5e737d140faf1a27e87900485f751f8f9d861408867a4f04e6bcdfcca4116c46`，其已有Normed.olean实际存在。

逐项固定源证据如下：

| 实际行 | 独立核对 |
| --- | --- |
| 13–21、46–47 | 文件明确多个自然矩阵范数均作非全局实例，Elementwise须显式打开作用域，不能从已有矩阵拓扑就默认推出Norm实例。 |
| 75–80 | Matrix.seminormedAddCommGroup明确“sup norm of sup norm”，实际定义为`fast_instance% Pi.seminormedAddCommGroup`。 |
| 84–89 | norm_def为两层函数范数的rfl；norm_eq_sup_sup_nnnorm精确等于两层有限sup的条目nnnorm。ℝ条目的nnnorm即绝对值对应的非负实数。 |
| 93–100 | norm_le_iff及norm_lt_iff分别在r≥0/r>0门下等价于全部条目的范数界。尤其eta>0时，目标2的矩阵norm<eta恰等价于四个条目绝对差均<eta。 |
| 178–183 | Matrix.normedAddCommGroup实际为`fast_instance% Pi.normedAddCommGroup`，提供真实NormedAddCommGroup结构，不只是一个孤立Norm符号。 |
| 201–206 | Matrix.normedSpace实际沿用Pi.normedSpace，实数上的矩阵多项式连续性可在该范数线性空间中消费。 |
| 208–216 | namespace Norms.Elementwise内显式以`[scoped instance]`注册Matrix.seminormedAddCommGroup、normedAddCommGroup、normedSpace、isBoundedSMul、normSMulClass。外层namespace Matrix下，其确切作用域名正是Matrix.Norms.Elementwise。 |
| 223–228 | 另一个Linfty operator章节才是sup行和；v2没有选择该作用域，所以不能把当前常数误解为行和范数。 |

拓扑与一致结构另行只读核实：Topology/Instances/Matrix.lean SHA256=`ac497268bcceab1bec286c4837554ebda1cead3cf6286f546b1decfb06771bc8`，47–48行既有矩阵拓扑正是`inferInstanceAs (TopologicalSpace (m→n→R))`；Topology/UniformSpace/Matrix.lean SHA256=`3005ef69c4dd0963286e8de63e44975b5e449a27c6cf35e2c19cd9c7a9a943df`，24–25行一致结构同样为两层Pi，31–35行给逐条目comap的Pi一致结构。Elementwise的Pi范数结构沿用这同一结构，故与既有矩阵拓扑相容；不是换了一个未核的新拓扑再声称旧连续性可用。

对当前Matrix(Fin2)(Fin2)ℝ，Fin2的Fintype和ℝ的范数/线性结构均明确存在。v2指定导入加作用域正好提供此前缺失的实例。这里只读核实例及其定义，不虚称已经重新elaborate五个候选声明。

## 第四阶段：来源与明确最大元素范数下的数学复核

本次重新读真实R1 239–257、438–443、523–529，实测SHA256=`3473d34ff20bd0d334b9ef3ea3c3ee167fba4d5cc3a742849820ce54d639e662`。源的Delta=Cov(X,X²)、S=Var(Y)、Lambda1=S/D−32ell/q及v_corr²=ell²(S−32ell D/q)不受这个有限维范数选择影响。ell>0和R>0时正根逆仍为(ell sqrt R)⁻¹；(30)仍是标量逆尺度误差预算。

真实原子可积/MemLp2、U7 actual协方差定义及source曲率门沿用已完成的独立源核对，现按v2明确实例复核五项：

1. β=4+sqrt10，共同actual fixedAtom支撑有|x|≤β，故任意k包括0满足|x^k|≤β^k。非负HasSum1给真实可和及概率，U11c任意原子有界函数API给幂矩真Integrable及所写L1界，未用不可积积分总化。
2. 各合法概率上X、X²、Y均共同有界，从而真实MemLp2；actual covariance_eq_sub和variance_eq_sub可合法把四条目写为m2−m1²、m3−m1m2（两次）、m4−m2²，S写为64(m2−m1²)−16(m3−m1m2)+(m4−m2²)。一至四阶矩由目标1给L1连续性，这些实多项式逐条目及S连续。对有限四条目和S分别取正半径后取有限min，全部条目差<eta；固定库Matrix.norm_lt_iff(heta)正好把四个条目界转成所声明最大元素范数界。无需误用行和系数或仅依赖未明确的“某个有限维范数”。
3. hm第0分量给真实概率；hw/hbase通过实际singleton质量给U7真实D>0及Lambda1>0。R=D·Lambda1>0，source系数32和q分母不变；不升级全局鞍点结论。
4. determinant为四条目多项式；最大元素范数控制每条目，所以R随L1局部连续。参考R0>0可先保R(v)>R0/2>0，ell>0给ell sqrt R0非零，t↦(ell sqrt t)⁻¹在此正域连续。再取共同更小正半径给标量误差<eta；不在sqrt=0或ell=0总化分支声明连续。
5. 参考finiteMass(r,J)只依赖前J项，hr/hj/hM/hc给实际概率，r无需Summable。第4项在该有限参考与hR处先给delta>0，C(ell)>0，取cap=delta/C。对之后任意合法s，前缀相等给整个finiteMass(s,J)=finiteMass(r,J)；s的真实Summable和limit旧质量非负及hM/hc给limit概率。U11b应用于s得L1(limit(s),参考)≤C·完整s尾<delta，再用第4项。cap先于∀s，构造不读取未定s；J=0为空前缀/全未来尾，仍正确。n不出现。

v2明确范数后，上述真实可积、正域和因果cap量词的数学内容无新增缺口。它仍只是(30)的正预算接口，不代表实际LLT/witness或最终对角已经构造。

## 最终v2声明裁决

STATUS: CORRECT

JUSTIFICATION: v2明确加入固定已缓存矩阵范数模块及Elementwise scoped实例，实际提供所需Norm/NormedAddCommGroup/NormedSpace；其两层sup范数在2×2实矩阵上就是最大元素绝对值，且与既有Pi拓扑/一致结构相容。五声明文本和定义体与v1精确相同，但本轮重新核过这个实际实例下的完整类型与数学意义。真实矩可积、多项式连续性、正radicand/sqrt/逆门和先cap后未来s均成立，未发现关键声明缺口。

本票仅批准v2声明/source gate；没有读取当前作者实现、失败日志、API或receipt，没有执行Lean构建或审计，不声称U11d实现已通过。旧scope/旧票保持历史原样，本轮只新增本报告。根A/B/C/D全部OPEN。
