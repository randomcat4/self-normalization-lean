# U3c 最终独立声明、来源与证明审查

## 第一阶段：实际定义与导出签名盲译

本节在本次读取最终证明、scope、R1、既有声明报告、receipt/Audit 或作者笔记之前落盘。仅读取实际 `FiniteStageMeasure.lean` 的导入、一定义与八个导出签名。实测源 SHA256=`1a32fb904e6ee9d2b0b48d92c4ebb3568452bb02500ce52a1a03eb01ae0256b1`，191行。前序声明审查上下文存在，本次从实际导出重新核对，不读作者 notes/API/frontier。

唯一新定义 finiteMass(ℓ,p,r,J) 是同一完整 AtomicIndex 上的质量：旧侧 finiteBase(ℓ,p,r,J)，新增自然数侧 j<J 时 r_j、否则0。它不是要求所有完整无限索引均严格正的权重。

八目标的独立数学翻译如下。

1. 若四特征矩阵非奇异且同一 p 满足目标 q 的旧矩方程，则每个坐标在完整索引上的 finiteMass 加权特征真实 HasSum 到 constraintTarget(q)。没有非负/可和 r 的额外前提；有限截断应保证此一般版本成立。
2. 任意固定 ℓ≥0、p 四坐标>0，存在同一 eps>0，使每条非负可和、总量<eps 的完整 r，对所有 J 和四个旧索引 finiteBase 都>0。eps 在 r/J 之前。
3. 若该阶段 finiteBase 非负且 r 全部非负，则 finiteMass 全索引非负，包含未来零项。
4. 任意参数下，π_J=atomicMeasure(finiteMass) 几乎处处落在 stageAtom 的有限值域，索引为 Fin 4⊕Fin J。
5. 任意参数下，P_J=originalMeasure(ℓ,finiteMass) 也几乎处处落在同一有限值域；两个纯 AE 目标都未承诺无条件概率性。
6. 矩阵门、旧矩方程与该阶段非负权重门下，P_J 真概率、恒等函数真实可积且均值0、AE 有统一双侧绝对值界；以 ℓ normalValue 再倾斜 P_J 精确返回 π_J。此项 ℓ 不限符号。
7. 相同矩阵门，且旧有限权重、r 全部严格正时，对每个活跃 i:Fin 4⊕Fin J 的实际 stageAtom singleton，P_J 的实质量严格正。没有全 AtomicIndex 正质量结论。
8. 存在同一 p>0、q∈(1,103/100)、eps>0 和 sourceEll 矩阵方程，使之后每条正、可和、总量<eps 的完整 r 同时给极限 limitingMass 全索引正、四个真实 HasSum；并对所有 J 给该 finiteBase 正、finiteMass 四 HasSum、P_J 真概率、恒等函数可积且均值0和对应有限值域 AE 支撑。p/q/eps 先于 r 与所有 J，全部阶段共享同一 r。

本节尚未读证明或裁决。下一阶段须核对真实有限补偿公式、源 j+1 偏移、J=0、有限与极限共同半径，以及零延拓对严格正性结论的限制。

## 第二阶段：冻结接口与真实来源

盲译先落盘后，才读取 scope 解释与真实只读 R1 113–145。实测 scope SHA256=`1693b5970255be976c08172fff0dab38afd4d9669f0a0774bba8bbd1f1d80d88`；既有独立声明报告 SHA256=`d49a86baaba2b98355095ec2d253f3579dd20ad5f28e6aeb9f3279279c5064af`；真实 R1 SHA256=`3473d34ff20bd0d334b9ef3ea3c3ee167fba4d5cc3a742849820ce54d639e662`，均匹配冻结值。独立空白规范化比较实际定义体与八个完整签名，9/9 完全相同，无前提、类型、量词或定义改变。

实际既有定义保持：`AtomicIndex=Fin 4⊕ℕ`，`fixedAtom=Sum.elim baseAtom addedAtom`；`addedAtom j=4+sqrt(10−2^(−(j+1)))`；`finiteBase ℓ p r J` 是 p 减同一矩阵逆乘 Fin J 上 r_j 与四特征的加权和。stageAtom/Weight 的新增侧索引恰为 Fin J。候选完整索引 finiteMass 在该活跃子集上等于 stageWeight，其外为0，没有另造原子或权重。

| R1 锚点 | 实际覆盖与限制 |
| --- | --- |
| 113–119 | 源 j 从1起，Lean 新索引从0起且定义内保留 j+1。活跃 j<J 精确对应源 j+1≤J。 |
| 122–126 | 实现 27–32 行的同一矩阵补偿严格保留前 J 项，未来零延拓，没有每阶段重新选择尾质量。 |
| 127–130 | uniform finite radius 同时保证全部 J 的旧质量正；最后 min 半径给同一 p/q 下极限全正及全部有限四矩。 |
| 132–135 | p/q/eps 在整条 r 和所有 J 之前固定；本文未实现后续 witness 后选尾对角。 |
| 137–140 | π_J=`atomicMeasure(finiteMass)`，P_J=`originalMeasure ℓ(finiteMass)`，使用已审 U4 的真实指数归一化、实际 singleton 与概率门。 |
| 142–143 | 仅对真实 P_J 给 x 可积、均值0及 AE 绝对值界；未把 π_J 均值q/4交换为0，也未提前输出独立样本或 V_n。 |
| 144–145 | 同一 P_J 以 ℓY=8ℓx−ℓx² 再倾斜精确返回同一 π_J。 |

## 第三阶段：191 行全证明、局部辅助与边界

完整读取固定哈希源1–191行后，在本单元 receipt/Audit/build 日志之前形成独立数学判断：CORRECT，无关键缺口。未读作者 notes/API/frontier。

| 实现行 | 精确检查 |
| --- | --- |
| 18–19 | Sum.elim 旧分支严格使用 finiteBase，新自然数分支以 j<J 截断；对 j≥J 精确是0，非只“趋于0”。 |
| 27–32 | hv 展开 finiteBase/compensatedBase，矩阵乘向量分配及结合后用 hM 取得 `M M⁻¹=1`，再用 hc 得 `M finiteBase+addedMoment=target`。hM 在实际需要处明确使用，未把总化奇异逆当真实逆。 |
| 34–44 | hnat 先在 Finset.range J 外证明截断加权项=0，再以有限非零支撑的 HasSum 定理给真实无穷求和。适用于任意有符号、不可和 r，因为只有有限多项被保留，未隐含使用概率非负性。 |
| 45–50 | 只转换该有限和的目标值：展开 addedMoment，把 range J 和改写成 Fin J 和，每个 j:Fin J 由 j.isLt 精确化简条件项。此处指标是 j.val，保持定义内 j+1 的源偏移；没有方向错误或遗漏边界项。 |
| 51–61 | 旧侧使用真实 hasSum_fintype，化为同一矩阵向量分量；新侧使用 hnat；HasSum.sum 合并到 Sum 索引。hv 的逐分量等式只替换和的值，输出原目标完整 HasSum，而非仅 tsum 等式。 |
| 68–76 | 一次取得 U1 的 compensation radius，统一界 B=(4+√10)²≥0。对任意 r/J，非负可和保证 `Σ_(j<J)r_j≤Σ'r_j<eps`；U3a 的新增特征界在 hell≥0 下对全部 j/k 成立。该同一半径直接给每个 J/i 旧质量严格正，没有从最终正性倒推早期正性。 |
| 81–88 | Sum 旧侧消费 hp；新侧按 j<J 分支分别消费 hr_j 或0≥0，覆盖未来零项。 |
| 94–102 | stageAtom 有限/可数值域可测。对实际 atomicMeasure 的每个加权 dirac 用 ae_sum_iff；旧原子以同一 Sum.inl i 的 range 见证给支撑。无须假定该权重正或概率。 |
| 103–107 | 新侧 j<J 时构造真实 Fin J 值 ⟨j,hj⟩，给精确 stageAtom 见证；j≥J 时 finiteMass=0、对应测度为0，所以 AE 支撑自动成立。不能从未激活 dirac 的位置得到错误额外支撑。 |
| 109–114 | P_J 对同一 π_J 的 tilted 绝对连续性把真实有限值域 AE 性质继承给 P_J；不以有界支撑冒充有限支撑。 |
| 127–133 | 从本单元已证 hw≥0、四个 HasSum 及第0坐标取得质量 HasSum1，满足 U4 真概率、中心化、支撑界和再倾斜的全部门。各项使用同一 finiteMass，ℓ 任意实数且指数在固定紧支撑上真实可积，不走不可积时的总化分支。 |
| 142–145 | 活跃正质量目标先降为全索引非负、完整四矩及总质量1，之后才调用 U4 的实际原子严格正性。 |
| 146–155 | 旧活跃索引用 hp 给对应 finiteMass>0；新活跃 j:Fin J 用 j.isLt 把截断权重精确化为 hr(j.val)>0。stageAtom 与 fixedAtom 的定义化简匹配同一实际 singleton；固定原子单射保证质量没有重数。未把 j≥J 的零项输出为正。 |
| 173–176 | 一次选 source starter 的同一 p/q；随后针对该 p 分别取得统一有限半径 epsf 与极限半径 epsl，选正的 min。存在量词在引入 r 和 J 之前；没有组合两个不相关的 p/q 见证。 |
| 177–181 | 对后来同一正可和 r，以 `Σ'r<min` 分别推出两个半径门。hf 对全部 J/i 同时正；hlimit 给 limitingBase≥p/2，结合 p>0 与 r>0，通过已审 `limitingMass_pos_of_lower` 得极限全索引正。 |
| 182–183 | 同一 hc、source 非奇异性、同一 r 的非负/可和门送入已审 limitingMoment_hasSum，给极限全部四坐标真实 HasSum，未把有限矩极限只写成数值趋近。 |
| 184–188 | 最后才引入任意 J，得到该阶段 hm 与 hprops，组合 hf、HasSum、P_J 真概率、真实中心化及实际有限值域 AE 支撑。所有阶段与极限共用先取 p/q/min半径和同一完整 r。 |

全部局部辅助 hv、hnat、hh、hnot、hsum、hset、hw、hm、hmass、hi、hnonneg、hf、hprops 已逐项审查。没有顶层私有数学引理。源外生成声明将在最后机械阶段依据实际 TYPE/白名单记录核查。

**J=0 与索引边界。** 所有 Fin J/range J 和在 J=0 时为空，addedMoment=0，finiteBase=p−M⁻¹0=p；hnat 的所有自然数项是0。Fin 0 新侧没有元素，支撑证明只有四旧点；未来所有新增质量=0。J>0 时活跃 j=J−1 包含，j=J 排除，恰对应源最后 j+1=J 和下一未来项J+1。实现没有 J>0 隐藏假设。

**有限概率律与非声明。** 真实 π_J 的概率性可由 hw≥0、HasSum1直接推出；其均值是q/4，P_J 的0均值来自第三特征的逆倾斜中心化而不是 π_J 均值。这里仅活跃原子正；未来零延拓使 U6b 所需全无限正质量和 U5a 熵目标所需全 w>0 均不成立，实现也没有导入/调用这些结论。有限阶段在源法向共振频率有格点结构，不能称为严格联合非格点。

固定参数源族完成的是同一 p/q/eps 对全部 r/J 的真实有限律与极限矩桥；没有证明定量 TV、有限阶段正 KL、全局鞍点唯一性、LLT、尾渐近或对角，根 A/B/C/D 保持 OPEN。

本阶段独立数学裁决：CORRECT。以下机械证据在本判断之后读取；不以本地回执摘要代替真实服务器核对。

## 第四阶段：真实服务器机械证据与生成辅助

在上述数学判断写下后，才完整读取本单元 `U3c-receipt.json` 与 `U3cAudit.lean`，实测 SHA256 分别为 `91be4b428782df07950ddb52b390b492a3e0fb379cab19b1208a246025cf27e7`、`466f1e33c119f7a206a6a56b772f11e9afe93c1fb02196eb1be8e0293e33811a`，均匹配冻结值。实际源无 sorry、admit、新 axiom、unsafe、native_decide，无 CR 或尾空白。

已完整审查 Audit 源：要求八目标存在且为 theorem、finiteMass 定义存在；遍历九个源声明前缀与模块私有前缀，拒绝项目新增公理，并对每项用 `Lean.collectAxioms` 检查全部传递依赖，只允许 `propext`、`Classical.choice`、`Quot.sound`。它记录实际 TYPE 与计数，并要求八冻结目标计数相同。

随后通过共享 `tools/server.py` 实际只读核对指定服务器源、承重导入、Git、pin 和既有真实日志，远端 exit 0、stderr 为空。没有执行目标/旧目标编译、Audit 重跑或缓存写入。

- 实际 worktree=`/root/rivermind-data/shao-lean-20261021/workspaces/lead-oq3`，branch=`feat/oq3-finite-laws`，HEAD=`da066a9ebcea65a5b257bfb7c1a2a6bf19601ceb`，与 receipt 基线相同。本报告不声称 main 已集成本单元。
- 真实 `FiniteStageMeasure.lean` SHA256=`1a32fb904e6ee9d2b0b48d92c4ebb3568452bb02500ce52a1a03eb01ae0256b1`，与本地完整审查源/回执相同。
- 真实导入 U1、U2、U3a、U3b、U4 的 SHA256 依次为 `800d9db8cb6749a31ecfe611409de92b10ea8bb2aef955bfd825ede7324f0ef0`、`0e2a081619976f88149707c2ef9311dc909003e61d3d0f7c4e21e6c3dbbc5a6d`、`0ea4c64fe9ef9b45fbf44d24312771a1dbfbcc5de8448564e3e87bdf17c7178b`、`59ddc48fb7b395f362939e58cbd9d7911685a6ed6e6574142e8a6d4ab3ee0c39`、`c7e7d19e8b70481b663bec1fd12ea9301d73313faaf35997e85aa9ba99f21811`，全部与已完整独立 CORRECT 的依赖及 receipt 一致；U4 明确为已审 LF 版本。
- receipt 记录原目标命令 `lake env lean -o .lake/build/lib/lean/Shao/OQ3/FiniteStageMeasure.olean Shao/OQ3/FiniteStageMeasure.lean` exit 0。真实 `runs/oq3/u3c-20261021/build-03.log` 实测0字节，SHA256=`e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`，与回执一致。
- 真实 Audit.lean 为1893字节，SHA256=`466f1e33c119f7a206a6a56b772f11e9afe93c1fb02196eb1be8e0293e33811a`，与本地已完整读取脚本一致；receipt 记录原 Audit exit 0。
- 真实 Audit.log 为6771字节，SHA256=`cee38042a3baf14c99471b1fff398d81df97fb16f887eb0e4885dd88bb155cca`，与回执一致。真实日志已完整读取，八个实际 theorem TYPE 保留全部非奇异/矩/非负或严格正门和共同参数的量词，没有仅信任作者计数。
- 两个真实生成辅助为 `finiteMass.eq_1` 和 `finiteMass_constraints._simp_1_1`。前者 TYPE 正是 finiteMass 的 Sum.elim/if 零延拓定义展开；后者 TYPE 为 `∀{n m:ℕ}, (m∈Finset.range n)=(m<n)`，是 43 行 range 成员到严格不等式的命题等同性化简。两者数学内容已逐项核对，无隐藏正性、矩或源假设；没有顶层私有数学声明。
- 真实汇总为 `U3C_FROZEN_THEOREMS 8`、`U3C_ALL_THEOREMS 10`、`U3C_ALL_DECLARATIONS 11`、`U3C_AXIOM_GATE PASS`。全部十一声明及承重导入的传递公理均在标准白名单内。
- 实际 pin=`leanprover/lean4:v4.36.0-rc1`，manifest mathlib revision=`807d3836b165983210ee2ecf3cd28f239436949c`。同一服务器恢复会话已实际探测 Lean `4.36.0-rc1`（commit `c9afcddf514a6772bd4d649f7cfc04eff0b9f15e`）、Lake `5.0.0-src+c9afcdd`，本次 pin 未变。

STATUS: CORRECT

机械覆盖：LEAN_FULLY_CHECKED，仅指固定哈希 U3c 的一定义、八目标、两生成辅助及其传递依赖的既有真实成功构建/公理审计。本轮另完成独立实际声明—源码—R1 忠实性及所有证明/局部辅助审查，没有根集成构建。

JUSTIFICATION: 冻结定义与八签名完全一致，有限截断真实 HasSum、统一小质量半径、有限活跃 AE 支撑、真实 P_J 概率/中心化/再倾斜、仅活跃原子正性、J=0 与源 j+1 偏移、同一 p/q/min半径对全 r/J 均有完整证明。真实源/承重导入/TYPE/成功日志和传递公理闭包全部相符，无关键缺口。有限阶段 KL、严格联合非格点、全局鞍点唯一性、LLT、尾渐近和对角未在此证明，根 A/B/C/D 保持 OPEN。
