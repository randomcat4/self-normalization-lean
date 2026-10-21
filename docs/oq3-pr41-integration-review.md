# PR41 独立冻结集成证据验收

STATUS: CORRECT / INTEGRATION_EVIDENCE_PASS

验收范围为冻结U5b的实际有限law、相对熵方向、七声明及已有独立证明/执行证据。
本轮不重新证明、不运行Lean或重型计算、不生成对象、不改源/lane状态/缓存、不联系
lead；唯一写入为本报告。FourierComparison声明提案和OddPower源码保持冻结。

结论：未发现源语义、量词、证明票或哈希绑定缺口；七目标可接收。另只读核实root
已完成的v27整库门PASS。正式receipt/publication、PR retarget和合并尚由root完成，
本报告不把待发布状态写成已经合并。

## 1. 冻结提交和字节链

PR：[randomcat4/shao-lean#41](https://github.com/randomcat4/shao-lean/pull/41)。
GitHub只读元数据、服务器commit对象及同名branch引用一致：

```text
head   feat/oq3-finite-rate  4e5522a6c94c2b5f43f9cbc2d099752e02491c61
parent feat/oq3-finite-laws  cc4af50f026ba37f66379dadbdf07e69b8bc6c1c
```

恰一个新commit、6个新增文件，`git diff --check parent head`实际exit0，无数学
依赖、root imports、manifest、锁或其它续作混入。以下每项冻结Git blob都与本机
实际读取的源/票/回执逐字节同SHA：

| 冻结文件 | SHA256 |
|---|---|
| `Shao/OQ3/FiniteStageRate.lean` | `e654bed5e1e132af328eb6763078c7eb84f740999b146cfb5aaa9ae7ed90e29f` |
| `docs/oq3-u5b/scope.md` | `f7d2180ec279d73d4775e3e92bb828a98d9d567eada6123198347b933bc57376` |
| `docs/oq3-u5b/statement-review.md` | `171c82c9b4d72d06df84e21286a10a81899eda244484c3840ab7ad7ffea03a73` |
| `docs/oq3-u5b/proof-review.md` | `fb0e46f0081768466734bada055fed58f4c55a90c1f55bfd049c5ea896fd6e43` |
| `docs/oq3-u5b/author-receipt.json` | `f0b6b69597467f6903bed864b99f36147bba9df7930538c51dbda6b8fb791c4f` |
| `docs/oq3-u5b/Audit.lean` | `34c46cbe78ea20262ed509b10ef2f615ad64e2ac2c478c7558efc7865144d110` |

另读本机 `drafts/oq3/U5b-pr-handoff.json`，SHA
`6077adafd58a0763c3f0128c994ded1d9bed1bee92a401b55d66ddab8e6b6681`，与上述
head/source/scope/票/receipt身份一致。作者receipt的“审查/提交尚待完成”是作者检查
当时的历史状态，由后来的完整独立CORRECT票和冻结head补齐；没有改写旧回执。

本轮独立文本提取比较七个实际完整theorem头与scope，仅空白归一化后7/7相同；
164行，零新定义，公开theorem恰7；禁用token与CR字节扫描均无命中。

## 2. 真实finite law、零质量和相对熵方向

实际读取U5b完整源码、两份完整独立审查，以及承重的AtomicMeasure、InverseTilt、
PositiveRate、FiniteStageMeasure/finiteBase定义；复用既有前序证明，不重证它们。
真实只读R1 `C:/game/shao/current/oq3/proofs/r1/report.md` 的本轮SHA为
`3473d34ff20bd0d334b9ef3ea3c3ee167fba4d5cc3a742849820ce54d639e662`。
137–159行定义逆倾斜P并给 `Λ0=ℓq+logZ=D(π||P)>0`；251–258行明确同一证明
适用于每个有限阶段。没有把这些行中的全局鞍点/协方差其它结论顺带接收。

实际对象为：

```text
π = atomicMeasure w = Σ_i ofReal(w_i) δ_(fixedAtom i)
Y(x) = 8x − x²
Z = inverseNormalizer ℓ w = ∫ exp(−ℓY) dπ > 0
P = originalMeasure ℓ w = π.tilted(−ℓY)
P.real{fixedAtom i} = w_i exp(−ℓY_i)/Z
originalAtomEntropy ℓ w = Σ_i w_i log(w_i/P.real{fixedAtom i})
```

fixedAtom是已证单射；两测度都集中于其可数值域，真概率门由非负权及HasSum w1、
实际可积指数与Z>0供应。因此这里确是 **D(π∥P)**，有限阶段为
**D(π_J∥P_J)**，没有将P作分子、π作分母。它是当前标准离散原子熵定义的认证，
不是新增一般Radon–Nikodym KL框架的定理。

finiteMass实际定义为 `Sum.elim (finiteBase ℓ p r J) (fun j => if j<J then r j else 0)`，
是同一AtomicIndex上的真实零延拓。源族中r严格正，故四旧点及j<J活跃新增点有
正质量，j≥J的未来点质量为0；一般有限率定理只需整条r非负，允许活跃前缀也为0，
严格性仍由两个旧点支付。没有伪造“finiteMass的全部无限索引都严格正”。

U5b先按w_i=0分支，整体加权项只由0乘法变成0=0；没有对log(0/0)使用正权log_div
等式。w_i≠0时由非负门推出正权，才调用旧 `original_log_atom_ratio` 的指定正项
接口，此时真实P同点质量严格正。零权时P同点也为0，正分子/零分母没有被遗漏。

## 3. 真HasSum、严格率和J=0

独立最终proof票先盲译实际导出头、比对scope/R1，再完整审查164行证明及局部
hpoint等全部辅助，形成CORRECT后才读取机械票；本轮完整复用此证明裁决，并核对
实现的实际调用点与服务器打印TYPE。

- hm第0、1、3坐标给真实HasSum w1、加权boundary和0、加权平方和q；
  用 `Y=x²−2boundaryFeature` 得加权Y的真实HasSum q。再乘ℓ、加质量乘logZ，
  并逐项用新加权恒等式，得到整个熵族 **HasSum到saddleRate**，之后才取tsum_eq。
  没有靠不可和时总化tsum默认值凑等式。
- 严格性声明明确要求ℓ≠0、两个给定正质量原子及其 **Y值不同**。严格Jensen的
  AE常量分支用正singleton质量提升到这两个点的精确相等；ℓ非零才能消去，得到
  与异Y矛盾。其余权重可为0；“X点不同”没有被错当成“Y值不同”。
- 得到 `exp(−ℓq)<Z` 后，两边真正在正域，log严格递增给 `ℓq+logZ>0`；再用新
  非负熵等式取得熵正性。ℓ=0时一般等式仍成立、率为0，严格签名正确排除它。
- 每个有限J固定使用 `Sum.inl 0/1` 两旧点，真实点−1与1，Y值−9和7。J=0时
  compensation为空、finiteBase=p，所有新增点为0，这两个旧正点仍提供严格率。
  126–133行处理finiteMass时调用本单元非负/两正原子接口，**没有套U5a全w>0定理**。
- 最后存在族只在极限分支使用U5a全正率/熵定理，因为同一次hfamily已经给极限
  limitingMass的全索引正性。此调用与有限分支有明确分工，符合旧接口原门。

最后族的量词为先存在同一p/q/eps（p>0、q∈(1,103/100)、eps>0及同一sourceEll
矩阵方程），之后才引入任意正可和且总量<eps的整条r，再量化所有J。极限P和
全部P_J沿用同一p/q/eps/r，p/q/eps不随r或J重选，sourceEll不变。π/π_J的均值
q/4与P/P_J的中心均值0没有交换。源族最后给entropy=rate>0，虽不再单列entropy>0，
其严格熵含义已由等式蕴含。

## 4. 既有作者执行及独立票绑定

本轮只读服务器固定commit和现有日志；UTC记录 `2026-10-21T16:40:56Z`。
七承重源在frozenhead与当前远端工作树逐字节相同，并均匹配receipt/完整独立票：

| 源 | SHA256 |
|---|---|
| FiniteConstraints U1 | `800d9db8cb6749a31ecfe611409de92b10ea8bb2aef955bfd825ede7324f0ef0` |
| SourceStarter U2 | `0e2a081619976f88149707c2ef9311dc909003e61d3d0f7c4e21e6c3dbbc5a6d` |
| SummableAtoms U3a | `0ea4c64fe9ef9b45fbf44d24312771a1dbfbcc5de8448564e3e87bdf17c7178b` |
| AtomicMeasure U3b | `59ddc48fb7b395f362939e58cbd9d7911685a6ed6e6574142e8a6d4ab3ee0c39` |
| InverseTilt U4，已接受LF版本 | `c7e7d19e8b70481b663bec1fd12ea9301d73313faaf35997e85aa9ba99f21811` |
| PositiveRate U5a | `8e727078d3a4f1db2392384b84cc31235ff69efa13dd5e44b23eac818a788f7b` |
| FiniteStageMeasure U3c | `1a32fb904e6ee9d2b0b48d92c4ebb3568452bb02500ce52a1a03eb01ae0256b1` |

作者检查时尚在parent cc4af50，目标字节与后来提交e654完全相同。receipt记录
目标命令 `lake env lean -o .lake/build/lib/lean/Shao/OQ3/FiniteStageRate.olean Shao/OQ3/FiniteStageRate.lean`
exit0；本轮实际读到 `runs/oq3/u5b-20261021/build-01.log` 为0字节、SHA
`e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`。

实际同目录Audit.lean为1716字节，SHA与上表34c46cbe...一致；Audit.log为5397字节，
SHA `94f403731435b86d4171af54553337e914f767efad09a7bb4e588a4998ee4cf8`。
本轮完整读取七个TYPE，保留非负、真HasSum、hi/hj、异Y、ℓ≠0、finite旧正性及
共同参数量词，末尾7 frozen /7 theorem /7 declaration、AXIOM_GATE PASS。
七项collectAxioms均恰为标准 `propext/Classical.choice/Quot.sound`，与作者exit0及
独立票的实际远端只读核查一致。Lean pin为4.36.0-rc1，mathlib为
`807d3836b165983210ee2ecf3cd28f239436949c`。

**审计口径明确区分。** 原U5bAudit实际使用七目标名前缀和模块_private前缀；
它逐项审了选中目标的全部传递公理，实际7项。它没有按moduleidx遍历整个环境，
故不能把该原票改称“一般无遗漏的全部module-owned枚举”。后者由下面root门补齐。

## 5. root已执行的v27门与待发布状态

收到root提供的既有结果路径后，本轮只读验证了
`/root/rivermind-data/shao-lean-20261021/logs/integration-v27/result.json`，SHA
`bc4bdf688805c669a96e6707862897794b07f6e0067cce051398b0333612d5d3`。
真实worktree为integration-oq3-v27，结果PASS，source_files_sha256中本目标仍为
完整e654bed5...；实际mathlib pin正确，source_scan PASS。所有版本、manifest、
整库build、theorem审计、all-declarations、module-coverage、diff-check均记录exit0。

本轮还实际核对四个原始log的SHA与result字段一致：

| 已完成root log | SHA256 | 实际末尾证据 |
|---|---|---|
| build.log | `0a4f7c34c80b332a2eb9f8fcbe10ac390bfeccf06aab83bc53feb83e85e24292` | FiniteStageRate及Shao成功，Build completed successfully |
| theorem-audit.log | `0561d24b3b8ac1af37761f6d4e6be98a93cae4058018e05c776c8861c2d3553c` | 843 public，1385 theorem |
| all-declarations.log | `500f3768d0d161d8cf314022d794869bd6cfb4bfe45fa0938b26fadffc7d942a` | 2003 project-owned constants |
| module-coverage.log | `f64cfafffbe8460f963f5db17e3b95c57af4f8fd58117bcb5e5cba4f136cc055` | 106实际project modules |

已读真实OwnedAudit源码：`env.getModuleIdxFor?`对应所属Shao模块筛选，逐项
collectAxioms并拒绝白名单外公理，覆盖public/private/generated及跨namespace常量。
因此prefix旧票与root新module归属门各自真实范围没有混淆。root记录v27较v26精确
增加7/7/7；本目标没有靠漏记额外常量获得单位计数。

这批root运行发生在本轮前，绝不是本审查重新执行的Lean。result UTC为
`2026-10-21T16:40:13.436654+00:00`；正式 `verification/receipt-v27.json` 尚待
本报告归档后由finalizer生成，此时不存在是已明确的发布步骤，不是缺失成功运行。
本机v27-publication checkpoint固定接受baseline
`22a5e1f97311ad40aa49efbcfab4f5fc67a65de3`，已含父PR39。

本轮最初GitHub snapshot仍以父feature为base并返回mergeable=false；它不是proof
或已完成整库gate失败。root随后明确其集成worktree无冲突、将retarget main并按
expected head执行。发布/合并前仍应刷新实际PR head/base，以固定4e5522a6及e654
源、同一父依赖和现有root成功门为准；保存finalizer提交/receipt/hash绑定。若源
字节不变无需重复旧成功目标，若有数学源或依赖变动须重新决定受影响gate。

## 6. 接收边界

接收的是：允许非负零延拓权重的真实可和离散熵恒等式、两个正异Y原子的严格率，
以及同一starter参数族中每个有限J（包括0）与极限的真原律概率和正率。

不接收一般RN-KL框架、全局正尾鞍点唯一性、协方差非退化/相关常数、定量弱Cramér、
有限或无限阶段LLT、尾渐近、尖点、产品TV或先witness后选尾对角。不能将KL>0
当作这些定理的替代。根A/B/C/D及其它完整根仍OPEN。最终publication/merge归root。
