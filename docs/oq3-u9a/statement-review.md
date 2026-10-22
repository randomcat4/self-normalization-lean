# U9a 独立声明与来源审查

## 第一阶段：仅 Lean 代码块盲译冻结

本节在读取scope解释、真实R1或共用路径/乘积测度源码之前落盘。只读取 `fifteenth-unit-scope.md` 的Lean代码块，实测SHA256=`cd6883e78387d9fbeb50d42bddcab9fc0a81955458d7228c53f98eb23e4c35c9`。三定义、十二目标，尚无实现或本单元机械认证；未读作者API/frontier/notes。

三个定义：对共享Shao.Path n的路径z，normalDeviation(q,z)=Σ_iY(z_i)−nq，tangentDeviation(q,z)=Σ_i z_i−nq/4；sourceTail(q,n)由共享energy(z)>0及 `sqrt(q)/4·sqrt(n·energy(z))≤Σ_i z_i` 构成。尚须核查Path与energy的真实定义，不从名称假定其内容。

十二目标签名的独立翻译：

1. 任意q/n/z，normalDeviation=8Σz−energy−nq。
2. 任意q/n/z，`(Σz)²−n(q/16)energy=(nq/16)normalDeviation+tangentDeviation²`，没有概率或正性门。
3. 任意实q与自然数n，sourceTail是可测路径集合。
4. q>0、n>0时，入sourceTail等价于energy>0、Σz>0及第2项右侧≥0，明确保留总和正号。
5. 同样q/n门下，若normalDeviation=d，则尾事件等价于energy>0、Σz>0和 `−(nq/16)d≤tangentDeviation²`。
6. 任意q/n/J，对每个坐标均位于有限阶段stageAtom值域的路径，存在整数k，使normalDeviation=mesh(J)k−nq。无n>0假设。
7. 每个完整fixedAtom的Y值≥−9；不是绝对值≤9。
8. 任意w，atomicMeasure(w)下AE Y≥−9；无非负/归一化门，只断言AE支撑性质。
9. 任意ℓ/w，originalMeasure(ℓ,w)下AE Y≥−9；也不无条件声称概率。
10. ℓ≥0、q≤2及路径逐坐标Y≥−9下，对所有n，exp(−ℓnormalDeviation)≤exp(11ℓn)。
11. 若同一概率μ下AE Y≥−9，则对实际n重乘积Measure.pi(各坐标均为μ)，上述指数界AE成立；包括n=0。
12. q<103/100、非负w且HasSum w1时，对实际atomicMeasure(w)的n重乘积AE给sourceEll版本同一指数界。q/w均为n之外固定输入，不选择随n改变的源律。

本节尚未核查共享energy是否为真实平方和、尾事件平方化的严格正号门、n=0/energy=0、实际Y下界、乘积AE逐坐标提升及常数11。后续不以作者预期代替这些独立判断。

## 第二阶段：真实来源与共用源码

盲译落盘后才读取scope解释、真实R1 400–408与495–510，以及指定服务器上的真实共享源。R1实测SHA256=`3473d34ff20bd0d334b9ef3ea3c3ee167fba4d5cc3a742849820ce54d639e662`，与冻结值相同。未读作者API/frontier/notes，没有新Lean实现或构建。

实际服务器共享源逐行读取并核得：

- `Shao/Basic/FinitePath.lean` SHA256=`898262898f9c088e2d10e6238e411b4397387b21b1b71a2b545c5edef936e1bb`。18行Path(n)=Fin n→ℝ；31行energy(z)=Σ_i(z_i)²；50–61行energy≥0且energy=0当且仅当所有坐标0。
- `Shao/Probability/FiniteIID.lean` SHA256=`d1b565489199d55af70a27c31a0f803a2b7433e78c9197a361b3c10c0598845b`。32–43行在可测坐标、独立与同分布门下，真实样本路径的推前测度等于 `Measure.pi (fun _:Fin n=>ν)`；包含n=0，未用一个共同随机变量的对角律冒充n重积。
- U8 `FiniteNormalSpan.lean` 在本恢复会话紧接前项已实际核对，冻结SHA256=`0374da4860edf8af8bbbb9172e4e93bfe9b6c37ac57672b85a4f58392475b7de`，其实际stageAtom_normalValue_lattice提供完整活跃阶段的精确mesh整数式。所消费U1真实Y定义/法向值、U3b原子AE值域及U4倾斜绝对连续性也来自已独立完整CORRECT且刚核哈希的固定源。

另只读核对固定Mathlib的实际有限乘积API，manifest revision=`807d3836b165983210ee2ecf3cd28f239436949c`；`Mathlib/MeasureTheory/Constructions/Pi.lean` SHA256=`bb89dee63d412cd1cc1f7f9fd7a81d64074139571960b2f0fcb66d8b763cd6ef`。402–407行 `measurePreserving_eval` 在各坐标概率门下给实际乘积的第i坐标到μ的保测度映射；360–369行也有坐标零集在乘积中的原像仍为零集，428–429行有乘积AE到逐坐标AE的关系。这些不是假定所有样本逐点都在支撑。

| R1锚点 | 候选的实际覆盖 |
| --- | --- |
| 400–402 | 阶段样本的精确层为meshJ·整数−nq，与源把平移约化到分数部分θ的同一网格一致；目标不另定义θ或断言相位返回。 |
| 404–408 | d是实际ΣY_i−nq，R是实际ΣX_i−nq/4，V_n²是样本energy。目标2给源恒等式(18)，目标4/5显式保留上尾S_n>0。 |
| 499–503 | 指数权重作用于真实μ的n重积，候选给固定μ下实际AE指数界，未将其替换成随n调参的律。 |
| 504–508 | 精确乘积换测度/标准化C_n等式尚未在当前十二目标中证明，不能因本单元界成立就宣称完成。 |
| 509–510 | 实际Y≥−9和q<1.03≤2给exp(11ℓn)支配；产品TV后续比较不在当前目标中。 |

## 十二目标的独立数学与边界审查

### 真正样本代数、可测性与平方化符号门

记S=Σ_i z_i、E=Σ_i z_i²=energy(z)、N=(n:ℝ)、d=Σ_iY(z_i)−Nq、R=S−Nq/4。U1实际Y=8x−x²，有限和线性直接给d=8S−E−Nq；精确展开得

```text
(Nq/16)d+R²
= (Nq/16)(8S−E−Nq)+(S−Nq/4)²
= S²−(Nq/16)E。
```

这证明前两目标对所有q/n/z成立，E不是方差或均值平方，不需要概率、矩或正性。n=0时所有和及E均0，两边仍0。

有限乘积路径上的每个坐标、S和E均连续；Real.sqrt在实轴全定义且连续，所以固定q的阈值函数 `sqrt(q)/4·sqrt(N E)` 连续。sourceTail是连续实不等式集合与{E>0}的交，因此任意q/n都可测；q≤0时的sqrt总化不影响这一纯可测性声明。

在q>0、n>0、E>0下，T=`sqrt(q)/4·sqrt(NE)`严格正且T²=NqE/16。于是

```text
T≤S  ⇔  S>0 且 T²≤S²
      ⇔ S>0 且 (Nq/16)d+R²≥0。
```

正S门对排除平方后的负支至关重要，实际第4签名明确保留。再代入hd:d=给定层值，非负条件精确改成 `−(Nq/16)d≤R²`，第5目标对正/负/零d都成立，没有只覆盖某一符号层。

E=0时共享energy_eq_zero_iff给全部坐标0、S=0；sourceTail按定义排除该路径，平方化右边也保留E>0，因而不会接纳零能量。n=0的Path0唯一空路径同样E=0，所以sourceTail为空集合。第4/5只在n>0、q>0下声明等价，未对零阈值时错误要求S严格正；其余原始代数/可测性包括这些边界。

### 阶段网格与实际原子下界

对每个坐标由hz取真实活跃索引，再由U8整数网格取k_i:ℤ，Y(z_i)=meshJ·k_i。有限求和后令k=Σ_i k_i，整数cast与乘法线性给d=meshJ·k−Nq，正是第6目标。这里每个坐标可有自己的索引/整数，不要求全样本选同一原子；n=0取k=0，J=0由四旧点整数法向值成立。

U1真实四旧Y值为[−9,7,6,12]，新增值为6+mesh(j+1)>6，故每个完整fixedAtom的Y≥−9。不能改成|Y|≤9（旧点x=2，即baseAtom 3，其Y=12），也不能单凭1≤|X|≤4+√10推出这个下界，例如x=−2满足该绝对值界却Y=−20。当前声明正确要求实际fixedAtom/AE原子值域。

atomicMeasure(w)对任意w都AE集中于完整fixedAtom值域，所以实际Y下界可沿该AE性质逐点继承，不需非负/HasSum门；负权在ofReal下被截成0也只减少支撑。originalMeasure对同一atomicMeasure的倾斜绝对连续性再把该下界继承给P。U8导入链已有U4的真实倾斜绝对连续性，无须偷偷导入未在该链中的U5a原子值域定理。两个无条件AE目标即使在总化零测度分支仍真，但不无条件声称概率。

### 精确系数11与真实有限乘积 AE 提升

若逐坐标Y_i≥−9，则有限和给ΣY_i≥−9N。N≥0及q≤2进一步给

```text
d=ΣY_i−Nq ≥−N(9+q) ≥−11N。
```

ℓ≥0时乘−ℓ正确反向，得到−ℓd≤11ℓN，指数单调即第10目标。q不需下界，ℓ=0时两边1，n=0时d=0且两边1；系数11恰来自9+2，没有使用不存在的|Y|≤9或交换不等号。

对第11目标，每个i:Fin n在真实π=Measure.pi(各μ)下的坐标评价映射保测度到同一μ（实际固定库measurePreserving_eval，所有μ概率门已给出）。所以μ-AE的Y≥−9分别拉回为乘积下第i坐标AE界；有限多个坐标的AE事件取交，得到乘积-AE z的 `∀i,Y(z_i)≥−9`。然后才逐路径用第10目标。这是实际n重积上的AE结论，不是把单坐标μ-AE直接断言为每条路径逐点成立。n=0时坐标条件空、乘积为空指标的一点概率，点态界仍为1≤1。

最后一个source目标的hw≥0/HasSum w1给同一π_w真概率；第8目标给其AE实际Y下界，sourceEll_pos给ℓ≥0，q<103/100<2给所需q≤2，准确满足通用n重积目标。q>0并不是此指数界的必要门，所以该签名只给q上界没有缺口；几何等价另由第4/5显式要求q>0。最后对象是倾斜律π_w的乘积，符合源C_n的期望测度，没有把π与P交换。

q/w/μ都是n之外的输入，可一次选定源族里的同一q与同一实际律后应用于全部n；这里没有∃μ_n/q_n或在样本量确定后重选P的结论。既有source family仍负责统一p/q/eps，当前单元只消费固定输入并提供样本几何与权重支配，不宣称后选尾对角已经完成。

STATUS: CORRECT

JUSTIFICATION: 三定义与十二签名忠实表达真实有限路径energy、源样本恒等式和似然界；sqrt阈值严格正时的S>0门、n=0/energy=0、stage整数和、实际Y≥−9、π/P的AE支撑继承、真正n重积逐坐标AE提升、系数11和q/律固定在n外均数学正确。真实共享FinitePath/FiniteIID及固定Pi API已只读核对，可按原scope实现。此为独立声明/source gate，未实施或构建U9a；乘积换测度、产品TV、LLT/层支配求和、尾渐近、全局唯一率及对角未在此证明，根A/B/C/D保持OPEN。
