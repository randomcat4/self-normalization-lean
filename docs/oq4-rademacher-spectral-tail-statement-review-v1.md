# OQ4 SpectralTail U1：来源到冻结陈述语义审查 v1

STATUS: CORRECT
SCOPE: SOURCE_ONLY
REVIEW_DATE: 2026-10-22
TARGET: frozen-rademacher-spectral-tail-v1.md，U1（第82–104行）

本判决只确认指定原来源到冻结 U1 的陈述忠实性。U1 是原第46–55行统一余项承诺在固定 Pair P2 上的精确展开，未发现参数、量词、余谱对象、时间域或衰减速率的偷换、扩大或缩弱。此处 CORRECT 不表示 U1 已获数学证明、Lean 认证或实施授权，也不重新认证上游身份。

## 1. 输入固定与读取边界

全部本地 shell 调用的 workdir 为 `C:/game/shao lean`。唯一写入工件为本报告；未修改 frozen、原 source、candidate、证明、Git 或缓存，未运行 Lean、数值探针或重计算。

三个数学输入均按字节计算 SHA256，结果与派发完全一致：

| 输入 | 路径 | bytes | SHA256 |
|---|---|---:|---|
| 唯一原数学来源 | `C:/game/shao/current/oq4/c01/spectrum01.md` | 4306 | `b65f9e0c2f9b40a28d092491b479bd20d0b8ee8a9ac940c3c4760cfff7d2670b` |
| 本次冻结目标 | `C:/game/shao lean/drafts/oq4/frozen-rademacher-spectral-tail-v1.md` | 8952 | `b220e1ca9f89e5f9a3328131b430fb54b9656e5113b93241adbde1aad627354a` |
| 直接固定上游 | `C:/game/shao lean/drafts/oq4/frozen-rademacher-spectral-pairing-v1.md` | 8661 | `69c5cf5822044e19520e10c4a6de4a31e0e8f43d296e477982a9c5637c85c6fb` |

来源 commit 为派发固定的 `35d4580b61e22e7145f47730045a09874ef93259`；本轮以文件字节哈希核对输入，未读取 Git 历史。三个数学文件均全文读取；实质核对集中于原第11–55行、Tail 第23–129行、Pair 第25–108行。原第58–119行仅用于确认后续问题的范围边界，未审查其正确性。

已读取的非数学规范输入如下，均只作角色、执行和编码约束，不作 U1 的数学依据：

| 路径 | bytes | SHA256 |
|---|---:|---|
| `C:/game/shao lean/AGENTS.md` | 3577 | `7bdcd9cd2af52ad99fa265b31222b9bb8926f4805b3a62bc74329b0998e6b983` |
| `C:/game/shao lean/SERVER.md` | 4350 | `398cc46b0acfa89d0fa358712ddca2050d99f3d6cec46b68fb7ab7cb1adba18a` |
| `C:/game/shao lean/coordination/TEAM.md` | 2958 | `ea3c8421aee3636707c4f7ab562bb6a5c79586ca245356b213de2f5420c5d34a` |
| `C:/Users/UIO/.agents/skills/math-theorem/SKILL.md` | 15101 | `062c52873e6fb70ffcf8bca993c94ee6313ace7684dd7b783cd0c45abda66a8d` |
| `C:/Users/UIO/.agents/skills/math-theorem/references/prompt-library.md` | 9866 | `6cf283b9b36027428240329f6e070222c0f53f7e489f52abb22cd01f9c731171` |
| `C:/Users/UIO/.agents/skills/math-theorem/references/openai-workflow.md` | 5570 | `cc0fa5b42793a1b0e4389fe7004ed33cea39e57f3b4ed21f599f368f81bead84` |
| `C:/Users/UIO/.agents/skills/math-theorem/references/lean-verification.md` | 4476 | `58ef00c297dd6be325b115e0a7f74404d1b91f9c72623576e3e1b2bccde676f3` |
| `C:/Users/UIO/.codex/skills/windows-gbk-utf8/SKILL.md` | 4844 | `d54eaa923c4dbf7acfe3a8e14f6a622aa346f66c2363c65104c053fbf9058705` |

未打开任何 intake/candidate 历史、anonymousproof（含 Pair/S1）、其他来源语义审查、math/formalreview、作者过程文件、新 Lean/private Source 或实现代码。Pair 已明列本轮所需对象、P2 与全部时间端点，故未继续读取 S1、AllModes、FiniteBasis、Iteration 的传递冻结接口，也未读取透明 defs 或公开 types。允许输入本身含有候选标识与派发状态文字；未沿这些标识追读外部档案。无意外暴露受限推理。

## 2. 原承诺与 U1 的量词映射

原第38–43行单独给出的是 `H→∞` 且 `n/H²→∞` 的双尺度 S2。不能只由这一渐近表述声称所有有限参数范围的 U1。本次判决同时依据原第46行“余项常数可统一取值”和第55行 `n/H²≥1` 的明确补充承诺，并沿用原第11–12行的 `h≥1`、`m=floor(h)`、`H=m+1`。原第46–55行没有另设大 H、奇偶或正生存前提。

| 语义项目 | 原文位置 | 冻结对应与判定 |
|---|---|---|
| 固定概率对象 | 第5–7、11–13、24–34行 | Tail 第25–37行、Pair 第27–37行保留从0出发的 Rademacher 产品律和实际路径概率；p 没有改成谱和的定义。闭条带含 k=0，在本域 h≥1 与原弱事件一致；n=0 的空路径约定保留。 |
| 全部格点胞元 | 第11–12行 | Tail 第39–43、96–98行量化全部自然数 m≥1 与全部实数 m≤h<m+1，正是原 h≥1 的 floor 参数化。弱端点 h=m 保留，上端不含；没有加入严格事件。 |
| 同一吸收尺度 | 第12、16–17、36行 | Tail 第41、43、98–99行固定 `H_N=m+1`、`H=(m:ℝ)+1`。H 不是 h，也不是独立的实吸收位置；指数和时间阈值均用此 H。 |
| 统一常数 | 第43、46、55行 | Tail 第84–104行是 `∃C:ℝ, 0<C ∧ ∀m ∀h ∀n ...`，C 在所有参数之前选择，独立于 m、h、n、epsilon 和奇偶性。把可取的 O 常数要求为正不改变其上界意义。 |
| 精确时间域 | 第55行 | Tail 第86、98行是 `H²≤(n:ℝ)`，与原 `n/H²≥1` 在固定正 H 上对应。n 仍为自然数；未加更强阈值、依参数的充分大时间或指定序列。 |
| 同一指数速率 | 第43、51–55行 | Tail 第90、99行保留 `C*exp(-π²*(n:ℝ)/H²)`。没有更换指数常数、尺度或用较慢速率代替。 |

因此，U1 不仅是逐 m 的估计，也不是某一条双尺度序列上的 O 结论。h 虽不出现在 R 的显示式中，全部胞元仍由量词和 Pair 的实际概率身份绑定，没有以省略 h 改变原弱事件范围。

## 3. R 的逐项一致性及主模态分离

Tail 第47–65行与 Pair 第39–60行的 alpha、beta、cot、tan、K、epsilon、a、rho、Z 定义相同。Tail 第68–73行与 Pair 第85–90行逐项一致：

- 求和索引是同一个 `K_m.erase 0`，符号是 `(-1)^ℓ`。
- 配对系数是同一个 `(cot(alpha_m,ℓ)+epsilon_m(n)*tan(alpha_m,ℓ))/cot(π/(4H))`。
- 时间项是同一个 `(cos(beta_m,ℓ)/rho_m)^n`，所有幂指数均为自然数。
- 中心项仍为 `Z_m(n)/(a_m*rho_m^n)`，没有更换全时间定义。

Tail 第78行的实际概率输出正是 Pair 第94行 P2；本轮只核对身份承诺的文本绑定，不证明 P1/P2。R 没有被改成任意误差函数，也没有用“存在某个 R”代替其固定表达式。

原第36–43行把首正模态和最负模态一起显示在主项中。Tail 第57、78、122行保留精确的 `epsilon_m(n)=(-1)^(n+m)` 及 `epsilon_m(n)*tan²(π/(4H))`。Pair 第75–79行明确其最负模态来源。因此负主模态没有被吞进 R，也没有丢掉时间或 m 的奇偶信息。剩余频率的配对和中心项处理与原第46–55行的“正负配对、其余奇数频率、零谱无贡献”相接，没有把未经配对的负谱视作正谱。

## 4. 有限边界、正时间与前提审计

1. **m=1、m=2 保留。** Tail 第96、120行没有删除这两种情形。其空余谱和及 m=2 的中心项时间区别，精确沿用 Pair 第96–98行；未用 `H≥H0` 排除它们。
2. **零谱只在正时间消失。** 由本域 m≥1，H≥2；U1 的 H²≤n 位于正时间。Tail 第63–65、80、121行仍保留 R 的全时间中心项和 `0^0=1`，没有把原第55行“零特征值没有贡献”扩成 n=0 的结论。U1 不对 n=0 要求该指数界；Pair 的空路径身份也未改动。
3. **归一化不是自由假设。** Tail 第65、108行把 a>0、0<rho<1、a*rho^n>0 保留为固定 Pair 的合法性承诺，不增加分母非零或正生存前提，也不以 p 作分母。
4. **没有缩小原范围的条件。** Tail 第102–104、118–123行没有增加固定奇偶子列、全谱为正、非零谱、无周期、混合、非格点、固定参数序列或正生存假设。来源只处理固定 Rademacher 分布，冻结未扩大为任意分布、任意实 coset 或独立实 H。
5. **原估计过程没有被当作输入公理。** 原第47行的“系数”略写未区分单模态、配对系数与归一化系数；Tail 第110–127行将同一显示 R 的系数控制、谱比界及求和界全部留为内部待证义务。U1 本身没有以这些尚待证明的估计为自由前提。这里确认的是来源承诺与目标的对应，不认证上述估计。

原文未逐项列出小 m、奇偶和 n=0 中心项，冻结通过固定 Pair 的定义显式暴露这些边界。这是统一承诺在既定对象上的必要范围展开，不是暗添数学假设；也不能据此把展开出的估计当成已经完成的证明。

## 5. 结论范围与未关闭事项

本次关闭的仅是 **U1 的 SOURCE_ONLY 来源语义门**。在指定输入版本内未发现必须退回修订的来源语义缺口；不提供证明或修稿。

状态只采用本轮派发：Iteration/FiniteBasis fully formal（PR82/PR86）；AllModes 作者 ready、父 imports 242/863 通过、fresh 最终独审中，尚非 fully formal；S1 与 Pair 各自匿名数学审查 CORRECT，尚未 Lean。未读取或重新认证这些产物。冻结文件末节保留了较早的状态记录，其进度文字不用于判断 U1 的数学内容。固定接口仍只是精确数学承诺，不能冒称全链已形式认证，也不能充作自由公理。

以下范围继续未关闭：U1 的数学证明及独立证明审查；上游实际声明接合和形式认证；U1 的 Lean 陈述、证明、构建与传递公理审计；将 Pair 与 U1 组合为原第38–43行完整双尺度 S2 的推论；S3–S5、Brownian 比较、strict 事件、其他 cosets、Spectrum 与一般 OQ4 root。Tail 第125–131行对此排除清楚。一次 U1 来源门通过不改变这些范围的 OPEN 状态，也不自动解除任何后续授权门。
