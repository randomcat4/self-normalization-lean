# FiniteIIDMoments 共享迁移独立源码差异审查

STATUS: CORRECT（冻结公共源、旧入口兼容和迁移范围）

本报告对新公共源码相对已接受旧源码的实际差异、最终旧兼容入口及所交付迁移证据作独立裁决：CORRECT。未运行本机或服务器 Lean，未重复作者已成功目标，未修改实现、scope 或他人文件；本报告不是内核检查回执。编译、rfl、消费者重建及传递公理门的执行事实由协调者提供并由冻结作者回执记录，与本报告自己的源码数学判断分别列明。

## 冻结绑定与审查范围

- 冻结迁移 scope：C:/game/shao lean/drafts/c12/FiniteIIDMoments-shared-scope.md。
  SHA256：3033eb9df9d7586a8b94912ff6ceef6a597275174309af7262b53ac1c080a8db。
- 新公共源：/root/rivermind-data/shao-lean-20261021/workspaces/shared-iid-moments/Shao/Probability/FiniteIIDMoments.lean，540 行。
  SHA256：d2417f73424ea90a13edb10bdad267d638d66fec432c3107362a2d0246fe2bfa。
- 已接受旧原源：/root/rivermind-data/shao-lean-20261021/workspaces/lead-oq56/Shao/OQ5/P35/FiniteIIDMoments.lean，539 行。
  SHA256：4b2c65ec7fb03767b6a469ef5918592c9a76e993ad95262e6a7aae6840c4520b。
- 既有独立声明审查：drafts/c12/FiniteIIDMoments-shared-declaration-review.md。
- 最终旧兼容入口的本地只读镜像：C:/game/shao lean/drafts/c12/FiniteIIDMoments-OQ5-compat.lean，104 行，对应同一共享 worktree 的 Shao/OQ5/P35/FiniteIIDMoments.lean。
  SHA256：8efe17261c763f6f56263c6db26f759a342500c26f8305a50e356ef686fa0027。
- 作者迁移执行回执：C:/game/shao lean/drafts/c12/FiniteIIDMoments-shared-review-receipt.md。
  SHA256：b02a0aacee1c9a271dd3faed5cd21889fea95c36c4756301613d1b8186e1e4f6。

本轮通过服务器只读请求实际核对两份源码哈希、完整原始 diff、公开声明位置与 imports。旧实现的概率数学作为已接受依赖复用；先前声明审查已读完整旧模块及两处 RowIdentity 依赖，并独立核对固定 Mathlib 版本中 Nat.cast_choose_two 的真实类型。本轮没有把作者成功编译或回执当作数学依据，也没有重验旧概率证明。

## 一、实际公开定义、量词和公式

新模块 namespace 为 Shao.Probability。第 25、28、31 行的三个定义对任意 m∈ℕ、任意类型 Ω、任意 Z:Fin m→Ω→ℝ 及 ω∈Ω 定义

    S(ω) = ∑ i : Fin m, Z i ω
    L(ω) = ∑ i : Fin m, (Z i ω)^2 * (S(ω) - Z i ω)^2
    P(ω) = ∑ i : Fin m, ∑ l : Fin m,
             if i < l then Z i ω * Z l ω else 0.

它们分别为 finiteFeatureSum、finiteLeaveOwnSquareSum、finitePairProductSum。全部坐标均在 Fin m 中，pair 使用严格 i<l，每个 unordered pair 恰计一次；L 中确实先减去自己的坐标。定义自身没有可测性、概率、非空或矩前提。

六个公开 theorem 共同量化任意 m∈ℕ、带可测结构的 Ω、概率 μ:Measure Ω、概率 ν:Measure ℝ 和实际坐标族 Z。前提是每个 Z i 可测、iIndepFun Z μ、每个 Z i 在 μ 下与 id 在 ν 下 IdentDistrib，以及 MemLp id 2 ν。定义 a=∫z dν、b=∫z² dν、v=variance id ν，则实际结论如下。

1. 第 352 行 finite_iid_leaveOwnSquare_integrable：L 在 μ 下可积。
2. 第 361 行 finite_iid_leaveOwnSquare_integral：

       Eμ L = (m:ℝ) * b *
         ((((m-1:ℕ):ℝ) * b) +
          (((m-1:ℕ):ℝ) * ((m-2:ℕ):ℝ) * a^2)).

3. 第 399 行 finite_iid_pairProduct_memLp_two：P∈L2(μ)。
4. 第 408 行 finite_iid_sumSquare_integral：

       Eμ S^2 = (m:ℝ) * b + (m:ℝ) * ((m-1:ℕ):ℝ) * a^2.

5. 第 516 行 finite_iid_pairProduct_integral：

       Eμ P = (m.choose 2:ℝ) * a^2.

6. 第 525 行 finite_iid_pairProduct_variance：

       Varμ P = (m.choose 2:ℝ) * v^2 +
         (m:ℝ) * (((m-1:ℕ):ℝ)^2) * a^2 * v.

这里 m−1、m−2 仍先在 Nat 中相减，再转实数；v 是实际方差，b 是原点二矩，二者没有互换。没有增加 m>0、均值零、方差正、全局三矩或四矩前提。section variables、include/omit 及显式参数排列相对旧源没有变化；除 namespace 所造成的常量全限定名替换外，全部六个 theorem 的声明文本相同。

## 二、完整逐字差异与依赖方向

实际原始 diff 只有以下四类，没有其他差异。

1. Imports：旧两条项目 import 被直接 Mathlib 来源替换，并显式加入 choose-cast 和 Ring。

       import Mathlib.Probability.IdentDistrib
       import Mathlib.Probability.Independence.Integration
       import Mathlib.Probability.Moments.Variance
       import Mathlib.MeasureTheory.Function.L2Space
       import Mathlib.Data.Nat.Choose.Cast
       import Mathlib.Tactic.Linarith
       import Mathlib.Tactic.Ring

   新文件确为七条 Mathlib import，零条 Shao 项目 import。被移除的是 Shao.OQ5.P35.RowIdentity 与 Shao.Probability.FiniteIID；并无隐藏的新项目 import。公共 Probability 源在项目层不反向依赖 OQ5。这是实际源码依赖结构观察，不宣称已经运行完整 Lean dependency command，也不声称七条 Mathlib import 每条都不可省略。

2. Namespace 的首尾：Shao.OQ5.P35 改为 Shao.Probability。
3. 旧第 31 行、新第 32 行：finitePairProductSum 从 unorderedPairSum 调用展开成上述严格 i<l 的相同双和。
4. 旧第 471 行、新第 472 行：hcnt 的 proof 从 pairCount_eq_choose m 改为 (Nat.cast_choose_two ℝ m).symm。

新增 import 净增一行，故 539 行变为 540 行。除此之外，三个定义的其余 body、两个私有定义、十七个私有 theorem、六个公开 theorem 的全部证明文本，以及 noncomputable、autoImplicit、open/scoped、变量、include/omit 均保持原样。

“唯一证明变化”在这里精确指源代码 proof 文本只有 hcnt 一处变化。namespace 以及私有常量全限定名必然改变，不能据此宣称 elaborated proof objects、生成名或 .olean 二进制字节不变。

## 三、两处实质替换的数学核对

### Pair 定义展开

已独立读取旧 RowIdentity 的 unorderedPairSum body：

    ∑ i : Fin n, ∑ j : Fin n, if i < j then H i j else 0.

把 H 代入 Z i ω * Z j ω，正好是新公共源第 32 行。这里仅做普通定义展开；没有变换求和顺序、使用交换性、除以二、改变计数或增加概率前提。绑定变量 l/j 的改名不改变定义性等价。

因此既有证明中对 P 的 L2 与真实矩公式仍指向同一个实际随机变量，不是换成双倍 ordered-pair sum。此处不要求迁移 RowIdentity 中任何 kernel、row 或 U-statistic 对象。

### Choose-two 的 hcnt

新源第 471–472 行 hcnt 的实际目标是

    (m:ℝ) * ((m:ℝ)-1) / 2 = (m.choose 2:ℝ).

固定 Mathlib/Data/Nat/Choose/Cast.lean 的 Nat.cast_choose_two 对显式类型参数 K，在 DivisionRing K、NeZero (2:K) 下给

    (m.choose 2:K) = (m:K) * ((m:K)-1) / 2.

因此 (Nat.cast_choose_two ℝ m).symm 与 hcnt 精确同型；实数实例提供其类型类前提，不增加 m≥2。m=0、1 同样成立。这里的实数 m−1 与公开公式中的 Nat 减法是两个不同表达式；本迁移只替换这一个已为实数多项式的 hcnt，没有在公共声明中错误地消掉 Nat 饱和减法。

## 四、概率证明和边界的保全

第 34–292 行的两个私有定义与 subset-sum helper、第 304–341 行 iid coordinate/leave-own helper、第 427–512 行 pair-statistics helper，以及六个公开证明，均与已接受旧源逐字对应；唯一例外是已核对的 hcnt。未引入新的概率推导、额外 moment hypothesis 或以结论作前提的循环。

迁移保留既有只用 L2 的真实内容：pair product 的平方可积依赖不同坐标的独立性；leave-own 先排除 own coordinate 后再分解与余和的独立乘积，未偷用单坐标四矩。所有原实际随机变量、μ、ν、iIndepFun 和 IdentDistrib 对象不变。

- m=0：S、L、P 均为空和，六个 RHS 相应为零；没有除 m、方差或样本量。
- m=1：P 与 L 为零，S 的二矩是实际单坐标原点二矩；原 leave-own proof 中 m=1 分支先于 m−2 的 Nat cast，仍完整保留。
- sum-square 和 pair-variance 中原 m=0 分支先于 Nat.cast_sub，保持不变；不在所有 m 上直接把 ((m−1:ℕ):ℝ) 替换成 (m:ℝ)−1。
- 非零均值、常值分布、零方差、负坐标仍允许。新源没有中心化约束、正阈值条件或额外积分归一化。

本报告依据逐字保全和两处已核对的数学替换复用已接受概率证明；这是独立源数学判断，不代表本轮执行了 Lean elaboration 或传递公理检查。

## 五、最终旧入口的实际差异和兼容审查

本轮完整读取最终 104 行旧入口，实际核对本地镜像哈希为上述 8efe1726…0027，公共镜像仍为上述 d2417f73…2bfa。旧入口只 import RowIdentity 和新共享模块，保留旧 namespace、autoImplicit、noncomputable、open/scoped、IID 变量与 include/omit。

旧入口第 20–27 行三个定义保留原 body。对前两个定义，本轮本地逐字比较与已核对的共享对应 body 相同；pair 的 body 则精确为原来的 unorderedPairSum (fun i l => Z i ω * Z l ω)。leave-own 中仍解析为旧 finiteFeatureSum，不存在额外的共享 alias 层。因此消费者原 restricted dsimp only 可继续直接展开旧 body；先前实际观察到的 ConditionalNumerator 第 243–245 行消费行为有明确的定义结构保全依据。

六个旧 theorem 位于第 39、48、60、69、80、89 行。每条 proof 只有一个全限定 Shao.Probability same-basename theorem 调用，依次输入 hZ、hIndep、hLaw、hν2，没有重新证明 iid 矩、改事件/随机变量或添加桥接假设。本轮将六个旧签名从 omit 行至实际类型末尾与共享源逐字比较，六条均相同；结合此前旧原源与共享源签名逐字相同，最终旧签名确实保持原件。旧九个全限定公共名字均实际存在；没有依赖消费者改名或只 open 新 namespace。

普通 delta 展开即可看到三条旧/新定义是相同实际函数。旧/新 theorem 的类型定义性相等，旧 proof 是共享 proof 的透明薄包装。这些是实际源码结论；下面另列协调者提供的服务器执行门。

## 六、执行证据及本审查实际范围

冻结作者回执记录、协调者确认的执行事实为：

- 共享源与最终兼容入口分别实际服务器 target exit 0，stdout/stderr 空；共享源先独立编译，未由旧 OQ5 合并环境补足名字。
- 独立 stdin 门实际编译三条任意长度/类型/函数族/观测的新旧定义 rfl、六条 fully applied theorem 常量 rfl 和既定 prefixSum/samplePath caller 桥，并检查全部 18 个新旧公开对象。该门不是仅对某一长度或某一函数的例子。
- 实际重建未改的三个直接消费者 ConditionalStatistics、ConditionalStudentizer、ConditionalNumerator，并先补足既有 ConditionalBackground、ConditionalMixture 依赖；所有 target exit 0、无诊断。四个缺失文件只作已接受字节的验证副本，不纳入迁移交付。
- 45 个公开/私有/生成声明的传递公理门通过，组计数为 shared 13、shared-private 23、compat 9、compat-private 0，白名单仅 propext、Classical.choice、Quot.sound。初始 audit driver 的局部变量关键字解析错误已修正后完整重跑，未改证明源。

回执给出的未改消费者及依赖哈希为：

| 已接受文件 | SHA256 |
|---|---|
| ConditionalStatistics.lean | 30961217d94582b790c8ad8c75b0a776fac253c973066bb3553d77c14821863a |
| ConditionalBackground.lean | bd8fbc670d0c29179994482f93aad25e48587ed423c34884f2f6f60adb7481dc |
| ConditionalMixture.lean | 3be0b68edb5435fb6c1136a0d6ab134e23f28dea4494d0d4d35bf93b2bd3a5be |
| ConditionalStudentizer.lean | 85766d90d01cb9e50e342183a6168a356b5ddd2cea84887c5d7439c7abb8eb62 |
| ConditionalNumerator.lean | a47d906cd619e57594a9eed98a3204c8218a4a8c82f8e1b9eb4ba6725ae08c13 |

本审查没有复跑上述门，也不把作者回执文字作为数学证明。实际独立完成的是冻结源哈希读取、公共源完整 diff、兼容源完整读取、六个签名字节比较和两处中性替换的源数学核对。本轮另尝试服务器只读确认当前消费者哈希，两次 broker 都明确返回 operation_may_have_started=false，故请求均未开始；未继续重试，也未据此声称自己额外核验了当前服务器消费者字节。已有迁移门的执行身份保持为协调者提供、冻结回执记录。

本轮还对两份实际本地实现完整扫描 sorry、admit、axiom、unsafe、native_decide，均无匹配。这一源码检查不能替代传递公理门，但与所交付冻结源一致。

## 最终裁决

CORRECT：新公共源 d2417f73424ea90a13edb10bdad267d638d66fec432c3107362a2d0246fe2bfa 相对已接受旧源，实际差异严格限制在获准的导入/namespace 和两处中性替换；最终旧入口 8efe17261c763f6f56263c6db26f759a342500c26f8305a50e356ef686fa0027 保留三个旧定义的展开行为及六个完整签名，以共享证明作薄包装。全部公开量词、仅 L2 假设、原点二矩/方差区别和零边界保全，未发现源数学或兼容缺口。结合协调者已提供的 rfl、消费者和全声明公理门，此冻结迁移范围可以接受。

交付仍限两份 owned 实现；四个 verification-only 消费者/依赖副本不应纳入该迁移。这一结论不替协调者执行 staging、commit 或联合 integration。本单元也不证明任何新的 Fourier 导数、阻尼、clock 概率、Gaussian/BE 比较或完整 C1/C2/OQ56 根结论。
