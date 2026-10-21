# OddPower 完整证明独立审查

STATUS: CORRECT

接受对象是固定源码 `OddPower.lean` 的三个公开定理及其全部私有证明，实际服务器模块名为 `Shao.Probability.QuadraticCharacteristicOddPower`。本上下文未参与 OddPower 的声明或证明编写；本轮仅编写此审查文件，未修改数学源码、冻结 scope、作者回执或共享文件，未运行本机 Lean，也未复跑已成功的服务器 target/audit。

## 一、身份、签名和执行证据的分离

本轮重新读取并核对：

- 实现：`C:/game/shao lean/drafts/c12/OddPower.lean`，603 行，SHA256 `d526459c86cab6fdd8d4fc207e4950e03993bac0a26e7c2c6a7567f747b1b838`。
- 冻结声明：`OddPower-next-scope.md`，SHA256 `005abcc7752ff48345617c7e946dc616494907ad57637017abff82b6ef989c3d`。
- 既有独立声明审查：`OddPower-declaration-review.md`，SHA256 `11aa17334de234f7a052f7617c9d345fb33655e7ac7639788b9a0d6fedf0c359`，声明阶段 CORRECT。
- 作者最终回执：`OddPower-author-receipt.md`，SHA256 `a4323f4ee042e35facff81a11ec3e039307963272de004533db4917181423f2a`。
- 作者 checkpoint、`OddPower-source-check.py`、`OddPower-source-check.json` 和 `OddPower-audit.lean`。

我另作了一次独立的文本提取比较，而非只信任作者的 assert 检查：三个实际 theorem 头与冻结 scope 中三个完整 Lean 签名仅在空白归一后逐字相同；共同 binders、量词、假设、局部矩定义、自然数减法及所有常数都未改变。显式公开定理恰为 3，手写 private lemma 恰为 12，新增定义为 0；对完整源码的 sorry/admit/axiom/unsafe/native_decide 扫描为零匹配。

作者的执行身份是实际 target/audit 的运行者；我的独立证据是下面逐段数学与 source 语义审查，以及对现有服务器工件的只读核对。服务器 worktree `takeover-odd-power` 的源哈希与本地相同，源提交为 `758409913957f711fcfa9934301a2bfeb405625e`。本审查不把自己未运行的 Lean 命令记为自己的机械验证。

## 二、三个实际声明的语义

三个定理均使用同一个真实概率 law ν，真实二次特征积分

    χν(u,v)=∫ exp(i(ua+va²)) dν，
    μ=∫a dν，m2=∫a² dν，m3=∫|a|³ dν，V=variance id ν。

实参数求导时 ν、v 和自然幂长度保持固定。raw 二矩和实际方差没有混同，μ 不被假定为零。

1. `quadraticChar_single_derivative_bounds`（71–119）：仅需概率与真实 h3；任意实 u,v 下，实际一阶导数减去 iμ 的 norm 至多 m2|u|+m3|v|，实际二阶导数 norm 至多 m2。允许零方差、常值或原子 law。
2. `quadraticChar_odd_power_residual_bounds`（266–368）：增加 V>0 和真实 γ=m3/V 的闭低频条件；对每个 ℓ∈ℕ，d(r)=χ(r,v)^ℓ−χ(−r,v)^ℓ 的零/一/二阶 jet 分别有冻结的 q^(ℓ−1)、q^(ℓ−2)、q^(ℓ−3) 付款，系数 N、N1、N2 都在自然数减法后才 cast。ℓ 不要求为奇数。
3. `quadraticChar_odd_power_lowFrequency_normalized`（429–601）：在 ℓ≤n、ℓ≥6、3/4≤nm2、n|μ|≤1、m2≤4V 下，T=ℓm2、A、B、R=sqrt(T)(1+sqrt(T)|u|)、E=exp(−Tu²/256) 均为同一真实 law 的实际表达式；结论三行常数为 2、4、18。没有输入所欲证明的 derivative bound、T<y²、条件均值零、第四矩或额外非零特征值。

三个签名完整对应冻结版本，没有通过删前提、缩小自然长度范围或更换 law 获得通过。

## 三、实际 source 推导及本单元的覆盖

本轮实际读取 main:546–551、622–625、673–678，以及 supplement:2343–2401、2445–2486、2860–2863、3420–3459；并重新核对原 source 哈希：

    main.tex       beb00f718487e36de433175c97f1d500cb48e7a92ce5bd5ad5d62bb132122d06
    supplement.tex b99f2ac4d2f39dd39772d98a5702b7a923c2f10f8730a08fc1b4cd6bba4742bd

source 2343–2357 的长度为 ℓ=n−i，T=ℓm2，odd Fourier factor 为 (1/2)[χ(u,v)^ℓ−χ(−u,v)^ℓ]Ξ(u,v)。当前三个定理只覆盖乘 Ξ 之前的真实幂差，没有将噪声导数或 Fourier 反演暗含进去。2477–2484 的零阶需求和 3441–3447 的三行表均由当前 A、B、R、T 的结构覆盖。

source 3431–3436 以减去 iμ 获得 individual derivative payment，并用 m3|v|≤κV|u|≤κm2|u|。实际实现遵循此 payment，且保留条件 mean 可能非零的 drift。source 3450–3452 的两种二阶计数为 ℓ(ℓ−1) 和 ℓ(ℓ−1)(ℓ−2)；实际实现采用等价的单个 power 精确求导公式与两个幂差的有限几何恒等式，而非真的将 geometric sum 连续展开两次。这一实现差异是合法代数重排，计数、剩余长度与交叉项二均逐项相同。

source 的 ℓ≥L2≥2J+4、J=8 给 ℓ≥20，足够当前 ℓ≥6。n*m2≤4/3 与 nV≥1/2 给 m2≤(8/3)V≤4V；原 source 的 n|μ|≤Λ_y<η0/2、η0≤1/16 给 n|μ|≤1。这里仅确认 source 适用性：实际固定条件 law 的完整 γ/m2 与长度运输仍是后续实例化义务，不把它们当成本模块已经证明的外部结论。

## 四、全部十二个 private lemma 与第一条证明

### 18–69：可积性与真实 single derivatives

- `odd_moments`：以真可积函数 1+|a|³ 支配 |a| 与 a²；分别处理 |a|≤1 与 |a|≥1，获得真实 L1/L2。概率假设只用于常数可积，没有把总积分默认零当作矩。
- `single_hasDerivAt`：取 Fin 1、X=id、样本测度 ν，使用真实 subsingleton independence 和 IdentDistrib.refl，专门化已接受 `iid_quadraticChar_power_hasDerivAt`。prefix sum/energy 的 singleton 化简正是 a 与 a²，得到 χ'(u)=i∫a exp(i(ua+va²))dν。
- `single_deriv_hasDerivAt`：同一 singleton 专门化已接受第二 derivative 的 HasDerivAt；获取的是整个 derivative function 的真实可微性，非对导数默认值的推测。
- `full_weight_integrable`：实相位 exponential 的 norm 恰为一，a exp 的 norm 恰为 |a|，由真实 L1 推出 complex integrability。没有原 law 四矩、MGF 或 bounded-support 前提。

71–119 的公开第一条在真可积的 weighted integrand 与 a 之间使用 integral_sub，才把 iμ 移入积分。全局实相位 bound 给

    |a| |exp(i(ua+va²))−1|
      ≤|a|(|u||a|+|v|a²)=|u|a²+|v||a|³。

右边两项真可积，积分得到所列误差。第二行复用 accepted finite-power derivative bound 的 ℓ=1，此时 V_raw+μ²=(m2−μ²)+μ²=m2，不需要 V>0。未发现可积性或导数存在缺口。

### 121–251：全自然长度 polynomial jet

- `bounded_power_difference`：从精确无除法几何恒等式开始。每个 range k 中的 i 满足 i+(k−1−i)=k−1，故 summand norm≤q^(k−1)，求和给 k*q^(k−1)，再乘 |x−y|。不要求 x、y 或 x−y 非零。
- `second_power_hasDerivAt`：先对所有 r 写出 (f^k)'=k f^(k−1)f' 的真实等式，再对右边求导，并用全局等式运输回 derivative function。Nat.sub_sub 保留饱和减法，得到

      (f^k)''=k f^(k−1)f''+k(k−1)f^(k−2)(f')²。

- `bounded_power_first`：精确拆成 k[(xp−yp)x^(k−1)+yp(x^(k−1)−y^(k−1))]，后项使用长度 k−1 的已证幂差。得到第一阶的 k 与 k(k−1) 两项。
- `bounded_power_second`：第二阶分解为 k[(xpp−ypp)x^(k−1)+ypp·powerdiff_(k−1)]，加 k(k−1)[(xp−yp)(xp+yp)x^(k−2)+yp²·powerdiff_(k−2)]。norm(xp+yp)≤2L 产生精确交叉系数二；后一个 powerdiff 给 k(k−1)(k−2)L²a0 q^(k−3)。仅需 ypp 的 m2 bound 加实际 second difference a2，足以付款 xpp，无遗漏。

所有乘数的非负性均从 norm bounds、q≥0 或 Nat casts 得到。无需对频率界或 damping q(r) 求导。

### 253–427：辅助 first bound、正性及归一化付款

- `single_first_bound`：将实际 iμ 加回，norm(iμ)=|μ|，得 L=|μ|+m2|u|+m3|v|，未删除漂移。
- `odd_third_pos`：若实际非负三矩为零，真 h3 和 integral-zero 判别给 |a|³=0 a.e.，故 id=0 a.e.、实际 variance=0，与 hV 冲突。因此 m3>0 是推论。
- `residual_exponential`：ℓ≥6、j≤3 给 ℓ≤2(ℓ−j)；m2≤4V 与 V≥0 给 ℓm2≤8(ℓ−j)V。乘 u² 后指数方向正确，故 exp(−Vu²/32)^(ℓ−j)≤exp(−ℓm2u²/256)。不存在残余自然长度负数。
- `normalized_drift_payment`：由 n|μ|≤1 得 n²μ²≤1；与 3/4≤nm2 的非负乘法结合给 nμ²≤(4/3)m2。再用 ℓ≤n 得 (ℓ|μ|)²≤(4/3)ℓm2，最后由 sqrt(T)≥0、sqrt(T)²=T 得 ℓ|μ|≤2sqrt(T)。整个证明没有先除 n 或 T，也未假设 n>0、T>0 后再补证。

上述十二个私有源码证明均已逐一审查，未见未付款的辅助结论或将目标改名为前提的情形。

## 五、公开 residual jet 的符号与小阶边界

266–368 令 f(r)=χ(r,v)、g(r)=χ(−r,v)。实现先取得全实数 r 上的真实二次可微性，并明确完成

    g'(r)=−f'(−r)，g''(r)=f''(−r)。

second chain 的两个负号确实相消；从未把 χ(−u,v) 当成 χ(u,v) 的完整共轭。实际 δ=f−g 的 derivative 与 second derivative 通过全局函数等式运输，才使用已接受 single odd derivative bounds。三项分别给 a0、a1、a2，a1 中的 2|μ| 被 triangle inequality 真正保留。负 u 的 individual first norm 与 second norm 由 abs(−u)=abs(u) 和真实 chain 运输。

闭低频 damping 只对同一点的 f(u)、g(u) norm 给 q，上述全局 differentiability 不依赖低频域是否在 u 的附近开。因此固定 v 的边界点也有效，不能误解为对不等式求导。

将精确一/二阶 power derivative 代入三个 deterministic helpers，得到冻结 jet，含

    N a2 q^(ℓ−1)
    +2 N N1 L a1 q^(ℓ−2)
    +N N1 m2 a0 q^(ℓ−2)
    +N N1 N2 L² a0 q^(ℓ−3)。

小阶核对：

- ℓ=0：d=1−1=0，导数均为零；N=0 支付全部项，几何和为空。
- ℓ=1：N1=N2=0，只剩原 single odd value/derivative/second derivative bound。
- ℓ=2：N1=1、N2=0，one-second 项仍在，two-first residual-difference 项消失；未把 H'' 整体错误删掉。
- ℓ=3：最后剩余因子确为 q^0=1。

上述边界不是只在说明中声称成立：HasDerivAt.pow、有限几何恒等式和 Nat.sub_sub 都在实际证明中以自然数 k 使用，无把 Nat 减法改成负实指数的步骤。characteristic 值可为零，q 也只被取自然幂，不用 χ'/χ 或 logarithmic differentiation。

## 六、归一化频带、常数和零频漂移

429–601 从同一真实 ν 的 variance identity 得 V=m2−μ²≤m2；由已经证明的 m3>0 与 hV>0，γ=m3/V 真正为正。于是可以合法消去频带中的 γ，得到

    m3|v|≤V|u|/128≤m2|u|/128，
    L≤|μ|+2m2|u|，N L≤2sqrt(T)+2T|u|=2R。

N1,N2≤N，并且所有因子非负，故 N1L,N2L≤2R、N1m2≤T。另有 N a0≤2A、N a1≤2B，三个 residual exponential 因子均≤E。

因此实际 proof 分项得到

    ‖d‖≤E·2A，
    ‖d'‖≤E·(2B+4RA)，
    ‖d''‖≤E·(2Nm3|u|+8RB+2TA+8R²A)。

以 (1+z)²≤2(1+z²)、z=sqrt(T)|u| 和 sqrt(T)²=T 得 R²≤2T(1+Tu²)。于是 2TA+8R²A≤18T(1+Tu²)A；其余两项的系数二和八亦由十八覆盖。第二行的 2B+4RA≤4(B+RA) 仅使用 B≥0。最终 2、4、18 与 exponent 1/256 均充分且方向正确，未暗用 nm2 上界或 T<y²。

u=0 时，γ>0 和频带强迫 v=0。d(0)=d''(0)=0，而一般 d'(0)=2iℓμ；B 中的 ℓ|μ| 因此必要且确实保留。非中心、有原子、负频率、闭域端点、f=g 或 characteristic 零点均不破坏上述证明。n=0 不满足归一化 hscale；未把这一不可能分支假装成新的输入。

## 七、现有实际服务器工件与完整公理审计

本轮只读核验服务器 `/root/rivermind-data/shao-lean-20261021/workspaces/takeover-odd-power` 及 `logs/takeover-odd-power/`，没有重跑 target 或 audit。

作者回执记载 pinned Lean 4.36.0-rc1（commit c9afcddf514a6772bd4d649f7cfc04eff0b9f15e）、Lake 5.0.0-src+c9afcdd、Mathlib 807d3836b165983210ee2ecf3cd28f239436949c；实际 `check-007` 和 `audit-002` 均 exit 0。服务器现有工件与回执逐项相符：

- 新源码 SHA256：`d526459c86cab6fdd8d4fc207e4950e03993bac0a26e7c2c6a7567f747b1b838`。
- 实际目标 olean SHA256：`28fed60b3306d4c4b9d673cfda1ebc04e2dfc7191a50d1e1d7dc9c26eb7d86f9`。
- `check-007.log` 实际为空，SHA256：`e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`。
- 实际服务器 `OwnedAudit.lean` 与本地 `OddPower-audit.lean` SHA256 相同：`6eab122b1dfb48df77ef0fe069585b652a1733f76d00945d46bcd2bc8b4dc6d4`。
- `audit-002.log` SHA256：`0c648e9ea895cc90b5c2868c7a118d3b3187108fac9fb92d116651e27296c59d`。

我读了实际 audit 源码和现有完整审计记录的结构/条目，而非只引用摘要。它依据 `env.getModuleIdxFor?` 的真实所属模块选择全部导入 Shao 常量，再对每个常量执行 transitive `Lean.collectAxioms`，遇白名单之外任意公理立即抛错。精确目标模块以 module-name equality 识别，不靠公开 namespace 前缀，故私有名字及其 generated proofs 也在范围内。

从现有日志独立解析得到 20 条 TARGET_DECL、221 条 DEPENDENCY_DECL；三条目标公开定理全部存在。20=3 public+12 手写 private+5 generated，其中两条 generated 的名字本身位于 `_private` 下，另三条位于 public theorem 的子名字下。不能把所有 `_private` 名字误数成手写引理；真实审计并未漏掉这两类生成项。实际输出为：

```text
AUDITED_TARGET_CONSTANTS 20
AUDITED_TARGET_THEOREMS 20
AUDITED_PUBLIC_THEOREMS 3
AUDITED_DEPENDENCY_CONSTANTS 221
WHITELIST_ONLY propext Classical.choice Quot.sound
```

现有日志无 error 行；221 个 transitive axiom 列表的并集恰为 Classical.choice、Quot.sound、propext。三个公开定理的独立 `#print axioms` 输出同样只含此白名单。本轮还只读核对了三个主要已接受依赖源哈希，均与冻结 scope 一致：

    QuadraticCharacteristic       8fd7815191dbd1ba9180159effe8c353d8b82d998d4d0d50bb6f957355b628f5
    QuadraticCharacteristicPower  5a51275c796d3bd0cc59b496a15b21e1c6bd5afd101b72f66a4c5e83511164c8
    LowFrequencyDamping           ffdeace2421a3c0fdf63def48eb96b882f9dc98014e5614d226a07f87a02bb65

作者修复过的 API/代数错误与一次 audit 搜索路径问题留在失败账中；本轮接受的是最终冻结源和最后成功的真实目标/audit 工件，没有将旧的部分 target 成功误作完整三条通过。

## 裁决与范围

CORRECT：固定源 d526459c… 完整证明三条冻结陈述。真实积分的一/二阶可微性与付款、全部十二个 private helper、负频率 chain、任意自然长度的 jet、小阶 0/1/2/3、正 γ、残余 damping、非零均值和最终 2/4/18 常数均无关键缺口；作者实际服务器机械检查与本轮只读核验的完整 module/dependency 公理证据一致。

本裁决不声称已完成 (1/2)Ξ 乘积的噪声导数、复频率/倾斜 law、cone 与高频区域、反演或振荡积分、真实 source 全部 γ/长度运输、平滑移除及 C1/C2 根结论。上述边界与冻结 scope 相符，不影响本三个 real-frequency undressed odd-power 定理的接受。
