# U21b AffineWeakCramer 完整独立证明审查

STATUS: IN_PROGRESS

本段是独立盲审不可改写前缀。先且只读取实际 owner TYPE 选块 u21b-actual-types.txt 的全部三项完整类型及延续行；尚未读取 AffineWeakCramer 实现、作者收据、build/Audit 日志或作者证明叙述。此前声明上下文存在，本次并不把旧声明批准当作实际 proof 已成立。

## 全部实际类型原文保全

```text
DECL Shao.OQ3.uniform_weakCramer_of_affine_frequency_bounds
TYPE ∀ {ι : Type u_1} (K : Set ι) (mu : ι → MeasureTheory.Measure ℝ),
  (∀ p ∈ K, MeasureTheory.IsProbabilityMeasure (mu p)) →
    ∀ (A : ι → Matrix (Fin 2) (Fin 2) ℝ) (b : ι → Fin 2 → ℝ) (L U beta c R : ℝ),
      0 < L →
        0 < U →
          0 ≤ beta →
            0 < c →
              0 ≤ R →
                (∀ p ∈ K,
                    ∀ (xi eta : ℝ),
                      L * √(xi ^ 2 + eta ^ 2) ≤
                          √((xi * A p 0 0 + eta * A p 1 0) ^ 2 + (xi * A p 0 1 + eta * A p 1 1) ^ 2) ∧
                        √((xi * A p 0 0 + eta * A p 1 0) ^ 2 + (xi * A p 0 1 + eta * A p 1 1) ^ 2) ≤
                          U * √(xi ^ 2 + eta ^ 2)) →
                  (∀ p ∈ K,
                      ∀ (xi eta : ℝ),
                        R < √(xi ^ 2 + eta ^ 2) →
                          ‖Shao.OQ3.jointCharacteristic (mu p) xi eta‖ ≤ 1 - c * (√(xi ^ 2 + eta ^ 2)).rpow (-beta)) →
                    have Y := fun p x => (A p).mulVec (![x, x ^ 2] - b p);
                    have nu := fun p => MeasureTheory.Measure.map (Y p) (mu p);
                    have Phi := fun p xi eta =>
                      ∫ (y : Fin 2 → ℝ), Complex.exp (↑(xi * y 0 + eta * y 1) * Complex.I) ∂nu p;
                    have cA := c * U.rpow (-beta);
                    have RA := R / L;
                    0 < cA ∧
                      0 ≤ RA ∧
                        ∀ p ∈ K,
                          MeasureTheory.IsProbabilityMeasure (nu p) ∧
                            ∀ (xi eta : ℝ),
                              RA < √(xi ^ 2 + eta ^ 2) → ‖Phi p xi eta‖ ≤ 1 - cA * (√(xi ^ 2 + eta ^ 2)).rpow (-beta)

DECL _private.Shao.OQ3.AffineWeakCramer.0.Shao.OQ3.affine_parabola_continuous
TYPE ∀ (A : Matrix (Fin 2) (Fin 2) ℝ) (b : Fin 2 → ℝ), Continuous fun x => A.mulVec (![x, x ^ 2] - b)

DECL Shao.OQ3.affine_parabola_characteristic_factor
TYPE ∀ (mu : MeasureTheory.Measure ℝ) (A : Matrix (Fin 2) (Fin 2) ℝ) (b : Fin 2 → ℝ) (xi eta : ℝ),
  have Y := fun x => A.mulVec (![x, x ^ 2] - b);
  have nu := MeasureTheory.Measure.map Y mu;
  have xiA := xi * A 0 0 + eta * A 1 0;
  have etaA := xi * A 0 1 + eta * A 1 1;
  have phi := ∫ (y : Fin 2 → ℝ), Complex.exp (↑(xi * y 0 + eta * y 1) * Complex.I) ∂nu;
  phi = Complex.exp (↑(-(xiA * b 0 + etaA * b 1)) * Complex.I) * Shao.OQ3.jointCharacteristic mu xiA etaA ∧
    ‖phi‖ = ‖Shao.OQ3.jointCharacteristic mu xiA etaA‖
```

## 独立类型、量词与源义务重建

1. 当前实际类型选块枚举三项 theorem；没有公开或私有定义体供先行翻译。
2. 两个公开名是 affine_parabola_characteristic_factor 与 uniform_weakCramer_of_affine_frequency_bounds；私有名属于当前 AffineWeakCramer 模块，语义是连续仿射抛物线统计量。
3. 先行选块显示的是 Lean 实际展开后的类型，不是 scope 中的作者注释；have 记法保留 let 固定对象的依赖顺序。
4. 唯一私有连续性定理对每个实 2×2 矩阵 A 和向量 b 都给 x↦A·((x,x²)−b) 的实际 Continuous。
5. 私有连续性类型不假设 A 可逆／对称、b 为均值或任何测度性质，预期能真实提供后续 map 的可测门。
6. 第一公开因子定理对任意实测度 mu、任意 A/b 与任意实频率 xi/eta 成立。
7. 它没有概率、有限测度、矩存在或相位 Integrable 假设，不能在 proof 中暗中补上这些前提。
8. Y 是这个同一个 A/b 的真实多项式统计量，nu 精确是 mu.map Y；没有更换律或选择额外像测度。
9. 变换频率 xiA=xi*A00+eta*A10、etaA=xi*A01+eta*A11，是候选转置作用 Aᵀu 的两个坐标。
10. phi 是 nu 上 exp(i(xi*y0+eta*y1)) 的实际复积分，不是抽象任意函数族。
11. 第一合取要求完整复恒等式：phi=exp(−i(xiA*b0+etaA*b1))*jointCharacteristic mu xiA etaA。
12. 第二合取要求实际积分的模相等，应该由相位模为 1 推出；不能只给两个独立的范数上界。
13. 原义务要求正确展开有限矩阵乘法并核负相位。A 非对称时错把 Au 当 Aᵀu 会使恒等式失败。
14. 任意测度下相位未必真可积；需实际库 integral_map 的 measurability 条件及总化语义，不能凭概率版 integrable_jointPhase 或“所有积分为零”跳过可测门。
15. 第二公开定理对任意 universe 中的类型 ι、任意 K、mu/A/b 族成立；仅在 p∈K 给真概率输入。
16. ι 没有可测／拓扑结构，K 不假设非空，p 不参与积分；不能偷偷增加联合参数可测性。
17. L、U、beta、c、R 在全部 p 和频率之前固定；L/U/c 严格正、beta/R 非负。
18. hfreq 对所有 p∈K 和频率给 L*rho≤rhoA≤U*rho，rho=sqrt(xi²+eta²)、rhoA=sqrt(xiA²+etaA²)。这是真欧氏半径，不是 Fin 2 Pi 的默认最大值范数。
19. hWC 仅给原始 mu p 在 rho>R 上的实际 jointCharacteristic 模≤1−c*rho^(−beta)。
20. 结论 Y/nu/Phi 由同一个 mu p/A p/b p 唯一固定；Phi 是实际像律上的复积分。
21. cA=c*U^(−beta)、RA=R/L 是明确数值，不是可按 p/频率重新选择的存在常数。
22. 结论先交付 cA>0、RA≥0，再对每个 p∈K 交付 nu p 真概率和所有 rho>RA 的目标 WC。
23. 所需负幂方向：rhoA≤U*rho 与 −beta≤0 应给 (U*rho)^(−beta)≤rhoA^(−beta)，才能得到更小减项的统一上界。
24. 负幂比较之前需由 rho>R/L≥0、L>0 和 hfreq 得 rho>0、rhoA>R≥0，不能用零点 rpow 总化替代正性。
25. 新 radius 必须用 L；新 c 必须用 U。所有常数在 K 和频率外同一固定。
26. 真概率像律应同时有 Y 连续／可测证据，不能仅依非可测 map 的库兜底概率 instance。
27. 该类型实际保留 beta=0、R=0、K 空、任意中心以及第一定理奇异 A。第二定理在非空 K 的双界自身限制频率坍缩。
28. 这里没有实际协方差、逆平方根或谱界的生产者；hfreq/hWC 都是诚实显式前提。拟 source 消费是 R2 仿射标准化保持指数的步骤，不是完整根 C/B。
29. 待逐行 proof 核：真正 continuity→measurability→map 身份、逐点相位等式、真实概率门、严格外区和 rpow 合法方向，以及全部三项实际 owner TYPE 与公理覆盖。
30. 原始根 A 已有独立正式 v40 验收；这不为本 C/B 后继提供数学捷径。当前完整 proof 结论必须独立于作者 PASS 标签。

--- END IMMUTABLE BLIND PREFIX ---

## 来源、冻结类型与本次范围

以下是在先行全部三项 TYPE 盲译已经持久化后，依次完成原来源、完整实现、实际库 API、全部 owner 类型及最后机械证据审查所得。此前 IN_PROGRESS 是历史检查点；本次最终状态在末节。

实际原件是 current/oq3/proofs/r2/report.md，SHA256 572e74aa9c12e2771f5543a5709a2807666eeea0a4076e7a3263e5c7bcf87f55。重新核对了 38–60、83–92、343–373 行。
R2 40–43 固定真实 W=(X,X²) 和指数倾斜；86–92 的 Y_theta=Delta(theta)^(-1/2)(W−m(theta)) 要求平移只有相位、线性标准化保持弱 Cramér 指数。343–369 先生产未标准化族缺口，再由谱(2)调整标准化常数。本模块只承担后半段明确频率比较下的真实像律转移。
冻结 scope78 的完整公开两签名经独立逐白空归一化比较与实际 source 24–34、71–98 一致；四个 imports、namespace、Matrix/BigOperators scope 及 noncomputable header 也一致。公开 let 的依赖和实际 phi/Phi 均未被替换为抽象代理函数。
此处不是实际 Delta 的逆平方根／白化或谱界生产者：L/U 双界和原律 hWC 仍是诚实显式输入。允许任意 A/b 的精确身份不声称 A 本身就是标准化矩阵。

## 完整152行实现的逐义审查

### 私有连续性定理：source 13–22

13–15 的实际私有类型与先行 owner TYPE 相同：任意实 2×2 A、任意二维 b，输出 x↦A*ᵥ((x,x²)−b) 连续。
16–19 使用 continuous_pi 后，逐坐标实际 change 到有限和 ∑j∈Fin2 Aij*((x,x²)j−bj)。这正是 Matrix.mulVec/dotProduct 的固定库定义，不依赖矩阵范数或未建立的 operator-continuity instance。
20–21 用 Fin.sum_univ_two 和真实向量构造的两坐标化简；22 的 fun_prop 此时处理的只是两项实多项式、常数乘法与减法。没有可逆性、正定性、概率或矩假设。
这个 helper 处理全部行 i；有限 Pi 连续性不会把二维统计量缩减为单一分量。它同时覆盖奇异、零及非对称 A。

### 精确仿射特征因子：source 24–69

24–34 的任意 mu 范围真实保留，没有 IsProbabilityMeasure／有限性／Integrable 前提。35–43 的局部 Y/nu/xiA/etaA/f/phi/k 只是公开 lets 的别名，并未另选测度或中心。
44–45 的 change 保留两项合取：完整复因子身份及模身份。
46 真实消费上述私有连续性，47 由实际连续的复指数、实坐标线性组合得到 Continuous f。实数和有限实 Pi 的标准 Borel 结构、复数的第二可数伪度量结构，支持 hY.measurable.aemeasurable 与 hf.aestronglyMeasurable。
48–49 使用的是实际 MeasureTheory.integral_map，而非一条隐含概率或 Integrable 的替身。
实际 Bochner/Basic.lean 1076–1086 的原型仅要求 AEMeasurable Y mu 与 AEStronglyMeasurable f (map Y mu)，返回真实 map 积分等式。上述 source 给足这两个门。
其下层 1065–1074 integral_map_of_stronglyMeasurable 的证明将可积与不可积分支区分：不可积支由 integrable_map_measure 等价保证两边同步 integral_undef；并非任意把某侧假设为零。因此任意无限 mu 的总化语义是合法 API 原义，不是漏加有限测度导致的不实推导。
50–57 是逐点而非积分线性推导：明确展开 Matrix.mulVec、dotProduct、Pi.sub_apply、Fin 2 两项和后，由 ring 证明 xi*Y0+eta*Y1=xiA*x+etaA*x²−(xiA*b0+etaA*b1)。
系数确为 xiA=xi*A00+eta*A10、etaA=xi*A01+eta*A11；非对称 A 下仍是 Aᵀu，没有误用 Au 或错置 b 到矩阵外。
58–62 先展开 f/k/jointPhase，再用复 exp_add 和实数到复数的乘法、加法嵌入恒等式。ring 仅交换标量项，不会改变真实测度；常数相位为负号 −[(Aᵀu)·b]。
63–65 依次重写真正 map 恒等式、真正逐点 hfun、integral_const_mul，然后 rfl 回到 jointCharacteristic 的定义。
实际 Bochner/Basic.lean 288–290 的 integral_const_mul 对复数常数／任意函数无可积前提成立，由 275–278 integral_smul 直接给出。这里没有对两个未证明可积的函数使用 integral_add；Complex.exp_add 只用于被积函数逐点恒等式。
实际 JointNonlattice.lean 20–24 的 jointPhase/jointCharacteristic 就是同 mu 的 exp(i(xi*x+eta*x²)) 与其复积分。此 rfl 不把推送向量律换成其他族。
66–69 先使用已经建立的完整复身份，再 norm_mul，实际 Complex.norm_exp_ofReal_mul_I 使 ‖k‖=1。无除相位、除积分、假定积分非零或频率非零。
因此两项公开输出均真实得到；没有只证明模上界后假装得到精确复相位身份。

第一定理对零测度、无限测度、零频率、任意中心、奇异／非对称矩阵都有效。这里不声称任意 mu 的相位真可积；任意测度目标的积分是固定库 Bochner 总化，而精确换元和非零单位相位乘法 API 在这种语义下已经证明成立。

### 同一个统一概率像律及严格频率外区：source 71–131

71–98 的完整类型忠实保留任意索引、K、A/b，只有 p∈K 时的真概率门；没有隐藏参数可测性或 nonempty K。
99–109 将公开 Y/nu/Phi/cA/RA 固定为相同表达式；cA=c*U^(−beta)、RA=R/L。在任何 p 或 xi/eta 引入之前，110–112 交付其严格正／非负性质。
110 的 rpow_pos_of_pos 接受 hU>0 和任意实指数；实际 Pow/Real.lean 116–117 由 exp_pos 得到 U^(−beta)>0，无需 beta 严格正。111 只用 R≥0、L>0 得半径非负。
113–114 固定任意 p∈K 后才局部装入 hprob p hp；这不是重新选择 mu p。
115 的连续性仍是同一 Y p。116–118 显式使用实际 Measure.isProbabilityMeasure_map_iff，参数为真实 hY.measurable.aemeasurable，右侧实际 mu p 概率实例已建立。
实际 Probability.lean 139–141 的 map_iff 需要这个 AEMeasurable 证据。虽然其 map 概率 instance 124–131 本身也包含非可测 map 的总化兜底分支，本 source 没有依赖那种兜底解释：连续性已确保是真正可测推送。
故输出 nu p 真概率；实际 f 连续且模为 1，在它上也是真可积（可由 Integrable.of_bound 与有限概率质量推导）。原律相位可积另有公开 integrable_jointPhase。证明此处不需要重复产出 Integrable 结论，因为调用的精确身份本来就是无条件积分 API。
119–124 固定当前频率后，r 和 rA 字面使用平方和的 sqrt；不以 Fin 2 函数空间的 max-norm 代替欧氏频率。
125 以 RA≥0 与 hout:RA<r 得 0<r，零频率没有进入任何负幂比较。
126–128 仅在 hL>0 下使用 div_lt_iff₀，将 R/L<r 变为 R<L*r；mul_comm 只调整标量顺序，没有除 r、R 或 beta。
129 是实际 hfreq p hp xi eta，得到 L*r≤rA≤U*r；130 由下界严格推到 R<rA；131 再由 R≥0 得 0<rA。
原律 hWC 的输入是变换后频率及这个真严格区域；没有把下界仅为 R≤rA 的边界当成外区。

### 精确负幂常数与最终模界：source 132–148

132–133 使用实际 Pow/Real.lean 565–569 的 rpow_le_rpow_of_nonpos：hx:0<x、hxy:x≤y、hz:z≤0，输出 y^z≤x^z。
在此 x=rA>0、y=U*r 且 rA≤U*r、z=−beta≤0，故精确是 (U*r)^(−beta)≤rA^(−beta)。这给减项的下界，方向与结论所需一致。
134–142 的 hcost 明确证明 cA*r^(−beta)≤c*rA^(−beta)。
136–141 的 typed hm 使用实际 Real.mul_rpow hU.le hr.le。其固定原型在 Pow/Real.lean 476–483 要求两个底数非负；本 source 已有更强 U>0、r>0，不以 0 的负幂总化越过正性门。
将乘法公式代入 cA=c*U^(−beta) 后只用结合律，精确得到 c*(U*r)^(−beta)，不是偷偷更换 c 或 beta。
142 只以 hc.le 乘上非负标量保持 hpow。此处 c>0 已在公共前提中，不需反向除法。
143–144 的 hnorm 是第一公开定理对同 mu p、A p、b p、xi/eta 的模合取实例，不是针对另一个 arbitrary complex family 的比较。
145–148 的 calc 先等于同原律变换频率特征模，再以 hWC p hp xiA etaA hRrA 给界，最后 sub_le_sub_left hcost 1 给 1−c*rA^(−beta)≤1−cA*r^(−beta)。
这是完整目标 Phi 的真实像律积分界。L 用在新半径 R/L，U 用在负幂常数 cU^(−beta)，两个角色未互换。
150 正常关闭 noncomputable 的匿名 section，152 关闭 namespace，没有局部 instance 或选项外泄。

### 边界、统一量词与假设消费

K=∅ 时 p∈K 子句真空，但 cA>0 和 RA≥0 仍于 intro p 前真实交付；证明没有从空 K 提取非空元素。
beta=0 合法：neg_nonpos、rpow_pos、mul_rpow 都保留等号边界；新系数 cA=c，没有暗用 strict beta>0。R=0 也合法，因为严格 hout 和 hR 保证所用 r/rA>0。
任意 b p 只影响单位相位；没有调用它为均值、参数连续或真倾斜均值不变等虚假性质。
第一目标允许 A=0、奇异、非对称；第二目标对非空 K 所输入 L>0 的全频率下界自行排除坍缩，不靠未证明的逆矩阵。
ι 没有拓扑／可测结构，proof 不对 p 积分。全族同一 L/U/beta/c/R/cA/RA 固定在 p 与所有频率之外，无 n 依赖，没有逐参数选常数。
source 没有由相位不可积推假命题，没有调用另模块 private API，也没有输入或生产未证的实际 covariance inverse sqrt。

## 全部实际所属常量、完整类型与传递公理

先行前缀已保存全部 actual-types.txt 的 44 行／2608 字节，不省略 universe、hprob/hfreq/hWC 的全部延续或五个结论 let。数学完成后又逐项读取实际 audit.log 的 DECL/TYPE/AXIOMS 选块全部延续并对照；原始完整日志未下载到本地。

| 实际 owner 常量 | 分类／完整实际语义／source 对应 | 实际传递公理 |
|---|---|---|
| Shao.OQ3.uniform_weakCramer_of_affine_frequency_bounds | public theorem；任意 Type u_1／K／mu 概率族；全部双边欧氏频率门、raw WC、Y/nu/Phi/cA/RA 固定及全频率合取；source71–148 | propext, Classical.choice, Quot.sound |
| _private.Shao.OQ3.AffineWeakCramer.0.Shao.OQ3.affine_parabola_continuous | private theorem；任意 A/b 的完整二维统计量 Continuous；source13–22 | propext, Classical.choice, Quot.sound |
| Shao.OQ3.affine_parabola_characteristic_factor | public theorem；任意 mu/A/b/频率，五个依赖 let、完整负相位复等式及模等式；source24–69 | propext, Classical.choice, Quot.sound |

实际 Audit.lean 不是按名字／namespace 前缀猜所属：它以 env.getModuleIdxFor? 取 env.header.moduleNames，精确比较 Shao.OQ3.AffineWeakCramer；对每个真实 owner 调用 Lean.collectAxioms，拒绝新 axiom 和白名单外传递公理。
其目标数组只含两个公开名，同时遍历全部 env.constants，所以私有连续性定理没有漏掉。pp.deepTerms/maxSteps 仅控制输出打印，不改 proof 语义或资源设置。
完整152行源实际只有上述三个 theorem 声明；所有局部 have/let 已按行审查。owner 结果与 source 及先行 TYPE 联合确证：3owned／3THM=2public+1private，0DEF／0generated；没有按 helper 名字猜零生成项。
本单元各项实际都是完整三项标准公理，未出现 sorryAx、propext 之外新 axiom、unsafe/native_decide/implemented_by 或设置弱化。通过的 owner Audit 只作为这一机械事实证据，不替代前文独立数学判断。

## 最后读取的机械／历史／版本绑定

本地 actual source、remote own source 及 run/source-02.lean 同为152行／7064字节，SHA256 29457076f283c08b093949d3c12cfb020ea0bb496e51573ad74554114e94031f。run 的实际冻结快照名是 source-02.lean，不臆造同名模块快照。
两个完整公开签名均独立从实际 source 抽取并与 scope 的完整 fence 逐白空归一化匹配为 true；无公开定义，四 imports 原样保持。未因证明需要加强任意 mu、beta/R 或 K 的前提。

| 真实新产物 | 行／字节 | SHA256 |
|---|---:|---|
| source-01.lean（完整失败版本） | 147／6938 | 3560ac9a6c8328ca820598d12f069a0e59231beaf304dcd9cfbe622e8150c0a4 |
| source-02.lean（完整冻结成功版本） | 152／7064 | 29457076f283c08b093949d3c12cfb020ea0bb496e51573ad74554114e94031f |
| actual-types.txt（本地与remote一致） | 44／2608 | 789a5fdadeb50018647116edb6d0b00b66340cd80ea0f09f46684214483a624d |
| Audit.lean | 45／1933 | eb5bc1e56cf9e48989ae351eb385a230e9478053a5fb625d69ca0ed2bbeb65cd |
| audit.log（实际小写文件名） | 50／2861 | 1605c616e189b0895c48f300c5c0591dfc25b0a52c10852aa805058e22839f69 |
| audit-receipt.json | 25／860 | 1dedec18ec65bf3488d4de2f7b448ddbfe86a081605811e7711988b84124719b |
| receipt.json | 168／7133 | 87de03a6e6b99ed859d27d477f82e77fdcc4606482823a05f45053540ca06c2a |
| build-history.json | 56／1509 | 1056de7986908c2c7a0e18ee0723712743a9a61c6824d3ccdad4608d7115b581 |
| build-01.log | 63／2426 | a6cd1baf0a2360fab88d296bcab6456f18e281db07ad4f91c18058cfdaf4bce1 |
| build-02.log | 8／352 | bddb54e999a437adc9529359b169faa1c4c76ebefb1cfed82f19734330a66b8b |
| prerequisite-hashes.json | 7／522 | 16b7c7e89379ff239b9dd3a18f655e3a010068b574275246f359df96be19d684 |

build-history 的两个记录都是完整两目标 source，非 partial。01 exit1、4.568715秒，实际小错误选块为 mul_rpow rewrite 没匹配到实指数形式及 end Shao.OQ3 遇到尚未关闭匿名 section；另有114行实例写法建议。
02 exit0、4.342666秒，为当前152行完整源码首次成功；日志非空352字节，仅114行同一条 letI 写法 style warning，无 error。不能写空日志或零 warning。
独立 snapshot diff 只有将该 mul_rpow 重写改为显式 typed hm 恒等式，及增加 end 关闭匿名 section；公开类型/imports/数学假设未变，未调设置、放宽命题或隐藏前次失败。
首次 module-owner Audit exit0、5.045017秒；实际 footer 为0 frozen DEF、2 frozen THM、3 all THM、3 all DECL、axiom gate PASS。没有重复成功 source/Audit、没有探针或导入 smoke。
记录原生内存8192MiB、j4、autoImplicit=false、CPU affinity14–17；审查者此次只轻量读取，没有运行 Lean/Audit/重编、写 cache 或触及外部 CPU0–9/80GiB。

正式五前置 path-key 字典的 canonical 紧凑 SHA 为 bc48253cce1ae61632e2f1c21945b41c6f7839c681075d8b9814140e54e3587f。它恰是声明阶段已独立核过并由正式 RootA74 接受字典提取的 AtomProjection／FiniteConstraints／JointNonlattice／SourceStarter／SummableAtoms 同五项与同 SHA；本次正式文件与该已接受绑定一致，不读作者 candidate JSON 为数学证据。
旧 Mathlib 公开闭图、直接8对象存在性、Lean4.36.0-rc1／Mathlib807d3836... 的 pins 使用声明阶段已通过证据；没有重扫图、重哈希稳定对象或重跑成功门。
实际观察分支 feat/oq3-affine-weak-cramer，HEAD59a531b89eff7c11e4fc53583067f2cd3b53a517（接受v39）；status 仅 ?? Shao/OQ3/AffineWeakCramer.lean。没有本模块 commit/PR。v40后仍由已冻结v39正常建独立分支不是改写旧 head，也不改变这五份前置语义。
冻结 scope 中 A OPEN／旧branch 等描述是冻结时历史，没有倒改。当前根协调正式状态为 A CLOSED_INTEGRATED_KERNEL_CHECKED（v40/PR164），B/C/D OPEN；本单元不再声称所有四根仍 OPEN，也不据自己两个辅助定理宣称 C 已闭。
所有 source/scope/旧票/receipt/shared/cache/pins/frozen heads 保持只读，未参与作者实现；不生成新 agent/chat/goal。作者 receipt 的数学叙述未作为前文证明依据，只在这里核其行政事实与实际产物一致。

## 最终独立裁决

STATUS: CORRECT
REVIEW: COMPLETE INDEPENDENT PROOF / SOURCE / ALL ACTUAL OWNER TYPES / EXISTING MECHANICAL EVIDENCE。
JUSTIFICATION: 完整152行实现确实建立同一统计量的连续可测门、任意测度下合法无条件 Bochner 换元与完整负相位身份，随后在真概率可测像律上以同一固定 L/U/c/beta/R 及真实严格外区正性完成负幂方向和精确常数传递。所有三项 owner 类型、完整续行与实际标准公理均核到，scope 未被加强，机械首次成功与修复历史无掩盖。

原始目标→消除义务→直接 consumer→剩余：R2 90–92／368 的仿射标准化保持指数→真实 Y=A(W−b) 像律特征复相位／Aᵀ 频率身份以及统一 cA=cU^(−beta)、RA=R/L→真实紧倾斜族 WC 后的协方差标准化→还须把 A 绑定 actualCov 的逆平方根或等价白化，真实生产谱双界与标准化矩，并完成根 C/B 的其余分析装配。
hfreq/hWC 是公开明确输入，不是本 proof 已生产的谱或单点稳定性结果；本节点不声称实际 covariance inverse sqrt 已实现、不声称一般无界族自动稳定、均值逆／C/B/D 根闭合或最优常数。A 的 v40 正式完成与此剩余界限分别保留。

不可改写盲前缀仍为89行／7053字节，SHA256 2b2ba320af0959fe09460ee44c6ef86f773f3e2b0849319ba1be0e33cdac8545；完成追加后逐字节复核其原样保留。
