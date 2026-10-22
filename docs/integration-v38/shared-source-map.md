# Shared global-rate proposal v1 — source and API map

状态：只读源/API核对；不是 Lean 检查、公理审计、独立声明审查或原根闭合。只读 remote 调用未激活 Lean，不读取 token、不写缓存、不启动任何重进程。服务器没有 rg，窄范围源码定位改用 grep/nl/sed；一次 JSON 请求被接入层拒绝且 `operation_may_have_started=false`，修正请求后只读读取。没有为此运行任何 Lean/probe。

## 1. 冻结来源与本轮所读资料

| 文件/版本 | 定位与用途 | SHA256/绑定 |
|---|---|---|
| `C:/game/shao lean/AGENTS.md`、`SERVER.md`、`coordination/TEAM.md` | root 拥有公共定义/Probability、远程唯一构建、作者/审查隔离；外部 CPU0–9/80GiB 不动；本轮更窄授权为只读提案 | 实读；无改写 |
| `C:/Users/UIO/.agents/skills/math-theorem/SKILL.md` 与 prompt-library、lean-verification、openai-workflow | 声明冻结、原义忠实性、边界、新上下文审查；本轮明确禁编译优先于一般机械检查建议 | 实读；未把源码读取写成 Lean 通过 |
| `C:/game/shao lean/drafts/oq3/root-contract.md` | §2真实概率、K、domK、EReal Legendre；§3固定律正尾唯一全局率极小；§4无界B保留有限开邻域及另加远区概率界 | `a3a55ceb4dcdd848967d979ec5eb1c277ac4539476728e7fdce119f01fd2757a` |
| `C:/game/shao/current/oq3/proofs/r1/report.md` | 全文实读；146–159固定候选与 rate；161–241原全局正尾论证及KL(9)/(10)；243–268协方差/曲率与本提案责任外界；全篇固定律消费背景 | `3473d34ff20bd0d334b9ef3ea3c3ee167fba4d5cc3a742849820ce54d639e662` |
| `drafts/oq3/next-global-tests-interface-proposal.md`、`general-kl-next-api-notes.md` | 原 OQ3→root 消费提议与一般 KL/域外总化风险；notes只作作者背景，不当作已接受证明 | 实读相关完整材料；不作自认证 |
| `drafts/oq3/u19a-pr-handoff.json` | exact PR146 head/base/source/review绑定 | head `5d14dbdb619fd7d2eb97ec31e049053de53be871` |
| `drafts/oq3/u19a-proof-review.md` | actual两类型与现有完整独立证明票；前缀历史 IN_PROGRESS、最终§5 CORRECT | `70f98f21119dea78526f6f0e4d242cc8c4caa17222fd47fd71b7a58ab57a1c05` |
| `drafts/oq3/u19a-actual-declarations.txt` | exact实际内核导出TYPE；两公共量词完整核读 | `37c55eb82cbf85ff728655666f5113acd3e7fe1a55eb780d932b9487adf8f3f2` |
| `library/SNAPSHOT.json`、`library/lean-toolchain` | v36 main/accepted/tree与工具链绑定 | v36 main82294da7 / acceptedf2a39a09；Lean4.36.0-rc1 |

## 2. PR146 exact source 与两个完整公共类型

实际读取命令使用 `git -C <lead-oq3> show 5d14dbdb619fd7d2eb97ec31e049053de53be871:Shao/OQ3/SourceGlobalExponentialTests.lean`，未依赖可能已经切换的 live branch 工作树。再次以 git object 字节 sha256sum 得 source `24c7029298efc869d785ad4e08dae1a6ea0ca788bf47357355a4e5c564a513df`。source imports 是 EnergyBernoulliMGF、PositiveRate、RegularCovariance，namespace `Shao.OQ3`。公共模块不得反向 import 这些模型源。

source119–133完整第一类型：

```lean
theorem source_saddle_exponential_value_bound
    (q : ℝ) (w : AtomicIndex → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hm : ∀ k : Fin 4,
      HasSum (fun i => w i * constraintFeature sourceEll (fixedAtom i) k)
        (constraintTarget q k)) :
    (∀ s t : ℝ,
      Integrable (fun x : ℝ => Real.exp (s * x + t * x ^ 2))
        (originalMeasure sourceEll w) ∧
      0 < (∫ x : ℝ, Real.exp (s * x + t * x ^ 2) ∂originalMeasure sourceEll w) ∧
      s * (q / 4) + t * q -
        Real.log (∫ x : ℝ, Real.exp (s * x + t * x ^ 2) ∂originalMeasure sourceEll w) ≤
          saddleRate sourceEll q w) ∧
    (8 * sourceEll) * (q / 4) + (-sourceEll) * q -
      Real.log (∫ x : ℝ, Real.exp ((8 * sourceEll) * x + (-sourceEll) * x ^ 2)
        ∂originalMeasure sourceEll w) = saddleRate sourceEll q w
```

source153–167完整第二类型：

```lean
theorem exists_source_tail_exponential_separator
    (q : ℝ) (hq0 : 1 < q) (hq1 : q < 103 / 100)
    (w : AtomicIndex → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hm : ∀ k : Fin 4,
      HasSum (fun i => w i * constraintFeature sourceEll (fixedAtom i) k)
        (constraintTarget q k))
    (a c : ℝ) (hc0 : 0 < c)
    (htail : (Real.sqrt q / 4) * Real.sqrt c ≤ a)
    (hne : a ≠ q / 4 ∨ c ≠ q) :
    ∃ s t : ℝ,
      Integrable (fun x : ℝ => Real.exp (s * x + t * x ^ 2))
        (originalMeasure sourceEll w) ∧
      0 < (∫ x : ℝ, Real.exp (s * x + t * x ^ 2) ∂originalMeasure sourceEll w) ∧
      saddleRate sourceEll q w < s * a + t * c -
        Real.log (∫ x : ℝ, Real.exp (s * x + t * x ^ 2) ∂originalMeasure sourceEll w)
```

类型使用 q/w 先量化，所有有限实 s/t，源的“finite exponential tests”不表示 w 有限支撑。第一 theorem 无 q-window、无全原子严格正、无协方差前提；第二是完整 c>0弱尾域，非仅可实现均值域/能量区间。两项没有 canonical globalRate、domK、EReal、导数或一般 KL 结论。

PR146相同依赖源（git exact head及本地library字节哈希相同）：

| OQ3源 | 精确位置与用途 | SHA256 |
|---|---|---|
| `Shao/OQ3/InverseTilt.lean` | 20–24 inverseNormalizer/originalMeasure；51–56真实概率生产；原律是反倾斜律而非 atomicMeasure | `c7e7d19e8b70481b663bec1fd12ea9301d73313faaf35997e85aa9ba99f21811` |
| `Shao/OQ3/PositiveRate.lean` | 20–21 saddleRate=ell*q+logZ；142–146正率 theorem真实前提包括 ell≠0与全w_i>0 | `8e727078d3a4f1db2392384b84cc31235ff69efa13dd5e44b23eac818a788f7b` |

## 3. 实读 pinned mathlib API

统一 remote 前缀：`/root/rivermind-data/shao-lean-20261021/lean/.lake/packages/mathlib/`。实际 `git rev-parse HEAD` 为 `807d3836b165983210ee2ecf3cd28f239436949c`。下列是源码定位，未运行 #check 或 import smoke；不声称 olean/cache closure 已核。

| 源路径与行 | actual API/语义 | 未来消费 |
|---|---|---|
| `Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`24–28、204 | Bochner积分仅在可积函数为真实积分，不可积总化为0；`integral_undef`要求¬Integrable | 必须用 domK 子类型，不许域外 Real.log总化 |
| 同上792–798 | `MeasureTheory.integral_exp_pos {μ : Measure α} {f : α → ℝ} [NeZero μ] (hf : Integrable (fun x ↦ Real.exp (f x)) μ) : 0 < ∫ x, Real.exp (f x) ∂μ` | T1确切调用；不需要概率/有限测度，只要NeZero和真Integrable |
| 同上990–1000 | `integral_const (c : E)` 值为 μ.real univ • c；`integral_eq_const [IsProbabilityMeasure μ]` 从AE恒值给实积分等于该常数 | 概率下零参数测试值0 |
| `Mathlib/MeasureTheory/Function/L1Space/Integrable.lean`137–146、166 | `integrable_const_iff`；`integrable_const [IsFiniteMeasure μ] (c : β)` | 概率律有限，零参数在domK；无限计数测度示例的边界解释 |
| `Mathlib/MeasureTheory/Measure/Typeclasses/Probability.lean`52–54、64–88 | 概率类要求 μ univ=1，经IsZeroOrProbabilityMeasure得到有限测度；`IsProbabilityMeasure.ne_zero`84–85，`IsProbabilityMeasure.neZero`87–88 | OQ3实际概率自动给NeZero；零测度不通过 |
| `Mathlib/Analysis/SpecialFunctions/Log/Basic.lean`59–61、103–108 | `Real.exp_log (hx : 0 < x) : exp(log x)=x`；`log_zero=0`、`log_one=0` | T1正值后真实还原；显示为何域外log0不可用 |
| `Mathlib/Data/EReal/Basic.lean`33–46 | EReal=WithBot(WithTop ℝ)，推导CompleteLinearOrder，注册Real→EReal coercion | 真正完整上确界无需BddAbove前提 |
| 同上55–70 | `EReal.coe_le_coe_iff`、`coe_lt_coe_iff`、`coe_eq_coe_iff`/`coe_ne_coe_iff` | 所有真实有限测试→EReal比较 |
| 同上254–271 | `bot_lt_coe`、`coe_ne_bot`、`coe_lt_top`、`coe_ne_top` | 候选coe L有限；其他点top合法，概率域非空排除bot |
| `Mathlib/Order/CompleteLattice/Basic.lean`211–236 | `le_iSup (f : ι → α) (i : ι)`；`le_iSup_of_le`；`iSup_le (h : ∀ i, f i ≤ a)`，均为CompleteLattice | T2、T3；完全不需有限sup或紧性 |
| 同上280–285 | `iSup_le_iff : iSup f ≤ a ↔ ∀ i, f i ≤ a` | 等价上界接口有现成原语，无需另加公共wrapper |
| 同上351–355、584 | `iSup_eq_bot`、`bot_lt_iSup`；`iSup_emptyset` | 空域给bot；非空有限测试给非bot |
| 同上201–202 | `sSup_image' {s : Set β} {f : β → α} : sSup (f '' s) = ⨆ a : s, f a` | 确认子类型 iSup 就是domK上实测试像集的扩展实sSup，无局部域替换 |
| `Mathlib/Probability/Moments/IntegrableExpMul.lean`112–116 | `ProbabilityTheory.integrableExpSet (X : Ω → ℝ) (μ : Measure Ω) : Set ℝ := {t | Integrable exp(t*X) μ}` | 现有域是单实参数，支持同样语义；本稿二参数域不假装直接等于该单参数域 |
| `Mathlib/Probability/Moments/Basic.lean`122–127、175–179、202–213 | 原生mgf/cgf总定义；不可积时mgf=0、cgf=0；正MGF/exp_cgf仍需真Integrable及非零 | 不 import该较宽单参数模块来掩盖域；禁止用cgf_undef充当域外K |
| `Mathlib/Analysis/Real/Sqrt.lean`148–149、177 | `Real.mul_self_sqrt (h : 0 ≤ x)`、`Real.sq_sqrt (h : 0 ≤ x)` | 仅下游OQ3候选尾域成员性；公共模块无需sqrt |
| `Mathlib/Order/Filter/Extr.lean`108–110 | IsMinOn本身不包含候选属于集合 | 本稿直接列hz₀及极小/等号唯一性，避免省略存在门，也不新增此import |

直接读取文件的SHA256：

```text
66837a733a5514a0fd824591ac10d43063c5a5cd94c9bdbbf80025686c16c670  Mathlib/MeasureTheory/Integral/Bochner/Basic.lean
ba85dea4b9ae08516ad8f1926ac2403cc7a386a8eaf6e057c55e668c427a1301  Mathlib/Data/EReal/Basic.lean
5af0d412e8f8a41c572908d31d9fc0a4745b3ede9165c846d0f788155d207e1f  Mathlib/Order/CompleteLattice/Basic.lean
0c2f73c5a7d1a27efc9e44d02ead60112bfe10e3cfbba2407ad3dbcd1c363a97  Mathlib/Analysis/SpecialFunctions/Log/Basic.lean
00ef2a106c0ae4032944cec021ad58d04c370cc9b84547bed95462ca5205e25b  Mathlib/MeasureTheory/Measure/Typeclasses/Probability.lean
d80e3495465030c1accca450935e4bfafcfe31d9b695e17f23ee9cfcea537759  Mathlib/MeasureTheory/Function/L1Space/Integrable.lean
73264d34c22038347bc73821a45442346ce12756475359325ebb9340a89af8fa  Mathlib/Probability/Moments/Basic.lean
9ddfb99776091f424dc7e1a86b6a456180e8186cae9ca1084541eff41aa9e3a8  Mathlib/Probability/Moments/IntegrableExpMul.lean
```

## 4. 本轮消除的设计不确定性与保留事项

设计层面已明确：公共K的域是完整真可积参数域；域内真正配分可由现成API生产；EReal具CompleteLinearOrder且四个基本iSup/coercion API足够接PR146；真实候选率值与完整正尾唯一极小性不必绕行未证的一般KL对偶性。所有这些是可供独立审查的提案理由，不是已编译/已独立证明的本模块。

未确认/未执行：三个定义与四类型的Lean elaboration；最小import传递闭包/olean readiness；生产实现；任何完整公理审计；独立声明审查票；source→canonical K导数/Hessian/局部逆图；KL(9)/(10)；D\U统一gap/概率上界；任何完整OQ3根。

下一消费者顺序应为：新上下文声明审查 → root冻结 → root按SERVER策略独立实现/机械门及完整证明审查 → OQ3/root下游同q/w/P适配PR146 → 仅核算实际消除的全局率桥，不扩写为整个根闭合。
