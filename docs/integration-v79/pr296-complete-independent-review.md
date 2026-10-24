# SourceOriginalIIDHalflineBudget 独立完整最终审查

STATUS: CORRECT

本审查接受冻结的一个公开定理及一个 local ⊤ 可测空间实例。生产源161行、每段证明、两个实际完整展开 TYPE、唯一非定理完整 VALUE、冻结头中11个 literal let 值及证明中6个局部 let 值均已实读。结论仅为原 AE iid family 与独立均匀排列上的两个半线 retained L 的真实可积性和 CR 支付。全部原根保持 OPEN，OQ3 保持 PAUSED_BY_USER。

审查者为 `/root/original_iid_halfline_budget_final_review`，新上下文、非作者；作者 `/root/permutation_reveal_candidate` 的零在途写权/执行 RELEASE 已先核验。使用 math-theorem 验缝流程，不使用 math-ultra，不再分派。本轮0新 Lean、0新 AX、0 producer 重编译、0缓存操作，既有成功证据按精确哈希复用。

## 精确版本与冻结

- PR296: https://github.com/randomcat4/shao-lean/pull/296，head `2097fb309dda526119eead79cf01e6d8d8882d73`，tree `3514de946469dcc5c88fc57bedb149fe91fbc7ab`，blob `b067f6525e029bf4c8ff9180661bf71e0a7fa79f`。
- 唯一新源 `Shao/Probability/SourceOriginalIIDHalflineBudget.lean`，8697 bytes/161行，SHA256 `ee93d25eb961501a70120768e5699b8fa35c939d58fa2300f46ac41aaeda9f72`。服务器 native Git 从作者 base 到 head 的差异确为仅此1源；未合并。
- 冻结 MD SHA256 `d68e014854ac228084c3e2921df5d75c4dccb70911754787f64b0d611fd63583`；正式 activation SHA256 `47a5528d7429d971a0efb34b993cb76ed76e4ec4d3c264b68b89b1a29890206a`。
- 对候选完整声明与生产 instance/完整 theorem head 作逐字比较，完全相同。新增的 Elab.async/maxHeartbeats 选项不改变数学声明。UTF-8无BOM、仅LF；禁止标识符扫描为空；打印无省略标记。

候选声明、完整数学证明及 scope 的 SHA256 分别为 `75da3b58b00590e3d2ba9356383e5f7ab76cb48b497b3b2c0e7f43155622d817`、`57aa36f1dbaa8fea8448848477fb760512e8d39d14d9d92f2930214c7a766384`、`8f51ded155ccc6fc0a13c6702b4d6d0759eadb702882e8d0d274979aa050d51c`，均与冻结绑定一致。

## 所有者完整 TYPE/VALUE 审查

| 实际所有者 | 实读与结论 |
|---|---|
| `labelPermMeasurableSpace`（源16） | 完整实际类型为 `(n : Nat) → MeasurableSpace (LabelPerm n)`；完整展开值是该可测空间完整格中的 `⊤`。与旧均匀排列律/乘积律的离散实例定义相同；没有从输入获取另一可测结构。CORRECT。 |
| `original_iid_actual_cutoff_two_halfline_budget`（源18–159） | 实读完整展开类型和整段源证明。`∃C>0` 在 Ω/μ/ρ/Q/n/X/x 之前；输入为概率性、明确的反射识别、n>0、AE可测、独立、固定ρ同律、ρ有限二阶矩/零均值/正二阶矩。输出同时含逐点 raw 身份、逐σ cutoff AE可测、每个r的实际L与有限绝对和 Bochner 可积，以及两个半线总积分≤CR。无目标可积性、map-law、尾界或预算当前提。CORRECT。 |

实际所有者由原审计器遍历环境常量、按 `env.getModuleIdxFor?` 的精确模块所有权选出，不按命名空间过滤；故私有或外命名空间生成声明不会被漏掉。实际只有2项＝1 theorem＋1 local-instance definition，0其他显式/生成定义或定理。原审计对每一项打印完整 TYPE，对唯一 definition 打印完整 VALUE，并逐名递归 `collectAxioms`；两项均仅含 `propext, Classical.choice, Quot.sound`。没有因仅审公开头而遗漏实例值。

冻结头11个值逐项核对如下；它们是实际函数/测度，不是新的自由参数：

1. `population := samplePath X`，逐点 `population ω i = X i ω`。
2. `rawEnergy := fun ω => ∑ i : Fin n, (X i ω)^2`。
3. `rawTerminal := fun ω => ∑ i : Fin n, X i ω`。
4. `sigmaSq := ∫ z, z^2 ∂rho`。
5. `scale := Real.sqrt ((n:ℝ)*sigmaSq)`。
6. `normalizedLaw := Measure.map (fun z => z/scale) rho`。
7. `R := Shao.truncationBudget normalizedLaw n 0`。
8. `h := 4*(n:ℝ)*sigmaSq*R^2`。
9. `nu := fun ω σ => energyCutoff (population ω) h σ`。
10. `jointLaw := mu.prod (uniformPermutationLaw n)`。
11. `L := fun J p r => sourceRetainedRemainder J (eventCompletionKernel J Q) (halflineDerivative J) (population p.1) x (nu p.1) r p.2`。

实际完整展开 TYPE 明示 product 的排列可测空间使用本模块实例，积分确在这个 `jointLaw` 上，`L` 中末坐标确为同一个 `p.2`。证明局部 P、lambda、Phi、kappa、L0、S0 六个完整值也已读；没有全局/private helper 或隐含新假设。

## 逐段证明审查

源58–64直接从 qualified canonical 定理取同一个普适C；此时所有原空间、律、桥律、n、family和x都未引入。概率实例由显式输入恢复，没有提高假设。源65–78用有限二阶矩与正二阶矩的既有 geometry 得 h>0、R≥0；`AEMeasurable.of_eval hX` 给实际原值 population 的AE可测，未替换成可测版本。energy为定义恒等，终点通过 `prefixSum_length` 得有限和恒等，均逐点包含AE异常点。实际 cutoff 全局可测与 population 合成，得到逐σ的原cutoff AE可测。

源79–102的 x=0 分支不调用正x canonical 预算。假设 sourceAlive 后在其前缀条件取k=0；实际墙为0且前缀和0，upper得到0<0，lower得到−0<0，矛盾。r<n时内层存活指标为假；r≥n时外层为零。因此每个实际L及有限绝对和逐点为0，真正常值函数可积；总积分0≤CR由C>0与R≥0支付。

源103–130在x>0时设置 `P=pi rho`、`lambda=uniformPerm`、`Phi(ω,σ)=(population ω,σ)`。对每i，IdentDistrib给 `map (X i) mu = rho`；AE独立向量的 joint-map API于是导出 `map population mu=P`。这里使用的 pinned `iIndepFun.map_fun_eq_pi_map` 接受AE可测，未错用旧 Measurable-only finite iid 头。`AEMeasurable.prodMap`及 `map_prod_map_of_aemeasurable`（lambda为有限概率测度，满足SFinite）推出 `map Phi jointLaw = P.prod lambda = revealLaw P`。这是完整配对律，sigma坐标没有被打乱、重新抽取或丢弃。再构造 `IdentDistrib Phi id`；map-law是结论中的证明步骤，不是输入。

源131–144正确满足每个实际 API 的条件：actual cutoff用h>0；eventCompletionKernel给F可测；明确的 hReflection 给实际半线导数可测与 KernelBounds 4；P为概率律，x>0。`source_parts_measurable_integrable`给逐σ/r的L0可测与每r在revealLaw P下的 genuine Bochner 可积。有限排列空间离散、可数，`measurable_from_prod_countable_left`把第一项提升为联合可测；绝对值及有限和给S0可测。没有将实积分的默认零值误当可积性证据。

源145–159取 canonical 实际预算的有限绝对和可积与CR结论。按完整值，`L0 J (Phi p) r = L J p r`、`S0 J (Phi p) = ∑r<n |L J p r|`以及kappa对应式均逐点定义相同。故 `IdentDistrib.comp` 后的 `integrable_iff.mpr` 真实转移每项L和有限绝对和的可积性，`integral_eq`逐半线转移积分；相加得同一C、同一R的最终预算。没有只证明重新排列向量的边缘分布后误判与sigma的依赖。

## 边界、原子与范围

n>0与原源n≥1一致，无n≥2假设；n=1的唯一秩和有限排列正常覆盖。排列空间有恒等置换，均匀概率律有效。重复数值仍按不同标签排列，无连续律或无原子假设。原空间无需标准Borel、完备化或可分性；只用给定可测结构与AE API。

`sourceAlive`保留raw energy>0、终点严格内部及全部严格前缀条件；`sourceRetainedRemainder`还保留r<n、r<nu与T>0。故零能量原子、κ=0、r≥n、零未来时间均由相同守卫处理。cutoff为首次严格T<h；T=h不被删去。小步阈值b²≤T/2及墙命中等号的crossing分支均由同一实际函数原封搬回，不靠忽略等号零测集。rho可无界且第三矩无限；本头没有高阶矩或支撑界。

**x=0的精确范围须保留：**这里证明冻结 `sourceAlive` 的扩展，其前缀量词含k=0，所以L恒零。`main.tex165–166`明确原一侧最大值排除时间零，原文 retained 预算也在x>0陈述；本结果没有证明x=0时该最大值事件与此 sourceAlive 等价。它不妨碍冻结定理正确，但不得据此宣称原一侧x=0比较或原根已闭合。

## 原文与旧 qualified 依赖

实际只读原文位于 `C:/game/shao/current/c12/`。main.tex SHA256为 `beb00f718487e36de433175c97f1d500cb48e7a92ce5bd5ad5d62bb132122d06`，supplement.tex为 `b99f2ac4d2f39dd39772d98a5702b7a923c2f10f8730a08fc1b4cd6bba4742bd`，与manifest相符。实读的原文范围为：main150–181（原iid/finite2/原R及时间零区别）、890–955（raw population与独立uniform标签揭示）、981–1038（三域transfer的B/E/G边界）、1077–1109（实际状态及CR支付）；supplement3913–3930（原R/h）、4360–4400（local profile）、4534–4600（κ、实际L指标及cn:paid）。

原能量、终点与归一化对应原文Q=ΣX_i²、ΣX_i及R_n(0)，没有把rho误假定为方差1/n；Lean的Q在本头为桥噪声律，不与原文raw能量Q混淆。原sourceRetained、projection、completion extension、cutoff的完整值和所有被调用公共头均已逐项读取与新证明交互核验。

直接复用 SourceActualLocalProfileBudget source `76d9019141bf7548e38b58fac1f7a7a5fc36e52f86f33951a7fdd8d185b9d587`及原attempt008 object `878d115de7bd5fcc77f6d372b193ca9c58d1779a8d5ae257246b2b8b22b50454`。根qualification SHA `7f6e626624b28f350e47072a21afb9527225d5a3c28ba8831408b6d9d8b5f1c7`，完整独审MD/JSON SHA分别 `b3dd2ddb48f2f1ea7d4188dce73e930c70dcb35426cf70aad6ab03b648095e04` / `1f64aa34160c01c339b6da7314893d3ede4777f34798bef2a3d13f59561090b9`。其完整526行、29所有者、5值与递归AX已qualified；本轮不重审旧proof。另核v78接受映射：PR293/main `acdc8bc99e7f8e75b7ef6925589c678c6fe85255`，历史qualification内 integratedInMain=false未被改写。

**HalflineReflectionIdentities Q仍是显式未支付的实际Brownian/bridge事件completion反射识别前提。**本证明调用它以获实际半线kernel资料；没有自己证明反射公式与实际Q的识别。interval解析/PDE/Taylor/local预算、interval负overshoot、terminal E、initial G及完整B/E/G装配仍未由此结果闭合。没有对独立新颖性作主张，此处贡献范围是已qualified canonical结果的实际AE原family消费者。

## 原服务器证据与不可变绑定

既有检查环境为 Lean `leanprover/lean4:v4.36.0-rc1`、mathlib `807d3836b165983210ee2ecf3cd28f239436949c`，共享只读package view `shared-v34/packages`。新源的原成功attempt002 object为 `003463e2e6246922453ba6f13577bcbf8db5184317cd7edd6a03ec514caa69bf`；工作树被审计导入的 `.olean` 实际realpath就是该原对象。旧依赖导入对象也实际指向原attempt008，哈希一致。原作者收据记 kernelExit=0、auditExit=0；成功kernel全文仅告警，实际完整types/values块连续包含于原auditlog，末尾计数2/1/1/1符合所有者图。

| 不可变证据 | SHA256 |
|---|---|
| attempt002.log | `864b4ac3e340ebcd7e1d0c8a8aaf1ec5bff4b1dfc22fb2573aba488b173b0318` |
| owned-audit.log | `e4b5c3aceeb56b273940520ede7de8e160a7a26694c929eba2a6c66a0accf510` |
| OwnedAudit.lean 原驱动 | `b2a2ea8f498eaaea7127a76511146c3015d5a8d71a54cce77a9eab124363f1f7` |
| actual-owned-types-and-values.txt | `556ebee3c286b34f43642443a0a5a065d9a245759e5d3f4494b82f2aa209e96a` |
| owned-audit.json | `00b1b57503870fa4e7a82294b24567330230c5d34f0cbc1dfab86f424f7aabdd` |
| receipt.json | `221f1a340739f9e76f4f113b4bcc304f9ecab3ded8421cd9f0325f4a1f3d0cf5` |
| 作者 RELEASE.json | `9a83f4d9ac2b2843f11e036d2b0bd69ffdc9abd9945eeef72e8997992c12f65d` |
| frozen-comparison.json | `903263ebf3b47aa4812ddf8f5a22632fbfa9e406c4afbbf0bd78c30d49e033e4` |
| dependency-bindings.json | `f1895014296e2980f3127ba0942eebdf4976b36e9d3a048c2aa1870e00dd4a35` |
| publication-api.json | `685a10309902fd3fc32bc57a5d69c6e09a9caaf716ba0e3b2f1523f2d6b99d96` |
| 已保留原失败attempt001.log | `b2989196801d696414e296e40af89e7318e94be2d8a1a1f355da2778e24f498b` |

本轮只读broker响应及全部本地哈希清单保存在审查目录。第二只读查询在已取得全部核心证据后，因为服务器无rg而退出1；保留原响应，第三响应仅以pathlib补读所缺的countable-product API，没有重跑任何Lean/AX。另一本地纯文本比较初次因空白delimiter失配报ValueError，已只修正比较器后核对通过；未改生产源或旧收据。成功旧检查未因这两项只读/文本查询重放。

来源头部保留“candidate only/no checks”的历史注释，冻结MD也保留尚未激活时的历史说明；这些不影响已由后续精确activation/原收据绑定的声明、证明或证据，没有为文字修饰改动冻结字节。

## 释放与遥测

无数学或证据 blocker。结论为 **CORRECT（冻结陈述、完整源证明与上述精确对象版本）**。根可复用本次完整最终审查作精确source acceptance，无需因进入根或上下文切换再作同一proof的重复审查。

请求配置为gpt-6.1-sol/xhigh；本上下文不能读实际运行模型/effort元数据或token遥测，实际字段及input、cached input、output、reasoning-subset均分别null，不作订阅百分比估算。所有审查工具调用已结束；随后单独写不可变reviewer RELEASE，writer/execution released=true、heavyActive=false、inflight=[]。本任务无进一步单元授权；未编辑生产源、作者证据、旧qualified文件或共享实现，未合并PR。
