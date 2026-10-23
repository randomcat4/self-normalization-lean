# 实际调节增量的前缀与求和一阶矩：独立完整终审

STATUS: **CORRECT**。完整阅读最终 202 行源码、两条完整冻结声明、原文指定段、服务器导出的全部 14 个实际所属类型及每项递归公理后，未发现关键缺口。接受范围仅为本模块的通用 iid 实际前缀一阶矩、精确恒等式与无权有限和一阶矩界。

审查者为 fresh、NEVERAUTHOR 的 `/root/common_regulator_sums_review`，模型 gpt-6.1-sol，推理强度 xhigh，使用 math-theorem。没有修改源码、声明、假设、旧报告、公共文件或缓存，没有启动子代理。本审查只写本 MD 与同名 JSON。实际输入、缓存输入、输出、推理子集计数未由工具暴露，JSON 明确留空，不换算订阅比例。审查完成后释放本槽，不自行启动下一单元。

## 精确版本、冻结与来源

- 模块：`Shao.Probability.SourceLindleyRegulatorFirstMomentSums`。
- 作者提交：`e32108dc19228e38d09f8a704a0dbaf58777181e`；父提交 `ea081d727abfd0c0171943da924d464ba9d0b56b`；树 `d0076245837079f439ee85403e70d87d0e35479a`。提交只改变目标单文件；其他未跟踪文件不属于本次审查或验收。
- 最终源码 SHA256：`e0e850c95578ec741669b56acfb3721e34cc8c6f5684a8aee316f7ab1ce59fbf`；9068 字节、202 行，UTF-8 无 BOM、LF、零 CR。已核对本地稿、服务器工作树、提交 blob 与原成功源收据相同。
- 对象 SHA256：`7c36447ba87dc2d4c1a41d3445cfca6fa1ff2841b6b99172d41ab9e1c6aa8f43`。
- 完整冻结文件 `coordination/public-regulator-first-moment-sums-declaration-freeze.md` SHA256 `e689205587ec7cb28507c6580a8e0806c524875f9ed99431a3e40c5576690a87`，冻结时间 2026-10-23T13:13:52.911244Z，早于本提交。
- 原完整候选 `drafts/c12-regulator-first-moment/next-dependency.md` SHA256 `6a9dc058147e85f925d708023c250feb0003138387608ae42668b89470a1ea95`。独立逐字比较最终两条完整公开头，分别匹配，声明 SHA256 为 `b4d408d8462993d24781ab0f37633926016f5f1c54ee0d0e03c383dec20f4d92` 与 `973161f1b4ef2edde1a95264791210f80d1c99fc32aa2a949c73f9debdd2cf51`。没有新公开定义。
- 原文 `C:/game/shao/current/c12/supplement.tex` SHA256 `b99f2ac4d2f39dd39772d98a5702b7a923c2f10f8730a08fc1b4cd6bba4742bd`；完整阅读 LF2137–2174、LF2217–2236。

原文 LF2170–2174 的时间编号为正整数 j，本模块的真实时刻是 j=i.val+1。原文先有 j E U_j=E S_j^-，再有 E U_j≤τ/√j+|μ|；LF2217–2220 将这些实际时刻的界相加。本模块取 τ=√V，完整保留这一精确常数及求和的常数 2，只支付 LF2220 的第一段不等式。后续源参数一致常数及晚时间估计没有随之自动成立。

## 完整冻结结论

ν 为任意实数概率测度，唯一矩假设为 `Integrable (fun a : ℝ => a ^ 2) ν`。对任意 N，P 为同一个 ν 的 N 重乘积测度，μ=∫a dν，V=variance id ν。没有其他概率律、耦合或时刻假设。

`iid_lindleyRegulator_prefix_first_moment` 对每个实际 `i : Fin N` 证明三项：原长路径的 `lindleyRegulator a i` 在 P 下可积；`(i.val+1) * E_P[U_i] = E_P[max(-prefixSum a (i.val+1),0)]`；`E_P[U_i] ≤ √V/√(i.val+1)+|μ|`。

`iid_lindleyRegulator_sum_first_moment` 对每个 N（包括零）证明原长路径的真实函数 `a ↦ ∑ i : Fin N, lindleyRegulator a i` 在 P 下可积，且其积分不超过 `2 * √V * √N + N * |μ|`。JSON 保存两条完整逐字 Lean 声明，不是缩略接口。

## 消费已接受生产者，未重审旧证明

完整读取被调用的 `iid_lindleyRegulator_last_first_moment` 公共接口，确认在 n=i.val 时，它恰在 `Path (i.val+1)` 的同一 ν 乘积律下给出真实末步 L1、精确恒等式和常数 1 界。其参数没有 prefix law、期望界、中心化、对称性或正方差输入。

生产者源 SHA256 为 `c2dcdb409763ba20386e064e6a8ed612bf060677da80442c727289ffc7ab3108`，对象为 `614998314b71f96ba81982605e12742a889cad3447c9e22ec3ef89ffdbeeec06`，均与已独立 CORRECT 的版本一致。已核对先前报告 MD SHA256 `3eaf85ace27cb8093f5690bf95cc8730c71c2463c1c90667e31dfb731a0f4758`、JSON SHA256 `379025c243233f5cc7f19d929880da80f989226aba6810b3e104e022f52a28d6` 的接口/来源与可积性结论，复用其旧证明及 kernel/全所属递归公理证据，没有重审或重跑旧证明。

对实际消费的 `Path`、`prefixPath`、`prefixSum`、`lindleyState`、`lindleyRegulator`、`iid_samplePath_map_eq_pi`，读取其完整相关定义/接口；服务器现有 Basic.Lindley、Basic.FinitePath、LindleyTelescoping、FiniteIID、MeasurablePath 源与对象哈希均与已接受生产者的绑定一致。JSON 保留逐接口哈希。

## 完整新证明审查

L23–31 的 `state_prefix_agrees` 对真实受限递推的时间 k 归纳。零步均为零；后继步都读取原长路径第 k 个坐标、在同一前态上加同一坐标后取 max 0，因此不只是状态同分布，而是逐路径完全相等。所有 k≤m≤N 索引证明合法。

L33–50 的 `sum_prefix_agrees` 将 `Fin m` 与 `Fin N` 中满足 val<m 的指标作双射，保留每个原坐标值；覆盖 m=0。它确实识别原前缀和，没有用路径末尾的总和代替。L52–62 通过加法、取负与 max 的可测性递归证明实际状态与调节量可测。

L64–81 的 `prefix_measurePreserving` 使用固定注入 `Fin m → Fin N, j ↦ ⟨j.val,_⟩`，保持原时间顺序。canonical product 的坐标函数真实独立；每个评价映射真实保测，从而每个边际 law 为 ν。将独立族沿注入限制，再调用 `iid_samplePath_map_eq_pi` 得到完整的真实前缀乘积律。此律在证明中推导，既没有作为假设，也没有从结论性一阶矩界倒推。已核对固定 mathlib 的 `iIndepFun_pi`、`iIndepFun.precomp`、`IdentDistrib.comp` 及可积复合接口。

L97–118 取 m=i.val+1 与真实前缀投影 p，定义 U 为该前缀最后一步调节量、B 为该前缀和负部。`state_prefix_agrees` 与原坐标相等给出逐点 `U(p a)=lindleyRegulator a i`；`sum_prefix_agrees` 给出逐点 `B(p a)=max(-prefixSum a (i.val+1),0)`。这里确为长样本的实际第 i 个增量，没有将长路径末步当代理。

L119–124 调用已接受末步生产者，并在积分改变量之前用 `hp.integrable_comp_of_integrable` 把已知真实 U 的 L1 拉回长路径。该 mathlib 接口只要求保测，不要求前缀投影为嵌入；这正适用于丢弃尾坐标的映射。

负前缀量也是真实 L1：原 h2 在概率空间上使 id∈L2⊂L1；每个实际乘积坐标通过保测评价继承 L1；有限前缀和于是 L1；可测的 max(-S,0) 逐点≤|S|，故亦 L1。等价地，可将已接受生产者所支付的前缀负部 L1 沿 hp 拉回。新源码没有另命名一个负部 L1 局部事实或将它列作额外结论，但这不构成缺口：此事实已由原矩假设实际保证，L128–136 所用 `IdentDistrib.integral_eq` 是合法的无条件积分同分布接口；这里两边均为真实有限期望，不依靠不可积函数的 Bochner 默认零值。

L125–136 从 hp 得 p 与目标恒等映射同分布，分别复合可测的 U、B，运输两项实际积分。L137–141 因而原样取得 `(i.val+1)EU_i=E S_(i.val+1)^-` 和 √V/√(i.val+1)+|μ|，保持同一 μ、同一 V，常数 1 没有损失，也没有加入新的 law 或 bound 前提。

L143–154 设 a=√n、b=√(n+1)>0。a²=n、b²=n+1 和 (b−a)²≥0 给出 `2b(b−a)−1=(b−a)²≥0`，仅除以正 b，得到 `1/√(n+1)≤2(√(n+1)−√n)`。n=0 也有效。L156–168 按 `Fin.sum_univ_castSucc` 分出最后一项，以空和为归纳基，使差分望远镜相消，得全部有限 N 的倒平方根和≤2√N。

L185–189 对原长路径的每个实际 U_i 取得 L1，先以 `integrable_finsetSum` 支付真实有限和 L1，再以逐项 L1 证明执行 `integral_finsetSum`。L190–200 对实际每项期望求和，把 √V 与 |μ| 提出，使用 √V≥0 乘倒平方根和界，得到精确 `2√V√N+N|μ|`。不存在以有限身份代替无限/根定理的提升。

边界核对：prefix 的 i∈Fin N 自动保证 m≥1 与 m≤N；N=0 时 prefix 无指标、总和定理实质处理空和及零右端。V=0 完整保留，从未除以 V 或 √V。μ 可以非零；ν 可以非对称、含原子；重值与 ties 由逐点递推直接覆盖。唯一矩条件保证真实 μ、V 有相应有限矩意义，没有暗加中心化、无原子或生存概率假设。

## 14 个实际所属类型及递归公理逐项

完整读取原始导出的所有实际类型（含 `pp.all` 展开）、每项递归 collectAxioms 结果。审计按 `env.getModuleIdxFor?` 的实际 owner 选所有常量，不按命名前缀或只挑公开定理。14 项均为 theorem，含 2 公开、7 个源私有定理、5 个生成定理；实际 definition 为 0，故无遗漏定义值需读。类型导出名集合与 owner 审计名集合完全相同。

下表短名省略目标模块的统一 private 前缀；JSON 保存每项完整名称、实际类型 SHA256、源/对象/导出日志哈希、完整阅读标记与结论。A 表示 `[propext, Classical.choice, Quot.sound]`，B 表示 `[propext, Quot.sound]`，均为递归公理集合。

| 实际声明短名 | 完整实际类型/证明义务的审查结论 | 公理 |
|---|---|---|
| `sum_prefix_agrees` | 所有合法 m≤N 下，真实前缀的 m 项和等于原 m 前缀和；有限双射正确。 | A |
| `iid_lindleyRegulator_sum_first_moment` | 全部原量词及真实 P/μ/V/有限和保留；L1 后交换积分，界为精确 2√V√N+N|μ|。 | A |
| `measurable_state_prefix._proof_1_1` | k+1≤m 与否定 k≤m 不能并存的合法归纳索引。 | B |
| `iid_lindleyRegulator_prefix_first_moment` | 对真实原 i 的 L1、精确恒等式和常数1界，无结论性附加输入。 | A |
| `sum_prefix_agrees._simp_1_1` | 过滤有限集合成员的 Prop 等式，条件完整。 | A |
| `prefix_measurePreserving` | 任意 N、m≤N 的真实固定坐标前缀投影保同一 ν 的乘积律。 | A |
| `reciprocal_sqrt_sum` | 包括 N=0 的真实 Fin N 倒平方根和≤2√N。 | A |
| `measurable_regulator_prefix` | 实际 U 函数可测，绑定正确原状态和坐标。 | A |
| `sum_prefix_agrees._simp_1_2` | 有限全集成员等于 True 的 Prop 等式。 | A |
| `reciprocal_sqrt_step` | 全 n∈ℕ 的真实实平方根不等式，分母正性由 n+1 支付。 | A |
| `iid_lindleyRegulator_prefix_first_moment._proof_1_1` | 任意 i∈Fin N 保证 i.val+1≤N 的合法前缀算术。 | B |
| `state_prefix_agrees._proof_1_1` | k+1≤m 推出 k≤m 的合法递推索引。 | B |
| `measurable_state_prefix` | 对所有 k≤m 的实际有界反射状态可测。 | A |
| `state_prefix_agrees` | 对所有 k≤m≤N，两个真实递推状态逐点相等。 | A |

以上 14 项全部 CORRECT。完整源码禁用构造扫描为空：无 sorry、admit、新 axiom、unsafe、native_decide。全部传递公理都在标准三项白名单中，没有漏掉 private/generated 项。

## 原服务器成功门与直接退出码

只读检查指定服务器工作树 `workspaces/common-centered-characteristic-v44` 及输出 `outputs/common-regulator-first-moment-sums`；没有执行任何新 Lean/kernel/公理命令。作者已释放 writer，实际 `ps` 中目标 Lean/lake 进程为空；没有将 ACTIVE 租约或派发视作执行证据。

- `attempt02.exit=0`；源日志 SHA256 `fba92798401e89109ac7d84c8cea11527992a1f6b153b3c1d2aada0eebf025a2`。全文只有既知只读共享 sparse mathlib 视图的 local-changes warning。
- `attempt02.source.sha256` 内为本最终源哈希；文件自身 SHA256 `523856010f8bf0dcccfe3d24b31d8ed98cb1bed4de9e337bc5ce15a352e67ca8`。
- `owned-audit.exit=0`；完整实际类型/递归公理日志 SHA256 `6058cb3600b82be8cf7b8d9dcde3a7e4139b898a01d9bf6e9b096eb4e9cf4444`（20443 字节），14 项全读；owner JSON SHA256 `12b2ea3b60f7941ebe4021f589f1f0659e81188a50527a2e7e76f0f550a1f7fc`。
- `owned-audit.source-object.sha256` 同时记录本最终源与上述目标对象；收据文件 SHA256 `c8a08f318dfbb917de858ef90de0bedd810d00e3b4c0d04d5d92ab5fe65e0a69`。
- 审计源码 `OwnedAudit.lean` SHA256 `740d084d4a2e45d539dae3f55b45feff23331729c6c2f1c0caa5512cb7b36ad6`，本地与服务器相同。已完整读其实际 owner 枚举、实际类型/定义值打印、递归 `Lean.collectAxioms`、拒绝非白名单和计数检查。
- 成功源码命令文件 SHA256 `5598e1df49300d0821ad556865706f5b98d1186b6f0ad08a4f3ffc081084e549`；完整所属审计命令 SHA256 `21d3e520094f2b591046ec7b662141c8d0303925061d1f589a9bdfe1d55db062`。两条完整原命令均已读取，且本地/服务器相同：Lean 子进程在 flock/taskset 下直接执行，无管道；随后立即 `rc=$?`，写 exit 文件并 `exit "$rc"`。因此 0 是 Lean 子进程直接退出码，不是后续打印程序退出码。
- 钉死版本实读为 `leanprover/lean4:v4.36.0-rc1`、mathlib `807d3836b165983210ee2ecf3cd28f239436949c`；包视图解析为 `cache-overlays/shared-v34/packages`。原命令 CPU10–13、共享 root-heavy.lock、M8192/j4/autoImplicit=false，符合既有资源约束。
- 原失败 `attempt01.exit=1`、失败源 SHA256 `991bd20b56756d05eaa4296e9b14f3ad89cde8d6709a73087f81c1625eba8ef8` 与日志 SHA256 `a307e995c390288450b0fad12353f421f18313ec71b12f029bb6a31bb05e4a6b` 均保留。没有覆写失败、重跑成功目标或扩大重建。

作者收据本地 SHA256 `14c3d6287520a1861944bf372aec9e1e74bc477a6a1cc35c236d8164e8cdce01`。上述完整命令、逐文件哈希、逐 owner 类型/公理绑定和接口哈希均保存在同名 JSON；原完整日志留在服务器，没有复制到工作区。

## 验收边界与交接

本精确源的两条冻结公开结论及全部实际所属声明可接受为 CORRECT；根验收可以复用本独立完整审查与原成功门，只核验新的实际整合风险，无须因到根层再重做旧完整证明审查或重跑本单元。

本结果未支付 LF2220 最后一段的源一致常数 C，未支付 LF2230–2231 的晚时间 C/n 源参数特化，未支付实际调节量二阶矩、真正源律生存界、能量倾斜及对应矩/漂移预算；不宣称完整 regulators 引理或 C1/C2 等原根闭合。数学新颖性不作新增主张；这是原文一阶矩链的忠实形式化接口。本独立审查结束，释放槽位。
