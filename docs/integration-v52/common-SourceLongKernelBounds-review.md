# 实际 early/long kernel 独立完整最终审查

STATUS: **CORRECT**

精确接受 `Shao.Probability.SourceLongKernelBounds` 在 commit `682edb5210f761529283ad2bd39c2e56e21b9322` 的版本。完整审查了 1212 行源代码与证明、原文到最终声明的对应、实际所属模块的全部 63 个声明类型、6 个定义值和逐声明递归公理清单。未发现关键数学缺口。服务器已有的精确源内核及公理证据可复用；本审查没有运行 Lean、重新收集公理或修改数学源码。

审查者 `/root/common_long_kernel_review`，fresh `gpt-6.1-sol` / `xhigh`，与作者 `/root/common_highfreq_author` 分离，NEVERAUTHOR。本轮使用 math-theorem，未使用 math-ultra，未启动子审查者。仅本报告与同名 JSON 属于本审查写入范围。

## 精确版本与冻结

| 对象 | SHA256 |
|---|---|
| 源码（63239 字节，1212 LF，无 CR/BOM） | `b963d28937988346d3dccd4673347f17d559c07b675603a07ffd07c3e33dc1b3` |
| 实际服务器对象 | `1b91d692c52f9801766cc6a20c46d61f4e58041eaca4b04f02964d74b93ce630` |
| 根完整声明冻结 | `ddd79b40cf50a8f226502d1d80153965b78fa9b8f8d61efadcc2b811e18beb55` |
| 完整候选声明 | `a8eee4f753641dbbef9fb56671f5ed2888fb74d75e80b1dda2b37e4311343fda` |
| 唯一有效完整源契约 | `949b910427bba705b22996c6d57d842d4ab962d935553d94e267cad3f5665dd1` |
| 实际及冻结 public header（逐字相同） | `80d2585bd2404c631437119b70c1d9a1c3c06b116b102d3d7d1e7968c8d89216` |
| 作者收据 | `523a862504804ce7d1c13ec489d084f45af79e8d68aabdc5f3f05b34e03c7d05` |

本机源、服务器源与冻结 Git blob 的字节相同；该 commit 只增加此单元。未要求整个作者工作树没有已接受依赖或未跟踪后续材料。实际钉死 Lean `leanprover/lean4:v4.36.0-rc1`、mathlib `807d3836b165983210ee2ecf3cd28f239436949c` 已只读核对。

## 原文与语义

只读原文 supplement SHA `b99f2ac4d2f39dd39772d98a5702b7a923c2f10f8730a08fc1b4cd6bba4742bd`，已完整读取 LF621–641、2342–2366、2464–2564；main LF373–388 的 SHA 为 `beb00f718487e36de433175c97f1d500cb48e7a92ce5bd5ad5d62bb132122d06`。对应 realkernel(i)/(ii) 的全空间界及其实际 Fourier 四域证明。根冻结明确批准了锥内使用较粗、但足够推出同一最终结论的中间界。

最终唯一 public theorem 的 `C, epsilon0, L2` 全部位于原始律及其他参数之前。原始概率律 ν0 具有真实二矩可积性、`n∫a²=1` 和原始均值零；x、epsilon、截断预算未变。ρ 是真实 `cond ν0 {|a|≤epsilon/(1+x)}`，μ、m2、m3 和 gamma=m3/variance 都由同一个 ρ 定义，未把条件律置为对称或均值零，也未要求 ν0 全局三矩。结论是实际 `sourceFutureNoiseKernel ρ (n-i) y (w,q)` 的奇一阶和偶标准嵌套二阶导数，所有实数 w、q，无额外 phase guard。自然数减法与 i=n 端点均保留；可微性对 m=0 也成立，正时间分支由实际守卫排除零时钟。

该定理在所写的较宽预算输入下直接证明界，没有把这组输入等同于完整 D3。source 允许缩小绝对 epsilon0；本实现实际支付了早期小性，而没有偷用另一个 eta0 条件。

## 全部证明体与承重检查

- **18–126，Gaussian 与尾轮廓。** 任意自然数阶 Gaussian 矩由真实可积定理得到；变量替换 t=√T 使用 t>0、t²=T，得到精确 `t^-(k+1)` 缩放。G 在 T 之前统一控制 k=2,3,4。`tailProfile p a u=(1+|u|/a)^(-p)` 对 a>0 的可积性从 p=2 缩放，再作逐点比较；逆幂尾主函数在 |u|≥a>0 下合法，无不可积时默认积分零的路径。
- **127–179，实际标记。** 完整消费已接受 cutoff 振幅族的 k=0、theta=0 光滑性、支撑和前三个导数界。标记的零阶及 weighted-v L1 都来自真实 `sourceMarkSine_norms`，以 w=0 支付其局部条件。outside32 同样以实际 k=0 标记调用，并保留 `min(y|u|,1)≤y|u|`；没有自由区域预算或自由标记函数。
- **180–304，实际频谱与加权轮廓。** 两个 spectrum 定义正是原始 raw powers 的半差/半和乘实际 Xi。概率特征函数及实际 Xi 的范数≤1，给全局 D/E≤1。低频半差用已接受 normalized odd-power 实际接口；偶部从同一真实 variance 的 damping、m2≤4V 得 `exp(-Tu²/256)`。加权轮廓的消分母都由 a>0 或 u≠0 支付。
- **305–441，四域切片。** `mark_slice_comparison` 对低域及严格补域构造可积非负 majorant，再作真实 v 积分比较。`four_region_slice_bound` 在 |u|≤b 与其补域分别使用阈值 |u|/a 和 |u|/c，低矩形和真锥没有混同；高域 |u|>b>0 支付 u≠0。j=1,2 的自然数差幂、逆幂尾以及所有系数符号均已核对。此处不把固定 v 的界乘上自由 v 积分。
- **442–553，完整二维积分及 Gaussian envelope。** `hH : Integrable H` 是实际二维假设，应用处由已接受真实反演公式提供。先取范数，再用真实 `hH.norm` 的 Fubini、AE 可积切片与可积主函数积分比较；没有从 uniform-v envelope 推出三重绝对 L1。Gaussian envelope 展成 k=2,4,2,3 的四项，每项可积性及积分加法均显式支付。
- **554–613，真实导数反演。** 标记积分核包含 `exp(ivq) cos(uw)`、真正未平移 k0 sine mark、u^k 和实际 D/E。前两因子范数分别为 1、≤1，故任意 w、q 都可用 w=0 标记界。完整消费旧 odd/even inverse 的可微性、真实 pair L1 和精确常数；此单元不重新假设导数等于形式积分。
- **614–824，实际四域总预算。** `a=128gamma,b=1/(128gamma),c=4h` 给真正四域。所有需要的切片可积性来自 pair L1；低 Gaussian 主函数和三个尾轮廓可积后才求积分。统一 K 的构造 `R=2^31*128^31*4^31`、`S=A*G+A*Cfull*P+D*P+1` 实际吸收七个系数。奇预算为 `Ky[M0/t³+M3(t^-5+t^-3+y t^-4)+gamma²+gamma^10/T^6+h^31 gamma^29]`，偶预算为 `Ky[t^-3+gamma³+gamma^9/T^6+h^31 gamma^28]`，t=√T。锥内、低外和高外各指数与积分尺度一致。
- **825–989，尺度吸收。** 从 gamma≤√T 得 `gamma^9/T^6≤t^-3`，再用 gamma≤2N3 得奇锥界≤2N3/t³；h、gamma≤1 支付高外两项。T≤4/3 给 t≤2 和 1≤8/t³。早期 T≥3/8 给 t≥1/2，实际得到 512(N0+N3)、512；长时间由 M0,M3≤(4/3)T(N0,N3)、y²≤T 得所需 t^-1、t^-3 界。没有漏掉 y 或错误使用正分母。
- **990–1212，最终源支付。** 从原始输入实际取得 ρ 概率/支撑/三矩、正 V、正 m2/m3、`3/4≤n*m2≤4/3`、gamma≤2h 及 gamma≤2n*m3。epsilon0=`min(delta/1024,1/1024)` 真正支付 `(128gamma)y≤delta` 和 `(4h)y≤delta`，且 gamma≤1/512。i≤n/2 给 n≤2m、T≥3/8；于是 `16384gamma²≤1/16≤T`，没有借 eta0。L2=16384、kappa=1/128 给 kappa√L2=1；实际 high-frequency adapter 支付长度和真锥守卫，σ=±1 的零阶 full(c) 经半和/半差给 hcone。`m≤(4/3)Tn` 从真实 n*m2 下界推出，支付长时间漂移及三矩比例。最后 C=`512*B*K` 同时吸收两项实际 Fourier 常数，且先于一切律参数。

## 实际所属声明与公理

按 `env.getModuleIdxFor?` 的实际 owner 选择全部 63 项，而非 namespace/public 前缀：57 theorem、6 definition，其中源码手写 25 theorem/lemma 和 6 definition，另有 32 生成 theorem。生成项是定义方程、显式代数非零简化、Nat.AtLeastTwo 以及已写自然数条件的 omega 后果。所有生成项的完整广义类型也已逐项读取，未只按名字推断。

原完整导出 273881 字节，SHA `439101d3657bb3040c2da51031cbebb2c94a2ffdc7cf6a8684db8b0c970f8dc6`，U+22EF 与 U+2026 均为零。阅读显示仅压缩重复标准类型类实例/投影树并恢复普通运算记号；全部数学量词、类型、测度、函数、条件及六个完整值均保留，原导出不改。逐 owner 覆盖与语义理由记录在 JSON 的 63 行 coverage 中。导出名字序列、原 audit log 与 audit JSON 三者完全一致。

审查过 audit 与 exporter 的完整实现：每一 owner 用 `Lean.collectAxioms` 递归查询，允许且仅允许 `propext, Classical.choice, Quot.sound`。63 项均在该集合内；没有 sorry/admit/new axiom/unsafe/native_decide。audit JSON SHA `a5634c6695f6f81be4958fcffe4e7710a50eac08d0429d60fde025e1f63dca2c`，audit log SHA `cc267775abfc655d54a11940eff4f04ceef61c8f06bdaa0a533c800acd4a327c`。审计器 SHA `1c9740a373f1605af08ddca97ec260d03f9a37a3d89ff31d46b2eba65d5e4283`；完整导出器 SHA `40e78a9655aee3071aae83f5bd960101b7c1955b85cb235d1a58a53d8cf36afe`。

## 原执行退出与可复用边界

已直接读取作者原 JSONL 的定向命令、启动与完成返回，而非依据另一审查者的转述。targeted12 在 `flock taskset lake env lean ...` 后立即保存 `r=$?`，随后诊断 grep 后 `exit "$r"`；原 session40374/chunk3e5f96 返回服务器及本地均为 0。因此这里认证的是正常包装链传递的实际 Lean 命令状态，未把尾随 grep 或组合 shell 的无条件成功当作 Lean 成功。

object13、owned audit、完整类型导出三个命令各自立即保存 `object_rc/audit_rc/export_rc`；前两项非零立即退出，最后即时写原退出 JSON，并以 export_rc 退出。原 session69459/chunkf576a8 的返回及现存 `{object:0,audit:0,complete_actual_export:0}` 一致。该 JSON 50 字节，SHA `4a5af72c94691bd8649d4b5897b2309d580e5a42386b56a195749481967c85a5`。targeted12 与 object13 各 11512 字节，SHA 同为 `ae7de74189cc48fc64f95ce801111c8252de8e67481a563009be8f53ff86c3cb`；仅旧 package-view 提示与源 linter 警告。最终 checks SHA `6608e22905af135253b7470092f033cc7b639dd0bb01a0ac0ba4bbde3fc9d845`。所有这些现存服务器文件的哈希均已独立只读核对。

全部原命令使用服务器 CPU10–13、root-heavy.lock、`-M8192 -j4 -DautoImplicit=false`。本审查仅观察原执行记录及精确现物，没有新的 Lean 执行或独立第二次内核运行。JSON 保留原 JSONL 精确行号/逐行哈希/调用及返回绑定。一次只读元数据查询误将审计脚本定位到 outputs，失败后改读工作树路径；该失败不属于 Lean gate，未修改源或重跑任何成功检查。

## 已接受依赖与范围

十个实际消费的生产者源码均与已接受 v50 source map 一致，实际 worktree 中的对象已测量；直接旧 odd/even inverse、full(c)、outside、mark 与 amplitude 的对象也匹配各自已接受票。完整消费了它们在本单元使用的接口，未重新委派或复审旧证明。v50 receipt SHA `d260630031cc2e9445cf9acac51fbc3962ab3cd9e6494612959b0cda81f17eb9`；各生产者、现对象和既有独审的精确哈希在 JSON 中。

接受范围仅为冻结的实际 conditional-law 全空间 early/long realkernel(i)/(ii) 导数界及其可微性。short(iii)、短时积分/时钟求和、regulator/probability/desmoothing、完整 C1/C2 和新颖性均不在本票认证范围。没有新增原研究根关闭声明；根仍须执行正常的精确接口与整合验收，复用本次完整独审和现有源内核/递归公理证据。

REVIEW_COMPLETE：审查写入范围已释放；无源码写权，无 reviewer Lean/audit 或子智能体任务。
