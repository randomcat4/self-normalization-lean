# SourceFiniteSecondCompactBudget 独立完整终审

STATUS: CORRECT

本审查是 fresh 独立非作者的 math-theorem 验缝回合。审查者为 `/root/finite_second_compact_budget_final_review`，作者为 `/root/true_energy_strip_author`；没有修改生产源、声明、作者收据、作者 RELEASE 或合格旧证据。配置要求为 gpt-6.1-sol / xhigh / fresh；运行时实际模型、实际 effort 和 input、cached input、output、reasoning subset 数值均不对本审查工具公开，分别记 null。没有新增 Lean／AX 执行、生产源写入、缓存写入、合并或子代理。

## 精确版本与完整覆盖

完整读完最终 665 行源及全部证明，完整读完 15 个实际所属类型的 46393 字节导出；也完整读完候选的两头、proof-candidate、source-scope、readonly-api-and-atom-audit、coupling-squeeze-detail。直接阅读原 main.tex 1107–1141 和 supplement.tex 3933–4026，核对 cn:hostcompact、zero、scalar、hostgap 的独立义务。原 main/supplement 只读。

- 最终源 SHA256：`4b653cba9a9f427cd1086a153e702d7d09f684814919f0a46cfff17da335d190`，37194 bytes，UTF-8 无 BOM、LF。
- 原 producer11.olean：`6b28b4f93b43ac3077989dacf8f52677557db9cae07033def1103a5dc306c2bd`。
- 全 actual TYPE：`038eae30b0bbf7bf420b904ccf79a9c10365acdcaf62244eb29454e85996639c`。
- owner audit：`1248ef9aadfd10f883ba1c4676426a49be4c2e55a15ca968983c7e8198e1c9b6`；owner index：`0f47c693e34f75c1080bfee2c6c70b9bd2271fbc801495b82b2be012665372f6`。
- 作者 final-receipt：`24f6a02c0e5c7720eaced7f81755b1799982b139c15c16c9fe90b97416088178`；作者 RELEASE：`1fe81aa07014cb75660f556a70193cd90e1093a11b7d101fb0b35efc63b602f1`。
- source-only commit：`bac90e6959e82b9bfa79e794d65e153325dfbda9`，[PR303](https://github.com/randomcat4/shao-lean/pull/303)。服务器 Git blob 等于最终源和原 source11；GitHub 只读确认同 head、单改动文件、draft=true、merged=false，base 为 accepted v79 main `927797d9d551e4b57e58abfaba7c7604f0cbcca4`。

作者 RELEASE 的全部 34 个绑定文件均逐个核对字节数和哈希。两个完整 public header 逐字节等于 root 冻结；冻结文件 `f6ef9202f8b73a260a0ac264114b883b5c146e4d78848613b1e1a0f53eed9e20`，freeze MD `99e21f4bcb8a8ae8e5272518ae849e0b378059903fbced9a901802b323974c1c`，activation `1ee3b37e88d64a932782101083d4f6aef381b795fe8f36c172a473407828d517`。全 lets、量词、假设不变。预授权 zero-energy import 和已有 Mathlib DCT import 不改变公开数学声明。

## 第一公开头：中心截断与预算极限

第16–255行证明的正是冻结的真实概率律构造。第65–98行由有限二阶矩导出一阶绝对可积，闭截断 cut 满足两个实际上界，center 同时受 K+1 和 L=E|z| 控制。第99–132行逐 K 证明 centered 的 Borel 可测性、2(K+1) 界、真实二阶及 rpow |Y| 3 可积、均值0和两级 map 的概率性。rpow 指数3通过 Real.rpow_natCast 精确转为自然三次幂；没有给原律添加第三矩。

第133–181行对每个实 z 用最终 cut=z 得点态极限，经 DCT 得 center→0、Y_K(z)→z、L²误差→0、v_K→sigma²。Y_K² 与 (Y_K−z)² 都受同一可积函数 2z²+2L² 支配，最终 v_K≥sigma²/2 从正极限推出。每个 K 的律和归一化律都已定义；早期 v_K=0 使用实数全函数除法，并未排除或偷加正方差。

第184–255行对任意固定实 u，scale_K→sigma sqrt(n)>0；在最终方差下界上，以 D(z²+L²)、D=4(1+u)²/(n sigma²) 控制连续核 F((1+u)Y_K/scale_K)。filter DCT 只要求最终支配，完全匹配早期退化情况。两次实际 integral_map 把预算搬回原 mu，得到真实 R_K(u)→R(u)，没有交换 u 的一致极限，也没有改成第三矩率或另一个预算。u=−1 和任意负 u 仍由平方支配及 F 连续性覆盖。首个成功 partial04 的完整第一头及证明字节在最终源中原样保留，抽取内容 SHA256 为 `bb62d07796f96ea771d7843edbaed2cf80e9c853c9851a6e0d276dabdac2a1ec`；本审查没有重跑 partial04。

## 第二公开头：原有限二阶矩 hostcompact

第401–663行中的 C=27C0+16+108/rho 在 law/n 之前选定，rho、C0 来自已合格原 raw one-sided 头。常数不依赖 law、n、x 或符号。实际 P 是 pi mu，实际 energy 是坐标平方和，目标是 maxWithZero(s•a) 的闭弱乘法事件；没有把方差或归一化终点替换为样本能量。

第423–450行证明 R≥0；R≥rho/108 时，两概率目标均在[0,1]，误差≤1 后由 C 支付。第451–460行 x=0 的 maxWithZero 事件逐点为 univ，2Psi(0)=1。没有错误推广为不含空前缀的 upperMax 在0阈值恒越界。

第463–539行只把 p=3 输入用于实际中心有界 pushforward 律 muK。其二/三阶矩和均值由第一头及 integral_map 搬运，正方差只在最终下界后使用。原 R_K→R<rho/108 保证最终 R_K<rho/27；私有 adapter 实际证明 R_K(y)≤(1+y)^3 R_K≤27R_K<rho，使用 raw 头的预算析取分支，不使用 beta 倒幂域，也不要求原律更高矩。A_K(a)_i=Y_K(a_i) 的 Measurable 与 map A_K(pi mu)=pi muK 由实际 pi_map_pi 得到；事件的可测性足以真实搬运概率。

第540–572行只在 Q(a)>0 上使用 f_K=maxWithZero(s•A_K a)/sqrt(Q_K)→f。Bad_K 明确包含 Q>0 且 Q_K=0 或 eps≤|f_K−f|；原 Q=0 不参加该商极限。每个路径的 Bad 指标最终为0，DCT 得 P(Bad_K)→0。第573–623行两个真实集合包含分别给 p≤q_K(x−eps)+p0+b_K 与 q_K(x+eps)≤p+p0+b_K，再把有界律的上下界传到原律。第624–663行选 eps_j=x/(2(j+1))，满足0<eps<x、eps≤1、eps→0；因 x≤1，有0<x−eps和x+eps≤2。Gaussian tail 连续，故保留原阈值原子地得到 |p−2Psi(x)|≤(27C0+16)R≤CR。没有使用 P(f=x)=0。

原 p0=P(Q=0) 的16R由已经合格的真正原 AE iid zero-energy producer 专化到坐标族支付，未把 p0 界作为公开假设。两符号只消费已合格 signed 头和连续的有限路径最大值，未用 law 对称。

## 全部15个实际类型逐名语义

以下私有简称展开前缀均为 `_private.Shao.Probability.SourceFiniteSecondCompactBudget.0.Shao.Probability.`；公共简称前缀为 `Shao.Probability.`。每一行均读过完整 pp.all/pp.deepTerms 实际类型，非仅源码头或名字清单。

| 实际名字（按以上前缀展开） | 类型语义与评价 | 递归AX |
|---|---|---|
| public centered_bounded_truncation_budget_limit | 任意概率 mu、n>0、中心有限正二阶矩；所有冻结 lets 及逐 K、点态、L²、方差、逐 u 预算结论完全保留。CORRECT。 | propext, Classical.choice, Quot.sound |
| public finite_second_one_sided_compact_budget | ∃C>0 先于所有 law/n；[0,1]、s=±1、pi mu 上真实 maxWithZero 闭弱事件误差≤CR。无额外前提。CORRECT。 | 三项白名单 |
| private fsc_vanishing_event_probability | 任意可测空间上概率 P、逐 K 可测事件；每点最终不属于事件推出 real mass→0。常数1支配的真实指标 DCT；无需统一最终 K。CORRECT。 | 三项白名单 |
| private fsc_third_moment_compact_input | ∃rho,C>0，rho≤1/16；真正有限三阶矩中心正方差律，R<rho/27、0<y≤2、两符号的27CR绝对界。它是 qualified raw 头的严格适配，第三矩不泄漏到 public。CORRECT。 | 三项白名单 |
| private fsc_original_zero_mass | 原 pi mu 的 energy=0 mass≤16R，只需有限正二阶矩和n>0。真实独立坐标与 IdentDistrib；sqrt(n sigma²)=sigma sqrt(n) 精确对齐。CORRECT。 | 三项白名单 |
| private fsc_third_moment_compact_input._simp_1 | 在 NeZero 2 下，命题 2=0 等于 False。无目标概率假设。CORRECT。 | propext |
| private fsc_third_moment_compact_input._simp_2 | 在 NeZero 3 下，3=0 等于 False。CORRECT。 | propext |
| private fsc_third_moment_compact_input._simp_3 | 在 NeZero 4 下，4=0 等于 False。CORRECT。 | propext |
| private fsc_third_moment_compact_input._simp_4 | 无零因子且a,b非零时，a*b=0 等于 False。CORRECT。 | propext |
| private fsc_third_moment_compact_input._simp_5 | reduced monoid-with-zero 中a非零，则任意自然数幂 a^n=0 等于 False。包括n=0。CORRECT。 | propext |
| private fsc_third_moment_compact_input._simp_6 | group-with-zero 中a非零，则任意整数幂 a^n=0 等于 False。CORRECT。 | 三项白名单 |
| private fsc_third_moment_compact_input._simp_7 | CharZero add-monoid-with-one 中，任意 Nat cast n 加1等于0的命题等于 False。CORRECT。 | propext |
| public finite_second_one_sided_compact_budget._simp_1 | 任意x属于univ的命题等于 True。CORRECT。 | propext |
| public finite_second_one_sided_compact_budget._simp_2 | ¬(p∨q) 等于 ¬p∧¬q。CORRECT。 | propext |
| public finite_second_one_sided_compact_budget._simp_3 | 线性序中 ¬a≤b 等于 b<a。CORRECT。 | propext |

实际 owner 选择依据 env.getModuleIdxFor? 与目标模块完全相等，覆盖2 public、3显式private、10 generated；未用 namespace/public 过滤。15个均为 thmInfo，defnInfo=0、other=0，因此全非定理 VALUE 数确为0，不存在未审定义或实例值。完整导出有15个类型块，名字集合与 owner index／audit 完全相同。

## 原操作、机械证据与旧依赖复用

三个 helper 的完整头都逐字节保留。独立打开原 session 指定 offset 的真实 FileChange completed 事件，核其 raw line SHA、event ID、line/byte offset、实际 content hash、started/completed 时间与首次 add 事件；heads01 5822<body5850，heads02 5842<body5850，heads03 5911<body5931。稳定前缀18591041 bytes／5931行 SHA `c1e1c8981b6b5830d2a2d8e450eeb89f4ae7790dc1e56f04e9ff145af3f4dab9` 也直接验证。没有依靠mtime或作者布尔声明。body01后来只显式补 `(μ := P)` 以消除测度推断问题，最终完整证明已审；冻结头未改。不重读或改写旧 Terminal helper 的过程证据。

直接读取原会话第6095行 completed CommandExecution（event `exec-2bcc3d8c-afcd-4aab-ac19-5b29b378434b`）：同次调用复制 source11，以 root-heavy.lock、CPU10–13、-M8192 -j4 编译原 producer11，成功后让 audit import 指向该原对象；实际返回 CHECK11_RC=0 和 AUDIT11_RC=0。服务器只读重新核对原 source11、object、rc、check/audit logs 及48个原证据文件哈希。原日志的15个完整 TYPE 段重新抽取后与本地 all-owned-types 字节完全一致；没有额外 VALUE 段。audit 对每个所属常量实际 Lean.collectAxioms，全部仅 propext／Classical.choice／Quot.sound。审查源码无 sorry/admit/new axiom/unsafe/native_decide。check11无error；现有提示仅旧名弃用、未用项、实例建议与linter。审查者最初的只读提示分类器过窄导致一次断言失败，失败收据保留；查清原提示后只更正分类，不重跑任何Lean/AX。

固定 Lean `leanprover/lean4:v4.36.0-rc1`、mathlib `807d3836b165983210ee2ecf3cd28f239436949c`，packages实际指向 shared-v34。raw one-sided 的完整实际输入头已读，C0/rhoStar在law/n之前、2<p≤3、有限p矩和 x-domain OR budget-domain 完整核对；只消费 p=3 的真实 budget 分支。其合格源 `1422e5fea0fe097e7610b75603e666fb9cf86dbcfa8b767e09199cff4dd03546`、原对象 `eca84252844ff358e1473f3d6ba68b2f02b0ce0cfc445eaa2e545a31040010a8` 与作者导入对象相等，旧完整独审/qualification哈希已核，未重复其证明审查。

zero-energy 完整消费头已读，概率空间、AE measurability、iid/IdentDistrib、有限正二阶矩、literal scale/normalizedLaw/rawEnergy 全部对齐。合格源 `9e4380fc2e70a64b6ff7661f5f34cde9c18c1e5537e24b4165faeb46c74aee45`、原对象 `2dbf2e7971700bc33e8fbc80c5146c7ad8ef6c9a5ee2da13dc2f7d082f3d90e5`、root资格 `dea6c4d5d11ba106989978cbf18112d88347b7bfeca6a541eeb1feadb8bb6c8c` 以及其独审/释放/服务器绑定文件的精确哈希均核验，导入只读symlink确指原成功对象。没有再次证明或执行该producer。

FinitePath、TruncationBudget、TruncationIntegrals、Normalization、GaussianTail、MeasurablePath 的消费头/完整所需定义值已读；连同传递依赖 FiniteIID，源哈希等于 accepted v79 源图，实际导入对象等于 accepted v78 复用对象。已直接读取固定 Mathlib 的两个 DCT、pi_map_pi 与 iIndepFun_pi 实际头，逐项核其在此处的可测性、概率性和最终支配条件。尤其 F=z²min(|z|,1)、预算 n∫F((1+t)z)、实际坐标平方energy、0..n最大值及 Gaussian Ioi tail 的定义均与本证明一致。旧证据复用不扩展旧结论。

## 边界、反例与范围结论

n=1、小n、x=1、两符号、离散律、重复值、闭截断等号及原阈值原子均覆盖；R=0未另加正性。早期v_K=0完整定义；最终v_K>0才调用高矩输入。Q=0不作归一化收敛，而真实支付16R。已经完整核对候选给出的两个反例：归一化cutoff 1/2处 gamma2/3可分别不收敛；非对称中心律的全零路径经中心截断后 endpoint恒为−sqrt(n)，不趋原零值。这两项确实排除错误捷径；最终证明只传递连续F组合预算，且商极限明确限制Q>0。

本精确版本证明中心截断基础与有限二阶矩 hostcompact。它没有无条件 scalar closed CDF／hCDF／hScalar producer，没有 actual Brownian 半线初始值识别，也没有完整 initial G 或任何原根闭合。外部 scalar truncated inequality 的归属未被冒认。全部原 C12/OQ3/OQ4/OQ56 根保持 OPEN；OQ3保持 PAUSED_BY_USER。最终数学结论 CORRECT，完整机械信用来自已核绑定的原 check11/kernel/all15 recursive AX 成功证据；本轮复用，不新增执行。
