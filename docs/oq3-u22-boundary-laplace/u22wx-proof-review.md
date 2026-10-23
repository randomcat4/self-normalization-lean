# U22w / U22x 独立完整最终证明审查

STATUS: CORRECT
W_SCALED: CORRECT
W_WEIGHTED: CORRECT
X_CUTOFF: CORRECT
BATCH_INTERFACE: CORRECT
PRECISE_GAPS: NONE_IN_FROZEN_BATCH_SCOPE

日期：2026-10-23。本上下文为本批唯一 fresh 独立完整最终审查员，与实现作者分离。调度指定 gpt-6.1-sol / xhigh；本上下文未切换模型、未派生上下文。采用 math-theorem，不采用 math-ultra。工具没有提供可独立读取的模型运行时签名及输入、缓存输入、输出、推理子集 token 计数，故不编造这些观测或订阅比例。

完整阅读 W 的 91 行和 X 的 75 行精确 Lean 源码、两份完整冻结范围、全部 3/3 实际归属声明的完整打印类型，以及必要旧依赖接口和原源段落。全部新证明均作逐步数学审查；结论不只来自编译退出码。全局定义值为 0/0，局部 let 值亦逐项检查。仅复用精确源码绑定的已有服务器 kernel / 全归属递归公理证据，没有重编译、重跑公理审计或本地 Lean 调用。唯一写入为本报告。

## 1. 权限、精确版本和完整覆盖

已读取适用 AGENTS.md、math-theorem 及所需引用、SERVER.md、streamlined-acceptance-current.md，并定向读取 TEAM、REGISTRY、接管与重启入口的当前相关字段。OQ3 当前有效所有者为 01a1669a-bca1-75e0-9d87-d07baee7b90a，旧写者已释放，新写者已激活；本审查不取得 lane 实现写权，不修改共享文件、冻结源码、原源、缓存或版本锁。不启动 SOURCE / preflight / grant / prefix 流程。

本地目录：C:/game/shao lean/drafts/oq3/。服务器工作树：/root/rivermind-data/shao-lean-20261021/workspaces/lead-oq3。只读观测的当前分支为 feat/oq3-boundary-laplace，HEAD 为 3346440dea28ce226bad375c62b288163ea7479e，与收据父提交一致。

| 单元 | 模块 / 精确源码 | 行数 / 字节 | SHA256 |
| --- | --- | --- | --- |
| W | Shao.OQ3.BoundaryLaplaceScaledError / u22w-source.lean | 91 / 4437 | c4bf02eae7aceeb5febe2689f57e6aecdba59ac640a121ae2b82d2bce098bd29 |
| X | Shao.OQ3.BoundaryLaplaceCutoff / u22x-source.lean | 75 / 3891 | 53cd43f6aba9d97493b0cbf951ca1c8763ffa97a825f42e8a0106ba949a44b94 |

两份源码均严格 UTF-8、LF、CR=0。本地冻结源码、服务器当前对应源码、各 run 保存的 source-01.lean 逐字节同哈希。冻结范围 W hundred-fourth-unit-scope.md 为 46 行 / 2783 B，SHA256 c674b0286cbdf41bc5d664ade60f81b65ca9e069cdaf811910c04a1eb314b2ef；X hundred-fifth-unit-scope.md 为 35 行 / 2121 B，SHA256 01bda2105b8a3d39df4178e050b16572dbb2c7000abbd1fb3192cab232448c2b。服务器 scope.md 同哈希。三个完整声明逐一与冻结声明核对，空白规范化比较也全部相同，没有改对象、量词、假设或结论。

| 实际模块所有者 | 源码声明 / 证明范围 | 完整实际类型覆盖 |
| --- | --- | --- |
| Shao.OQ3.boundary_taylor_scaled_error | W7–35；W7–16 声明，W17–35 证明 | W actual-types 的完整第一项 |
| Shao.OQ3.boundary_weighted_scaled_kernel_error | W37–88；W37–54 声明，W55–88 证明 | W actual-types 的完整第二项 |
| Shao.OQ3.boundary_weighted_scaled_cutoff_error | X7–72；X7–25 声明，X27–72 证明 | X actual-types 的完整唯一项 |

W1–6、W36、W89–91 与 X1–6、X26、X73–75 的导入、命名空间、section、空行和收尾也全部读取。W actual-types 共 42 行 / 2117 B，SHA256 83668eae84927f057b6f7ecb364d3369fbce05273cf365bdc310d1e44ae91a65；X 共 29 行 / 1607 B，SHA256 bcab7693e26964121e3ac1629d8cd30714535b0281cb6758974000ed84097f3e。两份类型文件均与服务器保存文件同哈希，并与完整 audit.log 的对应 DECL / TYPE / AXIOMS 内容一致。

实际归属数由审计环境按 getModuleIdxFor? 枚举导出，再核对成功日志和实际类型名：W 恰为 2 个 theorem，X 恰为 1 个 theorem；没有私有或生成额外归属声明，没有全局定义或待补读 definition value。审计不只扫描公开目标名单。源码扫描没有 sorry、admit、新 axiom、unsafe、native_decide。

## 2. 完整声明的语义和必要旧接口

三个声明都是任意实值函数 F（及 A）在实二维坐标上的通用消费者。局部 Taylor、coercivity、amplitude 条件均对所有实 r,z、在闭矩形 |r|≤rho、0≤z≤rho 上量化；它们在 t,u,v 之前量化，不依赖某个待证误差结论。W1 假设 CF≥0、0<t≤1、v≥0 和缩放点位于该矩形，不要求 lambda 或 Lambda1 正。W2 另有 CA≥0、d>0、d≤c、d≤lambda、d≤Lambda1/2，以及完整局部下界和幅变化界。X 保留 W2 全部条件，并要求 rho>0，但移除缩放点位于矩形的限制，通过明确的 if 截零来得到所有 u∈ℝ、v≥0 的结论。打印实际类型精确保留这些量词、函数值、t² 除法、符号和不等式。

必要依赖 V 的精确源为 u22v-source.lean，49 行 / 2363 B，SHA256 5fbfe14dd8e6cf5bb36269c7b988d212e55cb4f0ba6eb5b943337581ed0f1ae7；服务器当前 V 同哈希。已核验既有 u22uv-proof-review.md 的 CORRECT 范围及 SHA256 09fcc0c7b78f3ac2eec58e30142ea588303c2d07d15ec78978f8dae0ca31b2f2，复用已完成的完整旧证明验收，没有重新开启 U/V 的完整审查。此次完整读取 V 源以核对 W 实际调用的接口：a,b≥D、|a-b|≤E、|w-w0|≤Q 推出 |w exp(-a)-w0 exp(-b)|≤(Q+|w0|E)exp(-D)。它允许任意实幅 w,w0，不暗加幅非负条件。

定向读取 R/T/U 的实际完整公开类型，并核对 Q/R、S/T 既有独立报告的 CORRECT 范围，不重审旧证明。R 的实际 F 使用同一逆图表和真实 Legendre 局部表达，给出 lambda=-theta.2>0 及三项 Taylor 界；T 的实际正下界仍以 Lambda1>0 为条件；U 对给定同一图表的真实逆协方差平方根幅给出正局部半径、正系数和 |A(r,z)-A0|≤C(|r|+z)。因此本批假设具有已建立的生产者接口来源，不是把想证明的 scaled/cutoff envelope 直接列为假设。

本批仍是这些接口的通用消费者，并未在 Lean 中声称已经完成所有实际图表、共同半径和常数的最终装配；未来实际实例须保证使用相同 F/A/图表，限制到各个正半径的共同子矩形，并提供同一个正 d≤c,lambda,Lambda1/2。尤其不能由 T 的条件式接口反推原源的 Lambda1 正性已经无条件闭合。这是冻结范围本身，不是本批证明缺口。

## 3. Wscaled：除法、系数与阶数

W18 从 t>0 得 t²>0。W19–24 的 hscale 把两个主项放入同一 t² 分母：lambda(t²v)/t²=lambda v，(Lambda1/2)(tu)²/t²=(Lambda1/2)u²；field_simp 使用 t≠0，后续 ring 只处理合法的实数代数。W25–26 用 |N/t²|=|N|/t² 和正分母等价变形，没有改变不等号方向，也没有在 t=0 使用除法。

W27 对 r=tu、z=t²v 使用原 hbound，z≥0 由 t²≥0、v≥0 得到。W30–32 中 |tu|=t|u| 使用 t>0，三项精确变为 t³|u|³、t³|u|v、t⁴v²。其和乘 CF 后恰等于 CF·t³·(|u|³+|u|v+t v²)，没有把 t⁴ 误写成 t³，也没有漏掉混合项。

W28、W33–34 利用 v²≥0 和 t≤1 得 t v²≤v²；乘数 CF·t³≥0 来自 CF≥0、t≥0，因此吸收方向正确。W35 将 CF·t³·P 写成 (CF·t·P)·t²，其中 P=|u|³+|u|v+v²，恰闭合 W26 变形后的目标。该推导不需要 u≥0、不需要 v>0，也不需要 lambda、Lambda1 为正。

Wscaled verdict: CORRECT。没有冻结范围内关键缺口。

## 4. Wweighted：共同指数下界与幅误差

W56–58 的全部局部 let 值为 a=(F(tu,t²v)-F0)/t²、b=lambda v+(Lambda1/2)u²、D=d(v+u²)，与最终目标一致。W59–65 以 t²>0 将 coercivity 除以 t²；c(v+u²)t²=c(t²v+(tu)²) 的恒等式正确，无须 c 另行非负即可作该正分母变形。

W66–71 中 v+u²≥0，故由 d≤c 得 D≤c(v+u²)≤a；分别将 d≤lambda 乘 v≥0、d≤Lambda1/2 乘 u²≥0 并相加，得到 D≤b。共同指数下界同时控制真实核与主核，未把 Taylor 小误差误当成全空间指数上界。

W72–73 正确调用 Wscaled 得 |a-b|≤CF·t·P。W74–80 对幅误差先使用原 hamplitude，随后 |tu|=t|u|，t²v=t(tv)，得到 CA·t·(|u|+tv)。由 t≤1、v≥0 得 tv≤v，并用 CA·t≥0 保持方向，得到 Q=CA·t·(|u|+v)。整个过程允许 A0 和 A(tu,t²v) 为负。

W81–86 以准确的 a,b,w=A(tu,t²v),w0=A0,D,E=CF·t·P,Q 调用 V 的 weighted 比较，所有接口条件均已逐一证明。W87–88 只是把共同 t 提出，结果为 t·[CA(|u|+v)+|A0|CF·P]·exp(-d(v+u²))，与声明逐字一致。|A0| 不能省略，本实现保留了它。d>0 虽未被本点态推导显式使用，但保留了目标正衰减包络的强度；unused hd 警告不构成数学缺口。

Wweighted verdict: CORRECT。没有冻结范围内关键缺口。

## 5. Xcutoff：内外两区的完整检查

X28–31 的局部 let 为 B=CA(|u|+v)+|A0|CF·P、T=|A0|/rho·(|u|+v)。B≥0 依赖 CA,CF≥0、v≥0 及绝对值/平方的非负性；T≥0 另用 rho>0。没有把一个可能有符号的乘数用于不等式放大。

X36–44 的闭矩形内区，if_pos 保留实际缩放核；Wweighted 的所有 F/A、常数、边界条件及 hrect 两项准确传入。X43–44 用 T≥0、t≥0 和 exp>0 将 tB 的包络扩大为 t(B+T)，方向正确。

X45 的外区，if_neg 后原误差恰为 |A0|exp(-b)：zero_sub / abs_neg 消去外侧负号，abs_mul 与 exp 的严格正性正确处理主核指数。外区不需要对 F 或 A 施加任何矩形外估计。

X46–54 证明 rho≤t(|u|+v)，并完整覆盖失败原因。若 |tu|≤rho，则 hrect 为假强制 rho<t²v；由 t≤1 乘非负 tv 得 t²v≤tv，而 t|u|≥0，于是 rho≤t(|u|+v)。若 |tu|≤rho 为假，则 rho<|tu|=t|u|，再用 tv≥0 得同一结论。纵向失败时 t²v≤tv 的吸收明确使用 t≤1 与 t,v 非负；两种失败无需同时发生。

X55–61 仅在 rho>0 下除以 rho，得 1≤t(|u|+v)/rho。乘 |A0|≥0 后，使用实数乘除代数得到 |A0|≤tT。因此缺失的主核质量确由额外的 |A0|/rho·(|u|+v) 项控制，而不是忽略 cutoff 外部。

X62–66 与 Wweighted 相同地证明 D≤b，再以指数单调性得到 exp(-b)≤exp(-D)。X68–69 的两因子乘法使用 exp(-b)≥0 及 tT≥0，故 |A0|exp(-b)≤tT exp(-D) 合法；X70–72 利用 B≥0 再扩大至 t(B+T)exp(-D)。最后的包络与冻结 X 声明完全一致。

Xcutoff verdict: CORRECT。没有冻结范围内关键缺口。

## 6. 边界、退化值与量词攻击

u 无符号限制；所有涉及奇次幂的位置均为 |u|³，混合项为 |u|v，缩放绝对值使用 t>0，因此负 u 完整覆盖。v=0 时所有下界和吸收仍成立，未用 v 的严格正性。t=1 被包含，t=0 和负 t 被明确排除；t² 的所有除法只在 t>0 后使用。CF=0、CA=0、A0=0 都不引入除法或错误符号；幅无需非负。

矩形边界 |tu|=rho、t²v=rho 归入内区，生产者条件也是 ≤；外区按严格失败处理，不遗漏边界。X 中 rho>0 且 u=v=0 必在内区，外区推导不需另补该情形。W 不要求 rho>0，是因其只在给定局部点条件下成立且不除以 rho；X 新增 rho>0 正是外区比例控制所需。d>0 及 d≤lambda,Lambda1/2 保证声明确实使用共同正衰减系数，但本批没有声称已经证明包络可积。

各常数和局部全称条件先于 t,u,v，故固定数据后同一个多项式乘 exp(-d(v+u²)) 对所有允许 t 一致；未把逐点选择的常数误报成统一常数。X 的全局只指 u∈ℝ、v≥0 的截零函数点态结论，不是对原始 F/A 的矩形外全局控制。

## 7. 精确服务器证据和公理覆盖

服务器 run 为 /root/rivermind-data/shao-lean-20261021/runs/oq3/u22w-20261023 与同级 u22x-20261023。读取并核验各 run 的完整 build-01.log、audit.log、Audit.lean、收据、源和实际类型文件；文件哈希与本地工件及收据相符。既有成功检查使用 CPU14–17、native 8192 MiB、jobs4、autoImplicit=false，单 heavy lane 限制保留；本审查没有发出 Lean / lake 检查命令。只读确认当前 lean-toolchain 为 leanprover/lean4:v4.36.0-rc1，mathlib Git HEAD 为 807d3836b165983210ee2ecf3cd28f239436949c，均与固定版本一致。

| 证据 | W SHA256 | X SHA256 |
| --- | --- | --- |
| receipt.json / 本地对应 receipt | d494c89074757c36e138960fec4a3961a5d64b751f441a9bfcf408f1a7a71c9c | 153d365717630b1c3e0de10f0fcfec58ccc2c00d38ee800d78fff77d995ce318 |
| build-history.json | 7888c5a5e14ff83ba57d65842107972a217fc1efbd342f863299e9bb4210480e | ea49bff36fa1496924b229d9ecd3bc22080414c17b33e6b6a7324793c201a344 |
| build-01.log | e083328a23e1f8e2cadbb1a7c6cea53682ef0bc30c3bc689a26eda662626dfaa | d17a20240b8704d1c23055caa8883d3be42ffefbfa9e86e3e979577ac02dd405 |
| Audit.lean | a543fa54a27ed4f374dec7823e4179c5088f11c3e057893b70034f75b1ad4ef4 | eb5b19e19a29ac7776b04fb319c4138b9dc00e742c20a3503c229df3ef77e9c0 |
| audit-record.json | 02390c3fb667a56a6a7d92242934c5b417bcea9cf2ba857ff46ab8d0d1248350 | 7801744d36706196cc5bc82a346469313d3e893a85248fffb5b8921e0bac156d |
| audit.log | 030e62f6d66e6b99881abf8a8b6a21ef824efdf7c5e38ac06a1455a03574fb52 | 7f0b58e90f923f508e184b000d0190fe6660103ac270fcb45eb496ba7e3f1452 |
| audit-environment.json | dbd5931ec9c88f1d968f22c145411bf3e8fa2f587aaad86550c580da3be0ab6a | 029340a3b8334926bbd39070af4fadb578c4c080c47e924a3005f60e40312335 |

W attempt01 完整 kernel 成功 exit0、6.647954409942031 秒；AX 成功 exit0、5.458657406270504 秒。X attempt01 完整 kernel 成功 exit0、7.04899226129055 秒；AX 成功 exit0、5.523436609655619 秒。没有失败版本被隐去，也没有为了本次审查重放成功门。

两个 Audit.lean 完整按实际模块所有者遍历所有常量，拒绝新增 axiom，并对每个所有者用 Lean.collectAxioms 递归检查。成功日志明确输出 W 全声明=2、全定理=2、冻结定义=0，X 全声明=1、全定理=1、冻结定义=0，并各有 AXIOM_GATE PASS。全部三个实际声明各自的递归公理恰为 [propext, Classical.choice, Quot.sound]；没有缺失私有、生成或定义值覆盖。现存对象只读记录：W .olean 为 fd4904b34868cc51622118741f38f762366be5efafa0571659e88ec814e8a00a（455624 B），X 为 152711f7a5ac9eebdc7fd0b4e063d4be4187c4dd726f7a54419c793be2621893（251160 B）；必要 V 对象为 780eb1879be224113235fcbba8d1330c01cf7836b0db3448e5b20d772e8c63a2。

W 原始成功日志包含 ring normal-form 建议及 “ring tactic failed to close the goal” 建议文本，随后无 error，完整 kernel 记录为 exit0，精确源码的全实际类型和全归属 AX 日志也完整通过。该建议不能独立解释成完整证明失败；本审查另行逐步验证了其实际代数恒等式和不等式。W 的 unused hd 及通用 Lake 本地变化警告保留。X 的 if_pos / if_neg deprecation 警告同样保留，不为消警告改写精确成功源。没有据退出码跳过语义审查。

## 8. 原源对应、边界与最终裁决

原源只读文件 C:/game/shao/current/oq3/proofs/r2/repair01.md，SHA256 9d2e554838aa15b645aaf74a42468d423fed606aa91c1181d0dddf4e87c57cfd。完整读取本批绑定的 183–210 行，并为核对接口读取 135–182 行。源式(11) 的余项对应 W hbound，式(12) 对应 hamplitude，式(13) 对应 hmargin；183–187 行作 r=u/sqrt(n)、z=v/n 的缩放，对应本批 t=1/sqrt(n)、r=tu、z=t²v。W 给矩形内定量 order-t 核误差，X 加入矩形外截零后的主核补项，确实提供式(14) 路线所需的全半平面点态 envelope。源 209–210 行只要求相对 O(n^(-1/2)) 且无需奇切向项抵消；本批使用绝对值误差，没有虚构任何奇项抵消。

本批没有证明包络可积、积分估计、积分主常数、换元/Jacobian、原坐标缩放因子、相对 O(n^(-1/2))、实际概率或原 root B/D。X 的截零外区估计也不能替代原坐标矩形外真实概率质量的远层控制。原有实际谱、(WC)、0<beta<2/5、矩条件、全局 saddle/rate gap、Lambda1 正性、远层概率及外部结果归属要求全部保持原状态；通用消费者假设不把这些义务默默消去。全部原根闭合边界保持，辅助点态结果的接受不构成原式(14) 或原研究根接受。

最终分别裁决：Wscaled CORRECT；Wweighted CORRECT；Xcutoff CORRECT；batch interface CORRECT。完整 166 行源码、全部三个实际归属类型、0/0 全局 definition values 与全部新证明均已覆盖；没有冻结范围内的精确关键缺口。机械层面复用精确源的完整 kernel / 全归属递归 AX 成功证据，语义层面完成独立完整 source-to-statement / proof 核对。此结论仅适用于上述精确哈希与明示点态范围，不附带新颖性或根定理闭合主张。

审查完成。报告完成并核对字节后，本上下文停止全部工具和写入，不启动下一单元；后续是否接受或继续由 lane lead 处理。
