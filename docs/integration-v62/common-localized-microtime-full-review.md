# 实际完整噪声核微时钟局部导数：独立完整审查

STATUS: **CORRECT**。未发现关键数学缺口、隐藏前提或冻结声明偏移。此次结果覆盖 supplement.tex 895–907、922，并接合已接受的 908–920 尾界；原文 923–927 的真实 Taylor/regulator 期望误差及后续求和仍未完成，C12/C1/C2 根组保持 OPEN。没有新颖性声明。

审查者 `/root/common_localized_microtime_full_review` 是 fresh、非作者 gpt-6.1-sol / xhigh，使用 math-theorem，未使用 math-ultra。作者普通 FINAL 和不可变 checkpoint 已释放全部生产源/草稿写权、无在途操作。完整阅读本模块 1–794 行、完整数学候选及两条冻结公开头/全部 literal values、全部 17 个完整实际所属类型与原公理审计程序。报告只写本票、同名 JSON、coverage JSON 和指定观察目录；未改任何 Lean、候选、旧证据、library 或缓存，未创建 PR/合并，未运行本机或服务器 Lean/旧 DAG/旧 AX gate。

精确版本是 `Shao/Probability/SourceLocalizedMicrotimeDerivatives.lean`：42759 字节、794 LF、0 CR、无 BOM、EOF 恰一个 LF。工作树 `workspaces/common-short-kernel-v51`，分支 `feat/common-localized-microtime-derivatives`，提交 `d2878214808ef611dcf0b3380339f53c8c0fc0b5`，父 `81427457ef601ccf1bfc9ef25ae6fe80e3e99617`，tree `d35dc116a7c35b6da8d75f278fac5ef7b12e2ce0`。服务器只读核验工作树 clean、唯一新增源，工作文件、原 check003-source 快照和 Git 提交字节相同。

| 证据 | SHA256 |
|---|---|
| 完整源 | `bdf57fc81650cf1dbb43d42d70b8d9078ac3fdb00e7637913f1e67f0b7bc1633` |
| 同次成功 -o 对象 | `66feb3555bc4481e36a3698bfcae00e3d7a1a8615f8cb43f19e98315c93a9152` |
| 完整冻结 | `e9657dcd55df751d087f0ce261586dd459ed54bef2a1f0ff3c899ca565cfd279` |
| check003 原日志 | `0fb21274dedc9fbea753cbc19f4c01692f4a70e548b5698429ee4f559c2bb552` |
| 原 owned-audit 日志 | `c2915792579b94858ca42eb0c49f9dffd5be9477b6160f0cc2dd23796ce3db79` |
| 原审计程序 | `016c7c4afb2a5029845ce89531145fce3a9ebe7c41b343dc4d9fcff193276e07` |
| 完整 owner/传递公理 map | `40ba70874572d4c4c8a498b83366f3a923a837081561cd242584c6a7a337ad71` |
| 全部 17 个完整 actual types | `d7a99e49dc6d223fa2a05b9b610b3925363b0f423c0cba7fd443d3136f67c813` |

两条公开头与冻结文本逐字相同。第一头不加 clock 前提；第二头 L2、epsilon0 及其界在原始律之前，保留原始仅二阶可积、均值0、n raw2=1、真实预算与固定 x 条件律。冻结允许新增 private helper THEOREMS；实际为 15 private + 2 public = 17 theorem constants、0 definitions、0 额外 generated constants。源声明扫描、环境实际 owner map、原日志全部类型/零 DEFINITION_VALUE 互相一致；定义值集合真实为空。Unicode U+22EF、U+2026 和 ASCII 三点在源及实际类型中各为0。

1. **真实源语义和实际对象（18–65、257–320、489–517）。** 已读原文 supplement 895–927、463–483、522–531、538–545 与 main 546–571、610–625、650–667，以及实际 Path/prefixSum/energy、truncationBudget/truncationF、cutoff/test/scalar/chord/full-noise/kernel 定义。核中保留同一原固定 x 条件律、真实有限积路径及未中心化 S；两族各八条弦和独立 gamma V0 按实际 map 完整展开。`lm_kernel_scalar_eq` 对 map 和两次产品积分所需的可测性、[0,1]主导及可积性均显式建立；没有换成纯标量总噪声或使用未接受的 SourceBoundedYReflection。

2. **严格区间与两次求导（31–245）。** gamma>0、y>=0 给 lo<=hi，严格原事件等价于 Ioo。仅独立标量律使用真实连续密度；Lebesgue 端点无质量将严格区间转为区间积分差，不假设未来和无原子。FTC 和链式法则分别给 `chi/gamma*(r(lo)-r(hi))` 与 `chi/gamma^2*(rprime(hi)-rprime(lo))`，符号正确。密度及其导数紧支撑给共同正 M。`lm_scalar_average` 的 F、D、E 全部可测；F 由1主导，D/E 分别由有限常数 2M/gamma、2M/gamma² 主导；两次参数积分求导在全实轴邻域上付清所有条件。第二次通过第一阶导数在每点等于积分的全函数等式转移，无只在单点相等的漏洞。实际 pinned Mathlib 两个承重接口头也已读。

3. **支撑和几何支付（336–426、472–488、523–582）。** 正方差结合非负可积三阶矩排除 gamma=0。真实弦的 AE 坐标支撑经有限积与两族边缘给 |B|<=32h、|D|<=64h²；完整水平噪声<=34h。192 常数与 y>=2 给 h<=1/576、64h²<1、36h<=y/32；没有修改旧尾接口。局部 |w|<=h 时端点几何实际支付35h（36h提供余量）。非零最终 cutoff 参数 R=q+Q+D 给 R>1/16、y sqrt R>y/4；未把初始 q 误当最终 R。在 |S|<y/8 的好事件上两端点绝对值严格>1，密度为零，其导数用开支撑外的真实恒零邻域证明为零。中心指示函数通常为一；这里取消确实来自密度端点，不是指示函数为零。

4. **真概率因子和边界（544–616）。** E 精确是 `{y/8 <= |prefixSum a m|}`，保留原子等号。F1/F2 可测可积，分别以常数乘 E 的真实指示函数 AE 主导。P 是概率律，产品积分确实为常数乘 `pi.real E`，所以得到真实未来路径概率，而非目标测试函数概率或中心化 S−mμ。公开头虽限 q∈[1/16,5]，内部取消证明其实不限制初始 q，故两个 q 端点也合法。

5. **q>5 和 m=0（618–663）。** q>5 时真实 energy>=0 与纵噪声>=−64h²给最终 R>4，cutoff 让整个 w 实轴的函数恒零，再对完整常零函数得到两导数零。m=0 的真实 S=Q=0，|w|<=2h 与完整水平噪声给36h小于最终边界；因此函数为同一 cutoff 的积分、等于 f(q,0)，未误称函数为零。闭区间 |w|<=h 上两导数由空积真实坏事件概率0推导，故无需从闭集函数相等错误推出端点导数。

6. **原始二阶律接合（714–792）。** sqrt(L2+1)>=1 给 epsilon0<=1/192，epsilon<=epsilon0/2支付旧桥的epsilon<=1/2。x半窗和正分母给1+y<=2(1+x)，从而真实 hcut=epsilon/(1+x)<=h=epsilon0/(1+y)。已接受 law/variance/gamma 桥的完整消费头已读，同一条件律上推出概率、三阶可积、正V/gamma和gamma<=2hcut<=2h；未给原始律加三阶矩，也未把条件均值设零。唯一尾调用使用已验 `sourceTruncation_growing_microtime_abs_tail` 原样的 T=m*raw2、m<=n 和 clock，最后才得到 exp(-4y²)。C0*(2exp17+1)>0 同时放大概率因子和指数因子，所有除法/乘法保序的正性条件正确。

全部声明覆盖如下；每一行的完整 actual name、完整类型 UTF-8 SHA256、源区间、传递公理和逐项裁决在 `common-localized-microtime-full-review-coverage.json`。这里全部行的传递公理均严格是 propext、Classical.choice、Quot.sound，逐项 verdict 为 CORRECT。

| 声明 | 完整源区间 |
|---|---|
| `lm_test_measurable` | 18–23 |
| `lm_test_bounds` | 24–30 |
| `lm_scalar_interval` | 31–65 |
| `lm_scalar_hasDeriv` | 66–88 |
| `lm_scalar_first_hasDeriv` | 89–103 |
| `lm_density_bounds` | 104–120 |
| `lm_scalar_average` | 121–246 |
| `lm_unit_integrable` | 247–256 |
| `lm_kernel_scalar_eq` | 257–320 |
| `lm_endpoint_bound` | 321–335 |
| `lm_density_deriv_zero` | 336–343 |
| `lm_geometry` | 344–353 |
| `lm_cutoff_radius` | 354–361 |
| `lm_good_endpoints` | 362–383 |
| `lm_family_support` | 384–427 |
| `sourceFutureNoiseKernel_scalar_localized_bounds` | 428–664 |
| `sourceTruncation_growing_microtime_derivative_bounds` | 665–792 |

机械状态为 **LEAN_FULLY_CHECKED（只针对此完整冻结模块，复用原精确成功执行）**。check003 direct rc=0、17.660562992 秒，`-o` 在同次成功产生；一次 actual-owner audit direct rc=0、21.159866333 秒（含排队）。原审计按 `getModuleIdxFor?` 遍历每个真正 module-owned 常量而非只扫公开名称，并对全部17条调用传递 `collectAxioms`；原日志17条 TARGET_DECL/ACTUAL_TYPE 与 JSON 的每一完整类型逐条相同。源/对象在审计后未变。固定 Lean v4.36.0-rc1、mathlib 807d3836b165983210ee2ecf3cd28f239436949c、CPU10–13/root-heavy.lock/-M8192/-j4/autoImplicit=false 均与原回执一致。完整最后成功日志已读，仅既有包视图 local-change 警告和证明风格/建议，无错误；未为消警告改变冻结字节。

check001/check002 的旧 rc=1、源/日志哈希均保存；check002 的 `error(lean.invalidField)` 确实不匹配旧 `error:` 简报，不能把空 errors 数组视作通过。最终接受基于 check003 的真实退出码和完整日志，以及本次独立数学/类型审查。

已验尾模块源 `591d52e2a6dbcf3cf133a6b45d4ee3d8c4d482aafbf9ca8fcc4968b4c0d3afde`、对象 `81647e3ad96aa61d1cc6d0049dd8ed042b9dbb187c0b53d40d0f9a421d21194b` 与旧完整审查/coverage/root-qualification 的绑定哈希全部匹配，只复用其已接受证明。未重新审旧 tail 证明或重编 producer。

审查完成后释放本报告及观察目录写权，无在途操作、无子代理。下一真实源依赖为 supplement 923–927 的实际微时钟 Taylor/regulator 期望误差及其求和；本票不声称完成它、完整 growing-y 反射比较、最终概率链或 C1/C2 根闭合。普通 FINAL 结束本审查回合，不是后台继续机制。
