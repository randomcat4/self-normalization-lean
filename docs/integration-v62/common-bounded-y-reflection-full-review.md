# 完整 bounded-y 真实平滑比较独立审查

STATUS: CORRECT

审查者：`/root/common_bounded_y_reflection_full_review`，fresh `gpt-6.1-sol / xhigh`。独立于已释放写权的作者；本审查没有修改 Lean、前提、冻结文本、原凭据或旧依赖，没有启动子代理、编译、公理门、PR 或合并。

精确源为 `Shao/Probability/SourceBoundedYReflection.lean`，完整读取第 1–1543 行，包括 30 个 private theorem 的全部证明和全部局部值。共 84383 bytes、1543 LF、0 CR；SHA256 `eca369f19974ac5a2d5f00a75a064942f3d9e25ab085ae792f5c017bdc55f518`。workspace 源与两个冻结 draft 副本同字节。只读服务器核对分支 `feat/common-bounded-y-reflection`，HEAD `52f74f43a4e01903d0f7f4b11511434a0e2280b6`，parent `ba600e9fbcaeeb2142266a20ebf34b476605c911`，tree `71c25ed361e990a1e3b918b55c299a0a8c76a1ae`，唯一提交源文件即本文件，tracked clean。

冻结文件 SHA256 `15b440f142463092b5570d8b994542fdf56991a15a73209a3579cabc165982ed`。四个 public 头及其全部 literal let 与冻结文本独立逐字比对，仅归一空白后全部相等；private helper theorem 在该冻结中已明确允许。没有新增 global/private/generated definition，也没有未审查的定义值。

## 原文到实际陈述

完整读取原始只读 `C:/game/shao/current/c12/main.tex:609–668` 和 `supplement.tex:598–756`，并完整读取三个 candidate 文档、implementation-notes 与 production-handoff。真实 cutoff、严格 `|w|<y sqrt(q)`、固定密度、两族各 Fin8 的弦噪声、gammaV0、有限未来 product、真实 prefixSquares、regulator、delta 及最后的两个期望均保留。原律仅有限二阶矩、均值零、n 倍原二阶矩等于 1 与原截断预算；第三/四阶可积由有界条件律接口产生。条件均值 mu 没有设为零，没有中心化条件律。噪声依赖原固定 x 的 rho，随 y 使用同一律。

第四头生产 gamma<=y<=2 上的全部 abs-delta 可积、总 abs 误差、同一 psi 的实际 iid 望远镜等式和最终误差界。原文的近 x 限制没有被偷用；现有证明在已冻结的更大 bounded-y 区间成立。这只覆盖 supplement Step 3 的 bounded-y 平滑比较，不覆盖 growing-y 四区、localized micro/growing 完整概率、去平滑或 C1/C2 总根，也不提出历史新颖性结论。

## 完整证明核查

- **真实标量噪声（17–394）。** 先将密度积分中的严格事件精确转成 Ioo 端点积分，利用 Lebesgue 端点零质量转区间积分；y>=0 给半径非负与端点顺序。两次 FTC/链式法则的符号分别为 r(lo)-r(hi)、rprime(hi)-rprime(lo)，分母 gamma、gamma²。q<=0、半径0均在同式内成立。固定紧支撑密度及其导数给 M；F/D/E 全部可测可积，以概率空间上的常数作两次支配微分，再给 Lipschitz。展开真实 full-noise map 的 Fubini 保留两个 Fin8 族与未来路径；没有 m>0 前提，m=0 同样覆盖。泛律的第三矩为0会迫使 id=0 a.e.、方差0，故 gamma>0 并非调用者新增假设。
- **源尺度与矩（395–551、841–934）。** 正样本数来自已接受 n>=64；ns 在[3/4,4/3]、nV 在[1/2,4/3]、s<=gamma² 均来自真实源接口。预算显式支付 n|mu|<=1/8。一阶晚期界放宽为4/n，总一阶<=5；平方直接调用已合格 SourceLindleySurvival 的无条件原律定理，晚期<=96 exp(3079)b，总平方<=256 exp(3079)nb。没有把 survival 目标或待证概率比较作为前提。
- **两种计数与大推进（552–729）。** n-(j+1) 在 Fin n 上单射；容许 k=0 时项数<=A/s+1，全部 k>0 时另得<=A/s。两种界在证明中分开。大推进 J 明确 late、0<T<y²；真实 abs-delta<=1 给掩码积分<=概率，非负 regulator 的逐点平方 Markov 给256/y²，配合晚期平方矩与 ns>=3/4，C=512*(96 exp3079)足够。严格事件及相等阈值没有漏项。
- **含末端的微时钟（730–840）。** J 不排除 T=0，故 j+1=n 的未来长度0项在内。真实粗 Lipschitz 给 D<=Cr U/gamma，晚期一阶4/n；计数中的+1由 s<=gamma² 吸收为(L+1)gamma²/s，再由 gamma<=2nb 支付，C=16Cr 足够。L>=1、y>=0 与冻结一致。
- **偶奇位移与实际长网格（935–1170）。** 偶函数在0导数为0由链式导数唯一性证明，三次中值估计给 uO+u²E；这是相对候选1/2系数的合法内部放宽，由 public 存在常数支付。长网格的 k>=1 单步不等式以 r²=ks、t²=(k+1)s 与(r+t)(t-r)=s证明，因子4足够。有限 K 的首和<=4；次和取最小 a>=1，扩大到 Ico 并真正离散望远镜，得到<=4/y；空集也覆盖。辅助 range 中 k=0 倒数为0仅用于非负扩张，奇异尾和实际证明正 k，不以除零约定掩盖边界。两种 image 重索引都明确单射，无重数。
- **四段拼接（1171–1472）。** L=max Ll Ls、epsilon0=min el es。早期<=Kl(5+B)A；长时钟<=Kl(80+8B)A，y<=2 在长段最后支付；中间<=Ks(6+2B)A+CpN3；微<=Cm(L+1)N3，其中 B=256 exp3079，A=n|mu|+nb、N3=nb。中间集合先证明 T<y²，再成为原短时钟 Js 及正时钟 Jp 的子集；使用原 O/E 见证与非负子集和，不把两个 existential 阈值当成同一个见证。小推进在 U<=y/16 上调用实际局部位移，余下完整交给大推进。四集合显式穷尽所有 Fin n 项。实际选 C=Kl(85+9B)+Ks(6+2B)+Cp+Cm(L+1)，与所有内部常数放宽一致。
- **真实望远镜（1473–1543）。** psi 是同一 fullNoiseLaw 积分；其 future bridge 按实际定义 rfl。P 上真实坐标由 measurePreserving_eval 给同律、由 iIndepFun_pi 给独立；samplePath=id，故直接调用已接受 iid_lindley_telescoping 得到两期望差等于真实 delta 积分和。再用有限三角不等式和 abs 积分界，不把所需等式或比较写成调用前提。

## 全归属实际类型、公理及原始工件

实际环境归属集合为 **56 theorem / 0 definition**：34 个显式源 theorem（4 public、30 private）及22个 tactic-generated theorem。完整阅读全部56个实际类型。为避免仅重复大段类型类展开，使用152项精确可逆子串字典与56项残余文本；所有字典项、嵌套引用及残余均完整读到，逆序展开后与每一原 actual_type 字符串和其 SHA256 逐项相等，不是简短 pretty 摘要。U+22EF、U+2026 与 ASCII 省略号扫描均为0。

逐声明覆盖表记录实际完整 name、type SHA256、源父声明区间、generated 来源行、实际传递公理与 CORRECT 裁决。源中全部局部 let/letI、have 及其值和证明均随完整源读到；actual definition value 数目确实为0。完整审计脚本使用真实环境 module owner 选择，包括 private/generated，对每项调用递归 Lean.collectAxioms。

只读服务器确认原 check014.rc 与 owned-audit.rc 都记录0，原日志无 error: 或 error(；原同次-o对象 SHA256 `07c5d1236d6549b3ab897c9dba6fb2e63f2a14ef5e240b8f821a6389bbf6928e` 保持。工具链 `leanprover/lean4:v4.36.0-rc1`，mathlib `807d3836b165983210ee2ecf3cd28f239436949c`。kernel 日志 SHA256 `6fc2019713a810688370791889f4d81c06a82711633f25edc98d040965b4d6fd`；audit 日志 SHA256 `3c32cb2335ea8d3a8dc10f4f71c6acb6396aaee39155f8532a07bced511cb21e`。

独立重新解析原始审计文本（只读文本操作）得到56条：名称集合完全相同、每一实际 type SHA256 与导出文件相同、每一公理集合与 owned-audit.json 相同，零差异。公理并集仅 propext、Classical.choice、Quot.sound。actual-declarations.json SHA256 `918bfa39e691c609107de3a8f4a08507b88daaabf4c7787783fa40f907deea95`，owned-axioms.json SHA256 `6cfee42d5db236ebb696118bd84986a0f806351d1adac6f608d79ccc3b5c1fb9`。源禁用 token 扫描为空。没有将旧的空错误摘要当成成功；先前 multiline AXIOMS 抽取修复现由原日志逐项对账确认，本轮没有重放成功 Lean/AX。

完整消费所需旧接口及定义，共18个依赖源的本地哈希与已接受 v61 receipt、服务器实际源均相同，相关对象均存在。SourceLindleySurvival 原始对象还与 v60 qualified-source-bindings 中的 `5eb0dd2b431314562b2ff0866addd250ae940a83fbcfedb8c8e1fe28ae8f2f48` 精确相同。旧 CDF/survival/矩/长短核的已资格证明和工件按既有证据复用，不重复旧证明审查或编译。

报告配套：

- `coordination/common-bounded-y-reflection-full-review.json`：结构化裁决、证据哈希与精确范围。
- `coordination/common-bounded-y-reflection-full-review-coverage.json`：全部56声明逐项覆盖。
- `drafts/c12-bounded-y-reflection-review/`：可逆实际类型、消费接口和服务器只读观察。

**无 CRITICAL GAPS。** 本精确源的四个冻结目标可结合其原始 kernel/全归属公理成功凭据接受。所有原始总根的 OPEN 范围保持。审查写权现已释放，无在途操作；普通 FINAL 结束本审查回合。下一依赖是 root 对该精确源的验收与实质里程碑集成，不需要因换上下文重审未改的旧证明。使用量计数器未向本审查者暴露；输入、缓存输入、输出、推理子集均记录为未知，不推算订阅百分比。
