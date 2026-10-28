# GH271 独立最终审查：GaussianSmoothingScale

STATUS: CORRECT

JUSTIFICATION: 对精确冻结的三个公开定理和四个完整声明内 `let`，本次完整源码、全部实际类型、生成声明、来源语义及保存的首个成功对象审计核对没有发现关键缺口。结论严格限于修复尺度下的实分析恒等式及最终任意多项式阶衰减界。该结果没有证明原始小胞几何误差、实际高斯坏事件概率消费者或 OQ3 正面根定理。

## 独立性、权限与当前授权

本审查者为 fresh 独立最终审查上下文 `/root/oq3_gh271_final_review`。父 `/root` 是本单元作者；本审查未参加源码编写，也没有修改声明、前提、证明或机器证据。唯一写权限为本文件，其余工作区及原始来源只读。未再委派，未运行服务器命令、Lean、公理检查、上传、Git、API、缓存操作或跨聊天操作；只复用保存的精确证据。

已应用 `math-theorem` 及 `chinese-output-style`，完整读取技能及数学技能的 prompt-library、openai-workflow、lean-verification 引用。遵从项目的服务器专用与精确成功证据复用规则，不进行技能通用流程中的本地 Lean 探测或重复构建，不使用 math-ultra。

已选读 AGENTS 的所有权、作者／审查者分离和证据复用规则，SERVER 的版本与服务器规则、TEAM 当前入口，以及 `coordination/streamlined-acceptance-current.md`。TEAM 开头的旧协调者和暂停信息由其明确指定的 `currentAuthoritativeState` 覆盖。当前 REGISTRY 的 `rootThread` 及 `currentAuthoritativeState.rootThread` 均为 `01a17d3c-6dfd-7cc0-94ed-35d758a423a5`；OQ3 唯一所有者为 `01a16c48-80ee-7520-a9d9-faeeb6d05c78`。REGISTRY 中较旧的顶层 `coordinator` 字段不覆盖当前权威状态。

已完整读取当前 phase40 文件，SHA256 `2b69e1eb2251724f2236bd8176623e7445a794dbb12a4f17a346885469fba480`，6181B／222LF。人类“oq3开启，继续推进。”已覆盖旧 OQ3 暂停；本单元使用现有 OQ3 所有者、child ceiling1。phase40 指定 OQ3 CPU36–39、44–47，现有 `c12-heavy.lock` 专属 OQ3，native `-M8192 -j4`，项目同时 heavy 上限3。C12 锁名及内存 helper 的 phase39 名称属于历史别名，不是旧授权。本审查上下文自身 heavy0。

## 精确版本与完整读取范围

以下各文件已从磁盘完整读取；原始 report 按任务指定范围读取。SHA256 均由本次只读计算确认。表中 LF 是字节内容中的换行数。

| 工件 | SHA256 | 字节／LF |
| --- | --- | --- |
| u22gh-source.lean | a8cd0d6b6d2b8c71056c859ad099a0dd196a7d3fcccfdfaa88f15b9d093b46f1 | 2961／71 |
| u22gh-frozen-declaration.lean.txt | 5c2446343efdb9f08b4ec0d71952a30f1767a0cb2c952dde39f0a766e63c12e9 | 863／19 |
| two-hundred-seventy-first-unit-scope.md | 1550f819f00a804b85b59f8e94bcad2a9e2e372e86f3568b89275bf3b292132f | 1523／25 |
| u22gh-source-repair-clarification.json | fcae6fa034386b312b8d8a0e86f313cdd67bd2d081c36a0ec3c4ef95951d953c | 1043／14 |
| u22gh-primary-api.txt | 946327966ca7b1815bcad2376bc8427ad272d9d11f79d7f7fc356df9be3699bc | 1803／30 |
| u22gh-actual-types.txt | c61750da196684ae955f91f3bc5e729629832bec5c092e10072fbb0aaa229230 | 2442／54 |
| u22gh-Audit.lean | 7ad23602094087f27aac8bea82ecc0430af33799ca26d82ef1bce374ebee4e5c | 2197／49 |
| u22gh-audit-record.json | d7c8cb84954c73658bd27640cb7e593ad7ec208e305dcd00bef66e442a163b58 | 3589／112 |
| u22gh-build-history.json | 8efcf43caa0170f40de8bb4f33667d585260be6d3d7db0bf86cb13b6f2d4f844 | 2266／83 |
| u22gh-receipt.json | 6547c3c6bc2cb3a994aebf03a25c1ab5a8c8853aa599aa32ff169745e4ba1408 | 6039／195 |
| u22gh-bearing-dependency-binding.json | 9758a9c90cd873f80ac39ad94d3517a7a01b61789ab0aa5df00a619f487a3653 | 581／14 |
| u22gh-qualified-dependency-binding.json | 1a7520f14f20ed560eb9aeb8d75f2f15a20745a7eaf9a50d5c5a00fe43d8bc81 | 459／9 |
| u22gh-server-dependency-binding.json | 6a51cccc0d732a0f8be361755e2435b8c52fde6f63148bfcf1180b0085f39cd0 | 253／11 |
| u22gh-own-firstO-view-binding.json | e8d28875c2a614acaaef22d5cc38437f73552c41c1f319abe29136703653843e | 551／10 |

表中全部工件严格 UTF-8 解码成功，CR=0、BOM=false。源码与冻结声明保持原字节，无格式归一化、修复或重写。本次在源码抽取三个 `:= by` 前的完整声明，逐字节字符串比较均与冻结文件对应段相同；其中声明内 `let` 总数恰为4。冻结绑定时间为 `2026-10-27T21:55:44.336927+00:00`，其 `sourceImplemented=false`；后续 qualified 绑定与首轮检查绑定最终源码，没有把实现后声明冒充冻结版本。

原始只读来源另核对如下：

| 来源 | SHA256 | 字节／LF | 实际阅读范围 |
| --- | --- | --- | --- |
| C:/game/shao/current/oq3/proofs/r2/report.md | 572e74aa9c12e2771f5543a5709a2807666eeea0a4076e7a3263e5c7bcf87f55 | 20102／523 | 1–158、165–215、220–235、493–523 |
| C:/game/shao/current/oq3/proofs/r2/repair01.md | 9d2e554838aa15b645aaf74a42468d423fed606aa91c1181d0dddf4e87c57cfd | 5846／226 | 全文 |
| C:/game/shao/current/oq3/verdict.md | fd0a5732845aa96ab1725e6d1e52676502092e49d2c00225ce1fde26ac06f3b5 | 3041／58 | 全文 |

交接中的 `proofs/r2/verdict.md` 路径不存在；实际文件为上表 `oq3/verdict.md`，其精确哈希与交接指定哈希一致，因此没有把缺失路径当作缺失数学证据。三份来源也均 UTF-8、CR=0、BOM=false。

## 三个冻结声明的完整证明审查

### 1. log_square_gaussian_four_le_rpow（源码7–23）

完整前提是实数 `a,x`，`0≤a`、`0<x`、`1≤log x`、`2(a+log 4)≤log x`；结论是

\[
4\exp\bigl(- (\log x)^2/2\bigr)\le x^{-a},
\]

右侧使用 `Real.rpow`。记 `L=log x`、`c=log 4`。第11行给出 `L≥0`，第12行给出 `c≥0`。第13行的 `hp` 是 `(L-2(a+c))L≥0`，第14行的 `hq` 是 `c(L-1)≥0`。前者给出 `L²/2≥aL+cL`，后者给出 `cL≥c`，因此 `c-L²/2≤-aL`。这就是第22行 `nlinarith` 所需的完整实数不等式，没有隐含渐近假设。

第16–21行使用 `4=exp(log 4)` 以及实指数乘法公式，把左侧严格改写为 `exp(c-L²/2)`；`4>0` 由数值证明满足 `exp_log` 的条件。第22行使用实指数的保序性。第23行的 `Real.rpow_def_of_pos hx (-a)` 在明确的 `x>0` 下给出 `x^(-a)=exp(log x*(-a))`，与目标完全一致。指数是负的平方的一半，没有把 `(-log x)^2` 当作衰减指数。

量词覆盖任意满足前提的实数 `a,x`。`ha` 在这一个证明中未使用，说明本界在其余条件下实际上更强，既不使原声明失真，也不构成额外前提；保留冻结前提而不修改源码。`x≤0` 与 `log x<1` 不属于此声明，不能从 Lean 对零、负输入的全函数约定推得额外结论。

### 2. cubic_gaussian_smoothing_scale_identity（源码25–40）

完整量词是 `n:ℕ` 且 `1≤n`，完整声明内两个 `let` 为 `b=1/(2*(n:ℝ)^6)`、`eps=log(n:ℝ)/(n:ℝ)^3`。结论同时给出 `0<b`、`0≤eps` 和对应两个真实指数函数值相等。

第32–33行由自然数下界得到实数下界 `(n:ℝ)≥1` 及严格正性；第34行正性证明因而对真实正分母有效。第35–36行以 `log n≥0` 和正的 `n³` 证明 `eps≥0`。第37–40行在 `n≠0` 下清分母和环恒等计算，精确得到

\[
\frac{-\varepsilon^2}{4b}
=-\frac{(\log n)^2/n^6}{2/n^6}
=-\frac{(\log n)^2}{2}.
\]

`field_simp [hnp.ne']` 的非零条件有真实正性支持，没有通过零除法约定获得虚假身份。再对 `exp` 使用同余即可。边界 `n=1` 被覆盖：`b=1/2`、`eps=0`，两个指数函数值都是1；声明只要求 `eps≥0`，没有偷写或偷用严格正宽度。`n=0` 被显式排除。

### 3. cubic_gaussian_smoothing_scale_superpolynomial（源码42–68）

完整量词为每个固定 `a:ℝ` 且 `0≤a`，存在一个自然数 `N≥1`，对所有自然数 `n≥N`，用与上一声明完全相同的两个完整 `let` 同时得到 `b>0`、`eps≥0` 和

\[
4\exp\bigl(-\varepsilon^2/(4b)\bigr)\le\operatorname{Real.rpow}(n,-a).
\]

第49–50行把真实自然数嵌入趋向正无穷与 `Real.tendsto_log_atTop` 复合，得到 `log(n:ℝ)→+∞`；类型强制了实数对数，没有把自然数对数、整数除法或有限序列混入。第51–55行对三个最终事件取合取：`n≥1`、`log n≥1`、`log n≥2(a+log 4)`。第56行 `eventually_atTop.1` 给出同一个 `N` 对所有 `n≥N` 生效；第57行在 `n=N` 使用该事件，确实证明 `N≥1`。

第60–63行用本模块第二个定理得到当前 `n` 的严格正 `b`、非负 `eps` 和精确指数身份；第65行按身份改写。第66–68行从 `n≥1` 得到正实数输入，并将同一 `a`、`ha`、两个对数下界代入第一个定理。因而阈值可以依赖 `a`，并且是先选一个阈值、再覆盖其后所有 `n`；没有变成对每个 `n` 另选参数。`a=0` 正常覆盖；负 `a` 并非当前冻结接口承诺的范围。

三个证明均完整，未引入未冻结的假设、目标等价的未证引理、项目外部命题或数值有限样本。源码无积分、测度或概率定义，因此不存在用默认零积分值掩盖可积性问题的途径。

## 依赖、全部实际声明与公理覆盖

数学源码仅导入固定 Mathlib 的 `Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics`。三份 dependency binding 一致记录没有项目定理依赖；服务器绑定记录其所需编译导入已存在。主 API 摘录明确包含真实 `tendsto_log_atTop` 与 `rpow_def_of_pos` 的固定源位置和哈希。其余步骤是正性、实数代数、指数恒等式、最终滤子事件和自然数嵌入；第二、第三个声明对同一模块前面的定理使用不存在循环。固定版本为 Lean `v4.36.0-rc1`、mathlib `807d3836b165983210ee2ecf3cd28f239436949c`、shared-v34 只读包视图。

已完整读取54LF实际类型输出中的10个 DECL、10个 TYPE 和10个 AXIOMS；0个 VALUE。三个公开 TYPE 与上节完整声明相同，两个尺度定理各自保留两个完整 `let`。其余七个全部为本模块生成的定理 `Shao.OQ3.cubic_gaussian_smoothing_scale_identity._simp_1_k`，逐个覆盖如下：

| k | 实际类型语义与全部条件 | 传递公理 |
| --- | --- | --- |
| 1 | 任意含零、数字2且 `NeZero 2` 的类型中 `(2=0)=False` | propext |
| 2 | 任意含零、数字3且 `NeZero 3` 的类型中 `(3=0)=False` | propext |
| 3 | 任意含零、数字4且 `NeZero 4` 的类型中 `(4=0)=False` | propext |
| 4 | `Mul`、`Zero`、`NoZeroDivisors` 下，`a≠0`、`b≠0` 蕴含 `(a*b=0)=False` | propext |
| 5 | `MonoidWithZero`、`IsReduced` 下，对所有自然数幂，`a≠0` 蕴含 `(a^n=0)=False` | propext |
| 6 | `GroupWithZero` 下，对所有整数幂，`a≠0` 蕴含 `(a^n=0)=False` | propext、Classical.choice、Quot.sound |
| 7 | `AddMonoidWithOne`、`CharZero` 下，对所有自然数 `n`，`((↑n+1)=0)=False` | propext |

七个类型都是带完整类前提的非零简化命题，没有隐匿目标假设或未审查的定义值。三个公开定理各自的传递公理为 `propext, Classical.choice, Quot.sound`；全部十项的并集恰是这三个标准白名单公理。实际类型的十个所有者名称与 receipt 的 `all_owned_names` 精确集合一致。

已完整审查49LF审计源码。它以环境实际模块所有者 `Shao.OQ3.GaussianSmoothingScale` 遍历全部常量，拒绝该模块的新公理，对每个常量调用 `Lean.collectAxioms` 并拒绝白名单外传递公理，输出全部 TYPE；若遇到定义则另查 `.safe` 并输出 VALUE。它还确认三个冻结目标存在且为定理、实际目标数为3、所有者非空。实际输出是3个公开加7个生成定理，故0个定义值有充分覆盖，不是遗漏打印。源码禁用项扫描无 `sorry`、`admit`、新增 `axiom`、`unsafe`、`native_decide`。

## 保存的服务器证据与其精确边界

本轮复用已保存的 source-bound 首轮成功检查和同首个对象审计，没有任何重放。receipt 仍以 `PENDING_FRESH_FULL_REVIEW` 记录当时作者状态；本报告提供独立数学审查，不改写旧 receipt 为新的验收记录。

| 项目 | 保存记录 |
| --- | --- |
| 首次 native | attempt1，RC0，4.448743302375078秒；2026-10-27T21:57:17.144121+00:00 |
| native 日志绑定 | SHA256 c62a7ba411651e2af3713024f513df8106dffe23dbe7de3b70896037678dcf4a，476B |
| 同首个对象全部所有者审计 | RC0，5.316674714908004秒；2026-10-27T21:57:32.597619+00:00 |
| 审计日志绑定 | SHA256 b97cbabd42d1b21661f33d23ee265ec7ed3e0610b03ef99c8803042d44a1d8d1，2696B |
| 首个原始 olean | SHA256 731a13baa488a9370834d469584b34bd1c3d0de582635ab0feea4693447ba6c3，234856B |
| 源码 | SHA256 a8cd0d6b6d2b8c71056c859ad099a0dd196a7d3fcccfdfaa88f15b9d093b46f1，2961B／71LF |
| 实际所有者 | 10 TYPE／10 theorem／0 VALUE，3公开加7生成 |
| 完整 receipt | SHA256 6547c3c6bc2cb3a994aebf03a25c1ab5a8c8853aa599aa32ff169745e4ba1408 |

`u22gh-audit-record.json` 的全部字段均与 receipt 对应字段相同，build-history 的唯一条目也与 receipt 中内嵌历史完整相同；不存在失败后变更源码却复用旧成功记录的混版。任务交接记载0次失败、1条首界 `ha` 未使用警告；源码中该前提确实未使用，保持冻结不修复。完整本地 receipt 不另设 warning-count 字段，因此本审查不把交接警告计数冒称为新取日志的计数。

own-firstO 绑定指向服务器 `workspaces/lead-oq3/.lake/build/lib/lean/Shao/OQ3/GaussianSmoothingScale.olean`，只读 accepted-source-view 中增加该首个对象链接，旧入口改动0、共享缓存写入0、二进制复制0。两份 receipt 均绑定同一首个对象哈希；没有重新生产对象来补审计。

保存的 native 和 audit 资源字段都是 CPU36–39、44–47、native8192MiB、j4、`ROOT_OQ56_OQ3_40`，符合当前授权。前置服务器绑定记录 ownLockObservedFree=true、heavy0、inflight0、uncertain0。phase40 指定使用现有 `c12-heavy.lock`；本轮没有新观察或重拿锁。内存记录内 `phase=ROOT_OQ56_OQ4_39` 是已固定 helper 的历史字符串；helper 哈希 `0b3119b972b736fec56c818717462cfa8f1fea897dea94baa2120a19d2b1acda` 与 phase40 明确复用项一致，不能据此把实际 phase40 当成旧 OQ4 授权。

保存的 native 原始 cgroup 用量199290028032B、投影 admission 用量169863913472B；audit 对应199289917440B、169863548928B。两次记录均满足原始200GiB硬上限和投影180GiB guard；项目 RSS 加8GiB低于140GiB项目预算，host availability覆盖请求，系统／其它任务保留60GiB。记录明确未折扣 active file 或 slab、未改缓存、无 OOM 事件。本审查只核对这些保存记录内部与当前 policy 的对应关系，不把它们表述为本轮的实时进程、CPU或内存观察。未新取服务器日志或对象二进制，日志和二进制的哈希属于上述保存 receipt 的绑定证据。

## 原始来源到当前形式声明的语义边界

原 report 第117–140行使用 `epsilon_n=n^-3/log n`，频率窗为 `n^3 log n`；第195–215行明确以 `h=n^-3/log n` 控制真实曲边界小胞的高斯平均振荡。repair01 改用 Song 的 uniform-in-law weak-Cramér Edgeworth 输入，并在其自身第二节以 `h=n^-3` 给出振荡估计。GH271 选择的是另一个明确写出的高斯修复尺度：

\[
\delta=n^{-3},\qquad b=\delta^2/2=1/(2n^6),\qquad
\varepsilon=\delta\log n=\log n/n^3.
\]

当 `n>1` 时，当前宽度与 report 原宽度之比是 `(log n)^2`，与 repair01 的 `n^-3` 宽度之比是 `log n`。不能称为来源中同一个模连续宽度，不能直接继承原 report 的式(9)或其 `O(n^-7/2/log n)` 误差。原频率窗仍是 `n^3 log n`，与所选阻尼有代数关系 `delta*cutoff=log n`，但本源码没有证明 Fourier 尾积分估计或整段反演协议。

已完整读取并核对 `u22gh-source-repair-clarification.json`。它明确区分原始宽度与新尺度，保留原始假设，指出新宽度大 log²，且把实际变换后曲边／裁剪 `B_Q` 的新几何和加权振荡估计列为尚缺义务。scope 中“matches original frequency cutoff”和“不暗改原假设”的文字必须连同这份精确澄清理解，不能解释成“新旧模连续误差相同”。在此明确范围下，没有发生隐蔽前提修复。

还需要对真正的 `B_Q`（`Q∩D_x` 经仿射变换，可能带曲边和裁剪）证明宽度 `eps` 下的边界和内部加权误差，一致地达到

\[
O\bigl(n^{-7/2}\log n+n^{-6}(\log n)^2\bigr)=o(n^{-3}).
\]

这是尚未闭合的实际几何／加权分析义务，不由当前三个实分析声明推出，也不能用通用矩形边界代替。GH271 对任意 `a≥0` 的界只适用于其明确高斯表达式；将它应用到实际坏事件尚需独立的实际概率上界接口。GG270 及其缺失固定编译导入是后续消费者的独立问题，不是本源码隐藏的依赖；本单元没有声称其概率界已经通过。

原 report／repair／verdict 的严格 `0<beta<2/5`、p54 修正常数 `v_corr=-hat_t0*sqrt(detDelta)*sqrt(Lambda1)` 和 Song 外部 uniform-in-law 输入归属均被保留。当前纯实分析引理不需要 beta、倾斜律或鞍点假设，并不意味着在最终正面定理中删除这些前提。已接受的真正联合非格点反例证据保留；本审查没有重审或推翻它。原始来源的旧 `PROVED` 标签属于其历史非形式化论证状态，不覆盖当前 Lean 已证范围。历史优先性仍未认证；本单元属于辅助实分析结果，不能包装为新的 OQ3 研究根闭合。

原始正面 OQ3、B–D、远区、典范一致 Hermite 误差、实际小胞几何和去平滑消费者仍 OPEN。当前正确性判断只接受本报告绑定的 GH271 版本，不扩大这些范围。

## 使用记录与结束状态

配置要求：`gpt-6.1-sol`／`xhigh`，fresh 独立上下文。工具未向本审查上下文提供实际运行模型、推理档位或分类 token 使用量；以下未知值如实为 null，不把配置要求冒充独立运行计量：

```json
{
  "configured_model": "gpt-6.1-sol",
  "configured_effort": "xhigh",
  "actual_model": null,
  "actual_effort": null,
  "input_tokens": null,
  "cached_input_tokens": null,
  "output_tokens": null,
  "reasoning_subset_tokens": null
}
```

COMPLETED_STOPPED。本报告最终保存并从磁盘完整回读后，唯一报告写权限释放，之后不再写入。本审查上下文 children=0、heavy=0、inflight=0、pending=0、uncertain=0；未留服务器请求、子代理或待确认写入。该零状态只描述本审查上下文，不冒称整个 OQ3 分线的实时状态。
