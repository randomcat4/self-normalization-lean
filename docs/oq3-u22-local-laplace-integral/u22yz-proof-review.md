# U22y / U22z 独立完整最终证明审查

STATUS: CORRECT
Y_MONOMIAL: CORRECT
Y_ENVELOPE: CORRECT
Z_LEADING: CORRECT
Z_ERROR: CORRECT
BATCH_INTERFACE: CORRECT
PRECISE_GAPS: NONE_IN_FROZEN_BATCH_SCOPE

日期：2026-10-23。本上下文为本批唯一 fresh 独立完整最终审查员，与实现作者分离。按任务及 REGISTRY 配置为 gpt-6.1-sol / xhigh，未切换模型、未派生其他上下文。采用 math-theorem，不采用 math-ultra。工具未提供可独立读取的模型运行时签名；input、cached input、output、reasoning-subset token 计数均未提供，故不编造实际使用量或订阅百分比分摊。

完整阅读 Y 的全部 55 行和 Z 的全部 129 行精确源码、两份完整冻结范围、全部 4/4 实际归属声明的完整打印类型、两个完整 Audit.lean、成功 kernel / AX 日志，以及所需已验收 X 接口、原源段落和固定 Mathlib 主 API。全部新证明作逐步数学审查，不以 kernel PASS 替代 source-to-statement / proof 审查。全局 definition values 为 0/0，Z 的所有局部 let 值亦逐项检查。仅复用精确源绑定的既有服务器 kernel / 全归属递归公理证据；本审查没有调用任何 Lean / lake 检查。唯一写入为本报告。

## 1. 规则、所有权与精确版本

已读适用 AGENTS.md、math-theorem 及其必要引用、SERVER.md、streamlined-acceptance-current.md，并定向核对 TEAM / REGISTRY 的当前相关字段。OQ3 有效所有者为 01a1669a-bca1-75e0-9d87-d07baee7b90a，旧写者释放和新写者激活均为 true；本上下文只有报告写权，不取得 lane 实现写权，不修改其他所有者、共享文件、源码、版本锁或缓存。不启动 SOURCE / preflight / grant / prefix 仪式。

本地工件目录为 C:/game/shao lean/drafts/oq3/；服务器工作树为 /root/rivermind-data/shao-lean-20261021/workspaces/lead-oq3。只读核对服务器 HEAD 为 3346440dea28ce226bad375c62b288163ea7479e，与两份收据记录的当前父提交相同。固定工具链为 leanprover/lean4:v4.36.0-rc1；Mathlib HEAD 为 807d3836b165983210ee2ecf3cd28f239436949c。

| 单元 | 模块 / 精确本地源 | 行 / 字节 | SHA256 |
| --- | --- | --- | --- |
| Y | Shao.OQ3.BoundaryLaplaceEnvelope / u22y-source.lean | 55 / 2550 | dd71d4e6c92ee1ed778df1c04f6753c962335f99fe5927c230ac5a471012ef32 |
| Z | Shao.OQ3.BoundaryLaplaceIntegral / u22z-source.lean | 129 / 6339 | 1de2b65b14b26d0e5a564c9bce5a673f662187b1461633ddb6bfce4da6b9ac12 |

两源均严格 UTF-8、LF、CR=0。服务器当前模块源分别与本地源、run 保存的 Y source-01.lean / Z source-03.lean 同哈希。冻结 Y hundred-sixth-unit-scope.md 为 31 行 / 1848 B，SHA256 cc7eb5541b648621d989bbcc1fdc0ce4eb716df41a78b843056131bd64985e85；冻结 Z hundred-seventh-unit-scope.md 为 54 行 / 3305 B，SHA256 195154c28c20af2d7377308357c5a0977c5ba4dc9719c3918aaf28336780100a。服务器各 scope.md 同哈希。四份声明逐一与冻结声明完整核对，空白规范化的精确比较也全部为 true，没有改对象、量词、假设或结论。

| 实际归属声明 | 源码声明 / 证明 | 完整实际类型 |
| --- | --- | --- |
| Shao.OQ3.boundary_laplace_monomial_integrable | Y9–13 / Y14–32 | Y actual-types 完整第二项 |
| Shao.OQ3.boundary_laplace_error_envelope_integrable | Y34–39 / Y40–52 | Y actual-types 完整第一项 |
| Shao.OQ3.boundary_laplace_leading_integral | Z10–17 / Z18–52 | Z actual-types 完整第二项 |
| Shao.OQ3.boundary_laplace_cutoff_integral_error | Z54–80 / Z81–126 | Z actual-types 完整第一项 |

Y1–8、Y33、Y53–55 和 Z1–9、Z53、Z127–129 的导入、namespace、section、空行与收尾也全部覆盖。Y actual-types 为 16 行 / 752 B，SHA256 1c750ee8a5292fbf520ee1b98536a7c56cad3b0a3cf93cc3c910daad65ec73ed；Z 为 47 行 / 2692 B，SHA256 c5169a61d154b1db2715cc60485765cedb1720fe8c80cc2387ce30fe843ce327；服务器保存文件同哈希，完整 audit.log 的 DECL / TYPE / AXIOMS 内容一致。

两份实际模块各恰有 2 个归属常量，均为公开 theorem。审计按 getModuleIdxFor? 枚举实际模块所有者，不只审计公开目标名单；无额外 private / generated theorem，无全局定义和待补读 definition value。源码禁止项扫描未见 sorry、admit、new axiom、unsafe、native_decide。

## 2. 实际声明、测度与必要接口

四个实际类型与冻结目标一致。统一测度是 μ = (volume : Measure ℝ).prod ((volume : Measure ℝ).restrict (Set.Ici 0))，即切向全实线 Lebesgue 测度乘法向非负半直线 Lebesgue 测度，不是概率律或有限测度替身。Y 的 m,n 是任意自然数，d>0；Yenvelope 的其余系数是任意实数。Zleading 允许任意实幅 a0，要求 lambda,Lambda1>0。Zerror 完整保留非负 CF/CA、正 rho/d、共同衰减 d≤c,lambda,Lambda1/2，以及闭矩形上的全称 Taylor、coercivity、amplitude 条件。

Zerror 另明确保留每个 0<t≤1 的实际截断核 AEStronglyMeasurable 条件。它没有假设该核 Integrable、误差积分界、共同极限或原研究结论。只需逐个 t 的 AE 强可测性，声明没有积分或对 t 求可测性，因而不需要偷偷补联合可测性。F,A 仍为任意实值函数，局部数值界本身不必强迫其可测；这个分析输入有实质内容，不能省略或宣称已由原实际图表生成。

必要旧接口 X 为 boundary_weighted_scaled_cutoff_error，已完整读取 u22x-source.lean 的 75 行以核对使用界面；其 SHA256 为 53cd43f6aba9d97493b0cbf951ca1c8763ffa97a825f42e8a0106ba949a44b94，服务器当前源同哈希。完整阅读并复用 u22wx-proof-review.md 的既有 CORRECT 验收，SHA256 448c1533ada9adae319f58d2cd9f503794c217fe98870871bb87ab320a2bcefb；不重开 W/X 的未变化证明验收。X 给所有 u∈ℝ,v≥0、0<t≤1 的截零核与主核点态差，完整右侧为 t 乘 Y 的同一 Env；包括矩形外主核损失的 |A0|/rho·(|u|+v) 项。Z 所传 F,A、七个常数、全部局部条件、t,u,v 和符号均与该完整接口相同。

## 3. Ymonomial：真实 Gaussian / Gamma 可积性

Y15–16 从 m,n≥0 得实数指数 m,n>−1，覆盖 m=0、n=0。固定 Mathlib GaussianIntegral.lean:96 的真实 API 是 b>0、s>−1 推出全实线 x^s·exp(−b x²) 可积；Y17–18 取 b=d、s=(m:ℝ)。Pow/Real.lean:61 的 Real.rpow_natCast 对所有实 x 和自然数 m 成立，包含负 x；此处不是把只在 x≥0 可用的实幂规则误套到全实线。

Y19–22 取这个可积函数的 norm：‖u^m exp(−d u²)‖ = |u^m| exp(−d u²) = |u|^m exp(−d u²)。第一等式使用实 norm=abs、abs_mul 和 exp>0，第二等式使用 abs_pow。因此全实线负 u、奇 m 的符号被合法转为目标绝对幂；没有把原有符号多项式直接当成非负多项式。

Y23–25 调用 GaussianIntegral.lean:73 的真实 Gamma 型 API：s>−1、p>0、b>0 推出 x^s exp(−b x^p) 在 Ioi 0 可积；这里 s=n、p=1、b=d，所有条件分别由 hn、1>0、hd 提供。rpow_natCast / rpow_one 精确变为 v^n exp(−d v)。Y26–28 以 integrableOn_Ici_iff_integrableOn_Ioi 将 Ioi 改为 Ici，端点函数有限由 finiteness 给出，Lebesgue 单点 {0} 零测；没有丢掉正质量边界。

Y29 调用 Integrable.mul_prod，真实结果是 μ.prod ν 上 f(u)g(v) 可积，不要求把任一坐标常函数单独在另一无限测度方向积分。hV 的 IntegrableOn 正是相同 restrict 测度上的 Integrable。Y31–32 用 −d(v+u²)=−d u²−d v 和 exp_add，再作交换结合代数，把乘积精确识别为 |u|^m v^n exp(−d(v+u²))。该函数等式实际上对所有 v 都成立，未藏入额外支撑假设。

Ymonomial verdict: CORRECT。全体自然幂、负切向坐标、v=0 和零次幂均覆盖；可积性来自真实 Gaussian / Gamma 结果，不来自目标式假设。

## 4. Yenvelope：全部多项式项与任意系数

Y41–45 恰取 (m,n)=(1,0),(0,1),(3,0),(1,1),(0,2) 五个已证单项式，对应 |u|、v、|u|³、|u|v、v²。Y46–48 将前两个之和分别乘 CA 与 |a0|/rho，将后三个之和乘 |a0|·CF，再相加；所有项仍带相同 exp(−d(v+u²))。Y49–52 展开函数加法与零/一次幂，ring 仅分配结合系数，精确恢复冻结完整包络，没有遗漏线性、混合、平方或 cutoff 外区项。

可积函数的有限和与固定实系数乘法不要求系数非负，所以 Y 不需 CA/CF/rho 正性。rho=0 时 Lean 的实数除法按既定 totalized 语义给出 a0/0=0；这里仅作固定实系数的可积性陈述，不将它解释为零半径几何 cutoff。后续 Z 和 X 使用 rho>0，因此实际不等式与除法没有这个退化情形。Y 也不声称对任意有符号系数给出非负 majorant；所需非负性由 Z/X 的 hCA,hCF,hrho 与 v≥0 保证。

Yenvelope verdict: CORRECT。五种单项式及两份线性组合完整覆盖，不含目标可积性前提。

## 5. Zleading：可积性和准确主常数

Z19–22 的局部 μ,L 与声明 let 值完全相同。Z23–24 由 Lambda1>0 得 Lambda1/2>0，以真实 Gaussian API 证明 u↦exp(−(Lambda1/2)u²) 在全实线可积。Z25–28 由 lambda>0 得 −lambda<0，以 ImproperIntegrals.lean:77 的 integrableOn_exp_mul_Ioi 得法向指数在 Ioi 0 可积，再以同一 Lebesgue 无原子边界接口扩到 Ici 0。

Z29–31 用 integral_Ici_eq_integral_Ioi 和 ImproperIntegrals.lean:102：∫_(c,∞) exp(a v)dv=−exp(a c)/a，条件 a<0。取 a=−lambda,c=0，得到 −1/(−lambda)=1/lambda，符号正确。Z32–38 将 exp(−(lambda v+Lambda1/2·u²)) 分成切向与法向因子，未漏负号或 1/2；Z39–40 的 pi/(Lambda1/2)=2*pi/Lambda1 与正参数范围相容。

Z41–44 先以 hU.mul_prod hV，再乘任意实 a0，证明 L 真正可积。Z45–52 才计算积分：提出 a0，使用相同乘积测度的 integral_prod_mul，再用 integral_gaussian b = sqrt(pi/b) 与 hVI，得到 a0·sqrt(2*pi/Lambda1)/lambda。该顺序排除了把未可积函数的 totalized 积分默认为 0 来冒充求值。a0=0 或 a0<0 都被合法处理；求值是有符号积分，不应擅自换成 |a0|。无额外概率归一化、2*pi 或 Jacobian 被插入本定义。

Zleading verdict: CORRECT。它给出真实 Gaussian/正法向指数乘积核的可积性和准确积分，恰对应原源式(14)中尚未乘外部坐标因子的积分部分。

## 6. Zerror：AE 支撑、实际可积性与统一 order-t

Z82–92 的局部 μ,K 与声明完全相同，L 是幅 A(0,0) 的同一主核，Env 是 Y 的完整包络。Z93–94 不加前提地消费 Y 的实际 Integrable Env。Z95 由 0<d≤lambda 得 lambda>0；Z96 由 0<d≤Lambda1/2 得 Lambda1>0，因而 Z97–100 对任意符号 A0 合法取得 L 的可积性与精确积分。没有把所需 lambda/Lambda1 正性另藏为未声明的假设。

Z101–103 先证明 μ 几乎处处 v≥0。谓词 {p | 0≤p.2} 由 measurable_const / measurable_snd 的比较给出可测集，ae_prod_iff_ae_ae 将乘积 AE 转为逐坐标 AE，内层 ae_restrict_mem measurableSet_Ici 恰给出受限 Lebesgue 测度的支撑。这里无需声称 p.2 在全平面非负；v<0 上核的任意值对该 μ 无贡献，v=0 也没有被误排除。

Z104–106 先固定 C=|∫ Env dμ|+1，再引入任意 0<t≤1。hEnv 已保证这个积分是可积包络的真实有限实数积分；|I|≥0 所以 C>0，即使 I=0 亦成立。C 只依赖已固定的数据，不随后引入的 t 变化。

Z107–112 在 hvAE 的同一全测集上，将实数 norm 写为绝对值，完整传入 X 的全部假设，得到 ‖K_t−L‖≤t·Env。X 的右侧 t·P·exp(−d(v+u²)) 与 t·Env 的差仅为 mul_assoc；没有遗漏主核的 cutoff 外部损失项，也未另假设目标 integral error。

Z113–114 的 Integrable.mono' 真实 API 只要求可积实 majorant、被控函数 AE 强可测和 AE norm 界。majorant=t·Env 由 hEnv.const_mul t 可积；K_t−L 的 AE 强可测来自明确输入 hmeas t ht ht1 与已证 L 可积所给的强可测性。故 hDiff 是新推导的真正差函数可积性。Z115–119 再由 (K_t−L)+L=K_t 及加法封闭性证明 K_t 可积；推导不使用待证的 hK，没有循环论证。

Z120 用 norm_integral_le_of_norm_le 得 ‖∫(K_t−L)‖≤∫t Env。Z121 在 hK 和 hL' 已建立后才使用 integral_sub，随后以 hLI' 替换主核积分、Real.norm_eq_abs 转成绝对值，并用 integral_const_mul 得 t∫Env。此积分差展开有双方实际可积性，绝非在默认零积分之间形式相减。

Z123–126 由 I≤|I|+1=C、t≥0 得 tI≤tC，再交换乘法为 Ct。即使未单列 Env 的 AE 非负性，这个最后放大也成立；实际 Env 在 μ 支撑上确为非负，因为 CA,CF≥0、rho>0、v≥0 和 exp>0。边界 t=1 包含，t=0/负 t 明确排除；u 不限符号、v=0、A0=0、CA=0、CF=0 均不破坏推导。常数一致性只针对固定 F,A、lambda,Lambda1,rho,CF,CA,c,d 下所有 0<t≤1，不偷换成对尚未构造的倾斜参数/谱的一致性。

Zerror verdict: CORRECT。真实截断核 Integrable 与统一绝对 order-t 误差均由 X、Y、主核及明确 AE 强可测输入推导；冻结范围内无关键缺口。

## 7. 精确服务器证据及全归属递归公理

服务器 run 为 /root/rivermind-data/shao-lean-20261021/runs/oq3/u22y-20261023 和同级 u22z-20261023。只读核验本地/服务器 scope、当前精确源和成功保存源、receipt、history、Audit、audit-record、audit-environment、actual-types 的对应哈希，读取两份完整成功 kernel 日志及两份完整 audit.log。作者成功检查统一为 CPU14–17、native memory 8192 MiB、jobs4、autoImplicit=false；本审查无新增 heavy 命令、无本地 Lean 调用。

| 证据 | Y SHA256 | Z SHA256 |
| --- | --- | --- |
| receipt.json / 本地对应 receipt | ec331cae091c367f8adb510b744e9ba7792f41656c3477c8e72875cc772a6036 | f8429415f7070e65a40311f9bac7c84ea0fec670982172f0cce926b807ad5edd |
| build-history.json | 27f6ad68ae511d0e19b19638bfe7a9b4b041fd7179ac0bb0189b876125e90b89 | 15b706019a8dfdeab1382c9399c248b800225be53110baf04567f3c8a056586b |
| 完整成功 build 日志（Y01 / Z03） | af15990f208fb9d3c57bda10b2997f7166fcedabaf0148b6953d4977316e8570 | fe9a6b741bba0630c9977614157f0259907b0b7ebce576a9400b542ee4518626 |
| Audit.lean | f27ef581c2aa60e07d5820358beecfe06f15f19405ed176c964f52671cc88317 | a2b9831182a1014d82ef49bef9591b506ffa624830d388bea64acaad8878e85b |
| audit-record.json | a2591843e14e234bad9dbdc97eaebab57f58610d1863b4b29b607651de85ae76 | 5b8262b2179edcf3ee5d221801c1f61a53fbae745943a7bc117740a1e14975d0 |
| audit-environment.json | 976be52d9af83eca714cfc61dc7229a54d28f48ad0eebd2aaa39721b5d69bfbf | e21c97ef916466cee6c5afa6e25d829c29057d6a1b79468697905fe0298875f5 |
| audit.log | adc537a45851349efd616e0ffe0b3d129a31ab36c5f6e0349ab667dfe5621f87 | e60680910e9b2ab4be30fb81d0d1434f9fa23bdb686967854e166a155ffcd5c8 |

Y attempt01 kernel exit0、5.482848435640335 秒；AX exit0、6.279913522303104 秒。Z attempt03 kernel exit0、6.1840147487819195 秒；AX exit0、5.870188253000379 秒。Z attempt01/02 的失败源码及日志仍在 run 原样归档，其哈希与 history 相符；未覆盖或重放。Y 成功日志只有既有 Lake overlay 警告及两个 unused simp args，Z 成功日志只有 overlay 警告，均无 error。为消警告而改动精确成功源没有必要。

两份 Audit.lean 都完整枚举实际模块所有者，拒绝新 axiom，并对每个归属常量调用 Lean.collectAxioms 递归核验白名单。完整成功日志各输出 FROZEN_DEFINITIONS=0、FROZEN_THEOREMS=2、ALL_THEOREMS=2、ALL_DECLARATIONS=2 和 AXIOM_GATE PASS；全部四个实际声明各自的完整递归公理恰为 [propext, Classical.choice, Quot.sound]，无公开名单之外漏审的私有、生成或定义值。

只读确认 accepted-source-view 的 Y/Z/X 对象链接分别指向当前工作树对应 .olean；Y 对象 215256 B、SHA256 69863eb207ac052b2f670487960df91a035c5292d5bb4c544445797ea4cb5152，Z 对象 280304 B、SHA256 cdaf962c5386366b765b7f5ce890d6794c9fab6928e62f61329cdd68280e4bfa，X 对象 251160 B、SHA256 152711f7a5ac9eebdc7fd0b4e063d4be4187c4dd726f7a54419c793be2621893。依赖界面和源版本与新检查一致。

实际检查 Mathlib 的 GaussianIntegral、ImproperIntegrals、Pow/Real、Integral/Prod、Measure/Prod、Integral/IntegrableOn、Integral/Bochner/Set、Function/L1Space/Integrable、Integral/Bochner/Basic 九个所用主 API 源文件；每份当前字节均与固定 HEAD 对应 Git blob 完全相同。核对了 rpow_natCast、Gaussian/Gamma 可积性、integral_gaussian、半直线指数积分、Ici/Ioi 无原子边界、mul_prod、integral_prod_mul、AE product、mono' 和 norm_integral_le_of_norm_le 的实际条件，不凭相似名字猜测其意义。没有联网更新或更改依赖。

## 8. 原源对应、保留边界与最终裁决

原源只读 C:/game/shao/current/oq3/proofs/r2/repair01.md，SHA256 9d2e554838aa15b645aaf74a42468d423fed606aa91c1181d0dddf4e87c57cfd。完整读取绑定的 183–210 行，并读取 135–182 行核对 lambda、Lambda1、Taylor、幅和 coercivity 的上下文。原源以 r=u/sqrt(n)、z=v/n 缩放；本批对应 t=1/sqrt(n)，并为缩放后局部截零核给出实际可积控制与绝对 O(t) 误差。Zleading 精确求出 A0·sqrt(2*pi/Lambda1)/lambda，与原式(14)中两个 Gaussian/法向积分和幅 A0 的组合相同。证明使用绝对值界，不需要或声称奇切向项抵消。

Y/Z 是源忠实的通用辅助消费者，不是实际式(14)或原根闭合。尚未在本批 Lean 中把实际 C3/幅 germ、同一个图表、共同小矩形及实际 AEStronglyMeasurable 装配起来；未来实际 adapter 必须为同一 F/A 生成这些数据。原坐标 Jacobian / scaling factor、外部 e^(−n Lambda0) 与归一化、相对误差转换、矩形外真实概率远层、实际 Edgeworth/cells/far-probability 均未由此证明。X 对截零后的主核尾部的控制，不能替代原坐标矩形外真实概率质量的估计。

实际谱、(WC)、0<beta<2/5、矩条件、全局 saddle/rate gap、实际 Lambda1 正性、显式远层概率和外部结果 attribution 维持既有状态。Z 中 lambda/Lambda1 的正性是从该消费者明示的 d 界推出，并不自动证明原源实际参数满足这些界。A0 任意的绝对误差定理尤其没有凭空生成原源需要的正主项及相对归一化。原 OQ3 B/D 等尚未闭合根保持 OPEN；已有接受范围也不被重开或改写。

最终分别裁决：Ymonomial CORRECT；Yenvelope CORRECT；Zleading CORRECT；Zerror CORRECT；batch interface CORRECT。全部 184 行新源码、4/4 实际归属完整类型、0/0 全局 definition values、所有局部 let 值和新证明均完整覆盖；冻结范围内没有精确关键缺口。机械层复用精确源的完整 kernel / 全归属递归 AX 成功证据，语义层完成独立完整源到声明及证明核对；仅在上述精确哈希与明示辅助范围内可记为 LEAN_FULLY_CHECKED，不附带新颖性或原根闭合主张。

审查完成。报告写入并核对最终字节后，本上下文停止全部工具与写入，不启动后继单元；接受、发布和继续由 lane lead 处理。
