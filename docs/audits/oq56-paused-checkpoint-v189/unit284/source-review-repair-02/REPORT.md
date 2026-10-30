# unit284 修复02：同一独立审稿人的完整 T01 复审

STATUS: CORRECT

精确候选 SHA256 `f5e46a3d79fd9137097187de9c6a13763b8ab9c6baf0efb4f505332cde78bd3c`，20245B／451LF。已完整复审新的 T01 131LF；其他 32 段与修复01的已接受 SOURCE 覆盖精确相同，沿用既有独立审查，其中四个完整证明 T02／T03／T04／T05 共 167LF。当前证明覆盖并集为 298LF，当前源码 451 行全部有唯一的字节及行覆盖来源，未发现关键数学或声明忠实性缺口。

本裁决为 SOURCE_ONLY：`kernelChecked=false`，`qualified=false`。两次历史 native 均失败且无对象；新稿没有机器通过或实际生成所有者清单证据。

## 授权、输入与边界

新明确授权 `source-review-repair02-ACTIVATION.json`，58396B，SHA256 `8536c8405c616b4966ec112af06dc6cf440b213a27285a441407165740197d13`。全部 262 输入 SHA256／字节数匹配后先写实际 ACK。角色仍为原独立审稿人 `/root/oq56_unit284_review`，与作者保持独立，唯一写入范围是本新目录。旧封包、冻结、所有新旧源码、失败收据、共享文件均未修改。

当前冻结仍为 `c1afe91469de6082b7dd9f9b79bcf1f0725d8a2903e6ec23535efcc85a6f44f3`。10 个完整 HEAD 91LF、5 个字面 RHS 25LF／固定正文30LF、PRE／CLOSE、顺序和其余 32 段均逐字节核对；没有新增 option、声明、前提或警告清理。

## 完整 T01 131LF 审查

67–76 的完整冻结头仍要求同一个 ν 为概率，原 valid 行前提、w 的 L2、背景几乎处处 `0≤w≤R` 和原 M 界。77–84 定义相同 ell、cA、mA、S2、V2；85–90 用每行非负性及显式原行和建立 ell≥0 和可测性。

91–106 完整有限集归纳的目标始终为同一 ν 下 `fun o => Σi∈s,r(a i)o` 的可积性。唯一改变位于 97–100：空集经 `Finset.sum_empty` 化为显式 `fun _ : Ω => (0:ℝ)`。新证明项 `integrable_const (μ:=ν) (0:ℝ)` 并附完整结果类型，实例化的是固定库接口 `MeasureTheory.integrable_const`；α=Ω、β=ℝ、μ=ν、c=0，函数、值域、范数结构和测度与目标相同。有限测度要求由原 `[IsProbabilityMeasure ν]` 提供；没有新假设或新实例声明。101–106 的插入步仍以原行可积性加 ih，并由 i∉s 的 sum_insert 改写，最后取 univ。

107–130 用有限共同背景例外集、绝对值三角及每行包络给 `|cA|≤ell*w`；有限和积分的全部行可积前提已具备，得到实际均值恒等式及 `|mA|≤c*ell`。131–138 利用 w≤R 和 ell≥0 得背景范围，再以 ν 的概率质量 1 控制实际均值 `|mA|≤ell*R`。

139–156 对非负两侧的包络平方，ell²*w² 是来自原 hw2 的可积主函数；据此证明 cA² 可积、cA∈L2，以及 `0≤S2≤ell²*M`。157–172 将中心函数可积性与中心平方可积性分别建立；后者通过 `cA²-2*mA*cA+mA²` 的逐点恒等式和各项可积性，中心积分为零依赖的是实际均值定义及 ν 为概率。

173–192 完整平方展开在合法线性积分下给 `V2=S2-mA²`，保留了非零实际均值。平方积分非负推出 `mA²≤S2`，再得 `0≤V2≤S2≤ell²*M`。193–207 用实际均值的两种界证明中心范围 `ell*(R+c)` 和 `2*ell*R`，并将冻结结论全部组装。没有把范围平方当作方差，没有除以 ell，空异常指标和重复坐标仍覆盖。

## 精确覆盖与旧证据复用

T01 旧范围是 [2905,9003)／77–205／6098B129LF；当前 [2905,9083)／77–207／6178B131LF。完整当前 T01 已重审，未只审两行差异。其最小改变区间独立核验为旧源 [3758,3782)、新源 [3758,3862)，即24B替换104B；其余字节相同。

其余 32 段合计 14067B／320LF 精确复用。当前 T02 119LF、T03 20LF、T04 12LF、T05 16LF 合计167LF；其完整原行事实、176 lam=0 的原残差消费、整异常向量 Πη-a.e. 与背景 ν-a.e.、空乘积 Dirac、非空零因子乘积和相同原观测双和的既有独立审查均在精确组件上沿用。没有因上下文延续而重审旧 producer。

当前组件推导：HEAD91＋固定正文30＋证明298＋PRE18＋分隔11＋CLOSE3=451LF。字面 RHS25LF 单独绑定。`CHANGE-COVERAGE.json` 为33段分别列旧／新半开字节区间、行区间、输入哈希和覆盖来源；`SOURCE-COVERAGE.json` 为451行逐行给出唯一当前或精确旧覆盖；`PROOF-COVERAGE.json` 的新131LF与旧167LF无遗漏／重叠。旧最初的计数字段修正历史保持封存，本轮引用有效的修正后覆盖及修复01覆盖并集。

## 实际主 API

已重新完整读取固定 `Integrable.lean` 1–178，SHA256 `d80e3495465030c1accca450935e4bfafcfe31d9b695e17f23ee9cfcea537759`，57371B；固定 mathlib 提交 `807d3836b165983210ee2ecf3cd28f239436949c`。命名空间51、变量47–49、Integrable定义58–60、integrable_const_iff完整137–139以及 `integrable_const` 完整165–167 均核对。接口完整头为 `[IsFiniteMeasure μ] (c:β) : Integrable (fun _:α=>c) μ`，正文 `integrable_const_iff.2 <| .inr ‹_›`；这里确实是函数常数 λ，且值域的 NormedAddCommGroup 是原实数结构。后文原有 integrable_const mA 和 mA² 使用相同 ν 的有限性。其余主 API／176和278完整实际接口的已有读证据精确复用。

## 两次失败与后续门

native01 的原源 `7fa38d18…`、收据 `db657611…`、RC1／5errors1warning／noO 保留；v2消息提取修正保持纯元数据历史。native02 检查的是修复01源 `1072d741…`，实际 RC1，6.051585357636213秒，1error4warnings，无对象；收据 SHA256 `124b81f51359d90c01bad2bfd5d0a070277352b709c0676435b69a93f743bd10`，42820088B；诊断 SHA256 `b76d4c165f55f2ef7ef6ab438d817485e0622b74800c32ee639b71a6795c2a41`，4969B。其唯一错误是原空分支得到函数零记号 0，而预期为显式 λo=>0。新稿的具体修复对应这一位置，但本审查不声称新证明项已获内核接受。四个 warning 所在证明内容精确保留，没有放松 option。

本轮没有运行 Lean、AX、compiler、probe、SSH、网络、Git、API、上传、cache/resource修改或子实例。下一步须由 lane 另有授权执行当前精确源的新 native，成功后同一个 FIRST original object 的全部实际 TYPE、所有非定理 FULLVALUE、传递公理及新ACT门控最终复核。Bernstein、Delta、Mills、异常指数积分、PE-R／PE-L／NR／DC、OQ56/root 仍 OPEN。
