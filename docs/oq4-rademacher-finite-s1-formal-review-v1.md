# RademacherFiniteS1 独立最终形式审查 v1

STATUS: CORRECT
FORMAL_STATUS: LEAN_FULLY_CHECKED
SCOPE: frozen-rademacher-finite-s1-v1 的完整 C1–C5
CRITICAL_GAPS: NONE
SPECTRUM_STATUS: OPEN
ROOT_STATUS: OPEN

冻结 C1–C5 的陈述忠实性、匿名数学证明、完整规范源、实际模块原源检查、真实导入环境、扩展契约和传递公理检查全部通过。本结论只认证零起点完整有限 S1 与独立低阈值分支，不认证 S2–S5、strict 事件、其他起点类或一般 OQ4。

## 1. 版本、授权与访问隔离

本实例先独立完成 PREP，原报告 SHA256 915bfa7b867dca7cea454a2ea00bd140cacb57221b1146e8d9ddaed8883eb86e／12447B，现精确归档为 review/rademacher-finite-s1-prep-review-v1.md，最终复核指纹仍相同。本轮仅在 lead 明确 AUTHOR_CANONICAL_READY、writerNONE 后读取新源与匿名证明。

| 固定输入 | SHA256 | bytes |
|---|---|---:|
| 原 spectrum01.md | b65f9e0c2f9b40a28d092491b479bd20d0b8ee8a9ac940c3c4760cfff7d2670b | 4306 |
| frozen-rademacher-finite-s1-v1.md | e2e9240f739e737c83195f177dcd54707c023151cf3e4faf7f1d862e87b585fe | 10956 |
| 匿名 proof.md | 5145ecabae8fd09c46bddf35ceda431c27633f40e29221e1ef3e7c25aad2d401 | 15767 |
| 规范 Shao/OQ4/RademacherFiniteS1.lean | d51b0d0712867e7a078871a49e3ffa7c8c59edf6695e07a306b9fe7bb4c65d13 | 13559 |
| 作者唯一 olean | 96f0010c733402bcf2a67fac0a8a631ec3642e91c0dffaa57e6c2d1196f61a41 | 942160 |
| 固定 base receipt | 54e224be3cb66e8d8b5b8e62cfd46bb5a25f89338249bbbb5cab40ea787642e4 | 6013 |

固定基础分支 feat/oq4-finite-s1 @ b8bcf3561a20ee91894de23fdb842b4a381b15be。只使用已认证上游公开完整类型和透明定义；没有读取旧 theorem 证明体。新规范源的全部证明体已完整阅读。未读取作者 receipt、过程、notes、新声明清单、其他数学／语义／形式 review 或 intake；目录查找只看到这些文件名。所有 raw Expr、全登记、原始日志、二进制只在服务器，自有工具未采用其他审查者的脚本或 raw。

AGENTS.md、SERVER.md、TEAM.md 及 math-theorem 必要协议已在 PREP 完整读取。所有本机 shell workdir 为 C:/game/shao lean；全部 Lean／重计算只在指定服务器 workspaces/lead-oq4。所有最终 Lean 检查均单进程、taskset -c 0-3、无 -o。未执行 Git、安装、cache 写入、共享修改或旧数学目标重编译。PREP 一次仅版本查询遗漏 taskset 已如实归档；不涉及任何最终检查或 emit。

工具链为固定 Lean 4.36.0-rc1（c9afcddf514a6772bd4d649f7cfc04eff0b9f15e）、Lake 5.0.0-src+c9afcdd，mathlib 固定 807d3836b165983210ee2ecf3cd28f239436949c，pins 终检未变。

## 2. 完整原源与实际导入审计

独立 canonical no-o 检查成功。随后构建实际模块镜像：
final/source-mirror/Shao/OQ4/RademacherFiniteS1.lean。

只前置 12B 的 import Lean LF，然后连续保留全部规范原字节 13559B，再追加局部 run_cmd collector。未前置旧 OQ4 模块，未导入自身 olean，未用 --stdin 假设 mainModule。实际 lake env lean -R <mirror> <file> 运行后，env.mainModule 为 Shao.OQ4.RademacherFiniteS1。

原源收集规则是全部 getModuleIdxFor?=none，完全没有 name、namespace、public 或预计数量过滤；collector 的函数均为局部值，不增加环境 helper。实测：

| 分类 | 实际数量 |
|---|---:|
| 完整 source-owned 常量 | 68 |
| definition／theorem | 1／67 |
| 显式 public theorem | 19 |
| 显式 public definition | 1 |
| 显式 private theorem | 8 |
| 生成声明 | 40 |
| raw private／nonprivate 名称 | 22／46 |
| 生成项中 private／nonprivate | 14／26 |
| 目标 namespace 外原源声明 | 0 |
| 新登记实例 | 0 |

19 是显式 public theorem 数；cotangent 另计 1 个 definition。没有把 nonprivate 名称 46 误当作公开定理数。

实际 direct import 选取真实 target owner、target raw/user namespace，以及原源全名称，测得 68 项，全部 owner 为实际 target。完整 all42 则显式导入旧 41 后追加新目标，以实际 42 owner OR OQ4 raw/user namespace 全量选取，测得 union 931：100 definition、831 theorem，100 private。不是仅用旧计数加法作为证据。

旧独立记录 863 项、99 个 definition 的完整 raw Name、user name、kind、universe 参数、完整 Expr type、全部 definition/opaque body、axioms、unsafe/partial/private、实例标记和原 owner 均逐字段保持 exact。opaque 数为零。旧 namespace 外 owner 项也保持。Shao.OQ4.killedAction.congr_simp 仍保留 Shao.OQ4.KernelRecurrence 的原 owner。

原 Source 与旧 863 的真实 raw-name 交集本次实测为 0；此前没有预设不相交。Source/direct/all42 的全部 68 项在忽略来源固有 owner 差别后逐字段 exact，import owner 另逐项验证。实际集合身份是 all42=old863 union source68，没有缺项、额外项或未解释名称。

完整 Expr 以 reprPrec／Format.pretty 保存，未用 PP 文本替代，未截断深度或长度；新源所有 type/body 字段无省略号。旧记录已在 PREP 通过 512 层最深标记 smoke，并保留最大 147112B type 和 41936B definition body。本轮全部旧字段直接用固定原 raw 比较。

## 3. 全实例域与实际检索树

每个 InstanceEntry 的完整 keys、Expr value、priority、raw globalName、synthOrder、attribute kind 均比较。覆盖 active、global/scoped 原登记、private、未激活 scoped、erased、newEntries，以及每层 stateStack、activeScopes、scopeChangedDecls、delimitsLocal 和 active entries。

| 同范围比较 | 活跃实例 | scoped namespaces／entries |
|---|---:|---:|
| 原 Source 原 imports + Lean／direct target + Lean | 24838／24838 | 41／349 |
| 独立 old41 + Lean／all42 + Lean | 25020／25020 | 42／350 |

两组分别比较，不混不同导入范围的数量。old41/all42 的导入原登记均为 25453 entries；新增 target 模块的导出实例登记为 0。所有共同实际模块的原始登记数组 exact，Source/direct 与 old41/all42 的 active、scoped、erased、new、完整状态栈均 exact。

另独立导出真实 discrTree 的每条 path 和完整 entry，及每层状态栈的检索树。Source/direct 均实测 24838 项，old41/all42 均实测 25020 项；两组的每个路径及该路径内 entry 顺序、全部字段 exact。没有只检查 instanceNames 而忽略检索结构中的条目。

比较仅对无序的外层 map 枚举规范排序；每个 entry 的字段及 synthOrder 等顺序敏感数组、scoped PArray 内顺序、同检索路径内顺序均保留，不以递归排序掩盖差异。PREP 的独立 global/private/inactive-scoped/erased 实例 smoke 也保留。

## 4. C1–C5 的独立语义与证明核对

| 冻结项 | 规范对应与判断 |
|---|---|
| C1 | 第 29 行 vector_zero 对全部源 j 保留；第 88、102 行覆盖完整偶数 Icc 1 m 和奇数 range(m+1)。vector 的透明相位在零起点精确成为 j*pi/2，不先假设奇数。 |
| C2 | 第 107、130 行的整数状态双射把 s=-m,...,m 精确送到 k=0,...,2*m；sin 相位为 theta*(k+1)。第 142 行有限望远镜恒等式保留首末项；奇 j 的 cos(j*pi-t)=-cos(t) 给出未归一化 counting sum=cot(t)。第 165、179 行证明 0<t<pi/2 与 sin(t)非零。第 189、219 行得到计数和及旧 norm H 下的实际 coefficient，cotangent 透明定义为 cos/sin。 |
| C3 | 第 34–75 行给出全部指标、偶／奇合法区间、完整 partition、奇数单射及自然数逆 (j-1)/2。第 226 行实际重编号同一有限和，只以实际 vector_even_zero 消去偶项。独立契约还机械证明两个形式不交、逆的唯一性及首末端点。 |
| C4 | 第 256 行直接调用同一 law、真实 killedMass 的认证 AllModes 全模态等式，在真实整数起点0重编号。第 283 行通过非负 h 的真实桥接到 Measure.pi.real closedStrip。量词为全部 m>=1、m<=h<m+1、全部自然 n；没有正时间或谱正性条件。 |
| C5 | 第 308 行调用允许 m=0 的真实 killedKernel_row，证明零起点第一步测度行=0；第 315 行零步使用真实 Dirac，正步按 1+k 的实际半群次序，先积分第一步零测度。第 335 行桥接相同真实 closedStrip 概率。没有使用 m=0 全谱或 C4 退化式。 |

已完整阅读匿名证明并逐步核对：有限状态重编号、半角望远镜首末相位、奇数符号、全指标奇偶分拆、AllModes F=1 的实际系数及低分支半群方向均成立，没有未写前提或关键缺口。

独立 ExpandedContract-v2.lean 将 cotangent 展开为 cos/sin，将路径事件展开为 Fin n→Real 上的所有 k<=n 的真实 prefixSum 条件，并对真实 product measure 与真实 killedMass 同时验证。还检查全部 j 起点值、两种完整 parity 范围、计数和、旧 coefficient、角度与非零分母、唯一逆、不交、首末端点、完整高阈值显示式、同一和的 n=0、h=m 弱端点、低阈值零行、全部自然 n 的低分支及 h=0。该契约实际退出0。

边界检查无遗漏：
- n=0 使用同一完整 range(m+1) 求和与 cos^0，没有删除零谱项；第 297 行 finite_s1_zero 证明其值为1。自然数幂 0^0=1，零谱的 cot 参数为 pi/4，分母合法。
- m 为偶数时，奇数和内 j=m+1 的零谱项仍在原 range；仅正时间令 0^n=0。m 为奇数时该全源指标为偶数，因实际起点值0消去。
- j>m+1 的负余弦及末模态 ell=m 全部保留，幂在 Real 中有符号；无 abs、主模态替换、奇偶匹配、正生存或非零谱前提。
- closedStrip 使用弱 <=；h=m 被形式契约实际实例化，±m 保留，吸收点为 ±(m+1)。真实核限制不重新归一化。
- C4、C5 合起来覆盖全部 h>=0；floor 总述属可导出表述，不以另一个概率对象代替。没有把 weighted cosine 或 raw mass 单独当作路径概率。

## 5. 公理、命令和保护结果

完整新原源 68 项与 all42 931 项传递公理只含 propext、Classical.choice、Quot.sound；无 axiom kind、unsafe 或 partial。按词法移除嵌套注释、行注释和字符串后，规范源 sorry、admit、axiom、unsafe、native_decide 的 token 数全部为0。新实例登记为0，不能通过实例覆盖改变真实 law 或命题。

所有以下 Lean 命令均先 source 固定 activate.sh、再 cd 指定 worktree，统一用 taskset -c 0-3 lake env lean；无 -o，按次串行：

| 实际检查 | 耗时秒 | exit |
|---|---:|---:|
| Shao/OQ4/RademacherFiniteS1.lean canonical no-o | 5.046 | 0 |
| -R final/source-mirror 完整实际模块原源 | 10.133 | 0 |
| final/DirectAudit-v2.lean | 23.208 | 0 |
| final/All42Audit-v2.lean | 16.801 | 0 |
| final/ExpandedContract-v2.lean | 4.178 | 0 |
| final/tree-old41.lean | 7.666 | 0 |
| final/tree-direct.lean | 7.632 | 0 |
| final/tree-all42.lean | 7.649 | 0 |
| -R final/tree-source-mirror 的完整实际模块原源 | 9.037 | 0 |

完整命令、时间、退出码在各 run.json 和 tree-runs.json 中。强字段比较另以 taskset -c 0-3 python3 final-compare.py 实跑 3.613秒、exit0。

前后及最后一次保护均通过：旧 41 OQ4 源 + protected92 = 133 个旧 source/config 原字节不变；新规范源固定13559B；旧98产物 + 作者sole olean = 99 个产物指纹全部不变。没有额外目标 .ilean／hash／trace 等产物，自有 emit=0、live Lean/Lake=0、private compiled artifact=0。所有数学、公共源、根导入、pins、cache 均未修改；只写自有报告与自有服务器审计目录。

## 6. 自有证据与失败分母

全部原始证据位于：
/root/rivermind-data/shao-lean-20261021/workspaces/lead-oq4/repro_outputs/oq4-rademacher-finite-s1-independent-v1

PREP 的 old41-raw.json 固定 SHA256 4aa792a38452da52a74f926ef126571067b7f5d0893e2edf94a50ac6f62ce032／49094475B，作为原字段基线。

| final/ 自有工件 | SHA256 | bytes |
|---|---|---:|
| source-raw.json | eddcc75bc3105139258813d7795ed4e98ad5b77b634dd2f46a7c6dda4d4a56b1 | 56574879 |
| direct-v2-raw.json | 6c246296d4b521a8559b53cea803454e082113697ff7e72433bdfddad38fab2e | 56576718 |
| all42-v2-raw.json | b597928a8bab30b1ce9f0e5e562e51e2f792b311fbf115e8e59d80b84f397fb1 | 49435914 |
| final-comparison.json | 49916399f1dade5332c0b78885849aa3ae2c16ca9d08ffcf2d1fe11d3e6b11af | 1054 |
| ExpandedContract-v2.lean | b46b4e3068a2e129ce4780cedf3acd982db2904bf81bcb2688492837c22658bd | 6142 |
| tree-exact-comparison.json | 7fbf0abf68bd19a706a9206eb1e116f31890a79abc7e47461d51e978a26f129e | 507 |
| after-protection.json | 7068ec70410a4004941437255f78f3204857398a8f7c4eb9c7391229ecc281ed | 548 |
| final-failure-history.json | 8675eed352f88b9f89e5ddf8fe41a1893971f89c324bfad61c6b17cc15a9eac2 | 1438 |
| final-curated-receipt.json | ea5945082b0cbcf1bf3fa8f2782e22e7289941df76767b8fe3a0f0acf50f20dd | 1963 |
| final-artifact-manifest.json | d805c4eb0aebeb909070a7116cfe4944d96babd5abcf569d9ac6bd9ead266075 | 7858 |

失败与修正全部保留，未改任何数学字节：
1. PREP 所有失败与一次版本查询 affinity 偏差仍在原归档与 operational-failures.json，不删除、不改写。
2. DirectAudit v1 与 Source 的 active/scoped/erased/new/共同模块 entries 已 exact，但审计器的 open 作用域不同导致状态栈层数、activeScopes、delimitsLocal 不同。v2 使用相同局部 collector、相同 BigOperators／MeasureTheory 词法打开后，全部实例状态 exact；初版结果保留。
3. All42Audit v1 退出0并实测931；为同范围完整 registry 顺序审计，v2 将 target import 放在旧41之后。旧 common module entries 与所有域逐字段 exact，不以不同导入顺序产生的枚举形状作结论。
4. 最终比较器只排序无序外 map，保留所有顺序敏感 entry 数组；完整检索树又作了独立补充检查。
5. ExpandedContract v1 退出1，因为端点合取目标未先拆分而直接 omega；另有 if_neg 弃用警告。v2 显式构造 membership 合取并改用 simp [hn]，退出0且无输出。原失败源和日志保留。

没有未处理的数学、形式或保护缺口。结论为冻结 C1–C5：CORRECT / LEAN_FULLY_CHECKED。Spectrum 与 OQ4 根继续 OPEN。
