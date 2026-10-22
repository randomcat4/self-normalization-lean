# 实际 Ξ 一、二阶 u 导数：作者交付

STATUS: AUTHOR_GATES_PASS / INDEPENDENT_FULL_PROOF_REVIEW_PENDING。冻结的两个公开定理已经目标编译及全部所属/传递公理门通过；这不是作者给自己的独立 CORRECT 票，根整合尚未进行。

## 不变交付身份

- 分支 author/c12-xi-derivatives-v41；提交 82f477c88b63ca3b6a5d2371a9ef24e1a584ee8a。
- 父提交为 v40 accepted dc1604d8e9c88781166a0c797f45b84ff013673a。
- 唯一已提交文件：Shao/Probability/QuadraticFullNoiseDerivatives.lean，171 LF 行、7762 UTF-8 字节。
- 完整源码 SHA256：25f432d891b1c2a115b5ca91b1fb89fc888d52bf28547c3606f022f7d30ddcf5。本地归档、两次 runner 源快照、实际目标编译、实际 audit 和提交中的源码相同，成功门后没有编辑。
- 新公开面恰为两个 theorem：quadraticFullNoiseChar_derivatives（源码第 100 行）及 quadraticFullNoiseChar_derivative_bounds（第 142 行）；0 public definition。
- 冻结 header 和两个完整类型逐字匹配；类型 SHA256 分别为 aecfe0491042bf5322b18ff10304b33d85bb9714f3dbd55dd5cc288d872db54c、8baaf861356f752e4a97d573feeb82abdd894a56e104e7365729f852ce2d5b4d。source-check.json 记录匹配、完整输入、公开/私有声明清单及禁用词检查。
- 项目源 import 闭包为 9 文件（新模块 + 8 前置）；全部 8 前置源逐一与父提交 Git blob 字节相等。包含 QuadraticFullNoise.lean 的 SHA256 a280ff36549f2c59356fd4fa89b3e442eece91f2a0e3bb4eea553d3605e1a116。项目其他已跟踪文件无 diff；没有改根 import、manifest、总 state、其他作者模块或源码输入。
- 提交后 tracked diff 和工作树 status 都为空；没有 GitHub 发布、push 或 merge。

服务器工作树：/root/rivermind-data/shao-lean-20261021/workspaces/c12-xi-derivatives-v41。
服务器原始证据：该工作树 logs/c12-xi-derivatives/。本地完整源码、结构化证据、实际类型及本收据均在 C:/game/shao lean/drafts/c12-xi-derivatives/；原始完整日志和缓存二进制留在服务器。

## 完整证明连接

私有 noisePhase（第 9 行）就是既有正号相位。第 12–46 行分别证明相位范数为 1、第一乘子范数为 |z1|、第二乘子范数为 z1²，以及三个被积函数在实际测度下的可积性。第一、二个 dominator 直接使用既有真实绝对一阶矩与二阶矩，不输入候选导数或所需界。

第 48–57 行从实仿射相位经 ofReal_comp、乘 I、cexp 链式法则获得逐点实导数。第 59–73 行以 Set.univ 及 |z1| 作统一支配函数进行第一次参数积分求导。第 75–98 行以 z1² 作统一支配函数进行第二次参数积分求导；第二乘子通过 I²=-1 的明确环恒等式核对，不需要源律中心化。

第 124–139 行的公开导数证明从 quadraticFullNoise_law_data 登记同一实际 full law 的概率实例，从 quadraticFullNoise_support_moments 提取 M1/M2。它先对每个实数 r 建立真实特征函数的一阶 HasDerivAt，再把第二次加权积分 HasDerivAt 通过全 r 的标准 deriv 积分等式作邻域最终相等运输，得到真实标准一阶导数函数的 HasDerivAt。最后两个积分身份是这两个 HasDerivAt 的标准导数值。

第 157–169 行的公开界证明从同一真实矩定理提取 67/3*gamma 与 70/3*h*gamma。用第一公开定理重写真实导数，分别通过 norm_integral_le_of_norm_le 和两个逐点范数式连接到这两个矩预算。没有自由 Xi、替代律、源中心化、频率非零条件或新正则性前提；u0/v0 为任意实数，两个坐标轴与原点均被覆盖。

原范围是 supplement.tex LF2595–2605 的 h:supp:highderivatives(b)，证明 LF3355–3356。原文件 SHA256 b99f2ac4d2f39dd39772d98a5702b7a923c2f10f8730a08fc1b4cd6bba4742bd。锥内界、高频乘积、反演、去平滑及原 C1/C2 根仍 OPEN；本节点不计 v40 完成数量。

## 实际服务器门

所有新重型进程均先 source activate.sh，再 cd 指定 worktree；CPU10–13、原生 -j4 -M8192 -DautoImplicit=false，一次只有一个本作者重型进程。外部 PID143204 最终仍为 python3，affinity CPU0–9；未动其 80GiB 预留、家族进程或其他分线构建。

实际版本：Lean4.36.0-rc1（commit c9afcddf514a6772bd4d649f7cfc04eff0b9f15e）；Mathlib pinned commit 807d3836b165983210ee2ecf3cd28f239436949c；manifest SHA256 40e8e3385f2b0c8ae56fa9de6947301472379cb62eeb83247944827c38b8af6e。

1. 目标：lake env lean -j4 -M8192 -DautoImplicit=false -o .lake/build/lib/lean/Shao/Probability/QuadraticFullNoiseDerivatives.olean Shao/Probability/QuadraticFullNoiseDerivatives.lean。attempt02-result.json：exit0，6.921437s，maxRSS3409012KiB。首次实际 Lean 运行即通过，无证明修补或成功门重复。日志唯一内容为已有 Mathlib local-changes 提示。
2. 审计：lake env lean -j4 -M8192 -DautoImplicit=false logs/c12-xi-derivatives/Audit.lean。audit01-result.json：exit0，6.546821s，maxRSS3758452KiB。所有 13 个实际目标模块所属常量都被枚举，包括 2 public theorem、9 显式 private theorem、1 private definition 和 1 自动生成 noisePhase.eq_1 theorem，共 12 theorem/1 definition。全部 268 个实际导入 Shao 所属常量逐个 collectAxioms 传递审计，只出现 propext、Classical.choice、Quot.sound。
3. owned-audit.json 完整列出 13 所属项及全部 268 导入项的名称、真实 owner、种类和传递公理，无名称空间或 public 过滤遗漏。actual-public-types.txt 是实际编译环境 pp.all 下两个公开类型的完整输出。两个 public #print axioms 同样只得到标准三公理；Audit.lean 保留可复现审计源码。
4. 第一次 runner 仅因系统没有 /usr/bin/time 而在 Lean 启动前失败；attempt01-runner-error.json、空 attempt01.log、preflight 和源快照均保留。改用 Python resource/time 采集后，同一源码通过目标编译；没有删除失败记录。

## 如实记录的只读范围事件

解释 Mathlib 既有 local-changes 提示时，作者错误地请求 Git untracked 路径清单，遇共享 .gitignore 符号链接循环，意外枚举了缓存路径。已立即停止；没有写共享包或缓存、没有修复/重配共享环境、没有因此重复 Lean。原始 3927326 字节元数据留服务器 metadata-inventory-incident.json，SHA256 601126a2dfa287b8340499625d7472b4b6c682ee7c87729c0c4ea7abacc9b29f。本地只保存 inventory-incident.json 的有界事件记录。不能据此声称共享 Mathlib 源工作树 clean；本任务仅确认固定 HEAD、给定接受缓存、项目前置源字节不变及完整传递公理门通过。

## 证据 SHA256

- 目标日志 attempt02.log：51c34acb1f50fb265f877743d9162c7f2932ba37876f417a582cf8bfb5f175e7。
- 审计日志 audit01.log：e1fb7fb6019851a11d88311ee4268c870bfa5924a32f0590e1df965aa3c2d48d。
- Audit.lean：54a6ac03ba7ba90ac4eae3a7182d241d9494900dce522740477940f1cb191eb3。
- owned-audit.json：37f92624dc286b9469f06db5d6d63542ada6c60d1cf7f325781bb3250108d2df。
- actual-public-types.txt：a31bf56ee3c08a71b0862d05e2c1b7cbb682d6bb86dbd71520b2025cedbec2d4。
- metadata.json：1e0f20d9f9b807d8cd934aad4bec74484e1316113bc75653059a2316a95de2cf。
- source-check.json：d24f7ba611c4597679b81544a3d8afd02049535b735e4bb3e16f583ec224cef5。
- author-receipt.json：83084da3496a431b08256443758aaa9cda4897f9a6ae3bf731586a2a69a56ed2。

其余日志、资源快照、源快照与全部证据哈希见 evidence-hashes.json 和 author-receipt.json。本收据及源码交付后 STOP，由新的独立 reviewer 进行完整证明/类型/来源/收据审查，再由 root 决定整合。没有自认证独立正确性或原根闭合。
