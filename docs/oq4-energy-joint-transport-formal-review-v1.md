# EnergyJointTransport 独立最终形式审阅 v1

STATUS: CORRECT
LEAN_STATUS: LEAN_FULLY_CHECKED
SEMANTIC_TRANSLATION: AUDITED
E3_STATUS: OPEN
OQ4_ROOT_STATUS: OPEN

本票接受且仅接受冻结的联合尺度标量相对传递薄叶。新鲜、非作者审阅者独立完成来源—冻结—实际接口逐字段审计，以及三个正式服务器门；未发现关键缺口。没有据此认证共享双变量算子、killed 边界、K/Kv、条件能量 E4、随机分母或完整 E3/OQ4 根，也不作新颖性裁决。

## 认证对象与独立性

规范源为服务器工作树 `/root/rivermind-data/shao-lean-20261021/workspaces/lead-oq4/Shao/OQ4/EnergyJointTransport.lean`，SHA256 `fe6fe757c7fe997cc36727477b4d22f17c2373b7e90657d68f7b5d7ef8d2a39e`，22604 字节。唯一既有作者 olean 为 `.lake/build/lib/lean/Shao/OQ4/EnergyJointTransport.olean`，SHA256 `2979d67eb763a4a8e69f38dd736db5cee49e6169d93bc74f82c7bfce023d807a`，838888 字节。审阅没有 emit 或改动它们。

分支 `feat/oq4-joint-transport`，HEAD `51a137af89b4c7060ac4af0baf6410820bc76a4f`。基线收据 SHA256 `6a262871ac49132ccb475216a73e2d02e969fe06e329fc3f48842ae417bb4fad`。原始 `energy01.md` SHA256 `2e0387f0a35ca677853e45fff271cc2fb0e87db9ee9c6b2f00d3bcf56b51d9e6`；冻结稿 SHA256 `415ae0a03c480d3dcc2d370662a9d4e050d941fe609821d2996c5c69ceb42fb4`，6797 字节；匿名证明 SHA256 `69364de066f5f008f4130f3ba8665b1455a91dc6716ad643ff234983d7daac2b`，20436 字节。三个文本均独立核对；证明第 70 行原有公式排版未改字节。

准备阶段未读目标或私有 Source；收到 lead 的 AUTHOR_CANONICAL_READY 后才开始正式门。未读取其他审阅票推理、作者检查点或 intake。原准备票按原字节保存在 `energy-joint-transport-formal-review-v1.prep-history.md`，SHA256 `bfca20519ab4987f039cdf3dfc68b83efd983d93f5b87f52eaf02635ed933ad9`。

## 来源、冻结与实际声明的逐字段绑定

以下行号均是已核验 SHA 的规范源行号。只读取已认证旧模块的实际接口与透明定义，没有依赖其他未认证实现。

| 冻结义务 | 实际形式绑定与核验 |
| --- | --- |
| 固定原律及矩条件 | 总入口 339–344 行固定一个 `ν : Measure ℝ` 与概率实例；平方、绝对三次方真正可积、原均值 0、原二阶矩 1、β≤M、M,T≥0 全部显式保留。各 j 没有更换原 ν，也没有添加 M≥1、密度、对称、非格点或四阶矩。对应来源 7–24、47–58 行。 |
| 真实对象 | 12–19 行的 p、r、I 分别是实际 `energyTiltedLaw`、`energyLinearTiltLaw` 的 `Measure.pi` 闭条带概率，以及原 ν 的 `energyPathIntegrand` 积分。实际旧定义 `energyWeight`、Z、两层 `withDensity`、L、闭条带和能量积分体均已展开核对；九个新定义没有 `True` 或抽象概率替代。 |
| 内部选择同一 θ，先于全部长度 | 345–351 行是 `∃ θ, … ∧ ∀ n, n/h³→0 → …`，不把外部 θ 或 E2 当总入口前提。353–361 行先对输入对 (a,b) 用共同有限存在接口选择 Θ，再令 θ j=Θ(h j,s j)，没有接触 m、n 或样本。347–348 行返回该 θ 的 E2 与所有有限 m 路径结论。 |
| 内部有效尾部，保留早期零/负高度 | 364 行从 h→+∞ 推出最终 H≤h j；346、369–370 行在 h j<H 时 θ j=0。没有加入逐项正高度、逐项阈值或早期倾斜律的概率假设。所有概率性、正性和真实积分主张都位于这个尾部。 |
| 唯一联合尺度前提 | 总入口 350 行和辅助极限声明仅要求 n/h³→0；没有 n→∞ 或 n/h²→∞。124–157 行从 h 的倒数趋零及 n/h³→0 得 n/h⁴→0，并沿透明误差定义返回 e₂、e、δ₂、δ 及 exp(±e₂)、exp(±e) 的八项极限。恒零、有界和任意变化的 n 都包含。 |
| 实际概率性、矩、中心化、可积性、有限乘法界 | 41–52 行包含 E1、E2、L>0、Z>0 与完整 `energyRelativePathConclusion`。旧透明 E1/E2 含实际概率性、三种矩可积性、精确中心化及同一共同常数；旧路径结论 17–38 行含 e₂/e 非负、真实 I 被积函数的 `Integrable`，以及冻结的两组指数乘法夹逼。160–185 行从已认证接口逐项构造这些结论。 |
| 真正相对误差与零质量安全 | 47–52 行保留 δ₂·r、δ·r，58–64 行对每个 η>0 最终保留 η·r。101–108 行由上下指数界证明绝对值界，仅使用 r≥0，没有除以 r。故 r=0 时直接强制 p=I=0；没有以绝对差趋零冒充相对传递，也不声称无条件比值趋一。δ 的尾部非负由有限结论返回。 |
| 五项归一化与终点支付极限 | 31–39、188–273 行返回 n log L→0、|θ|h→0、Lⁿ→1、n(log Z−s/h²)→0、exp(−sn/h²)Zⁿ→1。237–239 行先从实际 `energyLinearNormalizer_pos` 得 L>0，再使用正底数幂恒等式；268–270 行对 Z 同样处理。254–259 行先用 E1 的 Pβn/h³，再以 β≤M 放大，没有在有限 j 把能量归一化因子设为 1。 |
| 三个空间的真实 iid 转接 | 66–99、276–307 行分别量化 Ων、Ωμ、Ωθ（独立宇宙参数 u,v,w）、各自概率测度、逐坐标可测、各族 iIndepFun，以及对真实 ν、μ、μθ 的 IdentDistrib。借实际旧概率等式得到 p̂=p、r̂=r，旧积分转接同时给出原律样本能量函数可积和 Î=I，再代入同一相对误差。371–374 行在已选同一 θ 的尾部对每个有限 m 和全部实现返回结论；没有跨空间或跨 j 的独立、耦合、共同空间或联合可测假设。 |
| 事件、边界与范围 | 实际 `Shao.closedStrip` 是全部 k≤n 的弱闭绝对部分和条件，包括 k=0；没有累计均值移边界。n=0、弱端点原子、格点和全零路径均未被排除。s=0 仍保留真实截断再归一化律与 Zⁿ；I 始终是能量加权原律积分。对应来源 (7)–(8)，不扩张为 (9)–(10) 或 E4。 |

六个显式公开定理实测为 `energyJointTransport_error_limits`、`energyJointTransport_finite_of_e2`、`energyJointTransport_normalization_limits`、`energyJointTransport_iid_of_e2`、`energyJointTransport_sequence_of_e2`、`energyJointTransport_common_bounds`。辅助定理允许已给 E2，但最终存在型总入口内部产生 E2 与同一 θ，因而没有把冻结结论重包装成前提。

## 实际执行的正式门

环境均先激活，再进入指定工作树；每次至多一个审阅者 Lean 进程，均为 `taskset -c 0-3 lake env lean`，没有 `-o`、Git 操作、cache 写入或 root/common/source 修改。Lean 4.36.0-rc1（commit c9afcddf514a6772bd4d649f7cfc04eff0b9f15e）、Lake 5.0.0-src+c9afcdd 与项目钉死版本一致；mathlib `807d3836b165983210ee2ecf3cd28f239436949c`。

1. **规范目标直接 no-o：通过。** 输入直接为 `Shao/OQ4/EnergyJointTransport.lean`；退出码 0，5.02 秒，stdout/stderr 均为空。它未使用审阅副本替代真实规范源。
2. **完整原源、实际逻辑模块路径、无筛选 allnone：通过。** 服务器自有 `fullsource-root/Shao/OQ4/EnergyJointTransport.lean` 保留规范源全部 22604 字节，仅在第一条原 import 后插入 12 字节 `import Lean\n`，末尾附审计。字节恢复测试与原 SHA 完全相同。命令使用 `-R …/fullsource-root …/fullsource-root/Shao/OQ4/EnergyJointTransport.lean`，实际 `env.mainModule` 为 `Shao.OQ4.EnergyJointTransport`。原 imports 环境实际仅导入 19 个旧 OQ4 依赖；没有额外 prepend 旧 37 或导入自己的 olean。逐一枚举所有 `getModuleIdxFor?=none`，没有名称/命名空间过滤或预设计数；实测 36，全部传递三公理合格。退出码 0，7.68 秒。
3. **实际完整 38 导入与精确对照：通过。** 显式导入保护集合的旧 37 加唯一目标，并用实际 `env.header.moduleNames` 比较精确集合；RademacherIteration 不在集合内。OQ4 所属模块 **或** OQ4 名称前缀的并集 759，实际 OQ4 模块所有者 759，仅 OQ4 命名空间 734；更广 Shao 所属模块或前缀并集 982，分别记录。759 个常量全部通过 `propext`、`Classical.choice`、`Quot.sound` 传递白名单。退出码 0，11.23 秒。

不把 pretty-printer 摘要作为完整类型证据：使用已实际烟测成功的原始 `reprStr ci.type`，保存完整 name/kind/universe/fullExprtype/axioms；无 pp.width、pp.maxDepth 或猜测选项。源 allnone 36 与实际导入目标模块所有者 36，在名称、种类、完整宇宙参数列表、原始 Expr 类型、公理集合逐项精确相同；另外比较九个定义的完整 Expr 定义体与实例注册标记，也完全相同。旧 723 个常量的完整五字段同样逐项保持。

新增全量实测 36=27 个 theorem 常量+9 个 def；后验分类为 6 个显式公开定理、3 个显式私有定理、18 个生成定理和 9 个定义。18 个生成项为 14 个 `_simp`、3 个新路径对象的 `eq_1`，以及实际归属本模块的 `energyRelativePathError2.eq_1`；最后一项虽有旧函数名称前缀，也未被漏掉。18 个新增常量的 universe 列表非空，包含生成 `_simp` 的 u_1/u_2/u_3；未将它们假定为空。注册实例使用实际 `Lean.Meta.isInstanceCore` 查询，新增注册实例为 0。文本危险项扫描无 sorry/admit/新 axiom/unsafe/native_decide；全量传递公理审计同时排除了隐藏依赖。

## 保护、不变性和证据位置

独立最终前后快照逐字节保护：旧 OQ4 37；从不可变 HEAD blob 再核对的 92 个公共/其他/根/版本文件（32 公共、56 其他源、4 根及版本锁）；更广的全部已跟踪非 OQ4 Lean 文件 152；整个本工作树 `.lake/build` 的 95 个现有工件；规范目标、唯一 olean、匿名 proof、包链接和 mathlib HEAD。集合与每文件 SHA256/大小全部相同；目标构建工件精确只有上述一个 olean；RademacherIteration 规范目标仍不存在。准备阶段自己的旧 OQ4 工件快照实测 37，最终扩大到整个 build 的 95，未将两者混称。最终实际 lean/lake 存活进程数为 0。

所有完整原始日志、类型/定义体、清单和脚本仅在服务器 `repro_outputs/oq4-energy-joint-transport-independent-v1/`。本地精简收据 `energy-joint-transport-final-receipt.json` SHA256 `7f86faea672a2663092d81653ef0f5dd25d1fa73ac9a363b7f991489b36ae22f`，14399 字节；它记录全部命令、退出码、计数、声明分类、关键文件哈希和语义门结果，不包含原始完整日志或 Expr。

关键服务器证据：

- 最终脚本 SHA256 `240331606553984e71240fe7ea76dcfff50227946450c0e2d9392d61512621c0`。
- 完整原源审计清单 SHA256 `e918cab3389015be7c2c616e2eb947d0c7a395c51413e505c8183beed4ce7c77`。
- 实际 full38 清单 SHA256 `1f82eeba013e6e7bbfa60e7f69ec3414fbbbe9f7f64ff390223513294d456c98`。
- 最终前/后快照 SHA256 `4650e271d791adda59299cc23c6249f51d6d2429bf66023ea1acd02802d4a24c` / `fc3231165c4cb9b4d7e1b31d30e57a769d4e59cbdfbca09e6a0f66134c8d7838`。
- 最终完整精简认证收据 SHA256 `b37a2a63d603b3faae848c7a9cf74cc28ec11294fc86ad2897fe612ee5069058`；原源字节恢复 v2 SHA256 `66e567a9ff77310b63a2959b82fd3586394692345bb5861f48df3ed1d0995241`。

工具准备错误保留历史：首次实例查询用了错误名称空间，exit 1；修正为实际 Lean.Meta 接口。第二次机制烟测发现 `--stdin` 即使给文件名也将 mainModule 设为 `_stdin`，故没有用于目标认证；改用实际逻辑模块路径 mirror/-R 后烟测成功。另一次补充元数据曾仅搜索 `.proof_` 而把“生成名称”标签列空，已留 v1 并在 v2 按全量清单减显式源声明修正；它从未参与 allnone 选择或精确比较。规范源、proof、olean 和数学前提均未修改。三个正式目标门均一次通过。
