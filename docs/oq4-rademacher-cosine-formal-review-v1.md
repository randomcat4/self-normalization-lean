STATUS: CORRECT
FORMAL_STATUS: LEAN_FULLY_CHECKED
SCOPE: 仅冻结 RademacherCosine 一步有限叶。
ROOT_STATUS: OPEN

# RademacherCosine 独立形式审查 v1

## 结论和固定绑定

冻结的全部有限义务均由实际 Lean 声明覆盖：内部证明实际二原子 law 的概率性，给出真实弱闭 killedKernel 的两原子行，供应真实余弦可积性，证明 Kcos 及真实核积分的一步主余弦身份，以及 0<a<π/2、0<ρ<1。独立目标 no-o、完整原源码检查、完整 36 模块导入审计均通过；源码环境全部新增声明与实际导入模块的全部自有声明逐项精确一致。无关键数学或形式缺口。

本次不接受完整有限谱 S1、S2–S4、时间 n 的迭代或生存质量结论。所有原完整根仍为 OPEN。数学审查原件维持 MATH_ONLY／LEAN_NOT_RUN；本报告只新增此冻结有限叶的实际形式核验。

| 工件 | 字节数 | SHA256 |
|---|---:|---|
| 固定源 `C:/game/shao/current/oq4/c01/spectrum01.md` | 4306 | `b65f9e0c2f9b40a28d092491b479bd20d0b8ee8a9ac940c3c4760cfff7d2670b` |
| `drafts/oq4/frozen-rademacher-cosine-v1.md` | 4709 | `9532d25fa6027881db213374980ef4a7273f96c3166847855d655fd18703e91c` |
| 匿名数学证明 `drafts/oq4/rademacher-cosine/proof.md` | 13237 | `1d599f635c633e11355f29ef5748e23e1e836486fc8fdc99d404b07afbfd8e6d` |
| 独立数学审查 `drafts/oq4/review/rademacher-cosine-math-review-v1.md` | 6701 | `0cacd6aaa1f3535c26a6e2118e24067696c49e88444823cbcb75d8740f97d08b` |
| 实际目标 `Shao/OQ4/RademacherCosine.lean` | 8414 | `c0ba478f9ed6b5aa75d7010d70835b37065a92e9878c65b086d3c3ff24e7f861` |
| 作者已生成的目标 olean | 429360 | `bbef5afc3922ee9fbfaaf6b1bc1d579b7ec762862e795e7a78165064bfb5aea3` |

固定 release 合同为 `feat/oq4-finite-continuation`，HEAD `c846961bd3dd7a4bac6178b04baa50393ab23cf2`。服务器 release manifest 的 SHA256 为 `ca90cf5958f135ca19e7e0003d5423204fe50250f6030b7b3e2a9c667a3c1a05`；独立核验其旧 35 个源文件的实际内容完全相等。本角色未调用 Git 查询或修改分支。

固定源第 11–21 行指定 m=floor(h)、H=m+1、整数状态和邻接递推。对 j=1，sin(a(r+H))=sin(ar+π/2)=cos(ar)，所以本叶是该一步递推的严格弱组件。这里只核对这个来源绑定，不据源中的完整谱或后续渐近候选结论判定本叶正确。

## 独立执行与保护范围

服务器工作区为 `/root/rivermind-data/shao-lean-20261021/workspaces/lead-oq4`；下文 R 表示其 `repro_outputs/oq4-rademacher-cosine-independent-v1/` 目录。原始日志、完整表达式表、前后指纹及所有二进制均只留服务器，没有复制到本地。

本角色先于 AUTHOR_READY 仅创建旧模块／公共文件／根文件快照及通用工具，并运行仅导入旧 35 模块的自检；直到 AUTHOR_READY 才读取目标内容。之后所有 Lean 命令均在服务器激活固定环境后执行，并使用 `taskset -c 0-3`，本角色最多同时一个 Lean 进程。所有检查均不带 `-o`，没有写入目标、作者 proof、冻结文件、根模块、公共模块、缓存、Git 或任何 olean。

实际版本命令均 exit 0：

- `taskset -c 0-3 lake env lean --version`：Lean 4.36.0-rc1，commit `c9afcddf514a6772bd4d649f7cfc04eff0b9f15e`，Release，x86_64-unknown-linux-gnu。
- `taskset -c 0-3 lake --version`：Lake 5.0.0-src+c9afcdd，Lean 4.36.0-rc1。
- `lean-toolchain` 为 `leanprover/lean4:v4.36.0-rc1`；manifest 中 mathlib rev 为 `807d3836b165983210ee2ecf3cd28f239436949c`。

| 检查／阶段 | 实际结果 |
|---|---|
| 独立 pre-snapshot | Python exit 0；旧35、common32、其他非 OQ4 56、根／版本4 |
| 初次远端工具写入请求 | 请求最终 exit 2；嵌套引号语法错误，后续找不到脚本；尚无目标读取和 Lean 执行 |
| 修正后旧35-only `lean --stdin R/AuditSmoke.lean` | Lean exit 0，Python exit 0，4.722 秒，新增常量0 |
| AUTHOR_READY 后保护检查、prepare-ready | Python exit 0；目标8414B和已冻结 olean 哈希吻合 |
| `taskset -c 0-3 lake env lean Shao/OQ4/RademacherCosine.lean` | exit 0，4.071 秒，日志0B |
| 首次 source（错误额外前置旧35 imports） | Lean exit 0，Python exit 0，5.326 秒，所有 none 实测34 |
| 首次 actual full36 compiled audit | Lean exit 0，6.826 秒；exact 比较 Python exit 1，正确拒绝两个 fullExpr 差异 |
| 修正 source 审计构造、prepare-ready | Python exit 0；未改目标或 olean |
| 最终 `taskset -c 0-3 lake env lean --stdin Shao/OQ4/RademacherCosine.lean` | Lean exit 0，Python exit 0，5.073 秒；完整原 source 加审计所需的 `import Lean` 和 run_cmd |
| 最终 `taskset -c 0-3 lake env lean --stdin R/CompiledAudit.lean` | Lean exit 0，Python exit 0，6.876 秒；实际完整36导入及完整exact比较通过 |
| 附加最终元数据 guard 首次执行 | Python exit 1；错误猜测全部 generated universes 为空，详见错误史 |
| 元数据诊断、修正后的最终保护门 | 均 Python exit 0；不重跑未受影响 Lean 检查；旧文件／目标／olean前后保护和 live0 通过 |

这里 R 在命令表中是路径简写；真实命令记录于服务器各 `*-run.json`，实际 stdin 文件名分别使用 `Shao/OQ4/RademacherCosine.lean` 和 `repro_outputs/oq4-rademacher-cosine-independent-v1/CompiledAudit.lean`。没有把 stdin 模块命名为审计临时模块后再忽略 private 名称差异。

## 审计脚本错误及修正历史

1. 初次采用远端 Python 外层三单引号封装脚本，与内部 Lean 审计模板的三单引号冲突，触发语法错误；后续脚本不存在导致请求最终 exit 2。没有文件创建、目标读取或 Lean 执行。改为独立的审查者脚本上传后，旧35-only smoke 成功。初始工具 SHA256 为 `9af6baf5c76addc507142a801522bbb22f749b6b4a545d9fa3c72195fc023b92`。
2. 工具 v1 将旧35 imports 额外放在完整目标 source 前面，改变了部分实数 NormedSpace 实例的选择。首次 exact 门在 `killedKernel_integral_principal` 和 private `integral_law` 的 fullExpr_type 上拒绝；两边均34，名称、种类、宇宙和公理集均相同，但未因此忽略类型差异。失败表和日志已保留。修正仅限审计构造：完整原 source 加 `import Lean`，保持 canonical 的实际数学 import 环境；旧35与目标共存另由 actual full36 imported 审计完整覆盖。lead 明确同意该修正。重跑受影响的完整 source 和最终完整比较后全部精确一致。未重跑环境未变且已通过的目标 no-o。
3. 附加 Python 元数据 guard 曾无依据地假设全部 generated 宇宙参数均为空，因两个 `_simp` helper 实际带 `[u_1]` 而拒绝。删除这一无依据假设，保留实际宇宙列表并以已通过的逐项 exact 比较验证；只重跑受影响的元数据／保护门，结果 exit 0。两条实际 `[u_1]` 已在下表完整列出。

最终工具 SHA256 为 `b23747e7deb8bb2d77782ff830466f6a8a51ae0fc08100b4053ea0bfcf1ce0c0`。`R/tool-correction-history.json` 为2146B，SHA256 `7469f0b843284b6a6ba22434bde1e5593b18e16af37cec1e367a60d62720fcab`。所有拒绝结果均保留，没有改目标或对失败记录作覆盖式删除。

## 全声明提取、精确比较与公理门

源码侧遍历 `env.constants.toList`，只按 `(env.getModuleIdxFor? name).isNone` 选择当前完整源码产生的全部声明，不使用 namespace、public 名字或任何根名称过滤，实测34。实际导入侧同样遍历全部常量，只按其实际所属 module 等于 `Shao.OQ4.RademacherCosine` 选择，实测34，覆盖全部 private、generated 及名称不在公开 namespace 前缀内的项。

每行记录完整 `name`、ConstantInfo `kind`、有序 `levelParams`、`reprStr info.type` 的完整结构表达式，以及递归 `Lean.collectAxioms` 结果。公理列表排序为集合的固定表示、行按完整名称排序；不删表达式节点、不改 binder 名字、不作类型类实例归一化或 private 名字重写。两张最终表的34行逐字段完全相等，均为188383B，SHA256：

`563c4110dfa79618c057019f15b2c416bb42c21e9960fe14e3e9d255921af856`。

全36审计显式导入冻结旧35加实际目标，并验证实际 OQ4 moduleNames 集合精确等于这36个模块。选择条件是“实际所属模块在 Shao.OQ4 下，或声明名在 Shao.OQ4 下”的并集，实测704；其中21个名字不以 `Shao.OQ4.` 开头。新增34中7个为 private 前缀名称。对全部704逐一递归收集公理并逐项拒绝白名单以外公理，结果只含 `propext`、`Classical.choice`、`Quot.sound`。目标完整源码亦通过 forbidden-token 扫描，未含 `sorry`、`admit`、新增 `axiom`、`unsafe` 或 `native_decide`。

以下是完整34声明表。A={Classical.choice, Quot.sound, propext}，B={Quot.sound, propext}，C={propext}；源表与导入表的 fullExpr_type 也均已逐行 exact 相等，完整结构表达式只留服务器。

| 完整声明名 | kind | universes | axioms |
|---|---|---|---|
| `Shao.OQ4.RademacherCosine.Kcos_principal` | theorem | [] | A |
| `Shao.OQ4.RademacherCosine.Kcos_principal._proof_1_1` | theorem | [] | B |
| `Shao.OQ4.RademacherCosine.Kcos_principal._proof_1_2` | theorem | [] | B |
| `Shao.OQ4.RademacherCosine.Kcos_principal._proof_1_3` | theorem | [] | B |
| `Shao.OQ4.RademacherCosine.Kcos_principal._proof_1_4` | theorem | [] | B |
| `Shao.OQ4.RademacherCosine.angle` | definition | [] | A |
| `Shao.OQ4.RademacherCosine.angle.eq_1` | theorem | [] | A |
| `Shao.OQ4.RademacherCosine.angle_lt_pi_div_two` | theorem | [] | A |
| `Shao.OQ4.RademacherCosine.angle_pos` | theorem | [] | A |
| `Shao.OQ4.RademacherCosine.halfENNReal` | definition | [] | A |
| `Shao.OQ4.RademacherCosine.halfENNReal._proof_1` | theorem | [] | C |
| `Shao.OQ4.RademacherCosine.halfENNReal.eq_1` | theorem | [] | A |
| `Shao.OQ4.RademacherCosine.integer_closed_iff` | theorem | [] | A |
| `Shao.OQ4.RademacherCosine.integer_closed_iff._proof_1_1` | theorem | [] | B |
| `Shao.OQ4.RademacherCosine.killedKernel_cos_integrable` | theorem | [] | A |
| `Shao.OQ4.RademacherCosine.killedKernel_integral_principal` | theorem | [] | A |
| `Shao.OQ4.RademacherCosine.killedKernel_row` | theorem | [] | A |
| `Shao.OQ4.RademacherCosine.killedKernel_row._simp_1_1` | theorem | [u_1] | C |
| `Shao.OQ4.RademacherCosine.killedKernel_row._simp_1_2` | theorem | [u_1] | B |
| `Shao.OQ4.RademacherCosine.law` | definition | [] | A |
| `Shao.OQ4.RademacherCosine.law._proof_1` | theorem | [] | A |
| `Shao.OQ4.RademacherCosine.law.eq_1` | theorem | [] | A |
| `Shao.OQ4.RademacherCosine.law_isProbabilityMeasure` | theorem | [] | A |
| `Shao.OQ4.RademacherCosine.rho` | definition | [] | A |
| `Shao.OQ4.RademacherCosine.rho.eq_1` | theorem | [] | A |
| `Shao.OQ4.RademacherCosine.rho_lt_one` | theorem | [] | A |
| `Shao.OQ4.RademacherCosine.rho_pos` | theorem | [] | A |
| `_private.Shao.OQ4.RademacherCosine.0.Shao.OQ4.RademacherCosine.absorbing_cos_zero` | theorem | [] | A |
| `_private.Shao.OQ4.RademacherCosine.0.Shao.OQ4.RademacherCosine.cut_cos_eq` | theorem | [] | A |
| `_private.Shao.OQ4.RademacherCosine.0.Shao.OQ4.RademacherCosine.cut_cos_eq._proof_1_1` | theorem | [] | B |
| `_private.Shao.OQ4.RademacherCosine.0.Shao.OQ4.RademacherCosine.half_ne_top` | theorem | [] | A |
| `_private.Shao.OQ4.RademacherCosine.0.Shao.OQ4.RademacherCosine.half_toReal` | theorem | [] | A |
| `_private.Shao.OQ4.RademacherCosine.0.Shao.OQ4.RademacherCosine.integral_law` | theorem | [] | A |
| `_private.Shao.OQ4.RademacherCosine.0.Shao.OQ4.RademacherCosine.law_map` | theorem | [] | A |

实测构成为4 definitions、30 theorem-info。源码有9个公开 theorem、4个透明定义、1个 instance、6个 private theorem；另有14个 generated 声明。`law_isProbabilityMeasure` 是 Prop 类实例，内核种类为 theorem，不能误计成第五个 definition。

## 完整公开签名及冻结语义核对

下列为实际源码公开签名转录，略去证明项。环境为 `namespace Shao.OQ4.RademacherCosine`，`open MeasureTheory`。所有9个公开 theorem 均在源表和实际导入表中验证为 theorem-info；实际核签名显式包含已内部证明的 `law_isProbabilityMeasure` 实例项，没有外部概率性参数。

```lean
noncomputable def halfENNReal : ENNReal := 1 / 2
noncomputable def law : Measure ℝ :=
  halfENNReal • Measure.dirac (1 : ℝ) + halfENNReal • Measure.dirac (-1 : ℝ)
instance law_isProbabilityMeasure : IsProbabilityMeasure law
noncomputable def angle (m : ℕ) : ℝ := Real.pi / (2 * ((m : ℝ) + 1))
noncomputable def rho (m : ℕ) : ℝ := Real.cos (angle m)

theorem integer_closed_iff (m : ℕ) (h : ℝ)
    (hmh : (m : ℝ) ≤ h) (hhm : h < (m : ℝ) + 1) (s : ℤ) :
    |(s : ℝ)| ≤ h ↔ |s| ≤ (m : ℤ)

theorem killedKernel_row (m : ℕ) (h : ℝ)
    (hmh : (m : ℝ) ≤ h) (hhm : h < (m : ℝ) + 1) (r : ℤ) :
    killedKernel law h (r : ℝ) =
      (if |r + 1| ≤ (m : ℤ) then
        halfENNReal • Measure.dirac (((r + 1 : ℤ) : ℝ)) else 0) +
      (if |r - 1| ≤ (m : ℤ) then
        halfENNReal • Measure.dirac (((r - 1 : ℤ) : ℝ)) else 0)

theorem killedKernel_cos_integrable (m : ℕ) (h : ℝ) (r : ℤ) :
    Integrable (fun w : ℝ => Real.cos (angle m * w))
      (killedKernel law h (r : ℝ))

theorem Kcos_principal (m : ℕ) (hm : 1 ≤ m) (h : ℝ)
    (hmh : (m : ℝ) ≤ h) (hhm : h < (m : ℝ) + 1) (r : ℤ)
    (hrlo : -(m : ℤ) ≤ r) (hrhi : r ≤ (m : ℤ)) :
    Kcos law (angle m) h (r : ℝ) = rho m * Real.cos (angle m * (r : ℝ))

theorem killedKernel_integral_principal (m : ℕ) (hm : 1 ≤ m) (h : ℝ)
    (hmh : (m : ℝ) ≤ h) (hhm : h < (m : ℝ) + 1) (r : ℤ)
    (hrlo : -(m : ℤ) ≤ r) (hrhi : r ≤ (m : ℤ)) :
    (∫ w : ℝ, Real.cos (angle m * w) ∂killedKernel law h (r : ℝ)) =
      rho m * Real.cos (angle m * (r : ℝ))

theorem angle_pos (m : ℕ) : 0 < angle m

theorem angle_lt_pi_div_two (m : ℕ) (hm : 1 ≤ m) :
    angle m < Real.pi / 2

theorem rho_pos (m : ℕ) (hm : 1 ≤ m) : 0 < rho m

theorem rho_lt_one (m : ℕ) (hm : 1 ≤ m) : rho m < 1
```

逐项忠实性检查：

- 源码第15–31行定义的是固定两个半权 Dirac 原子；概率性由总质量计算证明。没有把概率性、对称性或特征转移关系添加为用户前提。
- 第40–76行将实际实闭条件内部等价为整数绝对值条件，使用真实 `killedKernel_apply`、真实平移和 Dirac 限制。公式中的出界支为零测度，质量没有加回或归一化。row theorem 对任意整数 r 成立，限制回冻结域即可；未把主特征关系扩大为实起点。
- 第79–83行直接从 `killedKernel_integral_bounded` 给真实余弦的 Integrable。没有只写积分等式而依赖不可积时的默认积分值。
- 第95–147行用整数步长证明域外邻点恰为 |s|=m+1，并证明此处余弦为零，再计算实际 Kcos 二原子积分和加减公式；不是从自由 cosineCoefficient 偷换被杀核。
- 第150–156行通过实际 `killedKernel_integral_cos` 接到真实 killedKernel 积分。angle 直接使用 m+1，故吸收点为 ±(m+1)，不是 ±h。
- 主身份保持 m≥1、整数 r∈[−m,m]、m≤h<m+1。特别 h=m 使用非严格下界，边界原子 ±m 保留；r=±m 的外侧原子在 ±(m+1) 被杀且余弦为零；r=±(m−1) 到达 ±m 的半权原子保留。m=1 的两个次边界标签同为 r=0，其核仍是两个原子而无重复计数。这些条件均由实际 row 与整数等价式覆盖。
- 第159–181行给出冻结参数全部严格范围。部分 helper 在更大范围成立（例如 angle_pos 对全部自然数），不会削弱冻结主身份；ρ>0 和 ρ<1 仍保留 m≥1。
- 没有加入无原子、非格点或非周期性，没有引入 n，没有完整谱／迭代生存量声明，也没有改为严格事件。

## 前后保护、关键工件哈希和退出状态

pre/post 比较不仅逐项旧 SHA，还比较实际文件集合：旧 OQ4 正好35，common 正好32，其他非 OQ4 正好56，根／版本正好4；实际 OQ4 最终集合精确为旧35加唯一目标。全部既有内容不变，目标源码和 olean 的前后 SHA及字节数均与本文首表相同。

4个根／版本文件的前后固定 SHA256：

- `Shao.lean`：`6dc4c451432716f5d3027adefebf416ea42faef8dd1018be0017cc7fe153676c`。
- `lakefile.toml`：`444f3a3a01fd8ff99f219cff08a99b20459c0d177c4e2c884af9eead481daf44`。
- `lake-manifest.json`：`40e8e3385f2b0c8ae56fa9de6947301472379cb62eeb83247944827c38b8af6e`。
- `lean-toolchain`：`d581a24b57a4ae9e0b2132ca8ac7cc3ac336a9fc2751fe6b29414e2d434d54c4`。

| 服务器 R 下工件 | 字节数 | SHA256 |
|---|---:|---|
| `independent-pre-snapshot.json` | 15444 | `8b97bed0495a00abeead5432ea67ea9d7913b0a367286da0e0cec197baf9c356` |
| `independent-post-snapshot.json` | 15954 | `54fc3e54e066bd68068bd4c9895fac3f35f84d77c32e966da541a024b787788d` |
| `independent-ready-olean-pre.json` | 357 | `ceadafd8290ce09dc6f3e91412724bd3c50db1e7de396ad1bac522e03e195d29` |
| `independent-versions.json` | 1011 | `c359ce5ec48009938d55f740a5e9ae136163db9f5d9d5185af90864480a209b6` |
| 最终 `SourceAudit.lean` | 10036 | `3e299d133c869694e8e6c984e695b21ddb5f2df98bfe7cf6c269f56062b15220` |
| `CompiledAudit.lean` | 6525 | `e0b09c6dfd298b3adbe6be4aae9a1a2e9c266c391701c7581acd03edbb2f4e3a` |
| 最终 `source-owned.json` | 188383 | `563c4110dfa79618c057019f15b2c416bb42c21e9960fe14e3e9d255921af856` |
| 最终 `compiled-owned.json` | 188383 | `563c4110dfa79618c057019f15b2c416bb42c21e9960fe14e3e9d255921af856` |
| `full36-modules.json` | 1045 | `e02bad8e326aa3762a44d4c892c64ef5ca745a4d0c040bfbf4594e6371d39ff5` |
| `full36-owned-namespace.json` | 11337125 | `6d598ab6e3f177ddf2872d5c97e36f4500393cceb24d153dac593abd50d3c7a4` |
| 保留失败 `source-owned-v1-old35-prefix.json` | 190169 | `4ef23ac1032b54e030c058c0ec3affbf46e261acae6fa43525697b99b8b45b42` |
| 保留首次 `compiled-owned-v1-old35-prefix.json` | 188383 | `563c4110dfa79618c057019f15b2c416bb42c21e9960fe14e3e9d255921af856` |

目标 no-o 日志 SHA256 为 `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`；完整 source 日志16B，SHA256 `078d2a166c338f3d465c9af39b28f3483378d8d9a638f6f1125c5d69b8a0f635`；完整36审计日志13095B，SHA256 `dad24c4195a478e40c04818b033ee5c08e5d0b7ad53a4d7abc7afc7c90e678c0`。失败构造的日志和 run receipt 以 `-v1-old35-prefix` 后缀保留。

最终保护门实际扫描服务器本 worktree 的 lean／lake 进程，结果为空（live0）。没有后台审查进程。作者的唯一 emit 产物保持原哈希，本角色没有 emit 或任何 `-o` 操作。

本报告保存为 UTF-8 无 BOM、LF，恰一个末尾 LF。自身哈希和字节数在保存后计算，交付回执另列。
