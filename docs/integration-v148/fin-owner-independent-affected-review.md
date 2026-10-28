# Fin.insertNthEquiv.eq_1：实际导入归属变化的独立受影响范围审查

日期：2026-10-28。审查者：/root/original_d_strictness_source_review。仅审查 Fin.insertNthEquiv.eq_1 这个生成声明在 JO355 单模块闭包与整个 Shao 闭包中的实际类型、证明、归属和递归公理；复用原 JO 完整独立审查，不重新审查十一份证明。

**STATUS: CORRECT / AFFECTED_INTERACTION_QUALIFIED。两种实际闭包中的同名声明具有逐字相同的完整 TYPE、原始 TYPE Expr、完整证明及原始证明 Expr，不只是删去证明字段后的等价。实际变化仅为模块归属登记：单模块闭包登记于 Shao.OQ3.PositiveBoxSimultaneousDiophantine，整个 Shao 闭包登记于 Mathlib.MeasureTheory.Integral.Pi。实际相关外部声明的递归公理恰为白名单三项。原完整 SOURCE/proof 审查加本次完整实际声明交互审查，已覆盖这个具体风险，未发现关键缺口。**

## 1. 本次实际读取与精确绑定

本目录由 Root 提供的两份观察脚本、两份完整 stdout、两份完整 stderr、精确比较记录、观察成功收据、元数据恢复记录及 pinned 源摘录均已读取。两个完整输出分别整读，没有以摘要或省略号代替原始表达式。另以本地确定性文本分段重新比较 ACTUAL_NAME、LEVELS、FULL_TYPE、RAW_TYPE、KIND、FULL_PROOF、RAW_PROOF，七项逐字相同；四项长正文的 SHA256/字节数同时匹配 Root 比较记录。没有运行 Lean/SSH 或任何服务器命令。

| 本目录文件 | SHA256 |
|---|---|
| standalone.lean | 47b9bb9a49fffaa366eaca23d49659981f691d46a18d8ef086aa097214097c2e |
| aggregate.lean | 5cba2f94ced659527879460a87226462f4bd838c04e8500688c9421d6d1b4e51 |
| standalone.stdout.txt（22131B） | 49ef30e4c0d5e4c54683c9f12467e084e07b808876235090ab8c5cef3171ccef |
| aggregate.stdout.txt（22117B） | ca03234fbbecab1aed0b3df5ad28a047c99fa1b3f0a2ac94e9b0ef4ec3ff8143 |
| 两份 stderr（各149B，同字节） | 997043f80e28585c57a17eb918e9ffd0cd9ec7c1f88e155e46b830650f358bec |
| type-proof-comparison.json | 8c078eb3aef1145f52d30a2b76d1be3cd6d3a7450633173779861ec0c658ae56 |
| observation.json（4333B） | 527353cae4c612b65483d3de4e3540948d439b87dc1923f9a463e7fc859efba4 |
| postprocess-success-response.json | 4e65c981670e686dd1d26061b13f7d5474d1de3ed1454b54ca71c30b3e1a994f |
| pinned-insertNthEquiv-source.txt（4040B） | ae2bdfca838e060a326744f59ea0f733a31f8ad133f6fd56410e880ba96aa859 |

观察收据逐项绑定两份脚本及四份 stdout/stderr；本次重新计算的六项字节数/哈希全部相同。stdout 与相应 normalized 文本字节相同，本审查以完整 stdout 为准。

复用的原资格化证据位于 C:/game/shao lean/drafts/oq3/publication-u22-diophantine-witness/：

- JO355 源 PositiveBoxSimultaneousDiophantine.lean：f3d6f7c872ba5527d164623d83c6d5898503937fb81a72225b9e953d39ed5921。
- 原独立完整审查 u22jo-proof-review.md：2bf996fcfcbd25d0db8692b26f46d7b7a953e72bd62eeddcda025760f18c0e50；本次定向重读其 115–130 行及实际生成声明语义，未重审主证明。
- JO 全部三个实际 TYPE：528ea601968c8e61bd06a96180abf297f48d197f46ca178a6d283fb9c125fa03。
- JO 原 receipt：7ed1dde1e88fa723d86027b87d7b34dfc30fc754f17e4a66240aae222b8a86bf。
- JO 原首次成功对象：ac35dd8ed23ed8924f6a70b45e92b6191953e33f43213d241b93c60adfdb68de；Root 新观察仍绑定同一对象，219960B。

实际 defining source 是固定 mathlib807d3836b165983210ee2ecf3cd28f239436949c 的 Mathlib/Data/Fin/Tuple/Basic.lean，整文件 SHA256 e7b680bb3181fff915623cfa82d2e52424d423e5d5762578f3fe218533d8af48。已读摘录 1064–1144，尤其 1079–1084 的完整定义及两条源证明。实际聚合 owner 对应 Mathlib/MeasureTheory/Integral/Pi.lean，收据所绑定整文件 SHA256 43c50a9d9a683b2050e145154410a7260c3dd84f3ec3010630cc6b90572afcd9；该 owner 名字是实际环境结果，不是按命名空间猜测。

## 2. 完整命题、映射和两条逆律

两种闭包中 LEVELS 都是 [u]，KIND 都是 theorem。完整可读 TYPE 为：

    ∀ {n : ℕ} (α : Fin (n + 1) → Type u) (p : Fin (n + 1)),
      Fin.insertNthEquiv α p =
        { toFun := fun f => p.insertNth f.1 f.2,
          invFun := fun f => (f p, p.removeNth f),
          left_inv := fun f => Fin.insertNthEquiv._proof_1 α p f,
          right_inv := fun f => Fin.insertNthEquiv._proof_2 α p f }

没有分析、测度、算术、非空性或所需丢番图结论作为隐含前提。n 从 0 开始全量量化，α 是任意依赖类型族，p 是任意 Fin(n+1) 坐标。原始 Expr 明确包含 Equiv 的两端：

\[
S=\alpha(p)\times\prod_{i:\mathrm{Fin}\,n}\alpha(p.\mathrm{succAbove}(i)),
\qquad
T=\prod_{i:\mathrm{Fin}(n+1)}\alpha(i).
\]

正向映射 \(F:S\to T\) 把首分量插入第 p 个坐标、其余分量按 succAbove 编号插入；逆向映射 \(G:T\to S\) 提取第 p 坐标及删去该坐标后的依赖元组。两条字段的完整数学命题分别是

\[
\forall f:S,\quad G(F(f))=f,\qquad
\forall f:T,\quad F(G(f))=f.
\]

p 的值来自正向插入后的第 p 坐标，其余每个 i 的值来自 p.succAbove(i)；反向组合也逐坐标恢复原元组。摘录中的 left_inv 源证明为 by ext <;> simp，right_inv 为 by simp；它们证明这两个固定的逆律，没有增加任何前提。JO 第 26 行附近对 Fin.insertNthEquiv 的展开只使用这个实际等价的计算映射，原完整审查已经覆盖其 Fubini/坐标重排用途。

原标准 TYPE 中的 left_inv/right_inv 省略号只是打印器隐藏证明值。此次 pp.proofs=true、pp.deepTerms=true 输出已明确显示它们对应的完整 lambda 与命名证明常量，RAW_TYPE 则给出全部绑定、宇宙、依赖函数域、Equiv.mk 的六个参数以及两个证明字段。不存在把未知非证明字段删去后才判相同的情况。

两条逆律是 Prop 中的证明字段；当其类型和 F/G 固定时，证明无关性意味着更换同一逆律的证明不会改变这个 Equiv 的计算数据或带入新的数学假设。不过本案并不需要依赖这种较弱比较：两个 RAW_TYPE 连证明字段的常量引用、应用参数、绑定次序和 lambda 都逐字相同。

## 3. 实际证明表达式与精确相同性

两种闭包的完整证明值都是：

    fun {n} α p => Eq.refl (Fin.insertNthEquiv α p)

这是定义展开等式的反身证明；没有调用一个更强的假设定理去替代生成等式。RAW_PROOF 包含三个 lambda、相同的 universe u、同样的 Equiv 两端和相同的 Fin.insertNthEquiv α p 项。它与完整 RAW_TYPE 一起表明该声明确实是 pinned 等价定义展开的证书。

| 相同部分 | UTF-8 字节数 | 两闭包共同 SHA256 |
|---|---:|---|
| FULL_TYPE | 298 | 0406668fa2c027ba6a546714826e46c4d7d5f81b866722dc702500270cee7c62 |
| RAW_TYPE | 16673 | ac276399cbee7deef5560cdc00a47ad218491886075e3bf32b0d1e891e430cdd |
| FULL_PROOF | 49 | d961d1c683764c0115a5ad52833e8e763f9226d2369f508cf6ac3418ce7f7e2f |
| RAW_PROOF | 4899 | f364cd783553cb4b726a120f0faf87c06d1047e6fe98c8b6229aafa42850902f |

这四部分均不含打印省略号。本次独立逐字比较及本地哈希与表中相同；并非仅重复采信 comparison.json 的 PASS 字段。非定理 VALUE 数为零并不豁免检查 theorem 的证明值：本次已经实际读取 t.value 的完整打印和原始表达式。

## 4. 实际 owner 与递归公理

standalone.lean 的数学导入为 Shao.OQ3.PositiveBoxSimultaneousDiophantine；aggregate.lean 的数学导入为 Shao。二者另外共同 import Lean 用于环境观察，均实际调用 env.getModuleIdxFor? / env.header.moduleNames 取得归属。

| 导入闭包 | Fin.insertNthEquiv.eq_1 的实际 owner |
|---|---|
| JO 单模块闭包 | Shao.OQ3.PositiveBoxSimultaneousDiophantine |
| 整个 Shao 闭包 | Mathlib.MeasureTheory.Integral.Pi |

因此在聚合的 Shao 项目模块 owner 集合中不再列出这个名字，并不表示等式消失或被替换为不同命题。该名字仍真实存在，且完整类型与证明都保持相同。无需猜测 Lean 装载器内部究竟在哪一步形成归属登记，就能由实际两闭包证据解决本次数学风险。

standalone 脚本诚实地复用原 JO 全所属递归 AX，没有重复收集它。aggregate 脚本只对这个实际相关外部声明执行 Lean.collectAxioms，并逐项拒绝白名单外公理；完整实际输出为：

    AXIOMS [propext, Classical.choice, Quot.sound]

脚本的 theorem 分支同时排除“实际上是 axiomInfo 或其他声明种类”的替代。所需相关外部声明已完成一次真正递归公理核对，未借外部 owner 标签跳过它的数学审计；不需要因此重做其他旧 owner 的 AX。

observation.json 记录两次原观察 Lean 自然 RC0/RC0，并明确其证据基础：原执行在断言两个子进程成功及原对象前后相同以后，才因缺少 rg 的元数据后处理失败。一次恢复的 AssertionError 也保留为 postprocess-recovery-response.json；后续 postprocess-success-response.json 自然 RC0、零 Lean 恢复运行。这里不把外层 RC1 冒充 Lean 失败，也不将后处理成功冒称一次新的 Lean 检查。

两份 stderr 都只有同一个既有 pinned mathlib local-changes 警告；没有错误被删除。成功收据同时确认 JO 原对象不变，以及第一次成功的 Shao 聚合对象 SHA256 ac098b0a2bd41ff259707cce08e623ec8d5a75a7fe9a6a9cfe185c8a163b1e07、140600B 不变。未生产新的 JO 或 Shao 对象。本审查者只读取这些保存证据，不声称亲自执行服务器观察。

## 5. 原审查覆盖与三个计数口径

原 JO 独立完整报告已经对整个 source/proof、全部三个真实所属 TYPE、生成等式的全绑定、完整 pinned 定义及两条逆律源证明给出审查；还明确提醒 Root 检查该外国命名空间生成名的实际整合归属。本次补齐的具体缺口是：

1. 实际两闭包中完全展开的 TYPE 及 theorem 证明值；
2. TYPE/raw Expr/证明/raw Expr 的精确相同性；
3. 实际聚合外部 owner 的一次递归 AX 及首次原对象绑定。

因此原完整独立 SOURCE/proof 审查加本次受影响范围审查，已覆盖该生成声明所需的全部实际语义与交互证据，没有需要重新完整审查 JO 主证明或其余十个模块的数学变化。

Root 提供的 41 standalone、40 project actual、39 net-new 三个数口径一致：41 条 standalone 审查记录仍全部保留；Fin.insertNthEquiv.eq_1 在聚合中归属外部 Mathlib，故当前项目 owner 记录为 40；其中 Shao.OQ3.jointPhase.eq_1 是既有精确同名项目声明的复用，故净新项目名字为 39。qualified-units.json 中两个精确 fullname 都存在，前项是本次已解决的外部归属交互，后项沿用既有 CN/JH/JR 同名证据。这里没有以减少审查分母掩盖漏审，也没有删除一条数学结论；本报告不重新生成整工程库存或把计数调整当作新数学结果。

最终裁决：**该唯一声明的交互合格；没有关键 SOURCE/proof/TYPE/AX 缺口，没有承重假设变化，不需要重跑已成功的聚合、producer、旧 AX 或十一份完整证明审查。**

本次仅新增本报告，未修改源码、REGISTRY、台账或任何观察工件。封存的 original-d-strictness-source-implication-review.md 仍为 SHA256 6f1ba1abd4cd5280d7eaafb1cc3bc47388ab978cf9773781e0d56c8a5d36f9ee；本次判断不改变其 D 谱严格性已闭合、实际小正参数 GLOBAL 鞍点/完整应用仍 OPEN 的范围。未启动子上下文、未执行 Lean/SSH。规定 gpt-6.1-sol/xhigh；实际模型/强度和分项 token 遥测未提供，均记 null。
