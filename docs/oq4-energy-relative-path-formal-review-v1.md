# OQ4 EnergyRelativePathBounds 独立最终形式审阅 v1

STATUS: CORRECT
LEAN_STATUS: LEAN_FULLY_CHECKED（仅本冻结有限叶）
E3_STATUS: OPEN
ROOT_STATUS: OPEN

本票为新鲜独立形式审阅。冻结命题、原 source 与 canonical Lean 源码的语义对应，以及实际源码/导入完整声明和传递公理门全部通过；未发现关键缺口。6 个源码公开定理与 4 个定义不是 10 个新增原始概率义务。本票不认证联合渐近、K/Kv、条件能量 E4、共同二维算子或完整 E3/OQ4 根。

仅修改本报告及服务器独立目录，未修改目标源码、匿名证明、Git、root、common、版本锁或缓存。未读取其他审阅推理、作者检查点或作者审计脚本。匿名证明仅核对原字节和编码，未读取证明正文。

## 冻结输入与正式窗口

- 原 source：`C:/game/shao/current/oq4/energy01.md`，SHA256 `2e0387f0a35ca677853e45fff271cc2fb0e87db9ee9c6b2f00d3bcf56b51d9e6`，5244 B，UTF-8/LF、无 BOM。独立核对式7/8及第71–83行。
- 冻结：`drafts/oq4/frozen-energy-relative-path-bounds-v1.md`，SHA256 `ddc8a054559f6ec4ec423e913bfd4bb8e5a1b78f26bdefc68fbc9e26c49a7660`，5139 B，UTF-8/LF、无 BOM。
- 匿名证明：`drafts/oq4/energy-relative-path/proof.md`，SHA256 `1432a8270323a3dbfe948d12573fb5bee71afdc04d31256861e691d06506d484`，19657 B、375 LF、0 CRLF、UTF-8、无 BOM；两次原字节观察一致且匹配冻结值。
- 服务器工作树：`/root/rivermind-data/shao-lean-20261021/workspaces/lead-oq4`。
- 实测 branch：`feat/oq4-relative-path`；HEAD `d3a16df03abc97e0f6e4af81972eba4b99f5da90`。
- canonical：`Shao/OQ4/EnergyRelativePathBounds.lean`，SHA256 `7f9242f4116924f26c9c7b75313e4e37b49c13f7da4f4052e7a7585984a2b654`，19497 B。
- 作者唯一 olean：`.lake/build/lib/lean/Shao/OQ4/EnergyRelativePathBounds.olean`，SHA256 `63ff11baf6ac7a83c55df0ea0277ec840443a8329b47099ec79ec0d80c0cb406`，717928 B。独立 no-o/source/import 检查前后均逐字节保持。
- 基线收据：`verification/oq4-energy-relative-path/base-receipt.json`，SHA256 `cfc4a51055cce6bf6d4ee709b296f17ad29ecccb95029ad7b2e87544b3ce7136`，旧36逐项匹配。
- 准备阶段目标源码及 olean 均不存在，未读取或检查目标；收到负责人 `AUTHOR_READY` 后才启动本节正式审阅。

## 原源到形式陈述的忠实性

1. canonical 第10–38行透明定义两条误差及有限结论，严格使用既有真实 energyTiltedLaw、energyLinearTiltLaw、energyNormalizer、energyLinearNormalizer、Measure.pi 和 closedStrip。既有 closedStrip 确为所有 k≤n 的绝对部分和闭事件，含 S₀=0；energyPathIntegrand 确为事件内 exp(s(Qₙ−n)/h²)、事件外0的原ν积分，没有抽象密度替身。
2. 第56–177行辅助入口的原ν假设与冻结完全对应：原平方/绝对立方可积、二阶积分1、均值0、实际β≤M、M,T≥0、h≥既有 H(M,T)、|s|≤T。常数 P(T)、C(M,T)、H(M,T)没有引入 n 或额外分布依赖；实际概率性、h≥2、Z/L正性和可积性由既有已冻结接口供应。
3. 第81–102行以同一个绝对 closedStrip 内终点控制得到 exp(±C/h)L(θ)ⁿ 的夹界；没有用 n·mean 移动事件。第103–127行由实际 |log L|≤C/h⁴、L>0 和完整乘幂—指数恒等式吸收 Lⁿ，得到误差 C/h+C·n/h⁴。
4. 第128–175行保留真实能量积分的可积性和式7因子，先精确证明 exp(−sn/h²)Zⁿ=exp(n(log Z−s/h²))，再以 E1 的实际β误差及 β≤M 支付 P·M·n/h³。没有在有限 h 把该因子置1，未把能量加权 Iₙ 误当作无权生存概率。
5. 第180–190行内部调用 E2，返回完整 energyE2Conclusion，量词为 ∃θ，E2(θ)∧∀n，有限结论(θ,n)。同一个 θ 在 n 之前选取，未把总入口删成外部 θ 假设。
6. 第193–222、252–285、288–313行 iid 版本使用既有真实 samplePath/map 桥、可测性、iIndepFun 和逐坐标 IdentDistrib，返回原ν样本积分的真正可积性与精确积分相等。三种真实 law 使用三个独立概率空间；最终存在型入口先选同一个 θ，再对所有 n 和三组样本族给出结论，不增加耦合、共同边缘或生存条件下独立性。
7. n 为全部自然数，包含0；没有正生存概率或概率除法，故零质量情形仍保留。θ=0、s=0、T=0、h=H、弱闭端点及截断原子、全零路径均未排除。n=0 时误差仍按冻结为 C/h；s=0 时仍保留真实截断归一化。M<1 可为空类，未补 M≥1。未将有限夹界扩张成概率比值或联合渐近结论。

## 实测声明与审计范围

源码公开定理如下，行号针对上述 canonical 字节版本：

| 公开定理 | 行 | 覆盖 |
|---|---:|---|
| energyRelativePath_errors_nonneg | 40 | 两条透明误差非负 |
| energyRelativePath_bounds_of_e2 | 56 | 任意实际 E2 参数的三组有限夹界与可积性 |
| energyRelativePath_common_bounds | 180 | 内部 E2 选出的同θ、全n总入口 |
| energyRelativePath_integral_iid | 193 | 原ν iid 积分相等、可积性及加权夹界 |
| energyRelativePath_iid_of_e2 | 252 | 三个概率空间的全部 iid 结论 |
| energyRelativePath_common_bounds_iid | 288 | 同θ、全n、全三组 iid 实现的总入口 |

完整源码 all-none 审计枚举19个声明，actual import owner 枚举同样19个：6个源码公开定理、4个定义、1个 private theorem、7个自动生成 _simp theorem、1个 eq theorem。所有19个的 name、kind、实际 universe 参数列表、完整原始 Expr type 和传递公理集合逐项精确一致；源码 owner=None 与导入 owner=目标模块的来源元数据不参与这五项相等性比较。未作任何名称或命名空间筛选来生成源码声明集合。

7个 _simp 的实际 universe 分别包含 u₁/u₂/u₃，并非空列表；iid 声明保留原本 universe 多态性。完整 Expr 直接由 reprStr ci.type 输出，未设置 pp.maxDepth 等打印选项；新声明类型无截断标记。

| 范围 | 实测常量数 |
|---|---:|
| 旧36 OQ4 owner 或 Shao.OQ4 namespace 并集 | 704 |
| full37 的 OQ4 owner | 723 |
| full37 的 Shao.OQ4 namespace | 701 |
| full37 的 OQ4 owner 或 namespace 并集 | 723 |
| 上一并集中 namespace 外、依 owner 纳入者 | 22 |
| 更广 Shao owner 或 Shao namespace 并集 | 946 |
| 其中其他 Shao 依赖 | 223 |

准备阶段927是更广 Shao 并集，即704个 OQ4加223个依赖，未将927称为纯 OQ4 数。正式完整946个均执行传递三公理审计，因而覆盖全部723个 OQ4，包括 private 和 namespace 外常量。全部公理依赖仅在 propext、Classical.choice、Quot.sound 内；目标全文 forbidden-token 扫描通过，无 sorry、admit、新axiom、unsafe、native_decide 或 sorryAx。

## 实际执行与版本

全部 Lean 仅在指定服务器运行；每次亲和4核0–3、逐次1个 Lean、线程参数1，无 -o/-i/-c/-b 等输出参数。没有本地 Lean，没有缓存下载、构建输出或版本更新。每个检查前后都核对完整保护表和目标源码/olean，未重跑已通过的目标门。

实际 Lean `4.36.0-rc1`，commit `c9afcddf514a6772bd4d649f7cfc04eff0b9f15e`；Lake `5.0.0-src+c9afcdd`。实际 lake-manifest 的 mathlib revision 为 `807d3836b165983210ee2ecf3cd28f239436949c`，版本锁前后未变。

以下每条命令均先 source `/root/rivermind-data/shao-lean-20261021/activate.sh`，然后 cd 指定工作树：

| 检查 | 实际 Lean 命令 | 退出码 | 秒 |
|---|---|---:|---:|
| canonical 无输出重检 | taskset -c 0-3 lake env lean -j 1 Shao/OQ4/EnergyRelativePathBounds.lean | 0 | 5.94 |
| 完整源码 all-none | taskset -c 0-3 lake env lean -j 1 --stdin Shao/OQ4/EnergyRelativePathBounds.lean | 0 | 7.13 |
| actual full37 导入与三公理 | taskset -c 0-3 lake env lean -j 1 --stdin repro_outputs/oq4-energy-relative-path-independent-v1/ActualFull37.lean | 0 | 10.82 |

第二条 stdin 为必要的 `import Lean`、canonical 原源码、独立审计尾部；真实源码导入仅 EnergyE2Bounds 与 EnergyLinearPathLaw，未额外前置旧36导入。实际模块路径保留了 private 的完整名称。第三条独立导入旧36加目标，逐一检查37个实际模块都进入环境，然后按 owner/namespace 并集审计全部常量；末尾实际输出 ACTUAL_OQ4_MODULES 37。

原始日志和完整类型表只存服务器 `repro_outputs/oq4-energy-relative-path-independent-v1/`：

- `target-no-o.stdout.log` / `.stderr.log` 均为空且退出码0。
- `target-source.stdout.log` 为496991 B；SHA256 `21c208ed1da895bcfe9c19f637d133853452fc3fb73c4e0db2002dc891e1905a`。
- `actual-full37.stdout.log` 为12615000 B；SHA256 `98b5f6de75c7f09eb51fd9c1f7cd543d3c27753961bd11207e101c0820eb1ca3`。
- `final-machine-receipt.json` SHA256 `0e964071c127814c0044998ad7b14732121959b5e66d3f3e9cc8759dcc162661`。
- `end-receipt.json` SHA256 `f680b736e266cb03b1d873bfde1a55c0b76cf6d1e14cabd9cb4bc5470425ab18`。

## 前后保护与结束状态

精确集合及每文件 SHA256 均保护：旧36 + 32 Basic/Probability + 56其他 Shao源码 + 7根文件/版本锁，共131个既有文件。后95个覆盖负责人92标准表（32+56+Shao.lean/lake-manifest.json/lakefile.toml/lean-toolchain），并额外保护 .gitignore、AGENTS.md、README.md。各组文件集合及全部逐文件散列前后相等；唯一新增 OQ4源码是本目标。

`pre-snapshot.json` SHA256 `0b9bb64b248d1c675e71882d2b82b65b59e5da6fa44eb0cbfeffff8dc0579ae6`；`post-snapshot.json` SHA256 `61cd842600fc75aadd97653cd11cba8d81a458b54e48f02ec03e69fc19ff2890`。两文件结构不同，逐组精确集合/散列相等结论保存在后者及最终收据中。

2026-10-21T20:53:41.241923Z 独立检查指定 lead-oq4 工作树的存活 Lean/Lake 进程为0。源码、作者唯一 olean、branch/HEAD、原源、冻结及匿名证明均维持指定字节值；本审阅未产生 olean。

## 准备史及工具错误留史

准备阶段完整读取了 AGENTS.md、SERVER.md、coordination/TEAM.md 和 math-theorem 角色/Lean协议，记录实际版本和上述前置快照。旧36共存退出码0、广Shao927常量三公理门通过；真实模块路径私有探针的 universe [u] 被正确保留。已发布冻结 RademacherCosine 自检覆盖34/34完整声明，源码与导入五项精确一致；这不是 Relative 目标审阅，也未提前泄露目标。

本上下文保留以下全部工具历史，均未修改 source/olean、未缩窄审计范围：

1. PREP 编排字符串中未转义的 Lean 反引号在工具执行前被拒绝；没有远程执行，只修复字符串引号。
2. PREP 源码探针选到仅含导入的 Foundations，工具正确报 Empty declaration audit。保留失败日志和退出码；仅更换自检样本为冻结非空 RademacherCosine，34/34通过。零对零比较未计为通过。
3. 初版机器收据的 public_theorems 字段误把7个 _simp 与1个 eq也列为公开定理。完整19声明审计及比较从未漏项；保留 `final-machine-receipt-v1-unclassified.json`，仅在摘要中分开6个源码公开定理与8个生成项，未重跑 Lean或改 scope。
4. 所有目标检查和最终摘要已通过后，补充定位定义的 rg 搜索因服务器未安装 rg失败；记录错误后改用有界 Python 文本查找，未涉及 Lean 检查或源文件变动。

`tool-errors.md` SHA256 `bf754ccb2d54dda9cc925bd56e2019fc54bb02a99c65ebf66733a09516de12fc`。负责人告知的作者一次未知 pp.maxDepth 选项失败，仅作为来源元数据；不是本上下文的失败记录。本审阅未设置该选项，三个目标门均首次实际执行成功。
