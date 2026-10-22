# RademacherFiniteBasis 独立最终形式审查 v1

STATUS: CORRECT
FORMAL_STATUS: LEAN_FULLY_CHECKED
SCOPE: 冻结数学接口 v1 的 B0–B3
SPECTRUM_STATUS: OPEN
ROOT_STATUS: OPEN

独立最终审查通过。完整原始源码无产物编译、实际模块名 source mirror-R、全部 imported40 共存审计与展开后的冻结接口检查均通过。未发现数学缺口、隐藏前提、类型/定义体不一致或旧依赖变化。本结论仅覆盖有限正弦基和真实一步核；全部模态幂、S1、生存概率、cot 和、完整谱渐近及 OQ4 根仍 OPEN。

## 1. 独立性、输入与固定哈希

审查者为新鲜独立上下文，先在 PREP 阶段只读冻结命题、原始来源、公共指引和已认证接口，完成独立旧基线后 HOLD；收到 lead 明确 AUTHOR_CANONICAL_READY 才读取新 canonical 源码及获准匿名 proof。未读取其他审查、作者 checkpoint、其他匿名证明或 newAllModes 实现。没有修改数学 source/proof、common/root、Git 或缓存。

已读 AGENTS.md、SERVER.md、coordination/TEAM.md，以及 math-theorem 的 SKILL.md、prompt-library.md、openai-workflow.md、lean-verification.md。所有 shell 工作目录固定 C:/game/shao lean；所有 Lean 仅在指定服务器，单进程、4 核亲和、无 -o。

| 固定输入 | 字节 | SHA256 |
| --- | ---: | --- |
| drafts/oq4/frozen-rademacher-finite-basis-v1.md | 9862 | 4672baa6bc550de2a97ca9adc0730b5633f71458b2c3da8b02c2318131e05a7f |
| drafts/oq4/rademacher-finite-basis/proof.md（获准匿名证明） | 11037 | d009448ffe0ccb0c8634dde6541b9faaf1813807c65547614618d6c55b888dff |
| 原始 C:/game/shao/current/oq4/c01/spectrum01.md | — | b65f9e0c2f9b40a28d092491b479bd20d0b8ee8a9ac940c3c4760cfff7d2670b |
| Shao/OQ4/RademacherFiniteBasis.lean | 14217 | f61cd3f2ea5430c39faa69a96b3ca169d11d5f4585047d7a174491608e5f4f27 |
| 唯一获准目标 RademacherFiniteBasis.olean | 1207072 | 545d82672fdc48c38617a8c1ae594b17f2016c05e5e87d77d24ed651b6597208 |

服务器 worktree 为 /root/rivermind-data/shao-lean-20261021/workspaces/lead-oq4，分支 feat/oq4-finite-basis，审查时 HEAD 为 db692904c6977b2a783184838bb7a4d4acd98c77。Lean 4.36.0-rc1，commit c9afcddf514a6772bd4d649f7cfc04eff0b9f15e；Lake 5.0.0-src+c9afcdd；项目版本未改。

## 2. 实际检查与复现命令

以下命令先 source /root/rivermind-data/shao-lean-20261021/activate.sh，再 cd 上述 worktree。所有完整 stdout/stderr、每次尝试及退出码留在自有服务器证据目录 repro_outputs/oq4-rademacher-finite-basis-independent-v1/。

```sh
taskset -c 0-3 lake env lean Shao/OQ4/RademacherFiniteBasis.lean
OQ4_AUDIT_OUTPUT=repro_outputs/oq4-rademacher-finite-basis-independent-v1/source40-environment-raw.json taskset -c 0-3 lake env lean -R repro_outputs/oq4-rademacher-finite-basis-independent-v1/source-mirror repro_outputs/oq4-rademacher-finite-basis-independent-v1/source-mirror/Shao/OQ4/RademacherFiniteBasis.lean
OQ4_AUDIT_OUTPUT=repro_outputs/oq4-rademacher-finite-basis-independent-v1/import40-environment-raw.json taskset -c 0-3 lake env lean repro_outputs/oq4-rademacher-finite-basis-independent-v1/ImportAll40Audit.lean
taskset -c 0-3 lake env lean repro_outputs/oq4-rademacher-finite-basis-independent-v1/FrozenContracts02.lean
```

四项最终检查均退出 0。对应日志为 canonical-target-no-o.log、source40-mirror-R.log、import40-audit.log、frozen-contracts-02.log。canonical 数学源码第一次检查即通过。

source mirror 的内容严格为必要的 import Lean 加完整原始源码原字节，再加独立审计尾部。原始 import 只有 Shao.OQ4.RademacherCosine，没有 prepend 旧39，没有重命名 private 常量，没有导入自身 olean。实际 env.mainModule 为 Shao.OQ4.RademacherFiniteBasis；实际 imported OQ4 模块只有 CosineCoefficients、KilledCosine、KilledKernel、RademacherCosine，目标自身不在实际 imports 中。镜像原始源码段与 canonical 字节精确相同。

import 审计实际 OQ4 module set 精确为冻结旧39加目标，总40；完整 imported module set 也精确为独立旧基线的完整集合加目标，未仅检查名称前缀计数。

## 3. 全常量、完整类型、定义体及实例对照

API 先经真实编译器源码及 smoke 确认。环境采用 setExporting false。source 阶段无 name/namespace 筛选地收集全部 getModuleIdxFor? = none，得到 79 项；连同其必要旧依赖共选中148项。import 阶段全部 getModuleIdxFor? = none 为0，以 owner OR namespace 联合集合选中847项，即旧768加新79。

逐项直接比较 raw name、kind、universe、完整内核 Expr type、传递 axioms、全部 definition 原始 Expr body，以及实例注册标记。source 的 owner=None 与 import 的 owner=目标模块是预期归属变化；effectiveOwnerRaw 必须相同，除此以外每项捕获字段均要求精确一致。未按名称后缀替换 private 前缀，未按预期种类或公开数过滤常量。全部新79项零差异；旧768项全部字段及88个定义体也零差异。

| 实测新常量类别 | definition | theorem | 合计 |
| --- | ---: | ---: | ---: |
| 源码公开声明 | 7 | 9 | 16 |
| 显式 private 声明 | 3 | 17 | 20 |
| 自动生成声明 | 0 | 43 | 43 |
| 合计 | 10 | 69 | 79 |

全79项实际 raw name、分类、源码行、类型与定义体散列、axioms、实例标记见服务器 new79-classification-v2.json；完整原始类型/定义体见 source40-environment-raw.json 与 import40-environment-raw.json。所有79项的完整 Expr 类型及全部10个 definition body 已直接逐字段比对，不只比较公开声明或散列摘要。

公开定义对应源码行：states 8、modes 9、theta 10、mu 11、phi 12、vector 14、coefficient 15。三项 private 定义为 stateIndex 34、stateAt 35、cosSum 103；其完整原始 body 同样一致。

| 公开 theorem | canonical 源码行 | 冻结接口 |
| --- | ---: | --- |
| theta_one | 18 | B0 角度 |
| mu_one | 20 | B0 特征值 |
| phi_one | 24 | B0 全实轴主模态 |
| orthogonal | 185 | B1 |
| square_norm | 193 | B1 精确平方范数 |
| dual_orthogonal | 204 | B2 对偶身份 |
| reconstruction | 226 | B2 任意数据重建 |
| killedKernel_integrable | 284 | B3 真正可积性 |
| killedKernel_integral | 291 | B3 真实一步特征身份 |

旧768项为680个 theorem、88个 definition。旧 OQ4 实际注册实例为4个；全环境实际注册表25,020项，与 PREP 独立基线逐项精确一致。注册记录保留 priority、AttributeKind、globalName、keys、value Expr 和 synthOrder；AttributeKind 按真实 global/local/scoped 穷尽匹配，没有假定其具有 Repr。新79项实际注册实例0、erased 标记0、instanceReducible 标记0。这些零数值由实测得到。

全部847项传递公理并集恰为 propext、Classical.choice、Quot.sound；新79项并集相同，非白名单公理0、新 axiom 声明0、unsafe0、partial0。完整源码无 sorry/admit/axiom/unsafe/native_decide。完整 Expr 序列化未使用 pretty-printer 深度猜测；类型/定义体中省略号记录0。原始日志、Expr、二进制均仅在服务器。

## 4. 来源、冻结 B0–B3 与匿名证明的独立语义审查

结论：CORRECT。匿名证明和最终 Lean 实现虽有不同细节，均覆盖同一冻结 B0–B3；没有改变 law、索引、相位、范数、起点或量词。

- 固定对象：states 正是整数 Icc(-m,m)，modes 正是自然数 Icc(1,2*m+1)。theta=j*angle，mu=cos(theta)，phi(w)=sin(theta*(w+H))，vector 是该实函数的整数限制，coefficient 恰为 (1/H) 乘未归一化有限和。认证依赖实际 law 是两个半权 Dirac，实际 killedKernel 是平移后限制闭区间的次概率核。
- B0：theta_one、mu_one 透明接回认证 angle/rho；phi_one 对所有实数 w 成立，由 angle*H=π/2 得到正弦相位与主余弦完全相同，不限整数输入。
- B1：显式 stateIndex/stateAt 双射把真实整数状态平移到完整1..2m+1。有限余弦 telescope 同时处理非零正负差指标，再由积化和差得到全 j,k 正交。对角值是 H=m+1，而非状态数2m+1；H>0，square_norm 给精确平方范数。
- B2：vector_symmetry 与已证双射、B1 推出对偶身份，然后交换两个有限和重建。F 的类型严格为任意 ℤ→ℝ，没有可测、有界、有限支撑或 I_m 外值约束；系数只读取 I_m 内有限数据。FrozenContracts02 将重建结论展开为原始 Icc、实数正弦与1/H系数，实际检查通过。
- B3：phi 的连续性与全实轴界 |sin|≤1 在有限实际核上给出真正 Integrable。积分证明调用认证 killedKernel_row，分别证明两个真实原子子测度的可积性和积分；由 phi(±(m+1))=0 消去被杀死项，再用正弦加减公式得到 mu*vector。没有把任意频率代入主余弦定理，也没有另造矩阵或归一化核。
- 端点与模态：保留所有 m≤h<m+1，含 h=m；r=±m 向外质量被杀死，剩余行质量1/2。吸收点是±(m+1)，不是±h。j 的范围完整，含零模态j=m+1、负特征值区和末模态2m+1；没有正性、非零、奇偶或非格点前提，也未除以 mu。这里只量化整数起点 r∈I_m，未扩展到非整数状态类。

展开接口检查在原始实数正弦表达式下验证了 B0、B1、任意 F 的 B2、真 Integrable 及真实积分 B3，未为该检查补充前提。匿名证明的有限余弦和、对偶重编号、实际原子行及端点计算亦未发现关键缺口。

## 5. 冻结保护、产物与完整错误史

PREP 开始时 target ABSENT，独立锁定39个 OQ4源、92个受保护源/配置，共131项；每项工作字节、冻结映射及 immutable HEAD blob SHA256 一致。old96构建产物也逐项固定。最终再次核验全部131源/配置和96旧构建文件，变化0。canonical40 源文件集合精确为旧39加目标；全部构建文件总97，唯一新增文件为 .lake/build/lib/lean/Shao/OQ4/RademacherFiniteBasis.olean，其字节/散列保持获准值。

canonical-release-base.json 与 verification/oq4-rademacher-finite-basis/base-receipt.json 均为 SHA256 c83dc51619bafd76478da61754547d176f8a4dd16acda7ee63ab675c52c2d039；protected-base-source-map.json 为 cf3b164c60adf590af9749d6cdf894f11031c76ed316820111f433bd2858b76f；old96-build-artifacts.json 为 0b97775e542d48dd16e4b3b4d299e4ffae4da0f19685ee5aa8f689be6f6e5839。

审查者 emit0、数学修改0、Git/cache写入0；自有证据目录无 olean/ilean/IR/目标代码产物，新增 private 构建产物0，结束时自有 live Lean0。所有检查同步结束，没有遗留任务。

完整失败/诊断保留在 all-errors.json 及原日志，未覆盖任何失败文件：PREP 发现服务器无 rg 后改用 Python 读取 API；分类脚本v1遗漏同一行 @[simp] 的 theta_one/mu_one 标记，v2修正为9公开定理+43生成项，原先全79枚举/精确比对未受影响；FrozenContracts01 审查脚本有一次 partially-applied phi 的 simp 展开不适用和积分括号错误，退出1，保留原文件/全日志，FrozenContracts02 改用定义相等及修正括号后退出0。canonical 数学文件、证明及公理均未为审查修改。

## 6. 服务器证据收据

绝对目录：/root/rivermind-data/shao-lean-20261021/workspaces/lead-oq4/repro_outputs/oq4-rademacher-finite-basis-independent-v1/

| 工件 | SHA256 |
| --- | --- |
| final-independent-receipt.json | 75b2ef64da50d7e5fd9b9483797902ef75932aaf113afa7a79b741c0693bf600 |
| all40-exact-comparison-v2.json | 97081a3559b0c56eb745324eb1831d725fc7715abde030437ea436c02110b3b3 |
| new79-classification-v2.json | 95b26ae610e702134cd86edd0eb75efbfbd5526e4b30d8e9bb94f53f83e786cb |
| source40-environment-raw.json | 87d753c6c7b812ab2a534ef76098ac9c4640d0bcb31b94280d568983573d40ca |
| import40-environment-raw.json | 23d925df746cfb3b595c4d04ffb59d9c4edad05ca575e5e9ecea6aefafa70aa7 |
| old39-environment-raw-v2.json | 4c8b3e2ccaa1f1313340d78b29ddf80cc361d55be2c0ddb0aaa8424bc29504fb |
| audit-tail-v2.lean.txt | a66ab563ddcc2d537b7423f1ea3d0060476e7bf9a863dc28f204ddc35eafe1b8 |
| FrozenContracts02.lean | 47af30b919943b028a3df5d50fc42f092e6149e1bc6c7be0e03e0411d04f7cd6 |
| all-errors.json | 5bfeb3f5a56b1407ab9c9233e3c4ace701c51aa3bdee2ae9952ab3be6d17585d |
| prep-baseline.json | a914531d3cd41b973866142ad4c5192c49649062b5ee126afb999fa5e93de0a2 |
| prep-final-preservation.json | d77f978f5647256d581afca3f64755388a9d786a83a5ce4a4f81a783e49f5ef5 |

最终判定：冻结 B0–B3 为 CORRECT / LEAN_FULLY_CHECKED。未认证后继幂、S1、cot、生存谱表示或渐近；完整 Spectrum/OQ4/root 保持 OPEN。
