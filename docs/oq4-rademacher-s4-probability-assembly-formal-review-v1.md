# OQ4 S4 完整独立有界审查 v1

STATUS: CORRECT
LEAN_STATUS: LEAN_FULLY_CHECKED（精确私有 S4 完整模块范围）

最终 Source 为 31603B，SHA256 803ee8488697c8f335e35a32f32fdd31ca69d521e1071eef2018af5b12f775bd。完整原文/数学冻结/匿名证明/完整 Source 审查、实际 Native 声明语义核对、ALL OWNED 内核与传递公理门全部通过。未发现需要修正的数学、声明或实现缺口。

本判定只覆盖固定 Rademacher 的冻结 S4 第3–7节及其派生尾桥，依赖给定且实际绑定的 S3/DA1/DA2/Brownian 接口。没有进行发布或根整合；S5、strict、其他 cosets、一般分布、uniform-x OQ4 及整体 Spectrum/OQ4 根不因此关闭。

## 独立数学与 Source 结论

匿名数学证明全文293行（24651B，SHA256 8617940903362b85c6fc2dad2b437691c4d41874d8fb6568f0230ac905a9f2af）和完整 Source 1–708行均独立全文读入。首次证明曝光发生在阶段A release之后；未读94的解释、Native诊断推理、source-map/receipt、其他独审推理或S3实现证明。

37个公开声明（27定义+10定理头）去除注释/空白后与精确冻结逐项一致。两个私有辅助引理的完整证明也已检查。数学与Source的关键接线为：

| 范围 | 实际核查结果 |
| --- | --- |
| 定义及有限胞元 | 同一实际p/K、同一B/P/hB的b；m≥1且m≤h<m+1；δ=H−h∈(0,1]，弱整数左端δ=1；任意自然n，包含n=0时p=K=1。 |
| S4-ALL | 仅原三尺度前提；DA2导出H、N/H²发散及N/h⁴、1/H²趋零。实际S3提供正性和对数桥。Source取Ktime=Kpos=max(KT,Kalg)，正时间、H²≤N、正侧x→0、真实正性和log合法性都在结论侧。 |
| 误差及主项 | 同一具名C_DA=RademacherLatticeShift.C，在所有有限参数/序列之前固定。scale3=N/h³与实际eta3=logQ−Cdet分开。尾段eta3=logD−logT→0；正主项为π²/4·(N/h³)·δ；统一界C_DA·(N/h⁴+1/H²)。没有自由余项、逐序列常数或Brownian强误差率。 |
| S4-SUB | 从scale3→0导出固定M=1；实际logQ→0，最终正Q上使用exp(logQ)=Q，得到Q、QK→1及共同合法ε尾段。不要求额外M、单调、奇偶或全程正时间。 |
| 移位与返回 | 任意固定K0≥Kcell；shifted_inputs保留全j胞元和原尺度、同一M；shifted_objects保持同一j+K0上的实际对象。outputs_unshift用阈值加K0及k−K0+K0=k返回原序列。EVENTUAL/SUB_EVENTUAL保留非法有限前缀，不换事件或概率。 |

匿名证明的共同S3尾阈值简写可取有限max共同见证；Source明确并入Kalg。Source的历史状态注释不充当当前认证依据。详细逐节及Source区段追踪见phase-a-review.json。

## 实际 Native 声明语义

不是只核对声明文本：已全文读完actual-owned-interfaces.md第1–1336行，即全部63个所属声明的实际类型和全部27个实际定义体。

- 37个公开类型、26个额外所属类型（2私有辅助+24生成定理）均实际逐项审查；没有用公开列表过滤所属集合。
- 全部27定义保持冻结对象和表达式，包含TimeLegal、ProbabilityLegal、LogIdentities及S4Outputs的完整透明结论体。
- shifted_inputs的pp.all实际类型第970–1049行明确显示m_,n_:Nat→Nat，h_:Nat→Real；shift Nat m_与shift Nat n_仍返回Nat，仅比较实阈值时用Nat.cast Real。Kcell≤K0、固定M、弱胞元和所有输出量词均保留。第493行标准elab_without_expected_type属性没有改变数学命题或添加条件。
- 生成congr_simp、定义等式、自然数max/截断减法及数字证书全部被纳入内核和公理检查，其实际类型也已读完。各项读范围与CORRECT理由见actual-interface-semantic-review.json。

## 独立内核与递归依赖门

只运行一次完整私有检查。原Source字节位于组合模块offset0，随后追加9251B独立审计后缀；主模块确认为Shao.OQ4.RademacherS4Assembly。固定Lean 4.36.0-rc1、CPU18–21、-M8192 -j4 -DautoImplicit=false，直接调用固定binary，-R指向私有目录，未用-o、lake env、RLIMIT_AS或ulimit-v。

实际trustLevel=1025，skipKernelTC=false，autoImplicit=false。真实环境差集=模块所属集合=foldStage2三份完整roster一致：

| 项目 | 实际结果 |
| --- | ---: |
| 全部所属声明 | 63 |
| 所属定义 / 定理 | 27 / 36 |
| 公开定义 / 公开目标定理 | 27 / 10 |
| 私有源辅助 / 生成定理 | 2 / 24 |
| 完整递归closure常量 | 61213 |
| 实际项目依赖常量 | 593（126定义+467定理） |
| 实际递归项目模块 | 24 |
| 运行时绑定对象 / resolved leaf链接 | 30 / 30 |
| 所属及项目unsafe / partial / axiom-kind | 全部0 |

递归从全部所属常量出发，对每个访问常量同时遍历ci.type与ci.value? true，包含opaque/theorem proof值；之后才以实际Native模块owner识别项目依赖，未用header模块列表替代递归。24个实际owner逐项绑定到冻结source/olean路径和SHA，另外6个仅导入对象单列在actual-dependency-bindings.json。全部63所属及593项目依赖的公理仅为propext、Classical.choice、Quot.sound。

## 保护边界与工具失败记录

pre/post同时核对四份完整hash map及各自membership，数量50/218/268/107；HEAD=54a2db6cee45504f3bf52b04a51ad1409df4aaec，branch=feat/oq4-s4-assembly，4个CP refs、packages符号链接、全部30个source/olean绑定及30个resolved leaf链接均保持。canonical目标Source和olean在前后均ABSENT；原Source与组合字节未变。

首次Lean实际exit0，Native输出NATIVE_COMPLETE_PASS。随后独审运行器额外要求“24个递归模块集合=全部30个导入对象集合”的过强后处理断言失败。原运行器、tool-failure.json和已成功的audit-native.json均保留。父协调明确确认应逐实际owner精确匹配相应binding，并单列6个import-only对象；仅后处理修复，新增Lean运行0次，未重跑成功内核。最终check-receipt的exit0恢复依据写明：原运行器只有实际subprocess.returncode==0才进入出错后处理分支，同时Native完成标记和post guard已存在。

## 证据与范围

- 最终Native大JSON、raw Expr、完整日志及运行环境仅留服务器；本地只回取curated接口、所属公理清单、依赖绑定及小收据。
- Native JSON SHA256：35c84a5975a82a3017c2c5a7c0793994d29dd85d04365736564b082f7ef8af98。
- 本地check-receipt.json：4903B，SHA256 c74b5dfa83a2292501127e3acecea64ff6ff58b1a051318142ea9029c23efba7。
- 所有原始输入、工具、精简工件及服务器证据的字节/哈希/读范围见review.json；实际Source和原始数学输入在末次复核均未变化。
- 所有本地和远程写操作均在本独审owned目录内；未修改目标、上游、canonical、Git、cache或package，未回滚他人改动。

最终裁决：CORRECT。精确私有S4装配完整通过；发布/根整合另行处理。首次完整成功后已停止全部Lean，不继续实现或构建。
