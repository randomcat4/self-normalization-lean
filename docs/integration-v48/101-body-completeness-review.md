# 101 实际证明体打印完整性复核

结论：`MISSING_UNELIDED_KERNEL_BODY_RENDERING`。这是否定打印完整性的结论，**不是数学错误结论**。本次仅 LOCAL；新增 Lean、远程、上传、亲本执行和子代理均为 0。永久 `ALL101LeanSTOP` 保持，无 FINAL。

已完整读派生 gap、打印器源码证据、提取收据及提取器；独立解析两个 canonical 文件，核对其本地 SHA 分别为 `02b7fbe0989bc7612bc2fda2a8b745a644144c3a384e0ab8588e9b86b2bda5f7`（2277075B）和 `115a416b47827a90e7e065fcbf80ff18140261c197bf543ad38c816c6222805b`（3106471B）。原始 stdout 仍留服务器，绑定 SHA `f6298119f05f2d80c3bd82b76d7e800e0dc4bdd070e92ec12341ac168bb6608a` /5203867B；本轮没有重新读取服务器原始文件。提取器按实际标记保留完整文本，并未把打印器产生的省略补成证明。

独立计数确认 SOURCE=25、LATE=25。实际 metadata 全同；2 个 TYPE 和 1 个 BODY 的原文差异去掉空白后完全相等。25 个完整类型均无 `⋯`。8 个当前证明的 SOURCE 与固定打印体去空白逐项相同，固定打印没有提供额外缺失内容：

| 声明（均在 Shao.OQ5.P53） | body 中 ⋯ | 其中 `:\s*⋯` | 其余 ⋯ |
|---|---:|---:|---:|
| moments_global_rpow_exp_bound | 24 | 15 | 9 |
| moments_dyadic_hasSum | 11 | 3 | 8 |
| moments_shift_bounds | 24 | 13 | 11 |
| moments_positive_exp_bound | 24 | 11 | 13 |
| summable_sparseLabelMass_amplitude_rpow | 30 | 16 | 14 |
| summable_sparseLabelMass_shift_rpow | 25 | 13 | 12 |
| sparseLabelMass_amplitude_exp_tsum_le | 30 | 16 | 14 |
| sparseLabelMass_amplitude_sq_tsum_pos | 21 | 13 | 8 |
| 合计 | **189** | **100** | **89** |

100/89 是明确的文本分类：是否匹配冒号后省略的 `:\s*⋯`。89 不能解释成全部只是类型注记。最小反证是 `moments_dyadic_hasSum` 的 SOURCE BODY 在原 stdout 第 15251 行以单独的 `⋯` 结束（前文是 `⋯);`）；这是最终证明项的位置。固定打印也具有相同结尾。只需这个实际例子，便足以否定“所有完整证明体已无省略读到”的说法，无须机械重读其余数 MB 展开项。

独立支持属性头的解析得到 **98** 条固定打印，按顺序与 audit04 的 98 个 `#print` 全部对齐。原提取器报告 97 是正则未识别 `@[defeq] theorem Real.norm_eq_abs`；正文未丢失这条打印。修正计数不修复上述 8 个证明体的省略。当前 18 个词法声明均与固定打印对齐，其余 10 个 body 的省略计数为 0。

已读 pinned Options.lean 源证据（SHA `d0a49b7a18cc5d9efa691c86be8bd64cccef4ec982cfbebb6c412813819f3f50` /14900B）：15–17 行规定 `pp.maxSteps` 默认 5000，超过访问表达式预算后打印 `⋯`；243 行 `getPPMaxSteps` 直接读取该选项及默认值，不随 `pp.all` 提高。Basic.lean 的 omission/maxSteps 源段与此一致。audit04 未设置 `pp.maxSteps`。因此 `pp.all`、无诊断和 exit0 均不能推出无省略完整体；预算机制为本次缺口提供了直接的源码解释。

最新用户精简指示已停止恢复草案工作；`EightBodyRecovery-01.lean` **未创建**，未创建任何新执行包装器。旧源码、审计、控制稿与证据均未修改。打印义务仍如实标记 MISSING；按最新 AGENTS 可复用的完整源码证明审查和服务器内核/公理收据另见 `reused-source-proof-assessment.md/json`。这里不把旧机械打印门追记成已支付，也不申请或授予停止后的执行例外。HOLD。
