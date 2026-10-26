# Unit 219：kernel005 的 3 条 public2 点值化简诊断

作者 `/root/bounded_centered_fixed_formal_author003`，配置 gpt-6.1-sol / xhigh，自 repair004 全零 RELEASE 恢复。实际后端、模型、effort 与 input/cachedInput/output/reasoningSubset 不可观测，记录 null。唯一写入目录为 native-repair005；使用 math-theorem，未启用 math-ultra。本轮无 Lean/AX/heavy、服务器请求、上传、Git/API、子代理，也未编辑父实例的 220 模块或任何旧封印源。

## 输入与已有审查

activation005 的 11 个输入已逐一校验字节数和 SHA256。基线是 664248 完整源：188023 字节、3229 LF，SHA256 `664248ff27985283f74074a24e7359b9eaf217c9b8f6026994f532c1c69071bb`。kernel005 自然 RC1，3 条实际错误全部在 public2 原行 1889；没有 maxErrors 标记、成功对象或 AX。前后源哈希相同，失败字节与回执保持原样。

作者完整读取全部 3 条 curated 诊断（3371 字节），每条实际完整上下文均无省略中段。未下载完整 raw log，也无额外远程上下文请求。

已完整阅读新独立 reviewer004 的 report.md（28069 字节，SHA256 `8461d887b3df7e4e0011d16b441973f81fd31b871a7390e2938eeef190a1d41e`），其结论是对精确 664248 的 SOURCE_CORRECT_PENDING_MACHINE；它完整覆盖 16 个证明、5 values、P4 修订头和两个导出。该审查与本作者独立，实际全零 RELEASE 为 `9d6b3324b1613922fb92b65b373d939e26da05bb1350d7da691e36e02472d9b9`，父 SOURCE-only 接受为 `cc842c8e1812a82fb202e5d79d84c4ae93563de20a882cc08b35400c35b88bef`。本作者读取和绑定此报告不构成本轮自审合格，也不把 SOURCE verdict 当作机器资格。

## 唯一源修改

public2 的局部 hStopped 在原生 kernel005 已越过先前依赖 motive 处，当前 3 条错误来自其 integral_nonpos 后的同一逐点条件证明。实际目标仍显示为 `(fun b => if b∈S then ∫v,F(v,b) else 0) b ≤ (0 : Path t → ℝ) b`。原 split_ifs 在未先归约的函数表达式中分解了条件，却未得到 hFs b 或实数 le_rfl 所需的点值目标。

本轮只将该处改为：

```lean
        apply integral_nonpos
        intro b
        dsimp only [Pi.zero_apply]
        split_ifs <;> first | exact hFs b | exact (le_rfl : (0 : ℝ) ≤ 0)
```

dsimp 在此进行函数应用的 beta 归约并规范化零函数应用；之后条件分支成为真正实数不等式。选中分支使用原 hFs b，零分支使用明确实数类型的 0≤0，消除 Preorder 元变量未定及两个 le_rfl 类型不匹配。3 个原诊断的 SHA/字节/行列分别保留于 REPAIR-ERROR-MAP。

没有更改局部 hStopped 的参数、长度等式、Fin 边界证明、所用实际停止后缀接口、Phi 的真实可测性/绝对值界或 hsection。没有改变 selectedSuffix 的严格/闭边界、raw U/J² 的真正 L1 来源或原数学结论。新增的唯一源码内容是点值规范化和显式实数类型。

## 字节一致性与证据复用

相对精确已审查的 664248，本轮仅 public2 的完整证明体改变；其他 15 个完整证明体逐字一致。全部 16 当前冻结头、5 private defs、local instance、7 imports 的完整前缀逐字一致，P3 原有证明体局部 heartbeat 800000 不变。无新全局声明、import 或数学假设。累计相对 final007 的 14 个原证明体改变数量由实际 body hash 推导，不把 3 条诊断复制成 3 个改变证明体。

依据父已冻结的证据复用范围，下一独立 SOURCE 补审只需完整读取最终改变的 public2 证明；其他 15 个证明及 unchanged values/heads 的精确已有完整审查复用。它仍需结合最终精确源的机器证据。HEAD-CONSISTENCY/INPUT-SEAL 显式绑定这一 SOURCE-only 复用基础，不扩大其范围。

下一依赖是父实例对本候选精确哈希的 native006，再取得原成功对象上的实际完整 owned inventory、全部 TYPE、非 theorem FULLVALUE 和递归 AX，并由同一独立 reviewer 完成 public2 全证明补审与机器补审。当前无任何本源原生/AX 通过声称，actualOwnedCounts=null、formalQualified=false，C2/C12 OPEN。

源码扫描未发现 sorry/admit/axiom/unsafe/native_decide；这不替代 kernel。最终输入/源/head/error-map/payload/checkpoint/RELEASE 均绑定精确源。RELEASE 的 sourceWriter/heavy/inflight/LeanAX/uploads/GitAPI/children/externalRequests 实际全零；普通 final 结束本轮，无后台继续声称。
