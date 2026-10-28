# Unit259 四处 INTRO 修复独立补审

STATUS: CORRECT

**接受精确修复版的受影响 SOURCE/proof 内容；qualified=false，machinePending=true。** 新源码 SHA256 `778bf48efdda41717da921f6721648e49cebe4d7abd140fc83e4323502019740`，70286B/1111LF；新 PROOF.txt 为 `427c6ae9d37645d1d3f92ee514ae9978e4fe106946fdc93073cfb13f8678c0d2`，16422B/315LF。原完整 SOURCE 审查 `4ada7152813534cd16863b4d60a764e64d38adc00fe00f1d81d6d1fc0888e3cf` 与本次四行补审联合覆盖此版全部源码；没有重复审查未变旧证明。

首次 native 的实际 RC1、无对象、单一 introN 错误是已发生的 elaboration 失败，推翻了先前“无已知 elaboration 矛盾”的静态判断。原 SOURCE 接受没有机器通过含义；失败回执 `765f27a9aebc29c673cfc11f4598562880deb09fe9fa95ff79d088d8bb2d955a` 保留，不能当作内核通过或数学反例。本补审完整读取保存的 native01-actual-projection 与 actual binder-header/goal-prefix 诊断；没有读取或复制服务器 raw log，没有新执行。

实际逐字比较只发现源行 **840、841、842、1090** 改变，即 proof47、48、49、297。完整 exact.patch 的两处 hunk 与逐行差异完全一致，并可重建同一精确候选；其余1107行字节不变。preamble、780LF冻结声明和 closing 均保持，source 仍严格等于这些冻结部分与新315LF proof 的拼接。没有声明、前提、选项、别名、新证明步骤或数学常数改变。

主 intro 删除 `a s ηlocal C Tη Δ` 六个名字。独立从精确冻结 appended goal 提取89个 textual lets，并对结论及 let 类型/值的依赖做闭包，得到83个 live lets，顺序逐项等于修复 intro。六个死名字也独立恰为上述六项：a/s 仅供未使用的 ηlocal；ηlocal、C、Tη、Δ 没有通往 appended conclusion 的依赖。eta 自身直接为 actualNormalizedFamily ν(Y k)，不是通过被省略的 ηlocal 构造，所以省略这些命名不会移除实际 eta 或归一化事实。

保存的真实失败上下文从 νlocal 起有65个 header，原错误 intro 在这些已消去 lets 上继续命名，故 `a` 实际绑定到了 actualNormalizedFamily；其后 W/V/Q/D 等全部错位。当前 live closure 从 νlocal 起同样有65项，修复顺序与其一致。真实诊断直接支持主 intro 的修复原因；这项核对不把 lexical closure 当作新的 Lean 运行。

后段 intro 删除 `δ0 L0` 两个名字。精确冻结后段7个 textual lets 的依赖闭包为5项，顺序为 `β cWindow Fz δη Lη`，与新1090行逐字对应。δ0 只被未使用的 L0 引用；同一 beta-window 与最后8项 strict/cost/probability 结论均不依赖二者。旧 proof 后续只使用 live δη/Lη 和 retained moment packet，因而删除名字不会添加前提或削弱结论。原声明中所有 textual let 的原字节仍保留。

补审确认四个改动行以外的 signed correction、原 μ p 矩、同一 m0/eta、id/q方向、原 Hsource/physicalBad、reduced Ssafe、Borel symmetric-difference、full normalizers、显式2B和共同k0证明全部是原完整审查的精确未变字节。旧完整 SOURCE、STATEMENT、ACK、manifest 和失败证据没有改写。修复作者八个payload、十四个关键输入及精确 release/六零由本次独立重新核验；作者与 reviewer 权限分离。

issues=[]，sourceAccepted=true；**尚需新源码首次成功 native 与同首对象全部实际 TYPE/必要VALUE/递归AX及诊断，不能提前 qualified。** 本 reviewer 未运行 Lean/lake/PP/AX/服务器/网络/上传/Git/API，未创建子代理、Goal、计划或侧栏；P175 adoption 没有重放。请求模型 gpt-6.1-sol/xhigh，实际 model/backend/effort/四类 usage 不可见均 null。

当前 reviewer writers/heavy/inflight/pendingExternal/children/uncertain 六项0，保留同一独立审查权限，未写 FINALWRITE、未释放。下一步由 lead 对此新 source 执行 native02；本上下文等待新精确机器包。full OQ56、root、外部 SZ/CDF/relative/DC 均 OPEN。
