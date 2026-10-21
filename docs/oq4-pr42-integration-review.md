# OQ4 PR42 冻结集成证据验收

结论：**PASS_FOR_ROOT_INTEGRATION**。25 项冻结 payload、现有独立 statement/math/formal 票及三份 lead 收据一致，未发现数学范围或证据链阻塞。本票复用已完成的独立完整证明与 server 检查，不重新证明、运行 Lean 或访问缓存；只写本报告，不改数学源、lane 状态或其他所有者文件。

## 冻结版本与依赖次序

PR42：`feat/oq4-be-sp-blocks`，head `986675bdd753b59c3504f390a5bdf797f47f0711`。认证 base 为 `e6f9d300dbd991d6a55d8e4c1717dab2f35a5e2c`。base provenance 记录已接受 PR38 final head `724b910439148f40c471138bd6778a92148f169b` 与 accepted main `fc30d9dfab5763c764f608698089009d611d4664` 的共同 tree `e1d8430421c1f87cca3e7f043715168ba4ffd513`，随后整合前者；不把树等价误称为已整合 main merge 对象。

实际数学依赖是 `FiniteSurvivalLaplace + KilledBlockBounds → ReflectedSurvival → SpitzerKernelBounds`。后者复用既审真实残差、块质量与有限吸收；不存在反向依赖或将本次目标作为前提的循环。作者收据记录的是其历史执行基线；最终 formal 票、lead receipt 和上述接受基线共同绑定相同冻结源，不能单凭历史作者 HEAD 代替当前根整合。

本次本地只读逐字节检查：两 source、16 docs、3 audit 源、3 receipt JSON 和1 base JSON，共 **25 项**。其中21项已有 SHA 引用全部匹配；base JSON 与三收据内嵌 provenance 精确相同。另按已接受 `receipt-v24.json` 独立比较 curated library 中21个旧 OQ4 source 及 ClosedSurvival/FinitePath/FiniteIID/MeasurablePath 四公共 source，**25/25 原 SHA 保持**。该本地比较不冒充远端前后采样；远端23 OQ4 +4公共源前后保持的记录由冻结 formal/lead 证据承接。

原数学源 `C:/game/shao/current/oq4/b01/proof01.md` 实际 SHA 为 `7c51246eb02a0d694a366ce3ab5a3a9cca03723160c1291bce29dd817f68bc38`，与两收据及声明票一致。核对原 §3/5/6/8 的定位、两个冻结接口、匿名证明、最终源码和现有独立审查，没有新增外部结论归属。

## 25 项精确哈希账

下表路径为拟入 PR 的 archive 路径；对应本地 `drafts/oq4` 原票已逐项核对。所有 SHA256 均为当前原字节，未归一化或修改。

| payload | SHA256 |
|---|---|
| Shao/OQ4/ReflectedSurvival.lean | `b54b2300ef77375782e60a541bcffd6bed05ac4de61a776c6e0fd5e189568809` |
| Shao/OQ4/SpitzerKernelBounds.lean | `e9d956ed03c634f5214c4fd85905d86fa51f6b1e5663a43ed9d3f143fcf5e014` |
| docs/oq4-reflected-author-receipt.md | `9bacdfa6072d8a178bd77d221239288af59ba099eb51d41b87f60b6c46adf02b` |
| docs/oq4-reflected-declarations.md | `45520c713643ec9da074b77360ea7e4266f1e55acd1ee5e12502c1c663c93ba8` |
| docs/oq4-reflected-formal-review-v1.md | `5a6609e8f1de29e2fa7dfa2351b079336dd68b28e165ef3f8ab5c7cc3d07ef57` |
| docs/oq4-reflected-frozen-v1.md | `d70163cb3114dcf35787d6ab1159b80ca67ba6dc2598613ae252e3ec1126f2dc` |
| docs/oq4-reflected-math-review-v1.md | `0289954a28a1d3e9a8475b716ee84bd2025cef22a8eae1ce3ce50809ae3b0d00` |
| docs/oq4-reflected-proof.md | `25574bf05ec2e02b9a064762d2ca7565ae611aae2a3be3432876ec52d03ab266` |
| docs/oq4-reflected-scope.md | `0ba316641b93efcd028c369e2ce09fc0e54901beef811b8814fc8b418911e860` |
| docs/oq4-reflected-statement-review-v1.md | `840594eb5d3cdb732a217125efec74ba6f9d5ea3c161b57ccfca46daf35e6e56` |
| docs/oq4-spitzer-kernel-author-receipt.md | `30fdfb6aaa6bb54a19e071f33fbf99d73ab1ba8b243b0ebd9e9511bd6744ffbc` |
| docs/oq4-spitzer-kernel-declarations.md | `17efbc71a428e3954a114e755c93e23229192f02673ae762df3cab0ae9be3ff5` |
| docs/oq4-spitzer-kernel-formal-review-v1.md | `235e0398bf32956f1526cf7aa049195e61bf874002188d67ce15db5e96c171d6` |
| docs/oq4-spitzer-kernel-frozen-v1.md | `d93f79afc43c6463e3dc2b954f27e92e6e5585fef0505fe4c205e7ba86223ccd` |
| docs/oq4-spitzer-kernel-math-review-v1.md | `64b6780541ead74daf474a2487fd53d7e3f339c99962d080c1ba725528e23976` |
| docs/oq4-spitzer-kernel-proof.md | `dee48d583229544b65c63cf91faf8c5ca46dc95afaad275cdb36750ebb477936` |
| docs/oq4-spitzer-kernel-scope.md | `dd5c5272ae5fc7022061c6fd0c001b0b8300d4be9b25e24dbb1e9ed424a6f26b` |
| docs/oq4-spitzer-kernel-statement-review-v1.md | `a5eccf7f694316ea04abcc0d0631d3df7e83f39aaecbfd9bc5ba5bca4d33b54d` |
| verification/oq4-reflected/Audit.lean | `e8690b9a8c699c6b0a8eebd4fd015f9c50d0a5924a998c0b7092896f9413b89a` |
| verification/oq4-reflected/receipt.json | `25fa63825deea839f5d187229a084d92f40723ce3b8e650b0a69c4f4ff1fbf94` |
| verification/oq4-spitzer-kernel/Audit.lean | `d9603a3c076295959315272f0ebc59c35c970c27f44cc38223be60b5dcfc72bf` |
| verification/oq4-spitzer-kernel/receipt.json | `ad6347f46d88020f4a2c496836608148eea927b31973532e59c02decf7d56ecf` |
| verification/oq4-be-sp-blocks/Audit.lean | `b850ec0ac2eb8b92fcae6533b6e5f851049a8bd2aed76d934dba923b1c3dccfa` |
| verification/oq4-be-sp-blocks/receipt.json | `7533e496c0e9465e460f8723e83ed421fd57f6420c768e1ca0edbe58466d43e4` |
| verification/oq4-be-sp-blocks/base-receipt.json | `e341dbdd0280317921e952c7feecded3b47018afc7d1dd55e2b18eca18d55164` |

## 条件与语义范围

**ReflectedSurvival（15 public /29 owned）：** ν⁻ 是真实 neg-map law，真实有限产品与闭上/下前缀事件的反射涵盖 t=0、零前缀、任意 d、等号及原子。反射 CDF 精确为 `1 − P(X < −x)`，不把 `<` 换成 `≤`；同误差的严格 CDF 由原 law 的全 x 误差与实际高斯连续性/1-Lipschitz 推出。无原子性仅用于高斯，未要求 ν 无原子。输入只一个 ν-BE；ν 与 ν⁻ 的两份全 L>0、0<s<1 原始 SP 分别保留。二者供应真实双侧 S；AC 从一般 law 的闭 CDF 质量引理推出，不额外要求 β 为矩。最终既有谓词实际顺序是 `ν β C`，其展开与冻结自然数学界一致；冻结文字中的参数简写次序事项已由完整 formal 票明确解决。

**SpitzerKernelBounds（3 public /7 owned）：** β 在所有输出及 BE 输入中绑定真正 `∫ |y|³ ∂ν`。平方/立方真可积与二阶1推出 β≥1；块及最终吸收保留 id 真可积、均值0、二阶1、M≥0、β≤M、C_BE≥0。真实 S/AC 在内部取得；R3 返回实际残差绝对值的 Borel 可测性、真实 killed-row 可积性与作用界，R4 是同一实际 killedMass 界。无 reflected-BE、S/AC/O0/R3/R4、B1、条件后独立性或所求归一化质量界的输入。

精确常数为 `Cq=1+2C_BE`、`Cs=√2 exp(6+3C_BE)`、`Clayer=12 Cq Cs M(1+M)`、`E=π³M/48+2π Clayer(1+2M)`、`R=exp(π²)`、`H=2(1+(2Cs)R)R`。Cq/Cs 依赖外部 C_BE；不可自动称无条件通用数值常数。最终保留 h≥3、π(1+M)≤h、自然 N≥m=⌊h²⌋₊、闭 |z|≤h 以及

`((2Cs)R)(ER/h³)N + (2Cs M)R/h ≤ 1/2`。

smallness 是显式数值条件，未含未知目标质量。质量结论含全部 k≤N、特别 k=0；余弦增量要求 m≤k≤N，先作自然差 k−m 再转实数，包含 k=m、N=m。没有省略高度、时间或 smallness 条件；没有偷加第四矩、密度、对称、非格点或有界跳跃。

## 现有机械证据及根门

两独立 math 票在读实现前冻结为 CORRECT；其后各 formal 票分别绑定同一最终源码，记录 server 无-o目标、完整源码动态 `getModuleIdxFor? = none` 全新常量审计和真实22/23模块共存全部 exit0、无诊断。作者唯一发射对象；作者 receipt/summary 中的 independent PENDING 是保留的历史职责状态，最终独立 formal 票已单独补齐，不构成缺审。

新增36 owned 是 **18 public theorem +1 definition +1 instance +16 generated**，并非36个公开定理。包括导入名下生成的 `lowerBlockSurvival.eq_1`、`killedLayerConstant.eq_1`、`killedResidualConstant.eq_1`、`normalizedKernelCosine.congr_simp`、`normalizedKernelMass.congr_simp`。已读三个 lead audit 源，实际选择规则是 OQ4 namespace **或** owner 为 OQ4 模块，逐项收集传递公理并拒绝三标准公理外的项；因此未因 root 名或 namespace 遗漏 helper。单位实际 import 审计计数390/397，联合23模块411 owned，新增29+7=36，均 exit0；白名单只有 propext、Classical.choice、Quot.sound。

本票未重读远端 raw log，也未把 receipt 生成脚本自身当成实际运行证明；机械成功由已冻结独立形式票及实际 lead 收据承接。完整日志留 server，PR 不携 raw log、对象、缓存或历史失败候选。固定工具链为 Lean v4.36.0-rc1，mathlib `807d3836b165983210ee2ecf3cd28f239436949c`。

root 应在精确冻结 head 上核验这25项与 source 保存，加入两模块的根 import 和18个 public manifest 项，并由完整项目 owner 审计、源码禁用项/精确文件集、前后哈希、日志绑定、版本锁及 staged diff 完成整合。root 在本票完成前已报告 v29 实际整库门 PASS：864 public /1436 namespace theorem /2060 module-owned /109 imports，两个新源 SHA 不变，结果在 server `logs/integration-v29/result.json`。这是 root 的实际执行报告，本审查没有重复跑门或独立声称读取其结果；此时正式 receipt 尚待生成属于正常归档阶段。后续应把正式 receipt/报告归档与最终 commit/tree 绑定，不因重复成功检查延迟发布。

**不扩大闭合标签：** 仅显式真实矩、单 BE、两原始 SP 与高度/时间/smallness 下的有限供应链已接受。BE、两份 SP 本身、无条件 S/AC/O0/R3/R4 或 D8、Brownian B1、长时间 K/Kv、4/π、能量 E1–E6、完整窗口与 OQ4 全根仍 OPEN。无新增 blocker；最终整合、receipt 和 merge 由 root 完成。
