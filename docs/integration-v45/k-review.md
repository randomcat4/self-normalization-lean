STATUS: CORRECT

独立审查者：`/root/common_cone_review`；作者：`/root/common_cone_author`。本审查使用 math-theorem，未参与生产证明，未改生产源码、声明冻结、作者收据或缓存，未执行任何 Lean。核验复用作者成功的精确源码版本服务器内核检查与所属声明传递公理检查，并独立完成数学与源语义审查。

接受的唯一生产版本是 `drafts/c12-cone-derivatives/QuadraticChordConeDerivatives.lean`，SHA256 `783da67b50d58461a7d831cf6056d86387268cda3bf0927cf16855cf26dc5011`（16914 字节）。服务器对象 SHA256 `e6cae0ce8206f0800c9b0846e7f11c4d43f901d201b8d443e36104898e396cb8`。接受两个公开声明 `Shao.Probability.quadraticChordChar_cone_derivatives` 和 `Shao.Probability.quadraticChordChar_cone_derivative_bounds` 及其全部私有/生成辅助项；不是对 C1/C2 或整个 highderivatives 引理的接受。

已完整阅读这份 360 行生产源码、冻结的完整候选声明及源契约、现有 544 行 `QuadraticChordNoise.lean`，并核对 `LowFrequencyDamping.lean` 的真实配对平方矩证明。原文核对覆盖 main 650–702，另核 main 622 的正方差定义，以及 supplement 2381–2382、2470–2475、2596–2620、3325–3353。原 main/supplement 全文件哈希分别为 `beb00f718487e36de433175c97f1d500cb48e7a92ce5bd5ad5d62bb132122d06`、`b99f2ac4d2f39dd39772d98a5702b7a923c2f10f8730a08fc1b4cd6bba4742bd`，与冻结源证据一致。

实质审查结果如下。

1. **对象、量词与前提忠实。** K 是现有 `quadraticChordChar ν`，即真实 `quadraticChordLaw ν` 下的复指数积分。偏置独立配对密度是 `D²/(2V)`，独立三角变量的特征函数是 `2(1−cos t)/t²`，故真实 K 的有理表示归一化恰为 `V⁻¹`；`V = variance id ν = τ²`。源码没有把 K 换成任意给定核，也没有假定所求导数。`quadratic_pair_square_moment` 证明的是 `E(D²)=2V`，允许非零均值。h3、正方差、概率律与支撑条件均显式保留；原文 main 622 已有 `τ²>0`，有界支撑支付 h3。没有增加中心化、γ 尺度条件或衰减前提。对当前精确源码重新进行空白归一化签名比较，两个完整公开类型均与冻结候选完全相同；冻结候选 SHA256 为 `be14d61f60eacfc3b81f0e1fdf5e02e9e9b464a8f6b3ddfd49236181018eda05`，源契约 SHA256 为 `8b6be3ce246820d8dc3577d21d0c7f0e29c8392d9039cf85a02ac8847fbbb8dd`。

2. **有理核与一二阶导数正确。** 私有 `kernel`、`kernel1`、`kernel2` 的全部实际定义值已读。对固定 D、c，在 `u+c≠0` 处，逐次商法则给出

   `Q1 = D sin(Dθ)/θ² − 2(1−cos(Dθ))/θ³`，

   `Q2 = D² cos(Dθ)/θ² − 4D sin(Dθ)/θ³ + 6(1−cos(Dθ))/θ⁴`。

   系数、符号、实变量 u 的导数以及复数 `ofReal` 嵌入均正确。`cos_gap_bounds` 用半角恒等式与 `|sin x|≤|x|` 证明 `0≤1−cos x≤x²/2`；`kernel_bound` 还显式处理 Lean 总除法下的 t=0 分支。`rational_bounds` 的绝对值三角不等式及正分母运算给出 `|Q1|≤2D²/|θ|`、`|Q2|≤8D²/θ²`，没有漏掉负 θ 或 D=0。

3. **闭锥与积分求导没有缺口（源码 140–292）。** 对支持上的配对，`|a+b|≤2h` 和闭锥条件 `|v0|≤|u0|/(4h)` 给出 `|θ0|≥|u0|/2`。在实开球 `s=B(u0,|u0|/4)` 上，同一支持全集统一满足 `|u+v0(a+b)|≥|u0|/4>0`。这个论证不要求邻近点继续属于闭锥，故锥边界也完全覆盖。原 exact 公式中的连续零相位分支仅在这个邻域的零测补集上被去掉；私有有理核在 θ=0 的任意总除法值不改变真实 K 的积分。

   源码以同一个配对支持事件建立 `∀ᵐ p, ∀u∈s` 的下界与非零性，量词次序足以作统一支配。F0 全域受 `D²/2` 支配；F1、F2 在 s 上分别受 `8D²/|u0|`、`128D²/u0²` 支配，均由实际配对平方矩给出可积性。全部被积函数可测；两个逐点求导公式适用于同一支持事件的所有 u∈s。已核对当前 Mathlib `ParametricIntegral.lean` 284–289 的 `hasDerivAt_integral_of_dominated_loc_of_deriv_le` 全部假设，两个调用均逐项满足。

4. **第二阶结论是实际标准 deriv 的导数（源码 271–292）。** `hK` 先在整个 s 上把真实 K 与有理核积分识别；`hfirst` 对每个 u∈s 证明真实 K 的 `HasDerivAt`，而非只在 u0 给一个积分候选。随后 `hsecond` 使用这些邻域内的一阶 `deriv` 恒等式，结合 F1 的积分求导，得到 `HasDerivAt (fun u => deriv (fun r => quadraticChordChar ν r v0) u) d2 u0`。因此两条 `deriv` 恒等式由标准导数唯一性取得；不是把 Q2 命名为二阶导数，也不是只检查孤立点的候选值。

5. **最终 8/|u| 与 64/u² 常数预算完整（源码 294–358）。** 在原锥点，核界及 `|θ0|≥|u0|/2` 给出 `|Q1|≤4D²/|u0|`、`|Q2|≤32D²/u0²`；积分、代入 `E(D²)=2V` 后分别为 `8V/|u0|`、`64V/u0²`，再除以严格正 V 得到冻结界。实际复导数是实积分的 `ofReal`，复范数转为实绝对值合法。这条更直接的证明不依赖原文 Cauchy–Schwarz 中间路线，结论与原条件均未改变。

6. **全部所属声明及公理证据覆盖。** 完整阅读最终成功的 `actual-owned-types-and-definition-values-02.log` 第 1–1258 行，覆盖全部 41 个所属常量的实际类型及全部 3 个定义值。与 `owned-audit.json` 的所有权选择名单精确集合相等，无缺项、重复项或其他常量种类；分解为 2 个公开定理、9 个私有手写引理、27 个生成定理、3 个定义。生成类型均是对应的数值实例证据、非零化简/幂化简或定义方程，不引入额外数学前提。导出末行为 `EXPORTED_ACTUAL_OWNED_TYPES_AND_DEFINITION_VALUES 41`，没有错误、占位或 sorryAx。`OwnedAudit.lean` 依据 `env.getModuleIdxFor?` 的实际目标所属模块选择全部常量，逐项调用传递 `Lean.collectAxioms`；41 项全部只依赖 `propext`、`Classical.choice`、`Quot.sound` 的子集。当前生产源的 `sorry/admit/axiom/unsafe/native_decide` 扫描为空。

服务器证据均已只读核对哈希、字节数与作者收据的一致性：

- `author-receipt.json` SHA256 `55d34dcbe09c0b46465212bd481aca5e984864b96be0c2200f778585b894584c`；head `10655535e5656c96768819b33a2b9df0fa124f84`。
- 精确源 `targeted-05` 检查退出码 0；其空日志 SHA256 `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`。工具链 `leanprover/lean4:v4.36.0-rc1`，Mathlib 锁 `807d3836b165983210ee2ecf3cd28f239436949c`。这次原有成功检查未由审查者重复运行。
- 所属公理审计退出码 0；JSON SHA256 `cbd5195f9da9614a2d6d0872074947d977ccf98cd764bccb3b95291c6c8a68ea`；`actual-types-and-axioms-03.log` SHA256 `7285d836903bec4e1f27cc28521654e17f3deb3c12ac2d01ceb791eacf1c24e5`。
- 全所属实际类型/定义值导出退出码 0；`actual-owned-types-and-definition-values-02.log` SHA256 `12abe3d77d36942c1bc6306e071e5ca1d82e7be231706555ab43a08d36de45b1`（88396 字节）。早期失败导出日志不是本审查接受证据。
- 导入的真实 K 与平方矩源哈希分别为 `75069c06d5794a5e530e99260e6e3308656623ea39944ac70f1d958ffd40d275`、`ffdeace2421a3c0fdf63def48eb96b882f9dc98014e5614d226a07f87a02bb65`，本地已读源与服务器源一致。`borrowed-object-links.json` SHA256 `874a47feafe2c0676b7b628d9efe91f2be37a00b27a19bb4889d93ccbd13e64d`；其中 5 个链接逐一核对为指向记录的 accepted v43 只读对象的真实符号链接，目标哈希全部一致。没有因此重编或复制基线对象。

本冻结模块的证明与语义审查完整，机械覆盖可记为 `LEAN_FULLY_CHECKED`，范围严格限于这两个冻结公开定理及全部所属辅助项。无需修改生产代码。

消除的原源义务是 highderivatives(a) 中真实 K 的一二阶 u 导数公式与锥内逆幂界。下一消费者是现有真实 `quadraticFullNoiseChar_product` 中 `K(u,v)^8 K(-u,v)^8 sourceScalarChar(γu)` 的乘积/反射链规则。仍需实际 scalar Fourier 的缩放一二阶衰减与实际 Ξ 锥导数装配；highderivatives(c) 的中心化特征函数/协方差及至少六个未微分 chord 因子的 power-gap 装配也未完成。highderivatives(a) 整体、highderivatives(c)、C1/C2 均保持 OPEN；此票没有扩大原范围或提出新颖性主张。
