# EnergyE2Bounds v1 独立最终形式审查

STATUS: CORRECT
SCOPE: FULLY_CHECKED — 有限一维 E2 log 支付及同一中心 law 总入口
E2_INTEGRATION_STATUS: OPEN_PENDING_PARENT_ROOT_MAIN
ROOT_STATUS: OPEN

最终本机 `drafts/oq4/energy-e2/EnergyE2Bounds.lean` 与服务器 `Shao/OQ4/EnergyE2Bounds.lean` 实际 SHA256 均为 `41b7343861549f55ae86cddb514a5ed55612448b1ab0efc1e3bb580182746ca8`，11643B、175行，UTF8无BOM、LF、恰一末换行。检查分支 `feat/oq4-energy-e2-complete`，HEAD `69d44c430ba5b2b9a9f3e7c3bf8d4607118465ef`。最终接口和实现覆盖冻结数学域，未发现关键证明或语义缺口。

冻结声明 SHA256 `ca080103589803a6e152f746ecbc4272793585431826fe1b9217118e807d70fa`；匿名 proof SHA256 `77832539608025fab3220d6fb8a8e02d3aca5e676d3e7a9cde86a35baa334442`；已冻结独立数学票 `energy-e2-math-review-v1.md` SHA256 `0a014fe1aede8c8d7a325cbd976fe1e49404bd6ec4b0810dd1ba5cd7e546462f`。三者复核均未改。本票不重写原数学票。冻结文件绑定原数学源 `oq4/energy01.md` commit `35d4580b61e22e7145f47730045a09874ef93259`、SHA256 `2e0387f0a35ca677853e45fff271cc2fb0e87db9ee9c6b2f00d3bcf56b51d9e6`；这是冻结中的来源绑定，本轮没有扩大为对该原文件其他声明的认证。

未读取作者收据、总结、账本、检查点、译者票或新 E3 实现。只读了明确提供的旧源哈希基线，不把作者自述当正确性证据。没有改 canonical、proof、冻结、旧票、公共源、Git 或缓存，没有生成任何 olean，也没有重编旧目标。原始日志和审计输入只保留服务器。

## 证明体和冻结语义逐项核查

1. **共同 C2/H2，第9–28、59–65、132–136行。** 阈值正好引用旧 Hcenter；C2 逐项等于 1+K+K(A+2K)+(A+B)+exp(2)A，A、B、K 全部是原透明定义。非负与正 K 由既有窗口/中心接口内部给出，五项支配逐项证明。C2、H2 只依赖先固定的 M,T，未按 ν,h,s,θ 重新选择。实际共同入口输入保留原概率、平方/绝对三次矩真可积、单位二阶、原均值零、实际 β≤M 与共同高度/参数条件；没有 θ、方差、连续/可微性、小量或结论谓词输入。

2. **真正 MVT 辅助，第31–55行。** 实际 `exists_hasDerivAt_eq_slope` 在 t<0 时用于 [t,0]，t>0 时用于 [0,t]，连续性和每个开区间点的 HasDerivAt 均实际提供。代码分别证明 MVT 点 |c|≤|t|，以 0−t 或 t−0 的非零性合法还原斜率等式，再取绝对值乘非负区间长度。t=0 分支单独化简。辅助定理的全实 hd 虽比 MVT 最低需求更强，但两次实际应用都从既有全实导数叶内部供给，未加到 E2 原始输入中。

3. **第一次 MVT 供真实均值小量，第68–89行。** v(t) 就是同一 μ_t 下真可积中心平方的实际积分；全实 HasDerivAt 由导数叶给出。对每个 |t|≤|u|，再由 |u|≤K/h² 验证窗口域，窗口真实 v∈[1/2,2] 给 |v|≤2。第一次 MVT 得 |m(u)−m(0)|≤2|u|；实际中心叶初始身份给 m(0)=∫x dμ，E1 支付 |m(0)|≤A/h²。代码保留该误差并返回 |m(u)|≤(A+2K)/h²，没有误将 μ 原本中心化。

4. **第二次 MVT 供精确 log 系数，第92–113行。** 实际 g(t)=log L(t) 的全实连续性和 HasDerivAt g m(t) 来自已认证导数叶，L>0 是其 firstlaw 依赖内部供应。每个 |u|≤|t|≤K/h² 的 hb 由上一条实际均值定理给出。第二次辅助 MVT 覆盖正、负、零 t；实际 L(0)=1 得 g(0)=0。非负因子支付和环等式精确得到 K(A+2K)/h⁴，未丢 A、未改变2K²系数。没有假设 log 积分式，没有交换积分/求导或以形式微分替代真实 HasDerivAt。

5. **同一 θ 与透明结论，第118–164行。** energyE2Conclusion 只作输出，透明展开明确列出同一 μ_θ 的 m(θ)=0、概率性、a.e.闭支持、id/平方/绝对三次矩真可积、精确均值积分零及四界。共同入口只从第五叶一次 obtain θ，并将同一个 θ 传入 log、二阶、三阶及指数比较。第二阶从真实窗口误差 A/h+B/h² 经 h≥2、B≥0 降为 (A+B)/h；三阶用实际归一化比较 r_θ≤D²r、真实 r≥0、D²≤exp(2) 与 r≤A，得到 r_θ≤exp(2)A。五项支配给统一 C2。各积分都有 law 接口中的真正 Integrable 结论，精确中心积分不是不可积默认零。实际 μ_θ 仍是同一 μ 的 exp(θx)/L(θ) 密度测度，没有换 law 或为不同界重选 θ。

6. **固定 law 和端点，第167–173行。** 置 M=实际 ∫|x|³dν，非负性由实际 integrand 内部给出，β≤M 用 le_rfl。未加 β≥1 或新可积性。h=H2、闭 t/s 窗口、t=0、θ=0、T=0、s=0 和允许的任意原子均保留；小 M 的可能空原矩类未被新增 M≥1 排除。h≥2 内供所有正分母；未除以 A 或 K。原 ν 没有新增有界支持/指数/第四矩/密度/对称/非格点假设。该结论是实际原点二阶的近1界，精确中心来自单列均值零，并未偷换原与新 law 的矩。

## 实际全部公共签名

下列是实际最终源和运行时签名相互核对后的6个定理完整类型；为显示完整 section 参数，均值/log 两定理的原 section 参数已原样展开。`open MeasureTheory` 且位于 `Shao.OQ4`。3个定义分别为源第9行的 threshold alias、第11–15行的明确常数、第118–129行的透明结论；定义完整正文及所有新增常量的完整实际类型另在 source-allnew 日志中直接打印。

```lean
theorem energyE2Constant_dominates (M T : ℝ) (hM : 0 ≤ M) (hT : 0 ≤ T) :
    1 ≤ energyE2Constant M T ∧ energyLinearCenteringK M T ≤ energyE2Constant M T ∧
    energyLinearCenteringK M T * (energyLinearVarianceA M T + 2 * energyLinearCenteringK M T) ≤ energyE2Constant M T ∧
    energyLinearVarianceA M T + energyLinearVarianceB M T (energyLinearCenteringK M T) ≤ energyE2Constant M T ∧
    Real.exp 2 * energyLinearVarianceA M T ≤ energyE2Constant M T
```

```lean
theorem energyE2_abs_sub_zero_bound (f f' : ℝ → ℝ) (C t : ℝ) (hc : Continuous f)
    (hd : ∀ u : ℝ, HasDerivAt f (f' u) u) (hb : ∀ u : ℝ, |u| ≤ |t| → |f' u| ≤ C) :
    |f t - f 0| ≤ C * |t|
```

```lean
theorem energyE2_mean_small (ν : Measure ℝ) [IsProbabilityMeasure ν] (M T h s : ℝ)
    (hM : 0 ≤ M) (hT : 0 ≤ T) (hh : energyE2Threshold M T ≤ h) (hs : |s| ≤ T)
    (hSq : Integrable (fun x : ℝ => x ^ 2) ν) (hCube : Integrable (fun x : ℝ => |x| ^ 3) ν)
    (hsecond : (∫ x : ℝ, x ^ 2 ∂ν) = 1) (hmean : (∫ x : ℝ, x ∂ν) = 0)
    (hβM : (∫ x : ℝ, |x| ^ 3 ∂ν) ≤ M)
    (u : ℝ) (hu : |u| ≤ energyLinearCenteringK M T / h ^ 2) :
    |energyLinearMean ν h s u| ≤ (energyLinearVarianceA M T + 2 * energyLinearCenteringK M T) / h ^ 2
```

```lean
theorem energyE2_log_bound (ν : Measure ℝ) [IsProbabilityMeasure ν] (M T h s : ℝ)
    (hM : 0 ≤ M) (hT : 0 ≤ T) (hh : energyE2Threshold M T ≤ h) (hs : |s| ≤ T)
    (hSq : Integrable (fun x : ℝ => x ^ 2) ν) (hCube : Integrable (fun x : ℝ => |x| ^ 3) ν)
    (hsecond : (∫ x : ℝ, x ^ 2 ∂ν) = 1) (hmean : (∫ x : ℝ, x ∂ν) = 0)
    (hβM : (∫ x : ℝ, |x| ^ 3 ∂ν) ≤ M)
    (t : ℝ) (ht : |t| ≤ energyLinearCenteringK M T / h ^ 2) :
    |Real.log (energyLinearNormalizer ν h s t)| ≤
      energyLinearCenteringK M T * (energyLinearVarianceA M T + 2 * energyLinearCenteringK M T) / h ^ 4
```

```lean
theorem energyE2_common_bounds (ν : Measure ℝ) [IsProbabilityMeasure ν] (M T h s : ℝ)
    (hM : 0 ≤ M) (hT : 0 ≤ T) (hh : energyE2Threshold M T ≤ h) (hs : |s| ≤ T)
    (hSq : Integrable (fun x : ℝ => x ^ 2) ν) (hCube : Integrable (fun x : ℝ => |x| ^ 3) ν)
    (hsecond : (∫ x : ℝ, x ^ 2 ∂ν) = 1) (hmean : (∫ x : ℝ, x ∂ν) = 0)
    (hβM : (∫ x : ℝ, |x| ^ 3 ∂ν) ≤ M) : ∃ θ : ℝ, energyE2Conclusion ν M T h s θ
```

```lean
theorem energyE2_fixed_law_bounds (ν : Measure ℝ) [IsProbabilityMeasure ν] (T h s : ℝ)
    (hT : 0 ≤ T) (hh : energyE2Threshold (∫ x : ℝ, |x| ^ 3 ∂ν) T ≤ h) (hs : |s| ≤ T)
    (hSq : Integrable (fun x : ℝ => x ^ 2) ν) (hCube : Integrable (fun x : ℝ => |x| ^ 3) ν)
    (hsecond : (∫ x : ℝ, x ^ 2 ∂ν) = 1) (hmean : (∫ x : ℝ, x ∂ν) = 0) :
    ∃ θ : ℝ, energyE2Conclusion ν (∫ x : ℝ, |x| ^ 3 ∂ν) T h s θ
```

## 服务器真实命令、退出状态和审计范围

每次 Lean 前先 `source /root/rivermind-data/shao-lean-20261021/activate.sh`，再 `cd /root/rivermind-data/shao-lean-20261021/workspaces/lead-oq4`，开启 `set -e`/`set -o pipefail`；所有 Lean 均 `taskset -c 0-3`，本审查一次只运行一个 Lean 进程。

| 实际检查 | 命令/输入 | 退出状态 |
| --- | --- | ---: |
| READY前旧33+全部32公共源只读快照 | Python逐项SHA核对并写本审查目录的哈希清单 | 0 |
| 最终 canonical 目标 | `taskset -c 0-3 lake env lean Shao/OQ4/EnergyE2Bounds.lean`，无-o | 0 |
| 完整源全部新增声明 | 最终源原字节接审计附录，管道至 `taskset -c 0-3 lake env lean --stdin` | 0 |
| 34模块共同环境首次附录 | `taskset -c 0-3 lake env lean --stdin < coexist-input.lean` | 1 |
| 34模块共同环境修正附录 | `taskset -c 0-3 lake env lean --stdin < coexist-input-v2.lean` | 0 |
| 末尾全部源SHA与旧快照核对 | Python逐项SHA/清单字节相等检查 | 0 |

首次共同环境的3个错误均来自本审查脚本将命名空间 Shao.OQ4 用常量名称引号引用，报 Unknown constant；未改动 canonical 或任何证明。保留原输入/错误日志后，只将审计脚本中的前缀改为显式 Lean Name，再重跑共同环境。目标及完整源已成功，没有无理由重跑。修正版无警告/错误，才作为共同审计认证证据。另有一个只读 Lean API 文件路径探测初猜 /root/.elan 无匹配而退出1，没有执行 Lean 或改文件；随后按实际安装路径查源码退出0。所有其他只读签名/哈希/元信息读取退出0。上述脚本错误不是被忽略的证明缺口。

完整源审计以 `getModuleIdxFor? declName = none` 遍历整个实际环境，没有 namespace、root 或名称筛选，逐个打印完整实际类型与 collectAxioms。独立实测10新增：

- 3定义：energyE2Threshold、energyE2Constant、energyE2Conclusion。
- 6定理：上述完整签名中的六项。
- 1生成项：energyE2Constant._proof_1，仅依赖 propext；其余九项传递公理均为 `{propext, Classical.choice, Quot.sound}`。未用作者报数作为证据。

共同环境从冻结基线中的33个精确模块加新 EnergyE2Bounds 生成34个真实 import；环境实际模块计数也为34，不含其他新 scratch 模块。进一步对所有常量按“所属模块在 Shao.OQ4 下 **或** 名称在 Shao.OQ4 下”作并集审计：模块归属647项、命名空间635项、命名空间在归属外0项、并集647项，全部传递公理只在标准三项白名单内。该 owner 检查捕获名称前缀筛选会漏的12项：`Shao.closedUpper.eq_1`，以及 Path 的11项 private/生成声明。Path 的共同 private 前缀 `_private.Shao.OQ4.EnergyPathLaw.0.Shao.OQ4.` 下含 finitePi_withDensity_lintegral、energyPath_closed_density、energyPath_density_integrable、energyPath_energy_le，以及 energyPath_closed_density._simp_1_1 至 _simp_1_7；全都实际审计，没有忽略 private 或导入名生成项。两个总入口也单独打印标准三传递公理。

READY前基线JSON SHA256 `6e54f5918a98274c62f529c401b8d1785486214344b2fe86d2a285d9234d1e6c` 的旧33项逐个核对，包含完整 EnergyPathLaw 最终 SHA256 `3336b977fbe88ae4c27ff7531ffeec6e14c71508587ac2abae99bf475757a177`。全部32份 Basic/Probability 公共源递归枚举，没有只查直接依赖。旧33+公共32共65项从 READY前到最后保持；最终34+公共32共66项检查前后完整清单相同。旧32模块和公共32还与本审查者上一中心叶独立清单逐项一致。目标本机/服务器最终SHA匹配，原冻结/proof/math哈希复核不变。

本机和服务器最终源禁用项扫描均通过：没有 sorry、admit、axiom、新公理占位、unsafe、native_decide 或 sorryAx。实际 proof 体及谓词均已阅读，语义核查没有被 Lean 成功代替。检查完成 UTC `2026-10-21T19:41:13.538692+00:00`；本审查服务器进程全部结束，无遗留 live Lean。

## 原始日志定位与完整性

所有输入及完整原始日志仅保留服务器 `repro_outputs/oq4-energy-e2/independent-review-v1/`。成功日志全部零警告/错误；首次共同附录日志保留3个上述审计脚本错误。

| 文件 | 字节 | SHA256 |
| --- | ---: | --- |
| target.log | 0 | e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855 |
| source-allnew-audit.log | 79790 | d9b4da0d58f214799cab53040f5e066189ec63fa986592eda8eb34f3c96b4b22 |
| coexist-34-owner-audit.log（首次，exit1） | 4816 | b224a0daa3967e553389574b57d290ad73defb77cb1a5ba59d4c524ea2a46eb4 |
| coexist-34-owner-audit-v2.log（最终，exit0） | 90491 | db0123d5a8f34b6d9261e17a82bf8df343bc53e6c14ba972361b0f9cb38f071c |
| hashes-before.txt | 6639 | 02f2f9d41e94eaa625772d3498251403d943ec6e9977c51322c90962dcd0ccd8 |
| hashes-after.txt | 6639 | 02f2f9d41e94eaa625772d3498251403d943ec6e9977c51322c90962dcd0ccd8 |
| old33-common-before-ready.txt | 6544 | a0662431fd9937e075b08333259b4310e72510963474eb1c1e23f93fb64fd44c |
| coexist-input.lean | 3219 | a4f89e0c1ce172ee893191353ba96dc0a3759aa00eebec52c611fb5b3f7d246d |
| coexist-input-v2.lean | 3272 | aeafec01fc694e34b847338ef3b80aaef05b72ed517a8dac06cbd4e22ca7177f |

本票认证这一 source hash 上的有限一维 E2 新分析支付和同一实际 θ/law 汇总；调用旧叶的接口装配不多算独立原始承重义务。该本线最终门通过后，父级完整共同门及 root/main 整合仍另待。本票不输出 θ 唯一/选择、不认证 E3 路径或共同算子、E4 条件能量、K/Kv、随机分母或完整 OQ4 根；这些完整根全部 OPEN。
