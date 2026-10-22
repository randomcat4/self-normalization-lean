# EnergyE1Bounds v1 独立最终形式审查

STATUS: CORRECT

SCOPE: FULLY_CHECKED — 冻结的有限一维E1共同常数总接口及固定law推论

LEAN_STATUS: 指定服务器独立无-o目标、完整源码全部新常量传递公理审计、27模块真实import共存均exit 0，无警告。

审查日期：2026-10-22（Asia/Singapore）；服务器完成于2026-10-21T17:29:38.606051+00:00，实际HEAD为`28b459e8d6e30cc06c8402027c1a8ee18a08c5a7`。未读wrapper作者receipt、summary、ledger、译者票或其他审稿票。父实例独立import/module-owner与集成门不由本票代替。

## 冻结及源绑定

先只读冻结接口与匿名证明，冻结CORRECT / MATH_ONLY数学票SHA256为`450018ec375404824ea013e45ced72c3dfed279137f1dfeefbe89ba3624e1bab`，报告该SHA后才读取wrapper最终源；数学票及匿名证明保持不变。

| 文件 | SHA256 |
|---|---|
| `drafts/oq4/frozen-energy-e1-bounds-v1.md` | `ecb96626109a6517122e2d44cc49602c64478f61bd6b728c0208888c65901faf` |
| `drafts/oq4/energy-e1/proof.md` | `bc4893ea78553175ab49586d4769c2b09e2afd6cffd5e2149acc57eaab765e25` |
| 本机`drafts/oq4/energy-e1/EnergyE1Bounds.lean`及服务器`Shao/OQ4/EnergyE1Bounds.lean` | `448db6e250307358455e7c8da660ffdb094ddb5a42f0e7e81e9c08c02aa4d39d` |
| 直接依赖`EnergyTiltedLaw.lean` | `ea13bcf07671ee77a90910807f09f6c1c1deb95e1834f0715bcc042ab5ecbddd` |
| 直接依赖`EnergyLogNormalizer.lean` | `6bbf4093ed296e5fa40cc680f77670c5a3889d95a3679a1cfaf011a84efa6906` |
| 共同N0依赖`TruncatedEnergy.lean` | `bd8015535312de5812ccca340e5bb6e7dd2d1c55a8da1e627f6aa228500495c0` |
| 共同`Shao/Basic/ClosedSurvival.lean` | `bb6f334d2a7956ebf2d727d2feabd0765c30af33da4e8b4197f1fd658921811f` |
| 共同`Shao/Basic/FinitePath.lean` | `898262898f9c088e2d10e6238e411b4397387b21b1b71a2b545c5edef936e1bb` |
| 共同`Shao/Probability/FiniteIID.lean` | `d1b565489199d55af70a27c31a0f803a2b7433e78c9197a361b3c10c0598845b` |
| 共同`Shao/Probability/MeasurablePath.lean` | `827dc47b74dae67101a4d874f412e4cb55bafe1e67b9ba767c6896c0b7e58b41` |

最终源78行、4591字节。实际本机目标及上述N0/N1/N2副本与服务器一致。全部27个OQ4源及4项共同依赖在服务器检查前后SHA清单相同。未修改作者源、冻结、匿名证明、公共文件、Git或缓存。

## 完整签名与透明结论核对

1. **共同常数（第10–22行）。** `energyE1Constant T`恰为1+C_log(T)+C_μ(T)+C_m2(T)+C_m3(T)，只有T参数。支配定理只需T≥0；从N2取M=0获得C_log非负，从N1取三项矩常数非负，直接证明C_E1≥1及逐项支配。没有将M、ν、β、h、s引入常数，也没有改动旧系数。

2. **透明谓词（第25–39行）。** `energyE1Conclusion ν T h s`是实际命题合取，参数不含M。它明确展开为同一个`energyTiltedLaw ν h s`的概率性、id/平方/绝对立方三项Integrable、ae闭支持|x|≤2h、h≥2、同一`energyNormalizer ν h s`在[1/2,3/2]内，以及四个同C_E1(T)不等式。四项右侧都为原ν的实际`∫|x|³`，分母依次h³、h²、h、1；左侧依次真实log、均值、原点二阶误差及第三绝对矩。

   该def没有假设或抽象替代实际law/积分；两个主定理均把它放在冒号右侧结论，未作为hypothesis，也未将任一待证合取项回塞前提。

3. **共同矩类完整前提（第42–47行）。** 任意实Borel概率ν，M≥0、T≥0、同一`energyLogThreshold M T≤h`、|s|≤T，平方/立方真可积，二阶积分1、原中心∫x=0，以及实际β≤M，完整对应冻结。没有id可积、β≥1、倾斜概率性/可积性、Zerror、分子或矩界等额外前提。

4. **高度、实际Z与law内部供应（第48–57行）。** 调用N2 `energyLog_normalizer_close`取得h≥2及Z区间；因而h≥1和h>0，符合N1全部高度要求。内部取得实际β≥0以进行系数放大。随后调用N1 `energyTiltedLaw_moment_integrability`、实际概率定理及ae支持定理构造谓词前半部。weighted原函数可积性由N1内部已证桥供应，wrapper不再假设它们。N0/N1/N2共享真实对象，未使用不同的normalizer、重标度law或反射law。

5. **四界与同一常数（第58–65行）。** 实际N2 log定理及N1均值、二阶、三阶定理分别供应旧四系数结论。因为原β≥0及h>0，将支配关系乘β/h³、β/h²、β/h、β均保持方向，得到四个同C_E1(T)界。原中心只传给均值定理；第二矩左侧仍是|∫x²dν̃−1|，不等同方差，也未声称倾斜后均值零。

6. **固定law推论（第68–76行）。** 签名删除外部M，阈值精确为H(原ν实际β,T)。证明直接取M=∫|x|³，M≥0由非负立方积分供应，β≤M为自反。其余平方/立方可积、单位二阶、原中心、T/s及高度条件完全保留，返回同一透明结论。没有新增外部矩上界或β可自由选择的假设。

7. **一般质量/测试接口及范围。** 总结论不重复巨大Borel接口，但直接import同一N1真实law，`energyTiltedLaw_real_apply`和`energyTiltedLaw_integral`在本轮实际检查可追溯且可调用。它们提供所有Borel集真实实质量及加权Integrable的测试换测度，未被wrapper遮蔽或替换。T=s=0、h=H弱端点、零点/截断端点原子、不对称无界原ν都沿用冻结范围。s=0的law一般为归一化闭截断而非ν；没有第四/指数矩、密度、无原子或原有界支撑条件。M<1可以是空类，不需加M≥1。

## 独立服务器检查

使用`tools/server.py`正常broker，先source固定activate.sh再cd指定lead-oq4 worktree。三个正式验证命令都在指定服务器`taskset -c 0-3`、单进程顺序运行、无`-o`，没有发射目标olean、重编旧目标或写共享缓存。无不确定操作重放或旁路回退。

```text
TARGET_CHECK_EXIT=0
SOURCE_ALLNEW_AUDIT_EXIT=0
ALL_NEW_DECL_COUNT_NO_NAMESPACE_FILTER 7
ACCEPTED_27_MODULE_COEXIST_EXIT=0
ALL_27_SOURCE_AND_4_COMMON_HASHES_UNCHANGED=True
```

目标为实际`lake env lean Shao/OQ4/EnergyE1Bounds.lean`。独立完整源审计把服务器最终source直接接附录送`lake env lean --stdin`，打印共同常数及完整透明谓词，检查三个公开定理及N1/N2调用接口。随后遍历`env.constants.toList`的全部常量，仅以`env.getModuleIdxFor? declName`为`none`选出新项，对每项执行`Lean.collectAxioms`并拒绝标准三公理之外的项。无namespace、root、声明名或作者清单过滤。

实际枚举7项为：

```text
Shao.OQ4.energyE1Constant
Shao.OQ4.energyE1Constant_dominates
Shao.OQ4.energyE1Conclusion
Shao.OQ4.energyE1_common_bounds
Shao.OQ4.energyE1_fixed_law_bounds
Shao.OQ4.energyE1Conclusion._proof_1
Shao.OQ4.energyE1Conclusion._proof_2
```

五个显式声明传递公理均为`[propext, Classical.choice, Quot.sound]`，两个helper只依赖`[propext]`，无sorryAx。全部实际新项和helper均包括，筛选没有按新root名限制，亦能覆盖导入名称下新生成项。

真实同一Lean输入import全部27个OQ4模块：DelayedRecurrence、OvershootSum、OvershootMoment、VarianceScaling、Foundations、CosineCoefficients、KilledCosine、OccupationPayment、AveragedResidual、KilledKernel、KilledIteration、KernelRecurrence、CosinePowers、KilledPathLaw、KernelAbsorption、BoundaryOccupation、KilledBlockBounds、IntervalConcentration、LaplaceTail、LaplaceGenerating、FiniteSurvivalLaplace、ReflectedSurvival、SpitzerKernelBounds、TruncatedEnergy、EnergyTiltedLaw、EnergyLogNormalizer、EnergyE1Bounds（均`Shao.OQ4.`前缀）。共存时实际打印结论谓词并检查两个主定理、N1集质量/测试接口及两个旧closedUpper可测性定理，均成功。

本机和服务器目标禁用token扫描均0命中：`sorry`、`admit`、`axiom`、`unsafe`、`native_decide`、`sorryAx`。三个独立日志均0 warning/0 error。完整日志只留服务器`repro_outputs/oq4-energy-e1/independent-review-v1/`：

| 日志 | 字节 | SHA256 |
|---|---:|---|
| `target.log` | 0 | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `source-allnew-audit.log` | 8615 | `19b602d83ad766b2c38ebf296427596bb2310d1312ee9680fdb704b9a50c4012` |
| `coexist-27.log` | 3752 | `c8361772cb04ca141d0337b4a88dc58ba979d81973e31ea699d19a0172d4eb4a` |

## 裁决与认证边界

没有发现关键数学或形式缺口。冻结的有限一维E1共同常数入口、实际law性质、真可积性和固定law推论在本独立审查范围内得到完整覆盖。这是对既审N0/N1/N2的透明组合，不增加新分析结论。

**原E1有限形式覆盖的发布仍须父实例实际import/module-owner及集成共同门确认，本票不代替该门。E2、E3、E4、B1、BE/SP、K/Kv、随机分母、完整OQ4及其他全部完整根仍OPEN。**
