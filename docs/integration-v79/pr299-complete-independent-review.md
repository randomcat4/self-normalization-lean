# SourceOriginalZeroEnergyBudget 独立完整最终审查

STATUS: CORRECT

本审查只认证精确新源 `9e4380fc2e70a64b6ff7661f5f34cde9c18c1e5537e24b4165faeb46c74aee45`（157行、7797字节）及其原成功对象 `2dbf2e7971700bc33e8fbc80c5146c7ad8ef6c9a5ee2da13dc2f7d082f3d90e5`。结论是：在原概率空间、原 AE iid 有限族上，仅共同有限正二阶矩即可支付原实际零能量质量 `mu.real {Σ X_i²=0} ≤16 R_n(0)`。未发现关键数学缺口、隐藏中心化、高阶矩或目标概率前提。

审查者 `/root/original_zero_energy_budget_final_review` 为新鲜、独立、非作者上下文；配置为 gpt-6.1-sol / xhigh，不派生。ACK 已先写入专属目录。配置以外的底层实际模型标识、实际 effort 标识和 input/cached-input/output/reasoning-subset 计数在工具中不可见，分别记录 null；没有将原始 token 或信用估计解释为订阅百分比。

## 完整阅读与冻结忠实性

已完整读取工作区 AGENTS、math-theorem 及规定参考、SERVER、当前精简验收约束和所需协调字段；OQ3 保持用户暂停，所有原根保持 OPEN。未接管生产源或已释放作者职责。

完整读完新源全部157行及唯一公开证明31–155行；完整读完冻结文件、候选完整声明/数学证明/范围和 queued activation。用本地确定性字节比较独立确认公开定理的全部量词、假设和以下五个声明内 literal lets 与候选逐字相同：

1. `sigmaSq := ∫ z, z^2 ∂rho`，为原二阶矩；不是暗换成中心化方差。
2. `scale := sqrt ((n:ℝ)*sigmaSq)`，由 hn 和正二阶矩保证为正。
3. `normalizedLaw := Measure.map (fun z => z/scale) rho`，是真实原 law 的缩放。
4. `R := Shao.truncationBudget normalizedLaw n 0`，是真实 R_n(0)。
5. `rawEnergy := fun omega => ∑ i:Fin n, (X i omega)^2`，保留原实际零能量事件。

源显式公开定理1、private/global helper0、defs0、instances0。额外 `Elab.async false`、maxHeartbeats 选项不改变声明或前提。最终证明局部值为 u/g/Ui/U/m；与早期候选采用 proof-local pi-law 的实现选择不同，但没有改变公开头或声明内5 lets，也没有将 joint-law、可积性或目标事件预算移入假设。

冻结SHA `ce9891b85b932130a937a7b4e37a2098147f0aa08853996cd0eafeb4a79c3c6d`；activation `c86c625942b44c27a0da008756c2fed60139a7df55e7b770f20bda71ffc09ef8`；候选声明 `ce825014e7ab627c88330f8ce0a3a5def6621660dcadb8d84adb9c615e905cb2`、证明 `04ed584b2889aa11972df6b6c8e727033defd79351ce1a3a4161d3d7a5f733fb`、范围 `b3bf8f04280f0dd54cb9003213d3851762f6d1cb869b1ebb2ed65b286d2846dc` 均核对通过。

## 数学证明逐段评价

- **34–58，原归一化与预算。** n>0、sigmaSq>0 给 scale²=n sigmaSq>0；原平方可积性允许除以 scale² 并积分，因此 n E_rho[(X/scale)²]=1。`F(z)=z² min(|z|,1)` 连续、非负且 ≤z²，故 F(X/scale) 可积。通过实际 measurable map 的 integral_map 得 R=n E_rho F(X/scale)，并证明 R≥0。没有采用错误的第三矩可积性推断。
- **59–84，有界截断。** u(z)=z²1{|z|≤1} 为全局 Borel 可测且0≤u≤1，截断边界包括 |z|=1。逐点 z²≤u(z)+F(z)，以及 u(z)²≤F(z)：在小区间用 |z|⁴≤|z|³，大区间 u=0。后者的四次幂是有界截断表达式，不是原 X 四阶矩。
- **85–104，直接在原 Ω 上构造。** g(z)=u(z/scale)，Ui_i=g∘X_i，U=ΣUi，m=E_mu U。g 有界可测，故在概率律 rho 下属于 L²；每个 hLaw 经 measurable g 复合给 Ui_i 与 g 同分布，于是 Ui_i 属于 L²/L¹，有限和 U 属于 L²。积分和交换及同分布积分等式给 m=n E_rho g。未要求 X_i 全点可测，hX 虽未被显式用到仍原样保留；IdentDistrib 已含 AE 可测性，冗余前提不是前提改变。
- **105–118，均值与单坐标方差。** 两侧实际可积后积分逐点 z²≤u+F，并乘非负 n，得到1≤m+R。由 L² 的真实 variance_eq_sub 和 u²≤F 得 Var_rho g≤E_rho F(X/scale)。既没有用原均值0，也没有对不可积的原四次幂作积分。
- **119–133，原独立有限方差和。** 原 iIndepFun 在同一可测 g 下复合仍独立；每项 L² 已实际证明。IndepFun.variance_sum 的 pairwise 独立条件由 iIndepFun.indepFun 支付，函数和与 U 的相等为逐点 funext；用各 Ui 的同分布 variance_eq 得 Var_mu U≤R。旧方差和定理及已 qualified 的 FiniteIID/TruncationIntegrals 只消费原接口，不重审或重编旧证明。
- **134–155，实际原事件与16R。** R≥1/4 时概率≤1≤16R。R<1/4 时 m≥1−R>3/4。对每个 omega，rawEnergy=0 由非负有限平方和的 energy_eq_zero_iff 推出所有 X_i(omega)=0，因此 U(omega)=0。故原事件逐点包含于 {|U−m|≥1/4}。Chebyshev 以 U 的 L² 和正阈值1/4给外测度界；toReal_mono/ofReal 由概率测度有限性和非负方差合法转实值，最终≤16 Var U≤16R。没有先假定未来 scalarCDF/hostcompact/initial G 结果，也未丢弃原 Q=0 成本。

## AE、边界和原文范围

`mu.real` 是有限外测度值的 toReal；这里不需要把原事件未经证明地当作可测集合。实际 pinned API 的 `measureReal_mono` 对任意子集成立，只需上集测度有限；概率测度自动满足。`meas_ge_le_variance_div_sq` 只需 MemLp2 和正阈值，接受 AE 强可测代表。原零能量事件到偏差事件的包含关系在所有点成立，所以保留 AE 异常点，无 null 集代表替换或反向 map_apply 漏洞。有限族的原事件本也可作零测可测处理，但该证明不需要另加此接口。

n=1 完整覆盖，n=0仅由冻结 hn 排除；不暗加 n≥2。允许零坐标、零原子、重复取值、任意非中心共同 law、非完备 Ω、AE 异常点。R=1/4 归入单位概率分支；R=0 在小分支得零质量，不需增加 R>0。scale 非零由原假设严格保证。

已实际读取只读原文 `C:/game/shao/current/c12/supplement.tex` 的3913–3918归一化上下文、3959–3966 cn:zero 声明和3979–3984完整 cn:zero 证明。该原文件SHA为 `b99f2ac4d2f39dd39772d98a5702b7a923c2f10f8730a08fc1b4cd6bba4742bd`。原文使用同一 U、均值/方差界和16R Chebyshev；本形式化在原 AE 家族上直接实现同一路线，且正确允许不中心化（原中心化 law 为其特例）。原文标签/行号以实际文件为准，未盲从旧候选的近似行号。

该结果只支付 cn:zero。scalar CDF、finite2 hostcompact、initial G、terminal E、interval analytic budget 及原 C1/C2/OQ3/OQ4/OQ56 全部根不由本审查闭合；没有新颖性或整篇论文完成声明。

## 实际所属声明、完整类型与递归公理

审计driver完整读取。它遍历 `env.constants.toList`，按 `env.getModuleIdxFor?` 精确模块归属选择每个常量，包含 private/generated，不按显式源码定理数猜测；对每名执行 `Lean.collectAxioms` 并拒绝白名单以外的传递公理。所有 actual types 以 pp.all 导出，没有省略标记。逐名原日志与 JSON 的 kind/AX 同本地导出一一相同。

实际9名全为 theorem：1公开+8 `_simp_1`…`_simp_8`。非 theorem 所属数0、definition数0；因此 definition/opaque/inductive/constructor/recursor 等新非定理值确为0，不是“没有打印所以假定0”。新源只有一份完整公开proof；8名为该 proof 的编译器/简化器生成命题等式，未另写数学 helper。模块归属、名字及完整类型均实际核对；原产物没有逐名 tactic source-position 映射，本报告不伪造某一 `_simp_n` 对应的单个调用点。下表核对每个生成命题的全部数学前提及结论；其完整未缩写实际类型在文末逐名附录。

| 实际名后缀 | 生成来源与类型语义 | 递归公理 | 评价 |
|---|---|---|---|
| original_iid_zero_energy_budget | 显式15–30行完整冻结头；31–155行完整证明 | propext, Classical.choice, Quot.sound | CORRECT |
| _simp_1 | 唯一proof内生成；Zero/OfNat2/NeZero2，(2=0)=False | propext | CORRECT |
| _simp_2 | 唯一proof内生成；Zero/OfNat3/NeZero3，(3=0)=False | propext | CORRECT |
| _simp_3 | 唯一proof内生成；Zero/OfNat4/NeZero4，(4=0)=False | propext | CORRECT |
| _simp_4 | 唯一proof内生成；NoZeroDivisors、a≠0、b≠0，(a*b=0)=False | propext | CORRECT |
| _simp_5 | 唯一proof内生成；MonoidWithZero/IsReduced、a≠0，任意自然幂(a^n=0)=False | propext | CORRECT |
| _simp_6 | 唯一proof内生成；GroupWithZero、a≠0，任意整数幂(a^n=0)=False | propext, Classical.choice, Quot.sound | CORRECT |
| _simp_7 | 唯一proof内生成；AddMonoidWithOne/CharZero，(↑n+1=0)=False | propext | CORRECT |
| _simp_8 | 唯一proof内生成；Zero/One/LE/ZeroLEOneClass，(0≤1)=True | propext | CORRECT |

每个生成结论由其实际代数类型类和已给非零前提成立；等式两侧为命题，所以使用 propext 合法。_simp_6 的额外标准基础公理仍在白名单内。没有新 axiom/sorryAx 或禁止绕过。源码禁词检查 sorry/admit/axiom/unsafe/native_decide 均无命中。

## 原成功服务器证据与保留失败

没有启动任何新 Lean、AX 或旧producer检查，没有取 root-heavy.lock。以下是原作者已有成功结果的只读验证，不是第二次编译：

- 原 worktree `/root/rivermind-data/shao-lean-20261021/workspaces/common-original-zero-energy-budget-v77` 中源码、Git blob字节、本地冻结生产源码三者SHA完全一致。原输出 `attempt003.olean` 与当前目标 `.lake/build/lib/lean/.../SourceOriginalZeroEnergyBudget.olean` 都为450200字节、SHA `2dbf2e…f3d90e5`。目标 Git worktree干净；只有这一个源文件是该提交的改动。
- 原 attempt003 kernel exit0，owned audit exit0，由精确原作者receipt绑定。完整实际阅读1598字节 attempt003 原日志，只有既存 mathlib-view/deprecated-ite/unused-hX 警告，没有error。完整读取3424字节原 OwnedAudit driver。原11295字节审计日志中每个 TARGET_DECL 起至 AUDITED_TARGET_CONSTANTS 前的完整类型段，和本地11071字节导出逐字相同，segment SHA正是 `220280409f6dd2dc023ddfd0f1379ef2358d89c648428fe596e80b47bbf37d48`；9类型、0非定理value、0省略标记。
- attempt001/002 原失败日志仍在原服务器，完整只读核查而未拷贝到工作区：第一份为 integral_div_const API、truncationF 显式可测性和函数加法积分重写问题；第二份为 sigmaSq/sigmaSq=1 的显式非零证明。最终源分别用 integral_mul_const、显式可测/积分形状和 field_simp 非零证据修复。未把失败当通过，没有覆盖或删除原日志，也没有声称保留不存在的早期olean。
- Lean钉死 `leanprover/lean4:v4.36.0-rc1`，mathlib `807d3836b165983210ee2ecf3cd28f239436949c`；实际 worktree manifest、toolchain与只读 shared-v34/packages 解析路径一致。原运行资源receipt为CPU10–13、-M8192、-j4、root-heavy.lock；本审查0重型命令。既存 mathlib Git-view warning不被悄悄抹去；本次只核对真实消费的 Variance、Prod、IdentDistrib、Measure.Real 四份源码，overlay/legacy/钉死git blob字节三者全同，没有源内容漂移。
- FiniteIID 源 `d1b565489199d55af70a27c31a0f803a2b7433e78c9197a361b3c10c0598845b`、对象 `751221ecc043004a49a0905626c512b878ba2621a797ff7b6466b2a7ae60fb5c`；TruncationIntegrals 源 `d7432b7c579c6e6e0d9980af322437941f59f8f670bebd2dd4770f6cfcf1e234`、对象 `3badf67e4cf9f6f299f3618a072aed6582eb26a81d5c95a22190e3339b123c7e`；原依赖绑定逐项与实际服务器字节一致。旧 qualified 接口及对象复用，0 producer重编。

关键文件哈希：

| 工件 | SHA256 |
|---|---|
| receipt.json | 7a46ac0aa45f899078420e4b07080c544702388543ba2d2642c3d136db4187ea |
| 作者 RELEASE.json | f075132dc9988c78ab459ee154397dd6442cf2123ce5ba2f0bd04af4ade7422a |
| owned-audit.json | 9d2eafa4780f169c38e2f9d5970f75e48157a758de86f4d84e14c53efaa893e9 |
| OwnedAudit.lean | 50b1781ba09f5b2721969350442cfb1418715e66f166ac8a037cc51711812bdb |
| owned-audit.log（原服务器） | f10c9c27b6890c502ca15daa2f0d202efbb90c2a0ddb2dea390945494b4e59c5 |
| attempt003.log（原服务器） | a84541b31a38aca5c29ef0cacf0108211fc22a4fe055a0d35f0544ddf9ca1a25 |
| attempt001.log（原服务器） | 77a2281748ae2ae2319f921b6212c4a34320259396498bfbbf905f70d292b67f |
| attempt002.log（原服务器） | d5d7001f2afc21542c2807b12ff8c6afe0e4e46944b108dec110a3a6a2db3301 |
| frozen-comparison.json | a7d6daaf2650c8c082b7ceae2e61ab20620b10b0d87c4095bca44e1f37ffc845 |
| predecessor RELEASE | 9a83f4d9ac2b2843f11e036d2b0bd69ffdc9abd9945eeef72e8997992c12f65d |

完整新源为UTF-8无BOM、157个LF、0 CR，源/导出/driver/receipt/release/依赖/候选每个artifact的预期哈希均独立计算，不改已冻结字节。详细只读绑定为专属目录 local-binding.json、server-binding.json、relevant-pins.json、evidence-summary.json。

## 发表绑定、决定与释放

[PR299](https://github.com/randomcat4/shao-lean/pull/299) 当前通过连接的 GitHub 只读工具核对为 open/draft/未合并，head `2be8550ab989aae3f85b4599136d09b5694338ed`，一个改动源、157 additions、0 deletions；原服务器Git tree `2808e937a5f053e3e902f2b4d6d1ae9f152abedb`、blob `43e851689d5dafdb4b1d4b789e3b2c83e3226fcd` 匹配作者publication。main基线随后前进不改变本精确head证据。本审查未发评论、未修改PR、未合并。

决定：**CORRECT / qualified independent complete review**，可由根在精确源/对象一致时复用。阻断发现为0，生产源修改为0，新Lean/AX/heavy/cache命令为0，子代理为0，所有审查工具请求已完成，reviewer在途为0。作者原 writer/execution RELEASE 保持完整且未复活；本审查不取得其写权。此结果不假定父级或未来候选已支付任何其他原概率成本。reviewer精确不可变 RELEASE 另存专属目录，绑定本md/json哈希。

## 附录：9个实际完整未缩写类型

以下是已完整实际阅读并逐名评价的源绑定类型导出，不是重新运行或重打印。原导出文件SHA为 `220280409f6dd2dc023ddfd0f1379ef2358d89c648428fe596e80b47bbf37d48`。递归AX原行随每个类型保留；完整type哈希另在JSON每名记录。

### Shao.Probability.SourceOriginalZeroEnergyBudget.original_iid_zero_energy_budget

原 AE iid Fin n family，有限且正的共同原二阶矩；原实际能量为零的实值测度 ≤16×同一归一化 law 的 R_n(0)。完整头、全部假设及5个literal lets与冻结头逐字相同。

```text
TARGET_DECL Shao.Probability.SourceOriginalZeroEnergyBudget.original_iid_zero_energy_budget KIND theorem AXIOMS [propext,
 Classical.choice,
 Quot.sound]
ACTUAL_TYPE ∀ {Ω : Type u_1} [inst : MeasurableSpace.{u_1} Ω] (mu : @MeasureTheory.Measure.{u_1} Ω inst)
  (rho : @MeasureTheory.Measure.{0} Real Real.measurableSpace) [@MeasureTheory.IsProbabilityMeasure.{u_1} Ω inst mu]
  [@MeasureTheory.IsProbabilityMeasure.{0} Real Real.measurableSpace rho] (n : Nat)
  (hn : @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) n) (X : Fin n → Ω → Real)
  (hX : ∀ (i : Fin n), @AEMeasurable.{u_1, 0} Ω Real Real.measurableSpace inst (X i) mu)
  (hIndep :
    @ProbabilityTheory.iIndepFun.{u_1, 0, 0} Ω (Fin n) inst (fun (x : Fin n) => Real)
      (fun (x : Fin n) => Real.measurableSpace) X mu)
  (hLaw :
    ∀ (i : Fin n),
      @ProbabilityTheory.IdentDistrib.{u_1, 0, 0} Ω Real Real inst Real.measurableSpace Real.measurableSpace (X i)
        (@id.{1} Real) mu rho)
  (h2 :
    @MeasureTheory.Integrable.{0, 0} Real
      (@UniformSpace.toTopologicalSpace.{0} Real (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
      (@ESeminormedAddMonoid.toContinuousENorm.{0} Real
        (@UniformSpace.toTopologicalSpace.{0} Real (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
        (@SeminormedAddGroup.toESeminormedAddMonoid.{0} Real
          (@SeminormedAddCommGroup.toSeminormedAddGroup.{0} Real
            (@NonUnitalSeminormedRing.toSeminormedAddCommGroup.{0} Real
              (@NonUnitalSeminormedCommRing.toNonUnitalSeminormedRing.{0} Real
                (@SeminormedCommRing.toNonUnitalSeminormedCommRing.{0} Real
                  (@NormedCommRing.toSeminormedCommRing.{0} Real Real.normedCommRing)))))))
      Real Real.measurableSpace
      (fun (z : Real) =>
        @HPow.hPow.{0, 0, 0} Real Nat Real
          (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid))) z
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      rho)
  (hsecond :
    @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
      (@MeasureTheory.integral.{0, 0} Real Real Real.normedAddCommGroup
        (@InnerProductSpace.toNormedSpace.{0, 0} Real Real Real.instRCLike
          (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup)
          (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike))
        Real.measurableSpace rho fun (z : Real) =>
        @HPow.hPow.{0, 0, 0} Real Nat Real
          (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid))) z
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))),
  have sigmaSq : Real :=
    @MeasureTheory.integral.{0, 0} Real Real Real.normedAddCommGroup
      (@InnerProductSpace.toNormedSpace.{0, 0} Real Real Real.instRCLike
        (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup)
        (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike))
      Real.measurableSpace rho fun (z : Real) =>
      @HPow.hPow.{0, 0, 0} Real Nat Real
        (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid))) z
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)));
  have scale : Real :=
    Real.sqrt
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) (@Nat.cast.{0} Real Real.instNatCast n)
        sigmaSq);
  have normalizedLaw : @MeasureTheory.Measure.{0} Real Real.measurableSpace :=
    @MeasureTheory.Measure.map.{0, 0} Real Real Real.measurableSpace Real.measurableSpace
      (fun (z : Real) =>
        @HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid)) z
          scale)
      rho;
  have R : Real :=
    Shao.truncationBudget normalizedLaw n (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero));
  have rawEnergy : Ω → Real := fun (omega : Ω) =>
    @Finset.sum.{0, 0} (Fin n) Real Real.instAddCommMonoid (@Finset.univ.{0} (Fin n) (Fin.fintype n)) fun (i : Fin n) =>
      @HPow.hPow.{0, 0, 0} Real Nat Real
        (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid))) (X i omega)
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)));
  @LE.le.{0} Real Real.instLE
    (@MeasureTheory.Measure.real.{u_1} Ω inst mu
      (@Set.ofPred.{u_1} Ω fun (omega : Ω) =>
        @Eq.{1} Real (rawEnergy omega) (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))))
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@OfNat.ofNat.{0} Real (nat_lit 16)
        (@instOfNatAtLeastTwo.{0} Real (nat_lit 16) Real.instNatCast
          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 15) (instOfNatNat (nat_lit 15)))
            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 14) (instOfNatNat (nat_lit 14)))))))
      R)
```

### Shao.Probability.SourceOriginalZeroEnergyBudget.original_iid_zero_energy_budget._simp_1

Zero/OfNat 2/NeZero 2 下，命题 (2=0) 等于 False。

```text
TARGET_DECL Shao.Probability.SourceOriginalZeroEnergyBudget.original_iid_zero_energy_budget._simp_1 KIND theorem AXIOMS [propext]
ACTUAL_TYPE ∀ {α : Type u_2} [inst : Zero.{u_2} α]
  [inst_1 : OfNat.{u_2} α (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))]
  [@NeZero.{u_2} α inst (@OfNat.ofNat.{u_2} α (nat_lit 2) inst_1)],
  @Eq.{1} Prop
    (@Eq.{u_2 + 1} α (@OfNat.ofNat.{u_2} α (nat_lit 2) inst_1)
      (@OfNat.ofNat.{u_2} α (nat_lit 0) (@Zero.toOfNat0.{u_2} α inst)))
    False
```

### Shao.Probability.SourceOriginalZeroEnergyBudget.original_iid_zero_energy_budget._simp_2

Zero/OfNat 3/NeZero 3 下，命题 (3=0) 等于 False。

```text
TARGET_DECL Shao.Probability.SourceOriginalZeroEnergyBudget.original_iid_zero_energy_budget._simp_2 KIND theorem AXIOMS [propext]
ACTUAL_TYPE ∀ {α : Type u_2} [inst : Zero.{u_2} α]
  [inst_1 : OfNat.{u_2} α (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))]
  [@NeZero.{u_2} α inst (@OfNat.ofNat.{u_2} α (nat_lit 3) inst_1)],
  @Eq.{1} Prop
    (@Eq.{u_2 + 1} α (@OfNat.ofNat.{u_2} α (nat_lit 3) inst_1)
      (@OfNat.ofNat.{u_2} α (nat_lit 0) (@Zero.toOfNat0.{u_2} α inst)))
    False
```

### Shao.Probability.SourceOriginalZeroEnergyBudget.original_iid_zero_energy_budget._simp_3

Zero/OfNat 4/NeZero 4 下，命题 (4=0) 等于 False。

```text
TARGET_DECL Shao.Probability.SourceOriginalZeroEnergyBudget.original_iid_zero_energy_budget._simp_3 KIND theorem AXIOMS [propext]
ACTUAL_TYPE ∀ {α : Type u_2} [inst : Zero.{u_2} α]
  [inst_1 : OfNat.{u_2} α (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))]
  [@NeZero.{u_2} α inst (@OfNat.ofNat.{u_2} α (nat_lit 4) inst_1)],
  @Eq.{1} Prop
    (@Eq.{u_2 + 1} α (@OfNat.ofNat.{u_2} α (nat_lit 4) inst_1)
      (@OfNat.ofNat.{u_2} α (nat_lit 0) (@Zero.toOfNat0.{u_2} α inst)))
    False
```

### Shao.Probability.SourceOriginalZeroEnergyBudget.original_iid_zero_energy_budget._simp_4

Mul/Zero/NoZeroDivisors 下，a≠0、b≠0 蕴含命题 (a*b=0) 等于 False。

```text
TARGET_DECL Shao.Probability.SourceOriginalZeroEnergyBudget.original_iid_zero_energy_budget._simp_4 KIND theorem AXIOMS [propext]
ACTUAL_TYPE ∀ {M₀ : Type u_1} [inst : Mul.{u_1} M₀] [inst_1 : Zero.{u_1} M₀] [@NoZeroDivisors.{u_1} M₀ inst inst_1]
  {a b : M₀} (ha : @Ne.{u_1 + 1} M₀ a (@OfNat.ofNat.{u_1} M₀ (nat_lit 0) (@Zero.toOfNat0.{u_1} M₀ inst_1)))
  (hb : @Ne.{u_1 + 1} M₀ b (@OfNat.ofNat.{u_1} M₀ (nat_lit 0) (@Zero.toOfNat0.{u_1} M₀ inst_1))),
  @Eq.{1} Prop
    (@Eq.{u_1 + 1} M₀ (@HMul.hMul.{u_1, u_1, u_1} M₀ M₀ M₀ (@instHMul.{u_1} M₀ inst) a b)
      (@OfNat.ofNat.{u_1} M₀ (nat_lit 0) (@Zero.toOfNat0.{u_1} M₀ inst_1)))
    False
```

### Shao.Probability.SourceOriginalZeroEnergyBudget.original_iid_zero_energy_budget._simp_5

MonoidWithZero/IsReduced 下，a≠0 时任意自然幂 a^n=0 的命题等于 False。

```text
TARGET_DECL Shao.Probability.SourceOriginalZeroEnergyBudget.original_iid_zero_energy_budget._simp_5 KIND theorem AXIOMS [propext]
ACTUAL_TYPE ∀ {M₀ : Type u_1} [inst : MonoidWithZero.{u_1} M₀] {a : M₀}
  [@IsReduced.{u_1} M₀
      (@MulZeroClass.toZero.{u_1} M₀
        (@MulZeroOneClass.toMulZeroClass.{u_1} M₀ (@MonoidWithZero.toMulZeroOneClass.{u_1} M₀ inst)))
      (@NPow.toPow.{u_1} M₀ (@Monoid.toNPow.{u_1} M₀ (@MonoidWithZero.toMonoid.{u_1} M₀ inst)))]
  (n : Nat)
  (h :
    @Ne.{u_1 + 1} M₀ a
      (@OfNat.ofNat.{u_1} M₀ (nat_lit 0)
        (@Zero.toOfNat0.{u_1} M₀
          (@MulZeroClass.toZero.{u_1} M₀
            (@MulZeroOneClass.toMulZeroClass.{u_1} M₀ (@MonoidWithZero.toMulZeroOneClass.{u_1} M₀ inst)))))),
  @Eq.{1} Prop
    (@Eq.{u_1 + 1} M₀
      (@HPow.hPow.{u_1, 0, u_1} M₀ Nat M₀
        (@instHPow.{u_1, 0} M₀ Nat
          (@NPow.toPow.{u_1} M₀ (@Monoid.toNPow.{u_1} M₀ (@MonoidWithZero.toMonoid.{u_1} M₀ inst))))
        a n)
      (@OfNat.ofNat.{u_1} M₀ (nat_lit 0)
        (@Zero.toOfNat0.{u_1} M₀
          (@MulZeroClass.toZero.{u_1} M₀
            (@MulZeroOneClass.toMulZeroClass.{u_1} M₀ (@MonoidWithZero.toMulZeroOneClass.{u_1} M₀ inst))))))
    False
```

### Shao.Probability.SourceOriginalZeroEnergyBudget.original_iid_zero_energy_budget._simp_6

GroupWithZero 下，a≠0 时任意整数幂 a^n=0 的命题等于 False。

```text
TARGET_DECL Shao.Probability.SourceOriginalZeroEnergyBudget.original_iid_zero_energy_budget._simp_6 KIND theorem AXIOMS [propext,
 Classical.choice,
 Quot.sound]
ACTUAL_TYPE ∀ {G₀ : Type u_3} [inst : GroupWithZero.{u_3} G₀] {a : G₀} (n : Int),
  @Ne.{u_3 + 1} G₀ a
      (@OfNat.ofNat.{u_3} G₀ (nat_lit 0)
        (@Zero.toOfNat0.{u_3} G₀
          (@MulZeroClass.toZero.{u_3} G₀
            (@MulZeroOneClass.toMulZeroClass.{u_3} G₀
              (@MonoidWithZero.toMulZeroOneClass.{u_3} G₀ (@GroupWithZero.toMonoidWithZero.{u_3} G₀ inst)))))) →
    @Eq.{1} Prop
      (@Eq.{u_3 + 1} G₀
        (@HPow.hPow.{u_3, 0, u_3} G₀ Int G₀
          (@instHPow.{u_3, 0} G₀ Int
            (@ZPow.toPow.{u_3} G₀ (@DivInvMonoid.toZPow.{u_3} G₀ (@GroupWithZero.toDivInvMonoid.{u_3} G₀ inst))))
          a n)
        (@OfNat.ofNat.{u_3} G₀ (nat_lit 0)
          (@Zero.toOfNat0.{u_3} G₀
            (@MulZeroClass.toZero.{u_3} G₀
              (@MulZeroOneClass.toMulZeroClass.{u_3} G₀
                (@MonoidWithZero.toMulZeroOneClass.{u_3} G₀ (@GroupWithZero.toMonoidWithZero.{u_3} G₀ inst)))))))
      False
```

### Shao.Probability.SourceOriginalZeroEnergyBudget.original_iid_zero_energy_budget._simp_7

AddMonoidWithOne/CharZero 下，任意自然数 n 的命题 (↑n+1=0) 等于 False。

```text
TARGET_DECL Shao.Probability.SourceOriginalZeroEnergyBudget.original_iid_zero_energy_budget._simp_7 KIND theorem AXIOMS [propext]
ACTUAL_TYPE ∀ {R : Type u_1} [inst : AddMonoidWithOne.{u_1} R] [@CharZero.{u_1} R inst] (n : Nat),
  @Eq.{1} Prop
    (@Eq.{u_1 + 1} R
      (@HAdd.hAdd.{u_1, u_1, u_1} R R R
        (@instHAdd.{u_1} R
          (@AddSemigroup.toAdd.{u_1} R
            (@AddMonoid.toAddSemigroup.{u_1} R (@AddMonoidWithOne.toAddMonoid.{u_1} R inst))))
        (@Nat.cast.{u_1} R (@AddMonoidWithOne.toNatCast.{u_1} R inst) n)
        (@OfNat.ofNat.{u_1} R (nat_lit 1) (@One.toOfNat1.{u_1} R (@AddMonoidWithOne.toOne.{u_1} R inst))))
      (@OfNat.ofNat.{u_1} R (nat_lit 0)
        (@Zero.toOfNat0.{u_1} R
          (@AddZero.toZero.{u_1} R
            (@AddZeroClass.toAddZero.{u_1} R
              (@AddMonoid.toAddZeroClass.{u_1} R (@AddMonoidWithOne.toAddMonoid.{u_1} R inst)))))))
    False
```

### Shao.Probability.SourceOriginalZeroEnergyBudget.original_iid_zero_energy_budget._simp_8

Zero/One/LE/ZeroLEOneClass 下，命题 (0≤1) 等于 True。

```text
TARGET_DECL Shao.Probability.SourceOriginalZeroEnergyBudget.original_iid_zero_energy_budget._simp_8 KIND theorem AXIOMS [propext]
ACTUAL_TYPE ∀ {α : Type u_1} [inst : Zero.{u_1} α] [inst_1 : One.{u_1} α] [inst_2 : LE.{u_1} α]
  [@ZeroLEOneClass.{u_1} α inst inst_1 inst_2],
  @Eq.{1} Prop
    (@LE.le.{u_1} α inst_2 (@OfNat.ofNat.{u_1} α (nat_lit 0) (@Zero.toOfNat0.{u_1} α inst))
      (@OfNat.ofNat.{u_1} α (nat_lit 1) (@One.toOfNat1.{u_1} α inst_1)))
    True
```
