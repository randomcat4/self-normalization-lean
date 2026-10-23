# U21e 独立完整证明审查

## 不可改写盲审前缀

本前缀在读取新模块实现、冻结 scope、作者 receipt 或证明叙述、旧审查票之前写成。此前仅读行政规则与 math-theorem 角色/Lean 审查协议。唯一数学输入为完整 u21e-actual-types.txt（98 行，7626 字节，SHA256 d27df93d04c86ef5ca05d048fc61bd24a9a35c727fc8c63af2e43bf752d796b3）。我未运行 Lean、Audit、工具链探测或远程命令。

### 完整实际类型原文

```text
DECL Shao.OQ3.exists_compact_tilted_whitened_family
TYPE ∀ (mu : MeasureTheory.Measure ℝ) [MeasureTheory.IsProbabilityMeasure mu] (M : ℝ),
  0 ≤ M →
    (∀ᵐ (x : ℝ) ∂mu, |x| ≤ M) →
      ∀ (K : Set (ℝ × ℝ)),
        IsCompact K →
          ∀ (u0 v0 beta c R : ℝ),
            0 ≤ beta →
              0 < c →
                0 ≤ R →
                  (∀ (xi eta : ℝ),
                      R < √(xi ^ 2 + eta ^ 2) →
                        ‖Shao.OQ3.jointCharacteristic (mu.tilted fun x => u0 * x + v0 * x ^ 2) xi eta‖ ≤
                          1 - c * (√(xi ^ 2 + eta ^ 2)).rpow (-beta)) →
                    have mu0 := mu.tilted fun x => u0 * x + v0 * x ^ 2;
                    have D0 := Shao.OQ3.parabolaCovariance mu0;
                    ∃ m,
                      0 < m ∧
                        m ≤ 1 ∧
                          have lo := m * D0.det / (D0 0 0 + D0 1 1);
                          have hi := 2 * (M ^ 2 + M ^ 4) + 1 + lo;
                          have c0 := m ^ 2 * c / 2;
                          have mup := fun p => mu.tilted fun x => p.1 * x + p.2 * x ^ 2;
                          have D := fun p => Shao.OQ3.parabolaCovariance (mup p);
                          have s := fun p => √(D p 0 0 * D p 1 1 - D p 0 1 ^ 2);
                          have t := fun p => √(D p 0 0 + D p 1 1 + 2 * s p);
                          have A := fun p =>
                            ![![(D p 1 1 + s p) / (s p * t p), -D p 0 1 / (s p * t p)],
                              ![-D p 0 1 / (s p * t p), (D p 0 0 + s p) / (s p * t p)]];
                          have means := fun p => ![∫ (x : ℝ), x ∂mup p, ∫ (x : ℝ), x ^ 2 ∂mup p];
                          have Y := fun p x => (A p).mulVec (![x, x ^ 2] - means p);
                          have nu := fun p => MeasureTheory.Measure.map (Y p) (mup p);
                          have Phi := fun p xi eta =>
                            ∫ (y : Fin 2 → ℝ), Complex.exp (↑(xi * y 0 + eta * y 1) * Complex.I) ∂nu p;
                          have L := 1 / √hi;
                          have U := 1 / √lo;
                          have Q := 4 * U * (M + M ^ 2);
                          have cA := c0 * U.rpow (-beta);
                          have RA := R / L;
                          0 < lo ∧
                            lo < hi ∧
                              0 < c0 ∧
                                0 < L ∧
                                  0 < U ∧
                                    0 ≤ Q ∧
                                      0 < cA ∧
                                        0 ≤ RA ∧
                                          ∀ p ∈ K,
                                            MeasureTheory.IsProbabilityMeasure (mup p) ∧
                                              (∀ᵐ (x : ℝ) ∂mup p, |x| ≤ M) ∧
                                                MeasureTheory.MemLp (fun x => x) 2 (mup p) ∧
                                                  MeasureTheory.MemLp (fun x => x ^ 2) 2 (mup p) ∧
                                                    ENNReal.ofReal m • mu0 ≤ mup p ∧
                                                      (∀ (xi eta : ℝ),
                                                          lo * (xi ^ 2 + eta ^ 2) ≤
                                                              xi ^ 2 * D p 0 0 + 2 * xi * eta * D p 0 1 +
                                                                eta ^ 2 * D p 1 1 ∧
                                                            xi ^ 2 * D p 0 0 + 2 * xi * eta * D p 0 1 +
                                                                eta ^ 2 * D p 1 1 ≤
                                                              hi * (xi ^ 2 + eta ^ 2)) ∧
                                                        (∀ (xi eta : ℝ),
                                                            R < √(xi ^ 2 + eta ^ 2) →
                                                              ‖Shao.OQ3.jointCharacteristic (mup p) xi eta‖ ≤
                                                                1 - c0 * (√(xi ^ 2 + eta ^ 2)).rpow (-beta)) ∧
                                                          0 < s p ∧
                                                            0 < t p ∧
                                                              (A p).transpose = A p ∧
                                                                A p * D p * A p = 1 ∧
                                                                  (∀ (xi eta : ℝ),
                                                                      xi ≠ 0 ∨ eta ≠ 0 →
                                                                        0 <
                                                                          xi * (A p).mulVec ![xi, eta] 0 +
                                                                            eta * (A p).mulVec ![xi, eta] 1) ∧
                                                                    MeasureTheory.IsProbabilityMeasure (nu p) ∧
                                                                      (∀ (i : Fin 2),
                                                                          MeasureTheory.MemLp (fun y => y i) 2 (nu p) ∧
                                                                            ∫ (y : Fin 2 → ℝ), y i ∂nu p = 0) ∧
                                                                        (∀ (i j : Fin 2),
                                                                            ProbabilityTheory.covariance (fun y => y i)
                                                                                (fun y => y j) (nu p) =
                                                                              if i = j then 1 else 0) ∧
                                                                          (∀ᵐ (y : Fin 2 → ℝ) ∂nu p,
                                                                              √(y 0 ^ 2 + y 1 ^ 2) ≤ Q) ∧
                                                                            (∀ (k : ℕ),
                                                                                MeasureTheory.Integrable
                                                                                    (fun y => √(y 0 ^ 2 + y 1 ^ 2) ^ k)
                                                                                    (nu p) ∧
                                                                                  ∫ (y : Fin 2 → ℝ),
                                                                                      √(y 0 ^ 2 + y 1 ^ 2) ^ k ∂nu p ≤
                                                                                    Q ^ k) ∧
                                                                              ∀ (xi eta : ℝ),
                                                                                RA < √(xi ^ 2 + eta ^ 2) →
                                                                                  ‖Phi p xi eta‖ ≤
                                                                                    1 -
                                                                                      cA *
                                                                                        (√(xi ^ 2 + eta ^ 2)).rpow
                                                                                          (-beta)
AXIOMS [propext, Classical.choice, Quot.sound]
```

### 独立盲译：量词、假设、真实对象与结论

1. 输入是任意实数轴上的概率测度 mu、非负实数 M，以及 mu 几乎处处 |x|≤M 的真实有界支撑。没有抽象矩、任意给定协方差或任意给定特征函数作为结论的替身。
2. 对任意紧集 K⊆R²，任意参考倾斜参数 (u0,v0)，以及 beta≥0、c>0、R≥0，假设参考真实倾斜律 mu0=mu.tilted(x↦u0*x+v0*x²) 满足：所有欧氏频率半径 r=sqrt(xi²+eta²)>R 时，其真实 jointCharacteristic 的模≤1-c*r^(-beta)。类型没有要求参考参数属于 K，也没有要求 K 非空。
3. 在全部输入与参考 Cramer 假设之后、任意 p/frequency/k 之前，存在同一个 m，满足 0<m≤1。设 D0 为参考律的 parabolaCovariance；lo=m*det(D0)/tr(D0)，hi=2*(M²+M⁴)+1+lo，c0=m²*c/2。所有后续 raw 谱、测度比较与 raw Cramer 界必须使用这个同一个 m。
4. 对所有参数 p，mup p 是实际指数倾斜律，D p 是其实际 parabolaCovariance。s p=sqrt(D00*D11-D01²)，t p=sqrt(D00+D11+2s)。A p 是类型逐项给定的对称二阶矩阵，分母为 s*t。means p 是实际一阶、二阶积分组成的向量；Y p x=A p*([x,x²]-means p)，nu p 是其真实推前测度，Phi p 是 nu p 上 exp(i*(xi*y0+eta*y1)) 的真实积分。
5. 全局常数 L=1/sqrt(hi)、U=1/sqrt(lo)、Q=4U(M+M²)、cA=c0*U^(-beta)、RA=R/L。结论先断言 lo>0、lo<hi、c0>0、L>0、U>0、Q≥0、cA>0、RA≥0。这些断言在 ∀p∈K 之外；不能仅在 K 有元素时构造它们。
6. 对每个 p∈K，同一 mup p 是概率测度，保留 |x|≤M 的几乎处处支撑，x 和 x² 均属于 L²；同一个 m 还给出 ofReal(m)·mu0≤mup p 的测度序下界。对全部实 xi,eta，D p 的真实二次型同时夹在 lo*(xi²+eta²) 与 hi*(xi²+eta²) 之间。raw jointCharacteristic 在同一个 R、beta 下满足系数 c0 的界。
7. 对相同 p，s,t 严格正，A 对称且 A*D*A=I；对每个非零频率向量 z，z·A*z>0。nu p 为概率律；每个坐标属于 L² 且积分为零；任意两坐标真实 covariance 等于 Kronecker delta。因此结论是实际协方差白化，而非单纯矩阵形式恒等式。
8. nu p 几乎处处的欧氏长度 sqrt(y0²+y1²)≤Q；对每个自然数 k，该长度的 k 次幂真实可积且真实积分≤Q^k。包括 k=0 和 k=9，且没有把 k 作为常数选择的输入。对全部半径大于 RA 的频率，真实 Phi 的模≤1-cA*r^(-beta)。

### 盲审边界与待核点

- K=空集时参数结论真空，但 m 与全局正常数仍须产生；来源若暗用 K 非空将是缺口。
- 参考点不在 K 时也须成立；测度下界不能只比较 K 内相邻点。
- M=0 的输入字面允许，须由强参考 Cramer 前提排除其退化后果，不能暗加 M>0。同样需核 beta=0、R=0 的合法性；不应删去边界来成立。
- 频率零点通常被严格 r>R（R≥0）排除；谱界仍要求包含零频率。A 正定结论独立写出“xi≠0 或 eta≠0”。
- lo 使用 det/trace：需确保参考真实协方差正定、trace>0，且 hi>0 可由 lo>0、非负偶次幂推出。s,t 和分母的严格正性不能凭实数除法全定义而省略。
- raw 弱 Cramer 系数是 c0，白化后的 cA 必须以 c0 而非原始 c 为输入。需核同一 D、means、A、Y、nu、Phi 与同一全局 L/U/Q，避免选择两组不相容的见证。
- 字面“sqrt(两坐标平方和)”是欧氏长度；默认 Pi 范数可能是上确界范数。若证明库在两者间切换，必须有明确比较，不能将它们直接当成同一个范数。
- integral 是 Lean 的真实测度积分；在缺少可积性的上下文中它全定义也可能掩盖问题。需核概率、L²、所有自然幂可积性与矩界确实导出，而非依赖无意义积分值。
- 目前只知名字 parabolaCovariance、jointCharacteristic 与 tilted；其真实定义及导入来源尚未读取。不得仅凭名字接受语义。
- 类型未声称 generic Hessian、均值映射全局逆、无界支撑 B/D 分析或原根 C 已接受。本次结论必须限定于该完整有界紧倾斜族装配。

<!-- END IMMUTABLE BLIND PREFIX -->

## 数学、源码和完整实际类型审查（先于机械证据读取）

本节写成时，尚未读 u21e-receipt/build-history/audit-record/Audit/branch-created/statement-lead-full-read/prerequisite-hashes。已完整读新源码109行、scope81全部93行、root-contract，以及原R2来源38–60、74–76、83–92、343–373；另完整读取两个实际公开生产定理及必要实现，核对真实 covariance/characteristic 定义。未读 u21e-proof-plan、后续B/C notes、作者 scanner/candidate元数据或任何旧statement/proof票正文。

### 精确签名、导入和源码对象

- 新源 SHA256 3d83984f21c03755a7bf018755646a6464157b6eff72bc1555c33aafefcbc642，scope81 SHA256 dbd4392151790ce2a9e86cc84f8fe26fe6e116c84444d79fa31847fb53fd9d99，均实际核对。将源码14–81行末尾的“ := by”去除后，与scope17–84行逐字比较（仅统一行分隔符）完全相同。因此全部前提、let对象、量词和结论未漂移。
- 源1–2行正是冻结的 CovarianceWhitening 与 CompactTiltCovarianceSpectrum 两条 import；4–7行来源段和scope哈希一致；9–12行namespace/open/scoped/noncomputable与scope9行一致。没有额外 import、section变量或新增假设；108–109行正确结束section和namespace。
- 类型原文中的 have/显式全名与源码 let/记号展开相对应：mulVec即*ᵥ，transpose即ᵀ，rpow与sqrt均为Real函数，Measure.map的参数方向为真实源律推前。完整98行实际TYPE逐层核对源码14–81行，唯一公开目标是 Shao.OQ3.exists_compact_tilted_whitened_family；全部module-owner覆盖最终还须由机械枚举绑定，不能从namespace词法猜测。
- RegularCovariance.lean20–24将D定义为 variance(X)、covariance(X,X²)、variance(X²)的真实对称矩阵。JointNonlattice.lean20–24将jointCharacteristic定义为真实∫exp(i(xi*x+eta*x²))；29–35证明相位真实可积。新定理未替换为自由矩阵、自由中心或代理特征函数。

### 新实现109行逐段独立核查

| 新源行 | 核查结果 |
|---|---|
| 1–13 | 两条精确公开导入、说明、namespace、open与section合法且与冻结header一致；没有隐藏前提或证明设置。 |
| 14–22 | 唯一公开theorem。mu概率，hM/hb，K紧，参考u0/v0任意，hbeta/hc/hR和参考真实WC，均按冻结类型保留。 |
| 23–31 | mu0、D0、存在同m与lo/hi/c0/mup/D定义与实际TYPE一致。m在全部参数/频率/自然阶之外。 |
| 32–49 | s/t/A/means/Y/nu/Phi/L/U/Q/cA/RA逐项与169消费者完整let对象匹配；未另选归一化或中心。 |
| 50–64 | 正常数和p∈K后的raw七项按类型原序保留，包括真实概率、AE支撑、两项L²、同m测度下界、共同谱与c0-WC。 |
| 65–81 | 余下全部白化/概率/零均值/L²/identity covariance/欧氏AE支撑/所有自然矩/实际Phi-WC与169的完整结论一致。 |
| 82–86 | 仅一次调用170的exists_compact_tilted_covariance_spectral_bounds。参数依次为mu/M/hM/hb/K/hK/u0/v0/beta/c/R/hc/hWC；170本身不需要hbeta/hR，省略这两项并非删假设。其let mu0/D0与本地82–83行定义展开相同。obtain恰取得m、hm、hm1、hlo、hlohi、hc0、hfamily，未重新选择m。 |
| 87–91 | lo=m*det(D0)/trace(D0)，hi=2*(M²+M⁴)+1+lo，c0=m²*c/2，mup真实倾斜。均为同一170见证的定义别名。 |
| 92–95 | hprob=(hfamily p hp).1；hbound=(hfamily p hp).2.1。真实p概率/AE支撑，无额外类型类全族假设。 |
| 96–99 | hfamily右结合为 P∧B∧L1∧L2∧Dom∧Spec∧Raw。连续五个.2依次越过P、B、L1、L2、Dom，故.2.2.2.2.2.1确为Spec；.2.2.2.2.2.2确为Raw。没有把Dom或某个L²错当谱界。 |
| 100–102 | 仅一次调用169的uniform_covariance_whitened_moments_weakCramer，实例ι=R×R，K与mup原样，M/lo/hi/beta/c0/R原样。实际传入c是c0，而非原c。hM、hlo、lt_trans hlo hlohi、hbeta、hc0、hR、hbound、hspec、hraw逐项满足其签名；lt_trans : 0<lo且lo<hi⇒0<hi完全合法。返回hL/hU/hQ/hcA/hRA/hwhite与本目标常数逐字定义相同。 |
| 103 | 返回的唯一存在见证仍为m；原hm/hm1/hlo/hlohi/hc0和169的五个常数结论依次填满全局前缀。 |
| 104–106 | 对任意p∈K，hpProb/hpBound/hp1/hp2/hpDom/hpSpec/hpRaw恰为170的完整七项。最后八元tuple的第八项hwhite p hp被用作整个右结合余尾，从s>0一直到最终Phi界；它不是仅填一个末端原子。169完整结论327–345与新源65–81完全对应，故不存在被遗漏的白化、矩或特征函数结论。 |
| 107–109 | 仅空行与结束标记，无其他公开/私有定义或额外推理。 |

### 两个已接受producer接口与真正数学内容

170的完整公开类型见CompactTiltCovarianceSpectrum.lean182–214。其195行先给lo>0、lo<hi、c0>0，再给196–214的全族七项。必要实现215–245先以有界指数可积性得到参考与各参数真实概率、通过绝对连续继承AE支撑与L²；223–235以参考WC排除协方差零方向，取得det>0、trace>0并产生全局正lo。228–229只选择一次紧倾斜m。后续246–282用同m的measure lower比较真实方差，并用det/trace的二维恒等式导出同lo谱下界和共同hi上界。因此新模块没有把“全族谱”重新作为外来假设。

169的完整公开类型见CovarianceWhitening.lean291–345，尤其其lambdaMin=lo、lambdaMax=hi、c=c0替换后全部let对象与本模块一致。29–210的二维谱计算给出严格s/t、显式对称正矩阵A、A D A=I与L*r≤|Aᵀz|₂≤U*r。212–289用实际中心、真实推前和真实可积坐标证明零均值及 covariance=A D Aᵀ。382–491只从原M界、谱与WC推导五个统一常数、实际白化概率、坐标L²、identity covariance、欧氏支撑与所有自然矩，未输入目标结论。407–409的仿射WC传递使用同一族、A、实际means及频率双边界，未将默认Pi范数误认成欧氏范数。

具体欧氏审查：169的hfrequency与hrow是sqrt(两个坐标平方和)；439–448从它推出单项|Aij|≤U。450–472先逐坐标给|Yi|≤2U(M+M²)，再使用显式引理sqrt(y0²+y1²)≤|y0|+|y1|取得Q=4U(M+M²)。473–489将AE界沿真实map送到nu，并逐自然k使用pow_le_pow_left₀、Integrable.of_bound和概率积分界。故没有与默认Pi上确界范数混用，也没有把总化积分的0值伪装成矩存在性。

### 边界和量词攻击结果

- K空与参考不在K：170/169签名均无Nonempty或参考成员假设。实际必要构造CompactTiltDomination.lean15–28只由紧集上连续实函数取有界量max C 0，允许空集；30–45对任意参考u0/v0仍构造exp(-2B)>0，38–41的比较不要求参考在K。全局lo来自参考真实WC而不来自从K抽一个p。因此不发生真空参数族下无法选常数的问题。
- M=0：源没有暗加M>0。参考WC⇒所有非零方向方差>0的170前置证明99–180只用hc>0、真实L²及足够大的频率；若|X|≤0，它与variance(X)=0矛盾。此退化输入由已有WC前提排除，不是新定理漏掉一个允许实例。
- beta=0：rpow(U,-beta)=1且U>0，无除零或严格beta要求。R=0给RA=0，hR的非负形式全程保留。无论某些组合前提本身不可满足，新证明没有用额外beta>0或R>0。
- 零频率：raw/white WC只在严格半径>R/RA且R/RA≥0时使用，故不强求0处严格小于1；谱界则对全部xi/eta包括0有效。正定陈述显式排除零向量。
- 自然k=0：169的完整∀k证明对0同样可积并有积分≤Q^0=1，与nu概率相符；k=9直接实例化得到统一九阶绝对矩，可供delta=1的有界8+delta场景。未声称非整数矩已在此形式化。
- 全部m/lo/hi/c0/L/U/Q/cA/RA先于p/frequency/k选择；measurelower、raw谱、rawWC、whiteWC沿同m传递，且beta不变。没有参数联合可测性要求，也未在实现中悄悄引入。

### 原来源忠实性和范围

R2:38–60定义W=(X,X²)、真实倾斜及协方差/统一谱/标准化8+delta矩；74–76明确有界情形应自动产生统一矩与单点WC稳定性；83–92指定D^(-1/2)(W-mean)与相位、频率比较；343–369要求紧倾斜共同密度下界及m²c/2，371–373限制无界推广。新定理完整装配了这些有界紧倾斜标准化输入，并给出实际正对称白化和明确共同常数。它没有把“标准化族结论”作为输入，也没有只交付有限标量恒等式。

该结果不证明generic Hessian=actual covariance、均值映射逆、外部Song/Edgeworth、胞重建、Laplace或远概率链，不处理无界B分析或D十六原子/小x鞍点。原C最终冻结范围须由root另行验收；即使本模块数学及机械证据通过，也不能据此自行关闭C，更不能关闭B/D。原A已关闭范围仍仅修正vCorr/fixed x0。scope3行的v42/待v43是冻结时历史状态，当前正式继承v43由行政记录另绑定，不构成数学前提变更。

数学/源码/实际TYPE阶段结论：未发现关键缺口；证明是完整且精确的170→169组合。下一阶段仅核现有服务器机械证据与精确源码、全部actual-owner和公理的绑定。

## 现有服务器机械证据与精确工件绑定

本节是在上述数学、源码、全部实际TYPE审查完成并落盘之后，才读取指定机械记录写成；没有把作者receipt的语义叙述作为独立证明依据，也未读旧审查票正文。

### 新模块检查历史

- u21e-receipt.json 实际SHA256 0c1a631d6d990769de20944571f8d9d66623104431b057fc56197a0e8df54aba，与任务冻结值相同。它绑定同一109行/5716字节源码3d83984f21c03755a7bf018755646a6464157b6eff72bc1555c33aafefcbc642、同一93行/8682字节scope、同一98行/7626字节actual types。记录状态为作者完整通过、待fresh独立完整证明审查，没有把作者门当成独立票。
- 完整读取u21e-build-history.json：仅1项attempt=1，scope_complete=true、public_target_count=1、目标完整。2026-10-23T03:39:30.805568Z开始，exit0，6.068451201543212秒，日志0字节，SHA256 e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855，COMPLETE_SUCCESS。该新源没有已记录失败、partial success、成功后重跑或通过后改写；history实际SHA256 737df635f2e83e598974ccf5d33d90edaf212210a0624755fd7a393c6ddead4a与receipt相同。
- u21e-audit-record.json与receipt.audit逐项相符：2026-10-23T03:40:14.290180Z，exit0，5.495365500450134秒，审计对象仍是同一源码；Audit源SHA256 413abc428821b721df6471390c3fab6d25dcf92ccc90c88b97e27214764d408f，Audit输出SHA256 ba9d2dacb452953518f9590cd90035b9eb0a11ce584bde9fab52dd1c9467bb33、7740字节。此为首轮actual module-owner审计。没有复制或读取完整服务器rawlog。
- 构建与Audit均记录server CPU14–17、native memory8192MiB、j4、autoImplicit=false。所复用正式版本为leanprover/lean4:v4.36.0-rc1及mathlib807d3836b165983210ee2ecf3cd28f239436949c；未探测或使用本地Lean，也未请求安装、cache get、lake update或重建旧依赖。

### 全部actual module-owner和传递公理

已完整读u21e-Audit.lean，不仅检查文本namespace：它遍历env.constants，对每个常量用env.getModuleIdxFor?查env.header.moduleNames，只有真实所属模块Shao.OQ3.CompactTiltWhitenedFamily才进入审计。它对所有所属项拒绝isAxiom，并逐项Lean.collectAxioms，仅允许propext、Classical.choice、Quot.sound；每个实际所属项均输出完整DECL/TYPE/AXIOMS。独立目标检查强制冻结名字存在且isTheorem，targetCount==1；它另输出allCount/theoremCount，因此没有以“冻结名单有一项”替代整个实际所属集合。

首轮保存结果报告all_owned=1、all_theorems=1、public_theorems=1、public_definitions=0、private_theorems=0、generated_theorems=0；完整actual-types恰有该一项并输出标准三公理，与全源只有一个theorem、无辅助定义的逐行检查一致。因而本次审查覆盖100%的新actual module-owner及其全部TYPE，而非只抽查公开目标或按namespace猜测。每项的collectAxioms是传递收集，故两个已接受producer之后的证明依赖也在本目标传递公理闭包中受白名单约束。

Audit的两个set_option仅pp.deepTerms=true、pp.maxSteps=1000000，均为类型打印选项；没有改变内核、证明搜索可信度或数学前提。新源完整109行不存在sorry/admit/新axiom/unsafe/native_decide/implemented_by，亦无证明设置弱化。

### 正式v43继承、21项小header依赖字典与分支

- library/verification/receipt-v43.json实际SHA256 f46d66ddb73098bca1c3aa5a730372585105242dddab7c94515ea626879ebb60，version=v43/status=PASS，版本钉锁与标准三公理明确相同。正式行政接受记录coordination/integration-v43/merged.json绑定accepted_head=d80ba2a19fca34aa6e5dd765d6091900fe0c09c4、main=529aa59983f566fe38ca9d41f59b29f1bec4163f、同tree=0c08fa33511931678c7187754b6bb2926358cafc，并记录PR169/170内容经171整合且作者分支保留。根已明确允许正式继承，故不重做seed作者门或全库验收。
- 诚实区分元数据：v43 receipt中的code_commit=5b37f2d1ed10edc15c458ec9d0da8d36484ac028、code_tree=5879a74c653718383581151cb63d0d10f78891ce是其门执行记录；不把它们误写成最终accepted_head/tree。正式最终对象由merged.json、TEAM/REGISTRY和新分支记录绑定；实际数学依赖通过同一正式receipt的source_files_sha256/frozen_sources_sha256逐项绑定。v43历史另保留一次纯diff-check换行问题及已成功Lean日志复用；这不是U21e新源失败或重新编译，也未将这段历史删除或冒称整合从未有任何失败。
- 完整读取u21e-prerequisite-hashes.json：21项全部路径与值逐项等于正式v43.source_files_sha256，差异列表为空。文件SHA256 4d1f229c55124378e0f2e18f07831026a687316e559894c8af5f8f6af9244190；无空格canonical compact JSON的SHA256实际重算为a23be394287b75cdd2e89756d5c92ab081067e669c7286d4022c5a2f3bb15448，与receipt一致。两个直接seed源码哈希分别为169:d1f90abf2ecd59032dc5f934dbedbe9c3ab9e468f73b0d4f40b24b4a7851eec8、170:99b8b9b20f1860ddd7890d8b4d317825ce76572e1c0d209d6843340a33b0c634。比较的是正式字典，不是重新hash旧稳定源码或对象；未扫描全Mathlib图。
- u21e-branch-created.json记录新branch feat/oq3-compact-tilt-whitened-family从上述正式accepted head/同tree产生，无merge/rebase/reset；实际保存79个旧owned refs，计数已核，两个正式seed .olean仅一次确认已存在。本模块尚无新commit或PR；本票没有冒称已发布或整合。
- u21e-statement-lead-full-read.json仅用于时序和角色绑定：它记录fresh声明审查者与全文202行/23411字节最终声明审查已由lead完整读取，正式v43 notice已收到且开始生产源前通过。此处未读取旧声明票正文，未复用其数学判断。本独立审查自身已从实际TYPE先行盲译、再审完整实现。

新记录辅助哈希：audit-record=45c5ddc4c11765f0d74dbedc4f7a8e6b4a2886fa0997b8c90b2cb47930d6569e；branch-created=e25084b13f485b87cfa3af45386917e6700682da39325b1e1b311b57cf69492c；statement-lead-full-read=9a26265be0eea6a85f6adb1491e926e45ccd0ce744a670ad64aa86249f0b110a。这些是本次轻量本地记录校验，不是额外Lean门。

## 最终独立裁决

STATUS: CORRECT

JUSTIFICATION: 新实际模块全部109行、全部1项actual module-owner完整TYPE及其传递公理均已覆盖。冻结公开签名与header逐字相符；一次170调用给出的同m同时控制真实measurelower/lo/c0/共同谱/rawWC，五次.2投影的位置准确；一次169调用以相同族、相同真实D/means/A/Y/nu/Phi和c0消费它，0<hi由0<lo<hi合法推出，最后hwhite p hp恰是完整余下合取。概率、L²、真实积分、Euclidean sqrt的所有自然矩与统一WC均忠实于有界源范围，所列退化边界未被暗删。精确新源的首次完整严格server检查与首次actual-owner/collectAxioms门已有exit0证据，唯一传递公理为标准三项；21项前置源字典严格继承正式v43，未把kernel通过替代源语义审查。未发现关键证明、声明或现有证据绑定缺口。

接受范围：仅本新模块完整证明与现有server证据CORRECT，仍待root按原C最终冻结范围接受。B/D及generic Hessian、均值逆、无界B分析保持OPEN；A仅已接受修正vCorr/fixed x0范围。本票不作原根关闭、最优性、端点或新颖性声明。

权限与执行：本实例使用math-theorem，不用math-ultra；不spawn、不跨线程发送消息。唯一写入为本报告；其余操作仅本地轻量读取和新工件/记录哈希核对。未改source/scope/旧票/receipt/status/inventory/REGISTRY/TEAM/cache/pins，未访问C:/game/shao历史写权限，未执行远程命令、Lean/Audit/probe、工具链探测或重复成功门，未复制rawlogs，未触碰外部CPU0–9/80GiB任务。

不可改写盲前缀长度12307字节，SHA256 3638d9d6f6ddd2bd884844dde022d835af132d31646c11de0969a8d0b2465308。该前缀原始字节在各次追加前后均须保持相同；最终整份报告的行数、字节数和SHA256由稳定后读取给出，避免自引用哈希。
