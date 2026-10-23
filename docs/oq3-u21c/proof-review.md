# U21c CovarianceWhitening 完整独立证明审查

STATUS: IN_PROGRESS

本段为不可改写先行盲审前缀。先且只读取全部实际 owner TYPE 选块 u21c-actual-types.txt 的完整121行；尚未读取当前 proof source、作者收据／日志或证明叙述。已有声明审查上下文存在，本次不把它或作者 PASS 当作实际证明成立的依据。

## 全部六项实际TYPE原文

```text
DECL Shao.OQ3.uniform_covariance_whitened_moments_weakCramer
TYPE ∀ {ι : Type u_1} (K : Set ι) (mu : ι → MeasureTheory.Measure ℝ),
  (∀ p ∈ K, MeasureTheory.IsProbabilityMeasure (mu p)) →
    ∀ (M lambdaMin lambdaMax beta c R : ℝ),
      0 ≤ M →
        0 < lambdaMin →
          0 < lambdaMax →
            0 ≤ beta →
              0 < c →
                0 ≤ R →
                  (∀ p ∈ K, ∀ᵐ (x : ℝ) ∂mu p, |x| ≤ M) →
                    (∀ p ∈ K,
                        ∀ (xi eta : ℝ),
                          lambdaMin * (xi ^ 2 + eta ^ 2) ≤
                              xi ^ 2 * Shao.OQ3.parabolaCovariance (mu p) 0 0 +
                                  2 * xi * eta * Shao.OQ3.parabolaCovariance (mu p) 0 1 +
                                eta ^ 2 * Shao.OQ3.parabolaCovariance (mu p) 1 1 ∧
                            xi ^ 2 * Shao.OQ3.parabolaCovariance (mu p) 0 0 +
                                  2 * xi * eta * Shao.OQ3.parabolaCovariance (mu p) 0 1 +
                                eta ^ 2 * Shao.OQ3.parabolaCovariance (mu p) 1 1 ≤
                              lambdaMax * (xi ^ 2 + eta ^ 2)) →
                      (∀ p ∈ K,
                          ∀ (xi eta : ℝ),
                            R < √(xi ^ 2 + eta ^ 2) →
                              ‖Shao.OQ3.jointCharacteristic (mu p) xi eta‖ ≤
                                1 - c * (√(xi ^ 2 + eta ^ 2)).rpow (-beta)) →
                        have D := fun p => Shao.OQ3.parabolaCovariance (mu p);
                        have s := fun p => √(D p 0 0 * D p 1 1 - D p 0 1 ^ 2);
                        have t := fun p => √(D p 0 0 + D p 1 1 + 2 * s p);
                        have A := fun p =>
                          ![![(D p 1 1 + s p) / (s p * t p), -D p 0 1 / (s p * t p)],
                            ![-D p 0 1 / (s p * t p), (D p 0 0 + s p) / (s p * t p)]];
                        have m := fun p => ![∫ (x : ℝ), x ∂mu p, ∫ (x : ℝ), x ^ 2 ∂mu p];
                        have Y := fun p x => (A p).mulVec (![x, x ^ 2] - m p);
                        have nu := fun p => MeasureTheory.Measure.map (Y p) (mu p);
                        have Phi := fun p xi eta =>
                          ∫ (y : Fin 2 → ℝ), Complex.exp (↑(xi * y 0 + eta * y 1) * Complex.I) ∂nu p;
                        have L := 1 / √lambdaMax;
                        have U := 1 / √lambdaMin;
                        have Q := 4 * U * (M + M ^ 2);
                        have cA := c * U.rpow (-beta);
                        have RA := R / L;
                        0 < L ∧
                          0 < U ∧
                            0 ≤ Q ∧
                              0 < cA ∧
                                0 ≤ RA ∧
                                  ∀ p ∈ K,
                                    0 < s p ∧
                                      0 < t p ∧
                                        (A p).transpose = A p ∧
                                          A p * D p * A p = 1 ∧
                                            (∀ (xi eta : ℝ),
                                                xi ≠ 0 ∨ eta ≠ 0 →
                                                  0 <
                                                    xi * (A p).mulVec ![xi, eta] 0 + eta * (A p).mulVec ![xi, eta] 1) ∧
                                              MeasureTheory.IsProbabilityMeasure (nu p) ∧
                                                (∀ (i : Fin 2),
                                                    MeasureTheory.MemLp (fun y => y i) 2 (nu p) ∧
                                                      ∫ (y : Fin 2 → ℝ), y i ∂nu p = 0) ∧
                                                  (∀ (i j : Fin 2),
                                                      ProbabilityTheory.covariance (fun y => y i) (fun y => y j)
                                                          (nu p) =
                                                        if i = j then 1 else 0) ∧
                                                    (∀ᵐ (y : Fin 2 → ℝ) ∂nu p, √(y 0 ^ 2 + y 1 ^ 2) ≤ Q) ∧
                                                      (∀ (k : ℕ),
                                                          MeasureTheory.Integrable (fun y => √(y 0 ^ 2 + y 1 ^ 2) ^ k)
                                                              (nu p) ∧
                                                            ∫ (y : Fin 2 → ℝ), √(y 0 ^ 2 + y 1 ^ 2) ^ k ∂nu p ≤ Q ^ k) ∧
                                                        ∀ (xi eta : ℝ),
                                                          RA < √(xi ^ 2 + eta ^ 2) →
                                                            ‖Phi p xi eta‖ ≤ 1 - cA * (√(xi ^ 2 + eta ^ 2)).rpow (-beta)

DECL _private.Shao.OQ3.CovarianceWhitening.0.Shao.OQ3.whitening_spectral_data
TYPE ∀ (D : Matrix (Fin 2) (Fin 2) ℝ),
  D 1 0 = D 0 1 →
    ∀ (lo hi : ℝ),
      0 < lo →
        0 < hi →
          (∀ (xi eta : ℝ),
              lo * (xi ^ 2 + eta ^ 2) ≤ xi ^ 2 * D 0 0 + 2 * xi * eta * D 0 1 + eta ^ 2 * D 1 1 ∧
                xi ^ 2 * D 0 0 + 2 * xi * eta * D 0 1 + eta ^ 2 * D 1 1 ≤ hi * (xi ^ 2 + eta ^ 2)) →
            have s := √(D 0 0 * D 1 1 - D 0 1 ^ 2);
            have t := √(D 0 0 + D 1 1 + 2 * s);
            have A := ![![(D 1 1 + s) / (s * t), -D 0 1 / (s * t)], ![-D 0 1 / (s * t), (D 0 0 + s) / (s * t)]];
            0 < s ∧
              0 < t ∧
                A.transpose = A ∧
                  A * D * A = 1 ∧
                    (∀ (xi eta : ℝ), xi ≠ 0 ∨ eta ≠ 0 → 0 < xi * A.mulVec ![xi, eta] 0 + eta * A.mulVec ![xi, eta] 1) ∧
                      ∀ (xi eta : ℝ),
                        1 / √hi * √(xi ^ 2 + eta ^ 2) ≤
                            √((xi * A 0 0 + eta * A 1 0) ^ 2 + (xi * A 0 1 + eta * A 1 1) ^ 2) ∧
                          √((xi * A 0 0 + eta * A 1 0) ^ 2 + (xi * A 0 1 + eta * A 1 1) ^ 2) ≤
                            1 / √lo * √(xi ^ 2 + eta ^ 2)

DECL Shao.OQ3.centered_affine_parabola_mean_covariance
TYPE ∀ (mu : MeasureTheory.Measure ℝ) [MeasureTheory.IsProbabilityMeasure mu],
  MeasureTheory.MemLp (fun x => x) 2 mu →
    MeasureTheory.MemLp (fun x => x ^ 2) 2 mu →
      ∀ (A : Matrix (Fin 2) (Fin 2) ℝ),
        have m := ![∫ (x : ℝ), x ∂mu, ∫ (x : ℝ), x ^ 2 ∂mu];
        have Y := fun x => A.mulVec (![x, x ^ 2] - m);
        have nu := MeasureTheory.Measure.map Y mu;
        MeasureTheory.IsProbabilityMeasure nu ∧
          (∀ (i : Fin 2), MeasureTheory.MemLp (fun y => y i) 2 nu ∧ ∫ (y : Fin 2 → ℝ), y i ∂nu = 0) ∧
            ∀ (i j : Fin 2),
              ProbabilityTheory.covariance (fun y => y i) (fun y => y j) nu =
                (A * Shao.OQ3.parabolaCovariance mu * A.transpose) i j

DECL _private.Shao.OQ3.CovarianceWhitening.0.Shao.OQ3.whitening_map_continuous
TYPE ∀ (A : Matrix (Fin 2) (Fin 2) ℝ) (m : Fin 2 → ℝ), Continuous fun x => A.mulVec (![x, x ^ 2] - m)

DECL Shao.OQ3.parabolaCovariance.eq_1
TYPE ∀ (mu : MeasureTheory.Measure ℝ),
  Shao.OQ3.parabolaCovariance mu =
    ![![ProbabilityTheory.variance (fun x => x) mu, ProbabilityTheory.covariance (fun x => x) (fun x => x ^ 2) mu],
      ![ProbabilityTheory.covariance (fun x => x) (fun x => x ^ 2) mu, ProbabilityTheory.variance (fun x => x ^ 2) mu]]

DECL _private.Shao.OQ3.CovarianceWhitening.0.Shao.OQ3.euclidean_radius_le_abs
TYPE ∀ (x y : ℝ), √(x ^ 2 + y ^ 2) ≤ |x| + |y|
```

## 独立量词／假设／输出／原义务盲译

1. 选块列出六项 theorem，未列出 owner definition；两public、三private及一条旧定义名下生成等式的分类须结合随后实际源和module-owner Audit最终核，不凭名称前缀猜。
2. public centered_affine_parabola_mean_covariance：固定同一实概率mu，输入X和X²各真MemLp2，对任意实2×2矩阵A成立。
3. m=(∫X,∫X²)为同mu真均值，Y=A((X,X²)−m)，nu=mu.mapY；没有自由中心或另一律。
4. 结论为nu真概率、每个坐标真L²且均值0、所有实际协方差逐项等于A*parabolaCovariance(mu)*Aᵀ。
5. 第一public无非退化／A可逆／原子正性输入；必须保留退化mu及奇异A，不能借第二public谱门补前提。
6. 真L²须先支持积分线性和乘积可积；covariance_map、坐标MemLp推送及中心消除的真实可测与可积门须随后核。
7. public uniform_covariance_whitened_moments_weakCramer：对任意Type u_1、集合K及族mu，只在p∈K给真概率。
8. M、lo=lambdaMin、hi=lambdaMax、beta、c、R在全部p/frequency/k之前固定，M/beta/R非负，lo/hi/c严格正。
9. hbound给每p∈K同M的实际AE |X|≤M；hspec对实际D=parabolaCovariance(mu p)的二维二次型给共同lo/hi上下界；原始rawWC同族同c/beta/R。
10. D/s/t/A/m/Y/nu/Phi全部由这些输入明确let固定，不存在按结论重选白化矩阵／law／center。
11. s=sqrt(D00D11−D01²)，t=sqrt(D00+D11+2s)，A=[[D11+s,−D01],[−D01,D00+s]]/(s*t)。
12. 结论必须真正生产s/t>0、A对称、ADA=I与全部非零u的u·Au>0；白化恒等式本身不足以排除负白化矩阵。
13. L=1/sqrt(hi)、U=1/sqrt(lo)、Q=4U(M+M²)、cA=cU^(−beta)、RA=R/L，为固定显式数值。
14. 全局交付L/U/cA>0、Q/RA≥0，然后对全部p∈K交付正白化和同nu实际概率／坐标L²／均值0／协方差I。
15. 对同nu给真AE欧氏半径sqrt(y0²+y1²)≤Q；不是Pi最大值范数、不是只对源x的尚未推送陈述。
16. 对每个自然k给实际rho^k真Integrable及真积分≤Q^k，k0及Q0不可被非法约分抹掉。
17. 最后给真实Phi在RA外的WC，同beta和同cA，不能只输出任意代理函数族。
18. hspec是诚实输入；任意A/hfreq不再是public输入，必须由实际D的显式正白化生产全频率比较后消费已接受U21b。
19. private whitening_spectral_data：对任意实2×2矩阵D输入D10=D01、lo/hi>0及全部实频率二次型双界。
20. 其s/t/A与public公式相同，输出s/t>0、Aᵀ=A、ADA=I、u·Au>0及全部频率(1/sqrt hi)*rho≤rho(Aᵀu)≤(1/sqrt lo)*rho。
21. 该private不是actualcovariance自动生产者；public必须把真实parabolaCovariance、它的真实对称性和实际hspec交给此helper，不能另取手工矩阵。
22. private whitening_map_continuous：任意A和任意中心m下，x↦A((x,x²)−m)实际Continuous，不假设A可逆或mu性质。
23. private euclidean_radius_le_abs：任意实x/y的sqrt(x²+y²)≤|x|+|y|；须在随后真实AE/矩推导中正确使用，不能变成NormPi身份。
24. generated Shao.OQ3.parabolaCovariance.eq_1虽名称来自旧定义namespace，但本次actualowner选块已包括它，须核完整类型／传递公理，不排除。
25. 它对任意mu只给实际parabolaCovariance等于[[VarX,Cov(X,X²)],[Cov(X,X²),VarX²]]的完整定义等式，不提供概率／真有限方差／正定性。
26. generated定义等式不取代真L²和可积门；D的有限矩意义必须在public上下文独立落实。
27. 原source义务是实际协方差白化、零均值／单位协方差、标准化全阶矩和WC指数保持，不是抽象caller矩阵包装。
28. 重点疑点：分母真正性是否先于field/sqrt约分；NDN系数和positiveA是否真证；频率dot身份的transpose与上下界方向是否正确。
29. 重点疑点：实际mean界是否基于同mu真积分，AE支持是否按可测map正确方向转移，真Integrable是否先于积分单调及矩上界。
30. K空、M0、beta0、R0、零频率和k0都应保留。p不参与积分，不能偷加参数拓扑／联合可测性。
31. 本类型不输出actualtilt共同谱、Hessian=covariance或均值逆；不由这些helpers单独关闭完整C/B。
32. A已正式v40关闭；B/C/D仍OPEN。当前proof结论须独立于该行政状态与旧声明CORRECT。

--- END IMMUTABLE BLIND PREFIX ---

## 来源、冻结声明与本次审查范围

以下是在全部六项实际 owner TYPE 已先行盲译落盘之后形成。依次读取完整495行实现、scope79、实际原来源与固定库实现／公开API，独立完成数学判断，然后才读取作者receipt、首Audit和构建历史。没有读作者future/implementation/candidate/scanner笔记或以其说明替代数学。
实际R2 report.md冻结SHA为572e74aa9c12e2771f5543a5709a2807666eeea0a4076e7a3263e5c7bcf87f55；本门核38–60、83–92、343–373。它明确把实际谱(2)作为输入，使用真实Y=Delta^(-1/2)(W−m)，并要求统一矩及保持beta的标准化WC。
本实现的第二public真实消除“自由A／手工hfreq”的旧门，但仍诚实输入实际parabolaCovariance的共同谱。它不是compact-tilt共同谱、一般Hessian/covariance或均值逆的生产者，也不是完整C/B定理。
两个完整实际公开签名经独立抽取，与103行scope79的完整fence逐白空归一化匹配为true；三个imports和Matrix/BigOperators header未变。原冻结scope0952e68e...、已接受242行声明票及其126行前缀未改写。

## 全495行证明的逐义审查

### 三个私有helper：连续性、欧氏半径和真实谱数据

source12–21 在本模块内重新证明任意A/m下x↦A((x,x²)−m)连续；continuous_pi后逐行change为Fin2有限和，20–21化成两个实多项式组合。没有跨模块调用U21b私有连续性，也未要求A可逆、m是均值或任何测度门。
source23–27 的 euclidean_radius_le_abs 对任意实x/y成立。先给sqrt与|x|+|y|的非负性，再以sq_le_sq₀转平方，Real.sq_sqrt使用x²+y²≥0，最后以|x||y|≥0、sq_abs完成。它是真欧氏半径不等式，未把Pi默认max-norm叫作欧氏范数。

#### whitening_spectral_data的假设与真正分母门：29–87

29–51 的私有完整类型以任意实对称2×2 D和真实全频率lo/hi双界为输入；不输入det>0、s/t非零、A正定或任何白化结论。
52–61 的a/b/d/delta/s/t/den/N/A仅为公开公式的精确别名；其中N=[[d+s,−b],[−b,a+s]]、A=N/den、den=s*t。负号与条目均没有交换。
62–69 将谱下界用于(1,0)/(0,1)，真得a>0、d>0。
70–78 将它用于(−b,a)；hnorm证明b²+a²>0，再以lo>0得a*delta>0。mul_pos_iff的负分支被a>0消去，故真正delta>0，而非只从不完整det符号断言正定。
79–84 在delta>0和a+d+2s>0之后才得到s/t>0、s²=delta、t²=a+d+2s以及den≠0。后面的所有field_simp／逆消去都晚于这些证据。
85–87 用输入hsym把实际任意D的四个分量展开成[[a,b],[b,d]]；不假定某种外部Matrix.Symmetric instance，也不将只看上三角的二次型错误用于非对称D。

#### 精确有限代数和A正性：88–154

88–109 对NDN的四条分量逐项给出可独立展开的多项式恒等式。对角项被写为(s²−delta)、(t²−a−d−2s)的倍数加(st)²；两个非对角项都是b*(s²−delta)。代入已证hs2/ht2，精确得到对角(st)²、非对角0。
例如00分量直接等于a*s²+delta*(d+2s)，由s²=delta及t²=a+d+2s化为s²*t²；没有漏掉s、t或2的因子。
110–119 用Fin2全四项展开得到真实矩阵NDN=(st)²•I；不是仅证明trace/determinant相等就当作矩阵相等。
120–123 逐项给A=den⁻¹•N；124–126 逐项给Aᵀ=A。127以den≠0证明den⁻¹*den⁻¹*den²=1，128–133的Matrix.smul_mul/mul_smul及hN真实推出ADA=I。
134–154 单独处理A正定，没有把ADA=I当作足够条件。非零u=(xi,eta)先给xi²+eta²>0；旋转频率(−eta,xi)的谱下界给a*eta²−2b*xi*eta+d*xi²>0。
146–152 明确将u·Au写成[s*(xi²+eta²)+上述正二次型]/den；field_simp使用先前hden，153–154再用正分子与s*t>0得严格正。故没有选到负白化矩阵或依赖奇异逆总化。

#### 实际转置二次型与全频率sqrt比较：155–210

155–167 令v=Aᵀu，使用实际dotProduct_transpose_mulVec与mulVec_mulVec，把v·Dv变成u·A D Aᵀu；Aᵀ=A、ADA=I后等于u·u。
实际Matrix/Mul.lean1133–1135的原型确为x·Aᵀy=y·Ax，source160–161先用dotProduct_comm再用该身份，转置方向正确；不是把A D A与AᵀD A混同。
162–167 将已建立的真实D矩阵和Fin2坐标展开，得到q_D(v)=xi²+eta²，交叉项确为2*b*v0*v1。
176–179 又分别证明v0=xi*A00+eta*A10、v1=xi*A01+eta*A11，正是U21b所需Aᵀ频率坐标。
180–187 将完整上下谱界实例化于同v，并使用hquad；188–193证明r/rA的非负平方身份和sqrt(lo/hi)严格正。
194–201 在两侧非负后用sq_le_sq₀，得到r≤sqrt(hi)*rA及sqrt(lo)*rA≤r。
202–209仅除真正正的sqrt(hi/lo)，得到(1/sqrt hi)*r≤rA≤(1/sqrt lo)*r；210按实际坐标还原。没有除r/rA，所以这个私有结论包含零频率而非仅非零方向。
lo≤hi没有被全局偷加；空K应用只需要各自正性。泛型helper的D/hsym假设稍后必须由真实covariance完整填入，不能将其单独计为源模型结论。

### 第一public真实居中像律：212–289

212–226完整签名只给同mu真概率、实际X和X²的MemLp2及任意A；并未用第二public的谱门来强化第一目标。
227–237固定同mu积分的m、同Y/nu以及W/Z。hW逐Fin2消费h1/h2；hZ由真L²减有限测度下的常数L²建立。两个hmi是实际积分的定义等式。
238–241的hZmean先明确使用(hW i).integrable和integrable_const，再用integral_sub与真概率的常数积分得零。没有以未证明可积的积分线性或总化0制造均值。
242–250把实际Y坐标精确写成A的两项中心化函数和；显式函数hadd解决函数加法与逐点和的差异，两个.const_mul与.add真实给坐标L²。
251–254给Y连续、每个目标坐标连续，并以Measure.isProbabilityMeasure_map_iff的真实AEMeasurable证据建立nu概率。未借不可测map的兜底Dirac分支。
255–259在去掉中心前给对应hW的真L¹，满足实际Covariance.lean208–220 covariance_sub_const_left/right前提。
260–267覆盖全部四个坐标组合：两个对角通过Variance.lean197–201 covariance_self，两个交叉分别为定义和covariance_comm。D10=D01的实际定义与交叉反序一致。
此时hW/hZ/hYlp已先产生真L²；方差与协方差的乘积／居中平方积分有限，不能因为covariance_self原型仅需AEMeasurable就误称这里省略了真实有限性。
271–274以连续坐标的AE强可测与Y的AE可测调用实际memLp_map_measure_iff，将hYlp真L²推到同nu。
275–280在实际integral_map后，两个.const_mul的L²降L¹先满足integral_add，再提出常数并用hZmean，逐坐标交付nu真实均值0。
281–285的covariance_map_fun接收两个目标坐标的AE强可测和Y的AE可测；随后covariance_fun_sum_fun_sum明确接收两族每项真MemLp2，不是无条件拆开不可积协方差。
286–289先提出两侧真实标量、使用hZcov，再展开矩阵乘法／transpose，四项为Ai0*Aj0*D00+Ai0*Aj1*D01+Ai1*Aj0*D10+Ai1*Aj1*D11。结果精确是(A D Aᵀ)ij。
第一public因此对退化mu、奇异/零A仍成立；它没有引用旧RegularCovariance要求4+sqrt10界的专用正性定理来处理任意mu。

### 第二public的真实D／固定全局数据／WC消费：291–428

291–345完整类型与冻结一致；346–381的局部D/s/t/A/m/Y/nu/Phi/L/U/Q/cA/RA只是相同公开let别名，没有重新选择law、中心或矩阵。
382–385在全部p之前先证明L/U>0和Q≥0，分别由两lambda真sqrt正性及M≥0。没有从K抽取非空元素。
386–397把实际D p=parabolaCovariance(mu p)及其定义性D10=D01交给本模块spectral helper，并完整消费hspec p hp。这里的hdata不是任意caller矩阵包装。
398–406真实生产U21b所需的全部p／全部频率hfreq；它不是第二public的caller输入。407–409只调用一次已完整独立接受的U21b公开uniform_weakCramer_of_affine_frequency_bounds，用同K/mu/A/m/L/U/beta/c/R、hprob、刚产hfreq及实际hWC，获得同一cA/RA及同Phi的htrans。
410再固定所有全局常数，然后411才intro任意p∈K。hdata只作真实矩阵代数，不需要先对积分作运算；实际矩的有限意义在下面由同p的hbound完整建立，再使用第一public及单位cov。
412–421先局部建立真mu概率，再以MemLp.of_bound得到X真L²；abs_pow与真|X|≤M给|X²|≤M²，并再给X²真L²。未误用仅atomicMeasure版或旧固定支撑版可积定理。
422调用本模块第一public，交付同实际A/m/Y/nu的概率／均值与协方差。423装入nu真概率实例；424–428才将真实hcov=A D Aᵀ以hsym/hwhite改写到Matrix.one_apply，输出完整实际单位covariance。
虽然hdata在建立L²之前已做纯有限矩阵代数，它使用的是明示hspec；并未在那一步操纵任何未证有限积分。实际协方差／方差语义在hcov之前已有真实L²，顺序无总化漏洞。

### 真实均值、AE欧氏支持与全部自然阶积分：429–491

429–434用同mu真概率与两个实际AE界，经norm_integral_le_of_norm_le_const得到|m0|≤M、|m1|≤M²；hx/hx2真L²已独立建立，所以这些均值并非不可积时的总化替代。
435–438以已生产频率上界在e0/e1上实例化，得到A每行的真实欧氏长度≤U。439–448先平方非负的行半径及U，再由各条目平方≤行平方和得到全部|Aij|≤U。没有暗用Pi max-norm或遗漏转置导致行列混淆。
449重新使用本模块真实Y连续性。450–455在同源AE事件内取得|X−m0|≤2M、|X²−m1|≤2M²，没有将AE界当成所有x全点界。
456–465完整展开Yi两项，使用abs_add_le和两项明确abs_mul恒等式；两个乘积各自都正确取绝对值，01/02失败处的表达式修复未改变该数学命题。
466–469用hentry、hcenter及所需非负因子给|Yi|≤2U(M+M²)。470–472的欧氏helper与两个hYi真实给rho(Y)≤4U(M+M²)=Q，因子4足够且无漏sqrt2。
473–476用连续rho的可测次水平集及Y的真实AEMeasurable，通过ae_map_iff的.mpr将源AE界推向实际nu；方向是正确的源→像，不是只有ae_of_ae_map的逆方向。
477–484对任意自然k，先用sqrt非负和hsupport给真实范数bound ‖rho^k‖≤Q^k。
485独立交付Integrable.of_bound，真nu概率保证有限质量；487–489再用实际norm_integral_le_of_norm_le_const得到|∫rho^k|≤Q^k，并以积分≤绝对值完成目标。虽然这个norm API本身可在总化积分下表述，source已另外给出了真Integrable，并非借其默认0冒充矩有限。
这里没有使用integral_mono却漏掉可积门；实际走的是更强的范数积分界，真可积结论仍在同一个hmom中完整提供。
k=0时rho^0=Q^0=1，真实概率积分1，含Q0边界；k=9真实给有界标准化应用的8+1阶矩，不代表一般无界情形已完成。
490–491汇总同p的正白化、真实nu、hmeans/hunit、真hsupport/hmom及同一htrans p hp的模界；并未另选特征函数族或应用另一个中心。
493/495只正常关闭section/namespace，没有新的公共定义或设置改变。

## 真实固定库API与边界核验

实际Covariance.lean113–127、294–297要求协方差加法／双有限和各项MemLp2，并在内部用居中L²乘积可积；source236、244–250、284–285已给全前提。
208–220去常数需要对应Integrable；source258–259实际给足。309–320的map API需要目标坐标AE强可测及Y AE可测；source282–283明确填入连续坐标／连续Y。
实际Variance.lean197–201把自协方差与Var联系；结合本source先证真L²，两个对角是实际有限方差，不将evariance.toReal的总化当作矩。
实际LpSeminorm/Basic.lean631–633 MemLp.of_bound、1031–1033 memLp_map_measure_iff的有限测度／AE强可测／map可测门在source414–421、273–274分别满足。
实际Map.lean249–251 ae_map_iff需要可测目标谓词，source475–476真实生产；实际Bochner/Basic.lean1002–1006给有限测度常数范数积分界，source中两个真概率实例均在此前建立，mu/nu.real univ化为1合法。
Matrix/Mul.lean1133–1135真实转置dotProduct原型已独立核对；source159–167用其正确方向。所有标量inverse和sqrt跨乘只在s/t或lambda正平方根非零后；全频率比较没有除频率半径。
源码没有新增caller实际白化/频率比较，没有跨模块privatehelper调用，没有新covariance/概率/统计量定义。
K空时所有p内结论真空，L/U/Q/cA/RA仍全局真实交付；没有Nonempty K提取。M0从不作分母，非空族时它与严格谱的不相容不造成非法约分。beta0/R0在U21b真实公开生产者中保留，零频率在hfreq中完整包含。
参数p没有拓扑／可测空间要求，证明不对p积分；同一组常数始终在p、k、频率之外固定。任意原均值允许，实际中心在所有像律、矩、WC步骤里保持一致。

## 全部六项actual owner TYPE与传递公理

先行前缀完整保存actual-types.txt的121行／7681字节及全部let／universe／长hprob/hspec/hWC延续。数学完成后再从实际audit.log选取全部六个DECL/TYPE/AXIOMS区块，逐项核到全部续行；未下载原始完整日志。

| 实际常量 | 全类型语义及source对应 | 实际传递公理 |
|---|---|---|
| Shao.OQ3.uniform_covariance_whitened_moments_weakCramer | public；完整Type u_1族、真实bound/hspec/WC、所有明确let、正白化／同nu矩与WC；291–491 | propext, Classical.choice, Quot.sound |
| _private.Shao.OQ3.CovarianceWhitening.0.Shao.OQ3.whitening_spectral_data | private；D10=D01、lo/hi>0、全频率二次型双界，输出明确s/t/A及正性/白化/频率双界；29–210 | propext, Classical.choice, Quot.sound |
| Shao.OQ3.centered_affine_parabola_mean_covariance | public；真概率与X/X²真L²、任意A，输出同nu实际均值／协方差；212–289 | propext, Classical.choice, Quot.sound |
| _private.Shao.OQ3.CovarianceWhitening.0.Shao.OQ3.whitening_map_continuous | private；任意A/m下实际有限Pi统计量连续；12–21 | propext, Classical.choice, Quot.sound |
| Shao.OQ3.parabolaCovariance.eq_1 | generated；任意mu下完整定义等式，四项Var/Cov原文均保存，不提供概率／有限性／正定性；由本模块对旧定义的展开生成 | propext, Classical.choice, Quot.sound |
| _private.Shao.OQ3.CovarianceWhitening.0.Shao.OQ3.euclidean_radius_le_abs | private；∀x/y:Real，sqrt(x²+y²)≤|x|+|y|，无隐藏非负输入；23–27 | propext, Classical.choice, Quot.sound |

Audit.lean实际以env.getModuleIdxFor?取真正owner，并对env.constants逐项精确比较Shao.OQ3.CovarianceWhitening，不按namespace或旧定义文件猜所属。故parabolaCovariance.eq_1虽名称在旧定义namespace，仍完整计入本模块generated theorem，没有遗漏也没有误当新publicDEF。
actualowner共6THM=2public+3authoredprivate+1generated；0DEF。完整source只有五个手写theorem，和这六项owner联验覆盖全部locals/private/generated义务。所有六项实际都是标准三公理；没有新axiom、sorryAx或白名单外传递公理。
打印选项pp.deepTerms/maxSteps仅用于完整TYPE输出，不改证明语义。Audit的PASS是上述机械事实证据，独立数学成立的理由是前文实际逐行／API核验。

## 数学与TYPE完成后才读取的机械绑定

冻结scope79为103行／9256字节／0952e68e7cc354ebc1e6fd379f68caf8a27fd75b52ed9865dbac4576caecbfc8；本门未改其任何字节。两个实际公开完整签名逐白空归一化匹配为true；三个imports/header未变。
当前完整source本地draft、remote ownworktree与run/source-03.lean同为495行／24907字节，SHA d1f90abf2ecd59032dc5f934dbedbe9c3ab9e468f73b0d4f40b24b4a7851eec8。
源码独立声明扫描为3private THM加2public THM；禁止token（sorry/admit/axiom/unsafe/native_decide/implemented_by/set_option）扫描为空，符合完整逐行阅读；owner Audit进一步覆盖generated。

| 新冻结证据 | 行／字节 | SHA256 |
|---|---:|---|
| actual-types.txt（两端一致） | 121／7681 | ea9e1e1f4713e5937b4e36dab2ea6dfb19fe9d9fd457fa1237d277620b522855 |
| Audit.lean | 45／1943 | 64383ec3d306c68f7fcfb1bf30b7922479c9170877d826ff57c93964c737990f |
| audit.log（真实小写文件名） | 127／8072 | d5d7e6f486eb59c7a03f57caa15a37b6853c9be8d458f6050b296ec85bf25943 |
| receipt.json | 240／10468 | fbead0b13fe38468fa7bb5343c791611267f7629bddcc8747c27e2abc11bdff8 |
| prerequisite-hashes.json | 13／1143 | aaaad80ba1e961e554949b54c622dbfcc7f95784fa1dda8928f0c2451e1ebf5c |
| build-history.json | 83／2281 | 6465324308ff88983ffd489001dca916ff72fb2276a1b5fa8d666375f379ee09 |
| preflight-history.json | 10／425 | 33a385a20e46863152b19eff29d4c341de9e41412cda397a3f73e60dd189c71a |
| source-01.lean | 482／24469 | 5e5dcdef8915c6e619c77eaacc9236c8fd4d690c0b2caea7ef71bdd90b59307d |
| source-02.lean | 493／24816 | a507b2d8f72680fd59e759ec784458025e6f44bf279c8f5dba2e272366705e78 |
| source-03.lean | 495／24907 | d1f90abf2ecd59032dc5f934dbedbe9c3ab9e468f73b0d4f40b24b4a7851eec8 |
| build-01.log | 513／21615 | e6822361eca390947319899c6c3ebd5be00900797f405e7dca9331a575cadcdd |
| build-02.log | 28／1521 | 22e66a41aa078b7e1f7ddeddba6cf7801048e85ced834d0c04b26ba10fdefbe8 |
| build-03.log | 22／1102 | 0025579dcc9925eb65e19dd71dd4f03f73c5718f829992d0cb0d3cd0af2030fa |

历史首项是独立preflight guard：CRLF scope的fence splitter假设LF，失败于Lean/source snapshot之前。行政记录明确没有生成snapshot/log或启动kernel；修复仅在校验原scope字节hash后做内存解析换行归一化，不是scope／TYPE／假设变化，不能记为完整build失败或成功。
三次actual source记录均为完整两目标，不是partial。01 exit1／14.084212秒，错误选块涉及有限函数／矩阵scalar reducibility、相应不等式表达式及abs_add旧identifier；02 exit1／15.693808秒，只剩abs_mul两项化简的类型匹配问题；03为当前源首次完整成功，exit0／15.623900秒。
独立02→03 snapshot diff只将该绝对值估计改成hh加两个显式typed abs_mul重写，数学恒等式及全部公开输入不变；未弱化proofsetting或跳过任一目标。
03日志非空1102字节，四条实际style warnings：152行unused/unnecessary `<;>`各一条、412/423各一个letI实例写法建议；0error。不能写空日志／零warning，也不能把历史01/02失败隐去。
首次actualmodule-owner Audit exit0／5.417973秒；footer为0frozenDEF、2frozenTHM、6allTHM、6allDECL、PASS。没有重跑成功source/Audit，没有partial成功或探针。
记录实际CPU14–17／原生8192MiB／j4／autoImplicit=false；没有ulimit-v或资源弱化。审查者只静态轻量读取，未运行Lean/Audit/build/probe、改cache/pins或触及外部CPU0–9/80GiB。
正式11源字典紧凑canonical SHA为1218f35137fd25486e259b6a192747642d68edbfeadc63fa44fcbb0b0b45f59a，和本审查声明阶段从RootA74正式字典加完整接受166源独立复现的同一map一致；父166现也已被root正式v42整合接受。
沿用已完成的公开图／once12对象存在性／pins证据，未重扫全Mathlib、重哈希旧稳定源和对象或重复smoke。actual Covariance/Variance/Lp/Map API本次只按必要条目读验，没有再做构建门。
实际branch feat/oq3-covariance-whitening，HEADb3362fcb26bda08f5027ef3118ad6c759f0f5138，status仅?? Shao/OQ3/CovarianceWhitening.lean；没有本模块commit/PR。正常child分支以冻结166为parent与root后来v42整合不冲突，没有reset／merge／rebase／retarget。
所有旧source/scope/statement/proof票/receipt/metadata/shared/cache/pins及frozenhead均未改动。作者receipt的状态仍为PENDING_FULL_INDEPENDENT_PROOF，本独立票不是对其数学字段照抄。

## 最终完整独立裁决

STATUS: CORRECT
REVIEW: COMPLETE INDEPENDENT PROOF / SOURCE / ALL6 ACTUAL OWNER TYPES / EXISTING MECHANICAL EVIDENCE。
JUSTIFICATION: 完整495行源真实建立分母正性后精确正对称白化，真实生产全频率谱比较并消费一次同律U21b；第一public在真L²/概率门下建立同nu实际均值与ADAᵀ协方差，第二public从真实bounded门生成L²、单位cov、欧氏AE支持及每个自然阶真积分。完整实际六类型、全部private和旧namespace下generated均覆盖，实际传递公理白名单和首次成功历史绑定一致，没有实质缺口。

原来源→本节点已消除→直接consumer→仍缺：R2(2)、86–92／368标准化→给定实际谱时的明确正对称白化、同nu零均值／单位cov／统一欧氏全阶矩及同beta WC→真实紧倾斜族WC与标准化输入装配→仍须从具体紧倾斜族生产共同实际谱并与159组合，落实相关Hessian/covariance／均值逆和原B的其余分析；本节点不单独关闭C/B/D。
这里不再把“给定谱后的白化／矩／频率比较”列成未完成，它们已经本模块真实证明；未消去的hspec是诚实公开源前提。泛型helper单独不能冒充实际tilt谱生产者。
根A正式v40 CLOSED_INTEGRATED_KERNEL_CHECKED；父166正式v42接受；B/C/D仍OPEN。未据本proof终票提前记为作者commit/发布或最终rootC装配接受。

不可改写盲前缀仍168行／12505字节，SHA f12f8b39b8939b0801c7a21f0fabcf3673b60e6e2cdff7c59dfb665fd95490b6；追加后已按原字节复核完整保留。
