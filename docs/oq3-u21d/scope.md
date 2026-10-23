# U21d 冻结：实际紧倾斜族的共同协方差谱

状态：FROZEN_FOR_INDEPENDENT_STATEMENT_REVIEW。U21c完整327行CORRECT终票已lead全文读并核168行盲前缀，PR169精确发布/附chat，head c06e026254837782a706bcde0b8c7218c7f71eb4，0DEF2公开定理真实白化/矩/WC完成，待root整合。当前169branch clean；本单元无source/probe/Audit/newbranch/build。

来源：R2 report.md38–60实际谱(2)、74–76有界版本无隐藏一致前提、83–92实际标准化、343–369有界紧倾斜稳定性。R2 SHA572e74aa9c12e2771f5543a5709a2807666eeea0a4076e7a3263e5c7bcf87f55。root-contract§5原C已由159完成同m测度下界/平方缺口和原始WC；169完成给定实际谱后的白化/真实矩/WC。本单元消除实际compact tilt统一谱这一承重前提，随后还须与169真实装配，root决定原C闭合，B/D仍OPEN。

模块Shao.OQ3.CompactTiltCovarianceSpectrum，0公开DEF/2公开THM；namespace Shao.OQ3，open MeasureTheory，open scoped Matrix ENNReal NNReal，noncomputable section。精确imports：

```lean
import Shao.OQ3.CompactTiltWeakCramer
import Shao.OQ3.RegularCovariance
```

完整TYPE（不得静默加强假设）：

```lean
theorem parabolaCovariance_pos_of_weakCramer
    (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (M : ℝ) (hM : 0 ≤ M) (hb : ∀ᵐ x ∂mu, |x| ≤ M)
    (beta c R : ℝ) (hc : 0 < c)
    (hWC : ∀ xi eta : ℝ, R < Real.sqrt (xi ^ 2 + eta ^ 2) →
      ‖jointCharacteristic mu xi eta‖ ≤
        1 - c * Real.rpow (Real.sqrt (xi ^ 2 + eta ^ 2)) (-beta)) :
    0 < parabolaCovariance mu 0 0 ∧
      0 < parabolaCovariance mu 1 1 ∧
      0 < (parabolaCovariance mu).det ∧
      ∀ xi eta : ℝ, xi ≠ 0 ∨ eta ≠ 0 →
        0 < xi ^ 2 * parabolaCovariance mu 0 0 +
          2 * xi * eta * parabolaCovariance mu 0 1 +
          eta ^ 2 * parabolaCovariance mu 1 1

theorem exists_compact_tilted_covariance_spectral_bounds
    (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (M : ℝ) (hM : 0 ≤ M) (hb : ∀ᵐ x ∂mu, |x| ≤ M)
    (K : Set (ℝ × ℝ)) (hK : IsCompact K)
    (u0 v0 beta c R : ℝ) (hc : 0 < c)
    (hWC : ∀ xi eta : ℝ, R < Real.sqrt (xi ^ 2 + eta ^ 2) →
      ‖jointCharacteristic (mu.tilted (fun x => u0 * x + v0 * x ^ 2)) xi eta‖ ≤
        1 - c * Real.rpow (Real.sqrt (xi ^ 2 + eta ^ 2)) (-beta)) :
    let mu0 : Measure ℝ := mu.tilted (fun x => u0 * x + v0 * x ^ 2)
    let D0 : Matrix (Fin 2) (Fin 2) ℝ := parabolaCovariance mu0
    ∃ m : ℝ, 0 < m ∧ m ≤ 1 ∧
      let lambdaMin : ℝ := m * D0.det / (D0 0 0 + D0 1 1)
      let lambdaMax : ℝ := 2 * (M ^ 2 + M ^ 4) + 1 + lambdaMin
      0 < lambdaMin ∧ lambdaMin < lambdaMax ∧ 0 < m ^ 2 * c / 2 ∧
        ∀ p ∈ K,
          let mup : Measure ℝ := mu.tilted (fun x => p.1 * x + p.2 * x ^ 2)
          IsProbabilityMeasure mup ∧ (∀ᵐ x ∂mup, |x| ≤ M) ∧
            MemLp (fun x : ℝ => x) 2 mup ∧
            MemLp (fun x : ℝ => x ^ 2) 2 mup ∧
            (ENNReal.ofReal m • mu0 ≤ mup) ∧
            (∀ xi eta : ℝ,
              lambdaMin * (xi ^ 2 + eta ^ 2) ≤
                  xi ^ 2 * parabolaCovariance mup 0 0 +
                    2 * xi * eta * parabolaCovariance mup 0 1 +
                    eta ^ 2 * parabolaCovariance mup 1 1 ∧
                xi ^ 2 * parabolaCovariance mup 0 0 +
                    2 * xi * eta * parabolaCovariance mup 0 1 +
                    eta ^ 2 * parabolaCovariance mup 1 1 ≤
                  lambdaMax * (xi ^ 2 + eta ^ 2)) ∧
            ∀ xi eta : ℝ, R < Real.sqrt (xi ^ 2 + eta ^ 2) →
              ‖jointCharacteristic mup xi eta‖ ≤
                1 - (m ^ 2 * c / 2) *
                  Real.rpow (Real.sqrt (xi ^ 2 + eta ^ 2)) (-beta)
```

真实对象/门：D与D0为既有actual covariance，不是任意矩阵。全部概率/L²/支持为同mu的真实quadratic tilt产生，tilted_absolutelyContinuous.ae_le传递AE界；isProbabilityMeasure_tilted使用已接受quadratic_exp_integrable_of_ae_abs_le。不存在caller谱/atom正性/共同正定下界/协方差连续性或紧集非空假设；K可以空，M=0不从语法删去。beta/R任意实，正半径的rpow对任意指数严格正，所以正定步骤不需beta/R符号；后来消费169时仍诚实保留它所需beta≥0,R≥0。

正定路线：真MemLp2的f=xi*x+eta*x²，其实际variance用variance_fun_add/variance_const_mul/真实covariance线性给出字面二次型。若variance0，公开ae_eq_integral_of_variance_eq_zero得f为真实均值常数AE。任意正倍数T频率的jointPhase因此为同一单位模复指数，真概率积分的特征函数模=1。非零频率rho>0，取T=(|R|+1)/rho>0，实际新半径|R|+1>R，代入c>0及正半径rpow>0矛盾。非负variance故严格正；于e0/e1得a,d>0，于(-b,a)得delta=ad-b²>0；Matrix.det_fin_two与实际对称性绑定det。没有把非格点或非共振直接等同弱Cramér，也没有使用总化的不可积variance0。

共同下界路线：159给同一个m>0≤1及ofReal m•mu0≤mup。对任意真L² f，令z=实际E_mup f，则非负中心平方在mup真可积，Bochner integral_mono_measure传递积分，integral_smul_measure给m系数；在mu0展开实际中心平方积分=Var_mu0 f+(E_mu0 f-z)²≥Var_mu0 f。故Var_mup f≥m Var_mu0 f，不误用variance对measure无条件单调。对D0=[[a,b],[b,d]]，trace>0、delta>0，精确恒等式

(trace)*q_D0(xi,eta)-delta*(xi²+eta²)=(a*xi+b*eta)²+(b*xi+d*eta)²≥0

给q_D0≥(det/trace)*(xi²+eta²)。于是同m产生冻结lambdaMin=m*det/trace>0，所有分母先正后除法。

共同上界：真variance_eq_sub给Var_mup f≤integral f²；AE |x|≤M得f²≤2(M²+M⁴)(xi²+eta²)，真Integrable与概率把常数界积分。lambdaMax=2(M²+M⁴)+1+lambdaMin全局严格大于lambdaMin且正，无需从K非空抽取一个p。m、D0、lambdaMin/lambdaMax、M/beta/c/R均在p/频率/n外同一固定；WC仍为159的同m²c/2与同beta/R。159平方缺口已接受，不在本单元重复公开计数。

承重/剩余：本节点真实生产compact tilted covariance spectral(2)，直接consumer为169的uniform_covariance_whitened_moments_weakCramer，随后新装配冻结完整有界C输入输出。当前不import待整合169，避免新单元依赖未整合跨支源；root整合后再装配。没有宣称本单元单独关闭C，也不声称一般unbounded B、Hessian=cov/meaninverse、Edgeworth/胞重建/Laplace/显式远概率或D已完成。A正式v40 CLOSED；beta<2/5仍仅充分，不声称最优。

环境：两seed均已完整作者首成功及root正式接受闭图；18项目headerDFS字典来自正式v42 source_files_sha256，canonical e03503582ed63f55f9629bcbea056930e068049a2ad4df885c6399bee290659a。once18actualShao对象全存在，普通Lake own单Shao根；无全Mathlib重扫/重计、旧稳定源/cache重hash、新pin/smoke或缓存复制。pinned公开Variance162零方差AE、Variance272真L²加法、BochnerBasic621积分随测度单调均按真实源码定向读过。

执行：整份CORRECT声明终票lead全读核hash后，才从正式v42 accepted 7832c37251145161d095daac02e3506db90b3910正常新建feat/oq3-compact-tilt-covariance-spectrum，计划PRbase main；169与全部78旧owned refs保持。root独占merge/rebase/retarget/common/cache/pins。全部Lean仅serverCPU14–17/native8192MiB/j4/autoImplicitfalse/oneheavy，完整失败留史，首成功不重复；首次module-owner全部实际TYPE/公理覆盖private/generated后，再独立完整proof终票全读才接受提交发布。std3白名单，禁止sorry/admit/newaxiom/unsafe/native_decide/implemented_by/证明设置弱化。复用sole reviewer lease1，不新agent/chat/goal；外部CPU0–9/80GiB不动。
