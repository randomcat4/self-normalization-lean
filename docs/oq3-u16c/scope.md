# OQ3-U16c：三次局部余项下的负层加权代价余量

冻结v2，DECLARATION_REVIEW_QUEUED，尚未批准或实现。拟Shao/OQ3/LocalRateMargin.lean；imports Mathlib.Basic.Real.Basic、Mathlib.Tactic.FieldSimp、Ring、Positivity、Linarith、NormNum。namespace Shao.OQ3、noncomputable section。一个公开定义、一个公开目标。

来源R1 report.md SHA3473d34ff20bd0d334b9ef3ea3c3ee167fba4d5cc3a742849820ce54d639e662，361–383：局部二次率加三次余项、kappa²/2>ell、曲尾r²≥nqk/16推出nI−ell*k≥gamma*k+c*r²/n。本单元只证明这一确定性的数值余量步骤；真实Legendre率的展开、矩阵Hessian绑定、紧倾斜族统一Chernoff及远区间隙仍未证明。

```lean
def gaussianRateProfile (S T b y z : ℝ) : ℝ :=
  y ^ 2 / (2 * S) + (z - b * y) ^ 2 / (2 * T)

theorem exists_cubic_rate_weight_margin (q ell S T b D radius : ℝ)
    (hq : 0 < q) (hell : 0 ≤ ell) (hS : 0 < S) (hT : 0 < T)
    (hD : 0 ≤ D) (hradius : 0 < radius) (hgap : ell < q / (32 * T))
    (I : ℝ → ℝ → ℝ)
    (hI : ∀ y z : ℝ, |y| + |z| ≤ radius →
      gaussianRateProfile S T b y z - D * (|y| + |z|) ^ 3 ≤ I y z) :
    ∃ delta gamma c : ℝ, 0 < delta ∧ 0 < gamma ∧ 0 < c ∧
      ∀ n : ℕ, 1 ≤ n → ∀ k r : ℝ, 0 ≤ k →
        k / (n : ℝ) ≤ delta → |r| / (n : ℝ) ≤ delta →
          (n : ℝ) * q * k / 16 ≤ r ^ 2 →
            gamma * k + c * r ^ 2 / (n : ℝ) ≤
              (n : ℝ) * I (-k / (n : ℝ)) (r / (n : ℝ)) - ell * k
```

公开定义是明确的二次剖面，S/T/b是固定实标量；只有定理的S,T>0门下才作逆协方差型代价解释。它不定义实际Legendre变换或声称任意I是概率率。来源中的实例应为S=Var(Y)>0、T=Var(X)−Cov(Y,X)²/S>0、b=Cov(Y,X)/S；此时二次剖面是(Y,X)高斯二次型，kappa²/2=q/(32T)，hgap正是原严格间隙。把这些实际协方差和真实I下界接到该定理仍是后续解析义务，不在本单元偷偷假定完成。

hI是明确的原点邻域三次下界，弱于完整Taylor等式但强于仅二阶点态导数；不能用未量化O符号替代。D≥0允许D0，b任意带符号；ell≥0允许ell0；q,S,T,radius均真>0。见证delta/gamma/c在全部n/k/r之前固定。k是任意非负实层深度，不缩成整数；r可正负，k0/r0合法；n≥1保证所有除n真合法，不将n0的总化结果当作极限。

数学路线（未实现）：令A=1/(2T)、d0=16/q、B=|b|/T、gap=A−ell*d0。由hgap及q,T>0得gap>0。对任意y,z，正S/T及展开平方给真实剖面下界 Q≥A*z²−B*|y*z|，其中交叉项用|b*y*z|控制，舍去的y²与b²y²项均非负，不能丢交叉项或当b≥0。

令E=B*d0+4D*(d0+1)≥0，选

`delta=min 1 (min (radius/2) (gap/(2*(E+1))))>0`，

保证delta≤1、2delta≤radius、delta*E≤gap/2（分母E+1>0，不除E0）。选c=gap/4>0、gamma=gap/(4*d0)>0。

对n≥1置u=k/n≥0、v=|r|/n≥0、w=r²/n≥0。曲尾约束给u≤d0*v²及k≤d0*w；小邻域给u,v≤delta。于是|−k/n|+|r/n|=u+v≤2delta≤radius，先合法消费hI，不能省略邻域门。

交叉误差n*u*v≤d0*delta*w。三次误差先由(u+v)²≤2(u²+v²)，再用u+v≤2delta、u²≤delta*u≤delta*d0*v²和delta≤1，得

`n*(u+v)^3≤4*delta*(d0+1)*w`。

乘D/B非负后，真实nI≥(A−delta*E)*w；减ell*k时必须用ell≥0与k≤d0*w，故nI−ell*k≥(gap−deltaE)*w≥gap/2*w。最后gamma*k+c*w≤gap/2*w，得到目标。所有正分母和乘法方向均须在实现中明确，不能把q或n符号默认正。

本候选纯实数标准充分比较，不需新Mathlib缓存或项目公共源码；只读已核Basic.Real.Basic及五个tactic缓存真实存在。唯一reviewer仍须先盲译完整定义体与完整类型，再source/API/数学门审查；批准前不实现。当前U16b完整审查中，lead全文读完最终票后再派本声明门。非最弱/最优或新颖性结论。

它不证明实际I为Legendre率、不证明其Taylor界/协方差Hessian绑定、紧倾斜族质量常数、局部Chernoff(16)、真实负层概率(17)或远区exp尾；不能据此标负层支配、完整LLT、hW或根完成。根ABCD全部OPEN。


v2环境修订记录：v1 scope SHA9f660ea048c1b2a89ea4ce7f983ef60d8f631561fd52e7c3612bb538979f4133及其声明票e75a5553346aea1a2e272a2cad0af8f94b05e14d0ef52b84f79b85233f97672a完整保留。该票只读发现Data.Real.Basic是public import Basic.Real.Basic并带deprecated_module的兼容入口。v2唯一实质修订是显式导入规范Mathlib.Basic.Real.Basic；公开定义完整体/完整目标签名与v1去空白逐字相同。规范模块源hash f15de163c14198d9b60aeb8ac845b4540c198bbb2e80d6153d0dbc8a6c08936f及olean已由v1票实际核对。lead全文读完v1票后冻结本v2，仍须唯一reviewer完整类型/体盲译及环境修订审查批准前才实现。v1没有实施或Lean检查，不存在借更名改数学假设。
