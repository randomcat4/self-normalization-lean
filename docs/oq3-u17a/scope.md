# OQ3-U17a：有限伯努利指数试验与真实energy矩母函数比较

冻结v1，DECLARATION_REVIEW_QUEUED_INDEPENDENT_AFTER_U16J_DECLARATION；尚未批准或实现。拟Shao/OQ3/EnergyBernoulliMGF.lean。imports Shao.OQ3.SourceBinaryEntropyGap、Shao.OQ3.InverseTilt、Mathlib.Analysis.Convex.SpecificFunctions.Basic；namespace Shao.OQ3，open MeasureTheory，noncomputable section。零新公开定义、两个完整公开目标。依赖均为已接受旧模块，数学上独立于I/J；唯一reviewer优先I完整终票和J声明，在J作者实施期间可审本独立声明，不能并发占用第二reviewer。批准前不写本源/Leanprobe，不改变任何已冻结源。

来源 current/oq3/proofs/r1/report.md SHA3473d34ff20bd0d334b9ef3ea3c3ee167fba4d5cc3a742849820ce54d639e662，161–237二元熵充分gap及386–389远区控制。原源通过一般KL/随机Markov kernel证明唯一全局最小；本单元只准备R1远区加权概率的充分标量矩母函数路线，不冒称证明了source(9)/(10)、实际KL数据处理或任意rho的唯一全局鞍点。后续若以该路线闭合远区须另冻真实iid、样本几何和compact finitecover目标，当前不含这些。

```lean
theorem exists_binary_exponential_test (p z L : ℝ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hz0 : 0 < z) (hz1 : z < 1)
    (hL : L < binaryRelativeEntropy p z) :
    ∃ theta : ℝ, 0 < 1 - z + z * Real.exp theta ∧
      L < theta * p - Real.log (1 - z + z * Real.exp theta)

theorem bounded_energy_logMGF_le_bernoulli (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (hb : ∀ᵐ x ∂mu, |x| ≤ 4 + Real.sqrt 10) (q H t : ℝ) (hH : 0 < H)
    (henergy : ∀ᵐ x ∂mu, 1 ≤ x ^ 2 ∧ x ^ 2 ≤ 1 + H)
    (hsecond : (∫ x : ℝ, x ^ 2 ∂mu) = q) :
    Integrable (fun x : ℝ => Real.exp (t * (x ^ 2 - q))) mu ∧
      0 < (∫ x : ℝ, Real.exp (t * (x ^ 2 - q)) ∂mu) ∧
      Real.log (∫ x : ℝ, Real.exp (t * (x ^ 2 - q)) ∂mu) ≤
        -t * (q - 1) + Real.log
          (1 - (q - 1) / H + ((q - 1) / H) * Real.exp (t * H))
```

第一目标p in[0,1]、z in(0,1)、L严格小于已接受真实纯实binaryRelativeEntropy。要求存在有限实theta，并明确该真实二点指数normalizer严格正、测试值严格大于L。p0/p1必须保留，不要求L正/非负，也不把endpoint极限的无穷theta当有限见证。不定义任意新率，不把纯实binaryRelativeEntropy重命名成actual KL；它已使用0*log0的连续端点约定，实际完整定义与旧接受语义须核。

内部0<p<1可取alpha=p/z>0、beta=(1-p)/(1-z)>0、theta=log alpha-log beta。exp theta=alpha/beta，1-z+z exp theta=(1-z)/(1-p)=1/beta>0；正参数下log分解及环等式给测试值恰binaryRelativeEntropy，故hL给严格性。先证alpha/beta/normalizer正及分母非零才log/exp抵消，不从Real.log总化取值推概率。

p0端点binaryD=-log(1-z)，hL给Delta=exp(-L)-(1-z)>0。取theta=log(Delta/(2*z))，所有log参数/分母正；normalizer=1-z+Delta/2<exp(-L)且>0，严格log单调后得到测试值=-lognormalizer>L。p1端点binaryD=-log z，Delta=exp(-L)-z>0，令u=Delta/(2*(1-z))>0、theta=-log u。实际B(theta)*exp(-theta)=z+(1-z)*u=z+Delta/2 in(0,exp(-L))，于是theta-log B=-log(B*exp(-theta))>L。两端禁止套内部log(p)公式，不需极限/DCT或KL新缓存。

第二目标真实mu概率、hb一般AE固定有界、H>0以及真实AE 1<=x²<=1+H和actual二阶矩=q；q/t任意实参数，t正负/零均保留。真实假设实际蕴含1<=q<=1+H，但不能不经积分就凭名字用z=(q-1)/H in[0,1]。H只是任意给定真实bound，不在本单元偷换成sourceH；来源专化H=25+8sqrt10及mean q要后续另证。先用InverseTilt已公开integrable_continuous_of_fixed_bounds和exp多项式连续给任意固定t的真exp Integrable，mu概率/NeZero给真实Z>0。不可积时Bochner=0、log0或top.toReal都不能当normalizer。

设u(x)=(x²-1)/H，真实henergy/H>0给AE 0<=u<=1。Real.convexOn_exp.2应用点0和theta=tH、权重1-u/u（非负且和1），给exp(theta*u)<=(1-u)+u exp(theta)，所有theta实包括负数。由H非零环恒等式theta*u=t*(x²-1)，exp(t(x²-q))=exp(-t(q-1))*exp(t(x²-1))。右侧线性u函数也先由hb连续/多项式可积建立真Integrable，再在真实AE支持上积分单调。mu概率与hsecond、x²/常数/除H真可积给∫u=(q-1)/H，得到actualZ<=exp(-t(q-1))*B，其中B是冻结类型的真实两点normalizer。

取log前必须真证B>0：可以先合法推出z in[0,1]再证凸组合严格正，或利用actualZ>0和上界使expfactor*B>0，expfactor>0推出B>0。两条都不能借负数或0的log总化。随后严格正域log单调、log乘法、log(exp)给完整结论；H正确保所有/H非零，q/t不被当分母。t0时Z=1、B=1、log界等号，μ退化在x²常数也保留；无需实际正variance或非原子性。

静态已读 Mathlib/Analysis/Convex/SpecificFunctions/Basic.lean40–63和其236–237同类convexOn_exp.2用法，现成olean有；InverseTilt26–34的public一般连续可积接口已在H完整接受。具体全部实际API/import闭包/现成olean仍由本独立门核，不用Lean/#check探针。后续实际proof必须先完整public type盲译持久化，再source/完整proof/private/actual所有TYPE，最后receipt/build/Audit/pins。作者不写cache，不复制root公共源码。

未来数值仅供来源定位：actualsourceEll=log(31/30)<1/30（已接受sourceEll_lt_one_div_thirty），绝非等于1/30。实际source 1<q<103/100给7/200-sourceEll*q>1/1500，搭配已接受U14b binary gap可为每个远R产生finite energy test。compact finitecover和真实iid归一化尚未冻结于本单元，不能把该作者规划作为当前输出已证明。full17/19/LLT/hW/globalfar/source3一般KL/所有根ABCD仍OPEN，无Legendre最优/最弱/最优/新颖性主张。不cachewrite/rebase/merge。
