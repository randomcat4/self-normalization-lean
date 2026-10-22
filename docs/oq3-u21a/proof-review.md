# U21a CompactTiltWeakCramer 完整独立证明审查

STATUS: IN_PROGRESS

## 不可改写 actual TYPE 盲审前缀

先仅从当前实际source提取完整公开类型，尚未读本次94行证明体、actual TYPE／Audit输出或作者receipt。
此前声明正确后暂存的历史存在，但不替代本次独立proof审查。0公开DEF／1公开合取THM如下。

```lean
theorem exists_compact_tilted_weakCramer_bound (mu : Measure ℝ)
    [IsProbabilityMeasure mu] (M : ℝ) (hM : 0 ≤ M)
    (hb : ∀ᵐ x ∂mu, |x| ≤ M) (K : Set (ℝ × ℝ)) (hK : IsCompact K)
    (u0 v0 beta c R : ℝ) (hc : 0 < c)
    (hWC : ∀ xi eta : ℝ, R < Real.sqrt (xi ^ 2 + eta ^ 2) →
      ‖jointCharacteristic (mu.tilted (fun x => u0 * x + v0 * x ^ 2)) xi eta‖ ≤
        1 - c * Real.rpow (Real.sqrt (xi ^ 2 + eta ^ 2)) (-beta)) :
    let mu0 : Measure ℝ := mu.tilted (fun x => u0 * x + v0 * x ^ 2)
    ∃ m : ℝ, 0 < m ∧ m ≤ 1 ∧ 0 < m ^ 2 * c / 2 ∧
      ∀ p ∈ K,
        (ENNReal.ofReal m • mu0 ≤
          mu.tilted (fun x => p.1 * x + p.2 * x ^ 2)) ∧
        (∀ xi eta : ℝ,
          m ^ 2 * (1 - ‖jointCharacteristic mu0 xi eta‖ ^ 2) ≤
            1 - ‖jointCharacteristic
              (mu.tilted (fun x => p.1 * x + p.2 * x ^ 2)) xi eta‖ ^ 2) ∧
        ∀ xi eta : ℝ, R < Real.sqrt (xi ^ 2 + eta ^ 2) →
          ‖jointCharacteristic
            (mu.tilted (fun x => p.1 * x + p.2 * x ^ 2)) xi eta‖ ≤
              1 - (m ^ 2 * c / 2) *
                Real.rpow (Real.sqrt (xi ^ 2 + eta ^ 2)) (-beta)
```

### 独立量词翻译与所需门

1. mu为同一个实数域概率测度，概率实例为明确caller前提。
2. M≥0且mu下AE |x|≤M，允许M=0和退化概率。
3. K为实参数对的任意紧集，允许K为空。
4. u0/v0固定参考二次倾斜参数，不要求属于K。
5. beta、R为任意实数，c严格正；TYPE没有假设beta>0或R>0。
6. hWC只给固定参考倾斜律的全频弱Cramér上界，阈值为R<sqrt(xi²+eta²)。
7. mu0定义为同mu按u0*x+v0*x²的真实倾斜；不可利用不可积倾斜总化为0。
8. 目标存在同一个实m，先于所有p和所有频率选定。
9. m须严格正、m≤1，且新常数m²c/2真实严格正。
10. 对所有p∈K，第一结论为ENNReal.ofReal m乘mu0的真实测度下界。
11. 不仅是逐事件的未量化常数，也不是只给特征函数比较。
12. 第二结论为所有xi/eta的真实平方模缺口：m²(1−|phi_mu0|²)≤1−|phi_p|²。
13. 第三个结论保持同beta／R／真实欧氏半径，将参考WC常数换为同一个m²c/2。
14. 三个结论必须在同一个m、同一p／mu0／tilt和全部频率下成立，不能分别使用两个存在下界。
15. 目标不假设倾斜族的概率或exp可积，这些须从同mu概率与AE有界生产。
16. 参考u0/v0任意实，不能把只适用于小参数窗口的exp可积扩大全参数。
17. 若用已接受的更强norm收缩界，应先有0≤a,b≤1、0<m≤1及b≤1−m(1−a)。
18. 平方界必须先证右侧非负，再合法平方，不能对可能异号的不等式直接平方。
19. 预期代数身份1−[1−m(1−a)]²−m²(1−a²)=2m(1−m)(1−a)≥0须实际核。
20. hWC给c*rpow≤1−a；推出目标m²c/2界时必须核方向、m≥m²/2和rpow非负。
21. rpow底数sqrt(xi²+eta²)≥0，不必也不能暗用正R来除以半径。
22. beta任意包括0／负数，半径0时rpow按库实值定义；本目标应只用真实非负性而无非法逆消去。
23. 若K为空，所有forall p∈K结论可真空，但m正／≤1／常数正仍必须独立给出。
24. 若初始共同m0未能由非空K推出≤1，应实际取min(m0,1)并把测度下界与norm界都转至同m。
25. theta0不在K、M=0等边界都不能隐式要求nonempty或参考点属于K。
26. 不能把root已存在余弦平方模恒等式误报为不存在；本精确imports可能由更强测度decomposition路线消去此需求。
27. 所有测度／频率对象为真实jointCharacteristic，不是标准化后的代理特征函数。
28. 本结论不自动给标准化谱比较／root C组装或均值逆，原A/B/C/D仍OPEN。
29. 待核：全部94行proof消费的公共紧倾斜norm／measure接口、概率／积分门和相同m。
30. 待核：平方不等式的前提和rpow乘法次序是否完整，是否隐藏beta／R正性。
31. 待核：全部所属TYPE／公理是否确为唯一公开项，无private／generated遗漏。
32. 本前缀不预报kernel／proof终裁，不重跑旧图／pins／cache／Lean。

--- END IMMUTABLE BLIND PREFIX ---

## 全部实际proof／来源／公共API审查（receipt之前）

69行4608B盲前缀先持久化，SHA256 `90a40e5e729a50ce1149b489e55e5293ac57fcf8b99b2347a306fc89310becd5`；随后实读当前94行source全部内容、冻结scope73、原R2 343–369、CharacteristicMeasureDomination全部91行，以及CompactTiltDomination／TiltedMeasureDomination实际公共类型和必要生产体。未将此前暂存声明正确、作者路线或receipt作为数学证明。

### 原义务与实际对象

R2(20)要求同有界基律的紧二次倾斜族有共同正测度下界；(22)要求实际特征函数平方模缺口至少m²倍；366–369再给同beta／R的族WC常数m²c/2。当前TYPE的jointCharacteristic确为实际二维(X,X²)特征积分，半径字面为sqrt(xi²+eta²)，没有换成Prod最大范数，也没有假装已经做协方差标准化。

根共享库已有真实quadraticChar_gap_identity的Fubini／余弦证明，不能误报(21)不存在。当前精确imports不消费它，也未加入未证明的cosine恒等式作为caller输入；从真实测度残差decomposition产生的更强norm收缩，同样足够推出(22)。这是有效证明路线，不改变所需结论。

### 1–37行：作用域与完整公开TYPE

两imports恰CharacteristicMeasureDomination与Mathlib.Analysis.SpecialFunctions.Pow.Real，namespace Shao.OQ3，open MeasureTheory／scoped ENNReal NNReal，无公开DEF或额外假设。实际唯一target保留mu真概率、M≥0和AE界、K紧、任意u0/v0/beta/R、c>0、只在参考mu0上给hWC。所有m存在项在全部p／频率之外；同m同时交付0<m≤1、正新常数、真实测度下界、全频平方模缺口及WC界，没有拆成几个不同存在常数。

### 38–52行：共同m与参考倾斜真概率

38–39行消费公开exists_compact_quadratic_tilted_domination，在同mu/M/hM/hb/K/hK/u0/v0下取得一个m0>0及全p∈K测度下界。该公共类型没有Nonempty K或(u0,v0)∈K前提。实际CompactTiltDomination15–28先对连续参数差求紧上界，再取max C 0；43–49得到固定exp(−2L(M+M²))，没有提取K元素，允许空K和参考点不属K。

40–42行明确令m=min m0 1，lt_min生产m>0，min_le_right给m≤1；不借非空K来从概率比较反推上界。43–45行mu0是同mu真实参考二次tilt，先用quadratic_exp_integrable_of_ae_abs_le对任意实u0/v0给真exp Integrable，再isProbabilityMeasure_tilted建立真概率。实际helper在AE |x|≤M下以exp(|u|M+|v|M²)真有限常数支配并有真实可测，M=0也保留；不是把某个小参数MGF门放大到全参数，也没有不可积tilted=0捷径。

46–50行将m≤m0经ENNReal.ofReal单调性逐集合乘mu0 A，得到ofReal m•mu0≤ofReal m0•mu0。这里是ENNReal非负乘法单调，未对top.toReal做减法；两个标量均为真实有限实数的ofReal。51–52行由m>0、c>0和2>0得m²c/2>0，甚至K空时也实际交付此项。

### 53–60行：同一个m用于每个真实倾斜概率和收缩界

53行先交共同m／正性／上界／新常数，再intro p hp；m完全在p与频率之前。55–57行mup为同mu在p的真实二次tilt，同样先任意参数exp真可积再给其概率实例。

58行hlower=hscaled.trans(hfamily p hp).1是新同m的测度下界；不是原m0下界与另一个norm常数混用。59行以同mu0、mup、m、hm.le和hlower消费公开jointCharacteristic_norm_le_of_measure_lower的第二项，得到全频b≤1−m(1−a)。hfamily原有cosine积分比较没有被冒充norm结论；本source实际重新从新m的真实测度下界生产更强norm界。

实读该接受公共API17–62：lambda=ofReal m•mu0真有限，rho=mup−lambda真非负残差且rho+lambda=mup；真实有限measureReal_add_apply两个非top门给rho质量=1−m。单位相位在两个有限测度下真Integrable后才拆积分；残差积分norm≤1−m，scaled积分norm=m·a，三角不等式给实际收缩。它不是未证明的RN代理，亦没有把虚构不变量当概率。当前调用所有概率／有限／非负门均已满足。

### 61–76行：平方模缺口的真实代数门

令a=参考实际norm，b=目标实际norm，A=1−m(1−a)。65行jointCharacteristic_norm_le_one在mu0真概率下给a≤1；66行hbnd来自前述同m收缩。67行pow_le_pow_left₀以norm_nonneg b和b≤A给b²≤A²：由这两项本来就有A≥b≥0，合法平方，不需要额外假设异号也单调。

68–70行由m≥0、1−m≥0和1−a≥0生产H=2m(1−m)(1−a)≥0。71–74行ring实际核恒等式1−A²−m²(1−a²)=H。故1−b²≥1−A²=m²(1−a²)+H≥m²(1−a²)，75–76行change及nlinarith only只用hsq/hprod/hid得到目标，方向和系数精确。没有把1−norm²和1−norm混用，也没缺任何概率上界。

### 77–91行：同beta/R的精确m²c/2与实rpow

rho字面取Real.rpow(sqrt(xi²+eta²))(−beta)。81行只以sqrt_nonneg和Real.rpow_nonneg给rho≥0，不要求频率半径>0或beta／R正；82行c rho≥0。83行hWC在完全相同xi/eta/hfreq下给a≤1−c rho，从而88行hgap:c rho≤1−a。

85–86行m(1−m)≥0和m≥0推出m²/2≤m；87行对非负c rho乘这个因子不等式，89行对hgap乘非负m。与84行b≤1−m(1−a)相接，严格合法得到b≤1−m(c rho)≤1−(m²/2)(c rho)，90–91重排为1−(m²c/2)rho。没有除以频率、c rho或m，也不用beta／R的隐藏正性；实际c>0只用于新常数严格正。

因而任意实beta/R版本是代数更强的条件性传递，非声称beta≤0或R≤0属于原标准弱Cramér定义。半径0时rpow按固定库总定义仍非负；某些输入令hWC不可能，并不被用来替代实际概率或常数生产。原应用必须保留其正beta/R范围。

### 全边界与所有locals

K空时通过max C 0／min m0 1照样选到m>0≤1和新正常数，后续forall p vacuous而不泄漏Nonempty要求；(u0,v0)任意且不要求在K。M=0允许，helper仍给所有二次exp真可积／倾斜真概率。所有p／xi／eta使用同m，真实欧氏半径和阈值R不变，常数无n依赖。93–94仅结束section／namespace。全部94行和每个local已读；本源无authored private／DEF，实际是否产生额外常量仍按下面module-owner枚举独立核。

数学阶段结论：来源／完整TYPE及实际proof无CRITICAL GAPS，不能以成功构建替代以上实质检查。接下来读全部actual TYPE及公理，最后才核receipt／构建／依赖源绑定。

## 全部实际DECL／TYPE与公理覆盖

上述数学阶段之后读取actual-declarations.txt全部29行1648B，SHA256 `73cff7ad1f752b7b9f67d152ecb16d3d8f5489c5cee0240c0dd928229cc22078`。唯一实际TYPE及所有长续行原样如下：

```text
DECL Shao.OQ3.exists_compact_tilted_weakCramer_bound
TYPE ∀ (mu : MeasureTheory.Measure ℝ) [MeasureTheory.IsProbabilityMeasure mu] (M : ℝ),
  0 ≤ M →
    (∀ᵐ (x : ℝ) ∂mu, |x| ≤ M) →
      ∀ (K : Set (ℝ × ℝ)),
        IsCompact K →
          ∀ (u0 v0 beta c R : ℝ),
            0 < c →
              (∀ (xi eta : ℝ),
                  R < √(xi ^ 2 + eta ^ 2) →
                    ‖Shao.OQ3.jointCharacteristic (mu.tilted fun x => u0 * x + v0 * x ^ 2) xi eta‖ ≤
                      1 - c * (√(xi ^ 2 + eta ^ 2)).rpow (-beta)) →
                have mu0 := mu.tilted fun x => u0 * x + v0 * x ^ 2;
                ∃ m,
                  0 < m ∧
                    m ≤ 1 ∧
                      0 < m ^ 2 * c / 2 ∧
                        ∀ p ∈ K,
                          (ENNReal.ofReal m • mu0 ≤ mu.tilted fun x => p.1 * x + p.2 * x ^ 2) ∧
                            (∀ (xi eta : ℝ),
                                m ^ 2 * (1 - ‖Shao.OQ3.jointCharacteristic mu0 xi eta‖ ^ 2) ≤
                                  1 -
                                    ‖Shao.OQ3.jointCharacteristic (mu.tilted fun x => p.1 * x + p.2 * x ^ 2) xi eta‖ ^
                                      2) ∧
                              ∀ (xi eta : ℝ),
                                R < √(xi ^ 2 + eta ^ 2) →
                                  ‖Shao.OQ3.jointCharacteristic (mu.tilted fun x => p.1 * x + p.2 * x ^ 2) xi eta‖ ≤
                                    1 - m ^ 2 * c / 2 * (√(xi ^ 2 + eta ^ 2)).rpow (-beta)
AXIOMS [propext, Classical.choice, Quot.sound]
```

逐项核：真mu概率和AE有界、任意紧K、任意beta／R、仅c正与固定参考hWC作为输入；输出同一个m在全p和频率前，三个实质合取（测度下界／全频平方缺口／同指数阈值WC）完整保留。没有隐含Nonempty K、参考点属于K、手给族概率或beta／R正性。未将实际Euclidean sqrt半径换范数。打印器have mu0是原let，非新假设。

末阶段实读Audit.lean41行：21–25行遍历env.constants，env.getModuleIdxFor?后精确owner==Shao.OQ3.CompactTiltWeakCramer，而非namespace／stem猜测；26行拒绝新项目axiom，27–30行collectAxioms完整传递检查。实际计数0 frozen DEF、1 frozen THM、1 ALL THM、1 ALL DECL，故1public、0private／0generated／0DEF，与完整94行源码一致。该唯一项实际传递公理恰[propext, Classical.choice, Quot.sound]，无其他公理／sorryAx，没有漏掉自动生成义务。

## 最后机械绑定与恢复历史

### 精确冻结版本和当前source

- 原scope73本地／remote均48行4770B，SHA256 `b539efde780e8033134f2503dcfd8070a811fbae8db759814bc75d3c1829ea77`。
- 原声明终票仍180行17808B，SHA256 `0fa1c30e107e210c6878af43811442660928da5822900314ca9a3a96c71a3827`，保留旧暂存历史，不重新造statement gate。
- 当前本地source、remote own source和run快照均94行4473B，SHA256 `87d4560d0a896d7094e17153b2286408b509b605719977ee443cd688ba8b5544`。完整public TYPE与scope逐字（去末尾终止空白）相同，白空格规范比较亦PASS。
- 原R2直接来源SHA256 `572e74aa9c12e2771f5543a5709a2807666eeea0a4076e7a3263e5c7bcf87f55`；当前范围是343–369的有界倾斜稳定性，不是无界族的无条件密度下界。

恢复正式resumption-ack.json22行1308B，SHA256 `75d5bd69d100f78253178cb40ba9b8ffef0e0497b78a99b8361183cdf5079ecf`；记录旧声明字节不变、U20d接受发布后正常恢复。其no_U21a_source_yet是在21:41恢复检查点的历史事实，不当作当前仍无source的实时断言；之后当前实现／构建／Audit均有新正式凭据。旧scope中的未实施状态同样保留为冻结历史，而不倒改。

### 唯一完整构建与首actual-owner Audit

build-history.json24行592B，SHA256 `a4a667fbba5c0b3512564a640a6ed6454de94b17821c61375d95545e46167d77`，实际只有完整build01：exit0、4.7639285s、94行完整当前源首次成功。没有失败／partial／probe／源修复或成功重跑。

build-01.log16行712B，SHA256 `8a7609a600235a24ffc4821bde996210939622b3a387e69b29a029c281080961`，非空。选读真实诊断是44和56行各一条实例语法建议，共2warning、0error；不是空log，不因提示而关linter／修改proof设置或重复构建。

首次Audit exit0、4.7890331s，Audit.lean41行1777B SHA256 `790870e9cc6aafda3b73255cb465ef23bfc61fccf4ef6313c19dda4e0b779a04`；Audit.log34行1762B SHA256 `ce88ae2a731494ceeec2ed694c5dacacc34f74de1bc161a29d10f1973dd01066`。真实owner枚举／全部TYPE／公理已独立读，不以PASS一词自证。

### 正式receipt、15前置及git

最后读receipt.json208行8921B，SHA256 `0dd2ebbd4c2273f60b697c61550d5d870910bd08c65c4a4ad17c571d72339aae`，状态AUTHOR_KERNEL_AND_AXIOM_CHECKED_AWAITING_INDEPENDENT_PROOF_REVIEW，准确区分作者检查与本次终审。其frozen_signature_match通用状态字符串提到probability letI；本实际公开TYPE准确位置是caller概率实例加let mu0，倾斜概率的两个letI位于proof44／56，不能据该通用标签推断公开类型另有letI或额外前提。独立逐字比较已直接确定完整类型身份，标签不代替类型证据。

正式prerequisite-hashes.json17行1583B，SHA256 `5b99a57321e85aa47bc66623b6b038c942628eb427f89f631305798b59f666f2`，15项canonical源字典。末阶段逐项当前own源fresh hash匹配，缺失／不符0；compact独立重算`2b038a74d11a67ef91fcaceaf4dd5c3fa88de4757967e5e2d9d555851cf02bb5`，与原声明已独立核15图相同。本门未重跑完整图／pins／缓存／对象检查或任何成功smoke。

当前branch `feat/oq3-compact-tilt-weak-cramer`，HEAD `ffdedd610d0af501c3dd4672cf7f78d80eee543c`，tree `433377aee492752840f9396896bd00f668634442`，status仅`?? Shao/OQ3/CompactTiltWeakCramer.lean`。正常从root接受v38建新分支，无lane merge／reset／rebase／fetch／retarget；原158／156等8冻结head作为行政历史保留，当前不是这些leaf head被重写或假称全已合main。

native -M8192／-j4／-DautoImplicit=false、CPU14–17与固定Lean v4.36.0-rc1／Mathlib807d3836b165983210ee2ecf3cd28f239436949c沿已接受门；本review未重哈希稳定pins或whole cache。所有远程项目只读均taskset -c 14-17，未启动Lean／Audit／probe／heavy任务，未触外部CPU0–9／80GiB或全局资源，raw完整日志留服务器。未修改任何source／scope／receipt／Audit／旧票／shared／cache或他人文件。

## 最终完整独立裁决与剩余

STATUS: CORRECT

绑定原scope73完整SHA、当前94行87d4560d完整SHA、唯一actual模块owner TYPE及标准三公理、首次build01／Audit。完整proof、全部locals、真实倾斜概率／measure lower／范数收缩／合法平方／rpow和常数代数、准确来源及末阶段绑定均独立通过，未发现CRITICAL GAPS。结论不由作者route、旧声明或kernel PASS单独推出。

原target→实际消除：R2(20)同一个m真实测度下界及原(22)实际平方模缺口、同beta／R／实际Euclidean频率的统一族WC常数m²c/2。直接consumer是原C有界倾斜稳定性组装和原B倾斜族WC部分；本TYPE不需输入手工族bound，不把参考theta0限制在K，也保持空K／M0等边界。

剩余：协方差标准化后的统一范数／频率变换及相应常数、root C完整适配、root B Edgeworth／格胞／远区概率、均值邻域逆与其他根装配均仍待各自证明。任意实beta/R是代数推广，不声称原标准WC允许非正beta/R，也不声称最优指数。全部原A/B/C/D仍OPEN。旧DEFERRED_UNIMPLEMENTED是过去声明暂存状态；当前已有实际实现及本次独立终审，但接受／commit／PR仍须lead全文读本终票之后。

69行4608B盲前缀SHA256 `90a40e5e729a50ce1149b489e55e5293ac57fcf8b99b2347a306fc89310becd5`原字节保留；首部IN_PROGRESS为落盘历史，本节CORRECT为完整proof终裁。本报告外没有新agent／chat／Lean执行或写入source／旧票／cache／branch，也未commit／pub。
