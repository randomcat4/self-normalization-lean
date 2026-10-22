# U19b SourceGeometricScale 完整独立证明审查

STATUS: IN_PROGRESS

## 一、实际完整public TYPE先行盲译检查点

保留先前声明审查上下文，但本轮重新仅提取actual source的完整public TYPE并先独立重译；尚未读取本次102行proof、private/helper、生成项或作者receipt/build绿灯。0公开DEF；完整let表达式也保留，不只记录类型首行。

```lean
theorem source_corrected_scale_geometric_identity
    (q : ℝ) (hq0 : 1 < q) (hq1 : q < 103 / 100)
    (w : AtomicIndex → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hbase : ∀ i : Fin 4, 0 < w (Sum.inl i))
    (hm : ∀ k : Fin 4,
      HasSum (fun i => w i * constraintFeature sourceEll (fixedAtom i) k)
        (constraintTarget q k)) :
    let D : Matrix (Fin 2) (Fin 2) ℝ := parabolaCovariance (atomicMeasure w)
    let x0 : ℝ := Real.sqrt q / 4
    let a0 : ℝ := q / 4
    let v : Fin 2 → ℝ := ![1, 2 * a0 / x0 ^ 2]
    let curvature : ℝ := 2 * (-sourceEll) / x0 ^ 2 + dotProduct v (D⁻¹ *ᵥ v)
    0 < D.det ∧ 0 < curvature ∧
      0 < sourceEll * Real.sqrt D.det * Real.sqrt curvature ∧
      correctedInverseScale sourceEll q (atomicMeasure w) =
        (sourceEll * Real.sqrt D.det * Real.sqrt curvature)⁻¹
```

实际量词与let依赖独立翻译：

1. 任取实q且1<q<103/100。
2. 任取AtomicIndex→ℝ的w，每个w_i≥0。
3. 每个Fin4基点分支w(inl i)>0；新增分支允许0。
4. 每个k:Fin4，实际feature级数w_i*constraintFeature sourceEll(fixedAtom i)k真HasSum到constraintTarget q k。
5. 没有额外概率、det非零、curvature正或Hessian假设。
6. D在结论内let为同mu=atomicMeasure w的actual parabolaCovariance。
7. D类型为Matrix(Fin2)(Fin2)ℝ，不是任意调用者给的矩阵。
8. x0在结论内let为标准实sqrt(q)/4。
9. a0在结论内let为同q/4。
10. v在结论内let为Fin2实向量![1,2*a0/x0²]。
11. curvature在结论内let为2*(-sourceEll)/x0²+dotProduct v(D⁻¹*ᵥv)。
12. 所有let不是新前提，也不允许自由选值。
13. D⁻¹是实际固定库矩阵逆，类型没有预先提供Invertible。
14. 实数除法、sqrt和inverse都有总化约定，proof必须排除不合法门。
15. 第一合取项实际D.det>0。
16. 第二合取项actual literal curvature>0。
17. 第三项sourceEll*sqrt(detD)*sqrt(curvature)>0。
18. 第四项existing correctedInverseScale(sourceEll,q,atomicMeasure w)等于第三项几何常数的逆数。
19. 同一个mu/q/sourceEll始终固定，不能换为代理协方差或另一law。
20. q=0/x0=0已不满足前提，但proof仍需从hq0显式产生所需非零门。
21. det正和curvature正不能由总化inverse0/sqrt0假装成立。
22. 本type没有实际K/globalRate/domK/扩展supremum或Hessian定义。
23. 字面几何身份不自动证明它等于root canonical Hessian曲率；该桥另留。
24. 当前只是实际类型盲译，不是对实现或机械结果的接受。

后续依次审真实来源/冻结scope、全部102行proof及private、全部actualTYPE/axioms，最后机械绑定；不得凭旧声明CORRECT或作者PASS替代本轮独立证明审查。


## 二、来源及全部102行实现的独立数学审查

本节在先行55行actual完整TYPE盲译已落盘后追加。随后重新读scope69、真实R1 239–257及431–443，再完整读取102行actual source，包括唯一private和所有locals；之后读server全部9个actual DECL/TYPE的所有47行及公理行。尚未读取本单元receipt或机械PASS作为证明依据。

R1的实际Λ1=S/detΔ−32ell/q、v_corr²=ell²*(S−32ell*detΔ/q)，S=Varπ(8X−X²)，Δ=Covπ(X,X²)。scope/root literal公式设x0=√q/4、a0=q/4、t0=−ell，边界切向v=(1,2a0/x0²)，几何尺度=(−t0)√detΔ√curvature。本type只识别这个字面几何表达式与已存在correctedInverseScale的同law正域身份，没有定义root K/Hessian/domK/globalRate或替代其尚未证明的桥。

actual source唯一import是CorrectedScaleContinuity，两个authored声明为private inverse_tangent_quadratic和公开source_corrected_scale_geometric_identity，0DEF。公开前提／let绑定与先行实际TYPE逐项一致：q窗口、w≥0、4个基点权严格正和4行HasSum是全部调用输入；det正／曲率正／几何尺度正都必须产生，不能当作新隐含门。

### Private inverse_tangent_quadratic，源13–19

1. 完整实际type仅要求D:Matrix(Fin2)(Fin2)ℝ及D10=D01，不要求det≠0。它断言dotProduct ![1,8](D⁻¹*ᵥ![1,8])=(64D00−16D01+D11)/detD；这是固定库的总定义代数身份，不把任意矩阵自动当成非奇异。
2. 实际proof rw Matrix.inv_def、Matrix.adjugate_fin_two、Ring.inverse_eq_inv，得到detD⁻¹倍的!![D11,−D01;−D10,D00]。Fin.sum_univ_two展开两个有限和，hs把D10改成D01，ring得到(D11−8D01−8D01+64D00)/detD。
3. 该identity对奇异det0也成立：固定矩阵逆是0，实数除0也是0，两边都0。它因此不需要擅自增一个det非零假设，也不能被当作证明正定/正曲率的依据。主proof必须先另外证明实际det>0；实际源54已在调用74前取得该门，满足非总化使用要求。
4. Matrix.inv_def170真实是Ring.inverse(detD)•adjugateD；Adjugate372真实的行列负号及Ring.inverse_eq_inv426已在本人的声明门读固定源码并确认公开可达。这里inv不是逐项倒数、DotProduct两向量顺序和系数64/−16/1均正确。

### 公开proof：实际概率／基点正质量／协方差，源37–54

5. hm0借真实constraintFeature首行与constraintTarget首行简化得到HasSum w1；源39实际建立atomicMeasure_isProbabilityMeasure w hw hmass。没有从裸tsum或不可和总化产生概率。
6. 源40实际AE界hb为|X|≤4+√10。公开atomicMeasure_real_singleton在hw下给mu.real{fixedAtom(inl i)}=w(inl i)，与fixedAtom(inl i)=baseAtom i将hbase转成同mu全部基点真实正质量hbp；概率已先建立，测度有限，非ENNReal.toReal∞伪造。
7. D等五个let在proof45–49与TYPE内部表达式逐字相同；change50–53仅展开结论let，不增加新的调用前提或更换矩阵/法则。
8. 源54实调parabolaCovariance_det_pos(mu,hb,hbp)生产hD>0。该已独立接受实际API依赖真bounded moments和正基点：X/X²真L²、中心多项式真Integrable，AE零平方在−1、1、2三个正单点排除非零二次式，形成真实正def协方差并推出det正。当前proof不是凭任意det>0定义D正定，也没有让caller输入所求det。
9. 实际D=!![VarX,Cov(X,X²);Cov(X,X²),Var(X²)]，故D10=D01定义性rfl。normalVariance_eq_covariance(mu,hb)给S=64D00−16D01+D11；该接口的实际实现先真X/X²可积、EY线性及中心平方乘积可积，再展开actual covariance/variance。全有界支撑也直接保证所有四次矩有限，杜绝variance/toReal/Bochner总化替代真实矩。

### x0/v及负32项，源55–79

10. q>1给q>0，源56由sqrt_pos得sqrtq>0，57产生x0>0；58–61用div_pow和Real.sq_sqrt(q≥0)得到x0²=q/16。所有4、16、q、x0²的分母实际非零，没有在q=0/x0=0取消。
11. 62–66以hx0sq重写、a0=q/4展开，在hq.ne'后field_simp，再norm_num完成剩余2*16=4*8数值身份，严格得到2a0/x0²=8；67给literal v=![1,8]。这不是把normal方向(8,−1)误放到D逆中，v仍是边界切向的(1,8)。
12. 68–71同样在q非零后清分母得到2*(-ell)/x0²=−32ell/q，负号和32因子正确。ellipsis“field_simp <;> ring”的两个style提示不影响代数语义，机械事实下节单独记录。
13. 72–74在已建立hD之后才实调当前owned private inverse_tangent_quadratic D (by rfl)，再用同mu的normalVariance_eq_covariance把分子识别成实际S。没有cross-private访问或引用不在该import内的NormalTangentGaussian后继接口。
14. 75–79展开literal curvature，以hv/hneg/hquad重写后精确得到curvature=S/detD−32ell/q。q/w/atomicMeasure与existing correctedScale始终完全相同，未改坐标／中心／D顺序。

### 真曲率及sqrt尺度身份，源80–99

15. 80–82在hcurvature身份后实调公开atomic_curvature_pos q hq0 hq1 w hw hbase hm，获得真curvature>0。这项公开接口确切消费当前全部前提，不需要额外手工radicand、S或gap输入；其已接受证明从真实transverseVariance界、sourceEll<1/30和正q/S/det跨乘推出Λ1>0。
16. 83–90的hprod先把curvature换成S/d−32ell/q，再sub_mul展开，只在hD.ne'之后用div_mul_cancel₀，得到d*curvature=S−(32ell/q)d。因此当前corrected radicand其实是两个严格正数的乘积，数学上>0，没有sqrt负值总化。
17. 91–93将radicand改为d*curvature，固定Real.sqrt_mul hD.le正确使用非负第一因子门，直接得到sqrt(rad)=sqrt d*sqrt curvature。无需从平方相等删去符号，也没有漏绝对值。
18. 94–95以sourceEll_pos、sqrt_pos(hD)、sqrt_pos(hcurv)生产实际几何尺度G=ell*sqrt d*sqrt curvature>0，第三合取项真实成立；不只是说其逆是一个定义好的实数。
19. 96–99展开同一个existing correctedInverseScale，change仅以D局部名还原实际covariance；sqrt identity及mul_assoc使两个正实数的逆完全相同。没有重新定义常数、改变saddleRate或用root Hessian当作假设。

### 类型覆盖及边界

20. 正式TYPE全部let表达式保留：D/x0/a0/v/curvature是给定数据的定义性值，实际kernel TYPE虽pretty-print为`have ... := ...;`，仍是同一结论内let，不是新增前件。所有第一节量词／合取输出均有source中的对应证据。
21. q0或x0=0不在声明域；主proof显式从hq0取得非零而非忽略totalization。新增权可零、无限支撑可真实可和，但4基点权严格正保留，确保非退化。有限stage含J0如满足同输入可消费此定理，当前type未声称构造新stage family。
22. 相同D是tilted原子律mu下actual covariance，不是原originalMeasure均值为0的协方差偷换；root未来须另证其canonical K Hessian在对应theta处等于此D、参数/尺度同源。本恒等式不完成该解析桥。
23. 当前proof数学完整、所有所消费API前提可由给定模型实际生产。没有发现需要修scope/添加假设/变更实例/新增import的缺口。

## 三、全部9个actual DECL/TYPE和传递公理

完整proof审完后，server实际读取actual-declarations.txt全部47行、每个长续行与全部AXIOMS。不是按生成名猜义务，也不是只读DECL首行。下表完整列明每项的universes/typeclass及非零门；公有全TYPE与第一节相同，包含全部let续行。

T=`Shao.OQ3.source_corrected_scale_geometric_identity`；P=`_private.Shao.OQ3.SourceGeometricScale.0.Shao.OQ3.inverse_tangent_quadratic`。

| 实际顺序／DECL | 精确类型核验 | AXIOMS |
| --- | --- | --- |
| 1 T._simp_1_7 | ∀{R:Type u₁}[AddMonoidWithOne R][CharZero R](n:ℕ)，(↑n+1=0)=False | propext |
| 2 P | ∀D:Matrix(Fin2)(Fin2)ℝ，D10=D01→![1,8]⬝ᵥD⁻¹.mulVec![1,8]=(64D00−16D01+D11)/D.det；无det≠0前件，奇异情形是正确总化代数身份 | propext, Classical.choice, Quot.sound |
| 3 T._simp_1_5 | ∀{M₀:Type u₁}[MonoidWithZero M₀]{a}[IsReduced M₀](n:ℕ)，a≠0→(a^n=0)=False；IsReduced保留 | propext |
| 4 T._simp_1_1 | ∀{α:Type u₂}[Zero α][OfNat α 2][NeZero 2]，(2=0)=False | propext |
| 5 T._simp_1_3 | ∀{α:Type u₂}[Zero α][OfNat α 4][NeZero 4]，(4=0)=False | propext |
| 6 T._simp_1_6 | ∀{G₀:Type u₃}[GroupWithZero G₀]{a}(n:ℤ)，a≠0→(a^n=0)=False | propext, Classical.choice, Quot.sound |
| 7 T._simp_1_4 | ∀{M₀:Type u₁}[Mul M₀][Zero M₀][NoZeroDivisors M₀]{a b}，a≠0→b≠0→(a*b=0)=False | propext |
| 8 T | 全qwindow/w≥0/hbase/4HasSum后，全部实际D/x0/a0/v/curvature lets和四个输出逐行核对，无隐藏det或curvature输入 | propext, Classical.choice, Quot.sound |
| 9 T._simp_1_2 | ∀{α:Type u₂}[Zero α][OfNat α 3][NeZero 3]，(3=0)=False | propext |

实际9项全部THM=1public+1authoredprivate+7generated，0DEF。3项是标准完整三公理、6项仅propext，不能泛称每项都有三公理。生成项是非零逻辑义务，非新分析假设；全部axiom为白名单子集。下节最后再核Audit选择器、计数/现有build与完整hash绑定，当前未靠作者机械PASS代替proof。


## 四、最后读取的Audit覆盖／机械证据／hash与基线

完整独立数学和全部actual TYPE完成后，才读正式receipt、Audit.lean、必要log诊断/metadata、官方build-history和正式17源字典。作者状态`AUTHOR_KERNEL_AND_AXIOM_CHECKED_AWAITING_INDEPENDENT_PROOF_REVIEW`并非独立proof判定；其implementation叙述不作为本票数学依据。

39行实际Audit源先验证唯一冻结public名确为theorem，defs数组空，再遍历env.constants，选择public target stem所有后继及本模块`_private.Shao.OQ3.SourceGeometricScale`前缀，逐项拒绝axiom常量并collectAxioms传递检查标准白名单。当前完整source独立只含2个authored theorem，联合全部9个实际TYPE覆盖本实现和7生成项；这是source+stem/private-prefix覆盖口径，不假称module-index枚举。

Audit.log在server选取全部DECL/TYPE/AXIOMS和完整续行，字节等于actual-declarations.txt；摘要实际为FROZEN_DEFINITIONS0、FROZEN_THEOREMS1、ALL_THEOREMS9、ALL_DECLARATIONS9、AXIOM_GATE PASS。首Audit官方记录exit0，raw完整日志留server，没有下载到本地或写入新log镜像。

| 工件 | 行数/字节 | SHA256 |
| --- | --- | --- |
| actual source local/worktree/run/source-02一致 | 102 /4365 | 6361d54e22501bf85a6c683a7e85d9df05082bd6190cad73a8d03dc00f3e7470 |
| scope69 local /run scope.md一致 | 34 /6372 | fba06a40b1db81cfdb8dec02b8bb9bd5887a3b64b484e6491d7082c73477b2cf |
| 声明final local/remote一致 | 162 /18178 | e4ba8f117fe837b6eb792bc6c4394ff3165a31f2d6eca8cdcaafb9873445a10e |
| R1真实report.md | 只读原件 | 3473d34ff20bd0d334b9ef3ea3c3ee167fba4d5cc3a742849820ce54d639e662 |
| source-01完整失败版本 | 101 /4352 | 30368cbf5b46746abd38e512d3e883dc152ce39193e2d14c517922141cea909c |
| build-01.log（raw留server） | 23 /880 | 02bb7063364512974d3289631645e2990a1b16a72a223b9cda0c2b343d0f11c6 |
| build-02.log首次完整成功 | 6 /392 | e81311040cb9a556d9e60dc2f9fc17200248c8176efa745d7b712b85ba8d231f |
| build-history.json | 46 /1183 | defaf03b2e3113da4b3f95459ea8d5c4cb049969567f7b0bdb9da3bce2192f31 |
| Audit.lean local/remote一致 | 39 /1673 | 253c6d6629d5a3d52d2e95099a0d247596729b3acdf34869a87712b2bce5687f |
| Audit.log | 52 /2857 | 1754a5eeba9fad949082c1a53e92f53dd87794fda7617fde4fde9973bd3a4105 |
| actual-declarations.txt local/remote一致 | 47 /2743 | 81fd11d992bba421c5b5213259fb6fff522ec2c15c1b9e121c1d084fdd13a5f1 |
| receipt.json /local U19b-receipt一致 | 265 /11254 | 17823c7285a1dc88566e1742c51bde29063bb85af19314e3812a6f115fcccd06 |
| 正式prerequisite-hashes.json local/remote一致 | 19 /1766 | 9f579be17ffa72b4b08b449e427d16b928d6b5f9206cf7ef92abd809792ab7f9 |

实际完整public TYPE含全部letbindings与scope fence去空白比较PASS；旧source01完整type同样匹配，唯一import始终CorrectedScaleContinuity。当前源码authored declaration实枚举1public+1private、0DEF。剥注释后sorry/admit/axiom/unsafe/native_decide/implemented_by/set_option扫描无命中，CR字节0、尾空白0。

真实history只有两个不同完整source：01 exit1，02 exit0，无partial/probe或成功重复。server选取01错误行及实际goal，确为源62:36 unsolved goal `2*16=4*8`，不是缺q合法性、丢det门或数学命题变化。独立source01→02 diff只是在hq.ne'合法约分后的field_simp下一行加norm_num，增1行13B；未改public TYPE/import/private身份/假设。

02是当前完整102行首次strict成功，官方history/receipt均记exit0、4.170693秒。build-02.log真实非空392B，两条均来自源71 `field_simp <;> ring`的unusedTactic/unnecessarySeqFocus样式建议，0error；不得写成空log或无warning。没有为清style重跑同源成功target/Audit。该警告不改变任何证明门，上面的独立代数核验也不靠“compiler接受故无问题”替代。

实际作者target/Audit命令均指定server taskset CPU14–17、native`-M8192 -j4 -DautoImplicit=false`，target输出SourceGeometricScale.olean，首Audit读取本run Audit.lean。没有心跳/公理/autoImplicit语义弱化，无ulimit-v。本review不运行任何Lean/#check/probe/目标构建/Audit或import smoke；这里只读验收已经存在的真实成功与失败历史。

### 先决源／既有图／pins／Git

最后fresh重算正式17项当前项目源SHA：17/17与prerequisite字典及receipt map一致，0 mismatch；canonical相对路径键排序紧凑map SHA为`a1f4b5aa595cc437fb511345cdcd4b9d3471b3f88bcc50fbc7ea90247e421766`，与本人声明终票独立图精确相同。关键CorrectedScaleContinuity=b0391976b809b37b1d0d3cb591c2fc89c9291538e8bc9193db70dd2b1504a2a8、RegularCovariance=0add3476cc949edc593e15dc195934a6df78a41a55f4a2281f66095733d4c853、AtomicMeasure=59ddc48fb7b395f362939e58cbd9d7911685a6ed6e6574142e8a6d4ab3ee0c39未改。

本轮按要求复用完整声明图/pins/cache，不重复全图/oleans/成功smoke检查。旧独立静态证据physical17Shao/2747Mathlib、211外部停止叶；public2457内部+189外部停止叶=2646，内部source/olean缺0；外部叶未展开。Matrix.inv_def/adjugate_fin_two、Ring.inverse_eq_inv、Real.sqrt_mul及所消费实际概率/协方差/曲率接口均可公开到达，NormalTangentGaussian/C/U19a后继不是import dependency。没有依赖不可见private helper。

pins沿用本人声明核验及当前正式receipt同一版本：Lean leanprover/lean4:v4.36.0-rc1、Mathlib807d3836b165983210ee2ecf3cd28f239436949c；lean-toolchain SHA d581a24b57a4ae9e0b2132ca8ac7cc3ac336a9fc2751fe6b29414e2d434d54c4、lake-manifest SHA40e8e3385f2b0c8ae56fa9de6947301472379cb62eeb83247944827c38b8af6e。没有cache写、包升级、重复root KL gate或whole-directory哈希冻结。

最后实际Git branch=`feat/oq3-source-geometric-scale`，HEAD=`f2a39a09ebd50648bd61d68d7018aa01a9810ea0`，tree=`b6e72c992deceb0df88e772e50b2c42ba58ac4b4`（rootv36 main82294同树）；唯一status为`?? Shao/OQ3/SourceGeometricScale.lean`，U19b尚未commit/PR/接受。声明时U19a5d14干净head与此正常新分支的推进不是源码漂移；旧U19a/C冻结head由lead保留，本review无fetch/reset/merge/rebase/retarget或branch编辑。

所有review server项目命令CPU14–17只读，无heavy/Lean/探针，未触外部CPU0–9/80GiB任务或全局资源。未读作者implementation/future/candidate/scanner笔记或其JSON，正式receipt/17表只在数学与TYPE完成之后读取；只新增本地及授权remote报告，未改scope/source/旧票/shared/cache。

## 五、完整独立最终裁决

STATUS: CORRECT

JUSTIFICATION: 对冻结scope69和实际102行proof，完整public TYPE的全部let/量词、唯一private及所有locals、7生成项／9actual TYPE和传递公理均已独立核对。private纯2×2逆二次型身份虽正确涵盖det0的总化代数情形，主proof实际先由真概率/基点正质量生产det>0，再消费该lemma；q/x0分母、literal v=(1,8)、负32系数、actual S协方差身份、公开真曲率正性和det*curv radicand均正确。正sqrt乘法给同一个正几何尺度，再取逆恰等于现有correctedInverseScale；没有奇异inverse、variance或sqrt总化伪造。既有首次strict02与首Audit机械证据及当前source/pins/17前置绑定一致，未以机械绿灯替代数学审查。

原义务→消除义务→直接consumer→剩余：本模块完成R1实际source Λ1与literal几何二次型的身份、几何尺度正性及其逆与C已用校正常数的一致；直接consumer为root canonical saddle constant桥及C同最终law的rootA装配。当前0DEF，未定义root K/Hessian/globalRate/domK，也未证明其实际Hessian=该D、全局鞍点或扩展supremum桥；一般KL9/10、其他根装配仍需独立履行，不扩大新颖性／最优性声称。

根A/B/C/D全部OPEN。作者机械状态与本完整独立CORRECT分开，lead全文读取本final之前不接受/commit/pub。先行55行actual完整TYPE盲译检查点字节原样保留，前部IN_PROGRESS是历史状态，最终以本节为准；本review未修改任何源、旧票、冻结scope或他人文件。
