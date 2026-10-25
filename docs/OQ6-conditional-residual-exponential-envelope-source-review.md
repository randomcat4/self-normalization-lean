# 单元182独立完整源码终审

STATUS: CORRECT_SOURCE_REVIEW_PENDING_SERVER

QUALIFIED: false

审查对象是精确 `ConditionalResidualExponentialEnvelope.lean`，SHA256 `b30675c6dbfc53080435dcac9cae80485e982e7c7de20b45fd7457a8773420d5`，21065字节、394个LF。已完整独立读取全部源码、完整数学说明、冻结声明及其重复环境的无损重建、原文p51/p54/p44、被消费175/181的完整公共接口与实际公共TYPE、精确合格证据，以及主库相关完整环境前缀。没有发现数学关键缺口。此结论仅认证源码层面的陈述忠实性和证明推理；本审稿人尚未收到182自身的服务器内核、实际所属TYPE、非定理FULLVALUE及递归AX材料，不能提升为qualified或声称182已被Lean检查。

审稿角色为 `/root/oq56_exponential182_final_review01`，是作者之外的新独立上下文。作者在源码审查前已精确RELEASE0；作者文件、冻结文件、源说明、父级状态及任何共享文件均未修改。本审稿人只写本目录，没有服务器、Lean、网络、Git、上传、缓存、工具链操作，也没有派生子代理。

## 精确输入及冻结

冻结文件SHA256为 `49dfb606c43084f0660e68ac36c2c4760a7d507f5dcc9be7fde9e12d3dd4542a`，1419118字节；源码映射SHA256为 `c920e7d5ae5822aaf79c6bc3f033f8711ed7e72603c7af8f9abdcf4a59498d08`，2873832字节。父级源码接收记录 `e79863b6440a160c640ccb85cd80c8c3ab5eba4212a12f3a44710f387948c1f7`、实现激活 `fc21a9ed49d1dcb21bef9ccc53d073ad0ef3f9bebf4becdac716540fa3d317c7`、作者manifest `be04f48ab6bd6c4c2f86fcc0ad345876689084d733aa5917ec4b1bd7c5baa4de` 和作者RELEASE `5c90bf97a4b14aaf5ce8c724e98c2b49d79796606ba79266356552dc78490d2c` 均与本次实际文件相符。

源码前缀288字节、纯公开声明2872字节、证明分隔符和后缀均与冻结精确相同；纯声明SHA256为 `b58ee60c6428f7c78711ac01619bf11d435e7833eb0c00b5b8fb58d9e8a5b15c`。源码是UTF-8、LF，没有CR。公开声明只有一个定理，没有新增全局定义。输入22项保持181原参数的顺序、类型和语义，没有新数学假设，没有给Ω增加拓扑、标准Borel、无原子性或别的结构。

独立静态审查程序位于 `independent-static-review.py`；它重新核对601项字节、类型、值、顺序和材料化检查，当前601项均通过。这个数字只计确定性一致性检查，不能替代下述数学审查，更不是Lean通过数。详细结果在 `independent-source-bindings-and-static-checks.json`，完整类型/值/作用域/API覆盖在 `complete-typed-value-scope-api-coverage.json`。

## 原文到公开陈述

完整读过的原文精确绑定为：p51 `96920f428b8fc09788a6388103cefe398e3ec739129a5922b984babd09e99359`；p54 `e03649e1324def02de3ff234bcc94c9e1cb643e074a324e1817ef940f5e01c43`；p44 `3d6a674252a81b7ca051fd54aa0a621511ebce94af2f0bdf9b4eca8715bc5239`。

p51 S6使用真实原投影g、原典范残差r、同一个事件C_R={w≤R}及条件律。182没有改成新的统计量，也没有把截断改成{wstd≤R}。公开陈述第34–42行的g、r、M、W2、Cenv、aenv、wstd、tauStd、Mexp都在任何R、λ之前定义；N0也先于全部R、λ存在。Mexp是原μ下原伸展指数函数的积分，常数2统一于所有R≥N0及后续λ。

第47–65行保留实际C、d=μ.real C、ν=(μ C)⁻¹•μ.restrict C，随后定义H=g+g′+λr、κ=∫H d(ν⊗ν)、G=∫H(o,y)dν−κ、σ2=∫G²dν、σ=√σ2、K=H−κ−G−G′、Kstd=K/σ。结论是同一个ν⊗ν下两条AE不等式。未用λrC/σ重新定义目标，未将AE强化为逐点，也未从自由给定条件矩假设获得结论。

182是p51 S6到p44产品包络/伸展指数矩输入的适配。缩放本身对全部α>0成立，后续p44行能量/和矩消费者仍须0<α≤2。本件没有证明p44全q矩引擎、行集中、p54真实大余项付款、严格源预算、上尾/紧区间相对误差引擎或Mills平移。p54否定的“标准化p矩变化为任意多项式阶”没有进入前提、阈值选择、证明或输出。Shao–Zhou外部工具归属保留；不作新颖性判断。C2、C12、OQ56仍OPEN，OQ3仍单独PAUSED_BY_USER。

## 被消费的旧结果与精确付款

181消费源码是repair-01，SHA256 `2dd4569985df4b849ec4f1cc1e0320754a9d2fcec1db9ef994dd007c6fc4ddb4`；精确qualified-evidence SHA256为 `3f4edf3f127534637bb7c92507466a3c91b3a74050466e039cba849fe21e0e5d`。冻结中旧181源码 `952b979f6c526622ea7af0d6e3392c66250188391703a96663f11cbd8af91683` 是历史证明稿引用；父级实现激活已绑定精确新repair和未改变的公共接口，本审查没有将旧hash冒充当前输入。

175消费源码是repair-05，SHA256 `7c823038ce5d4d6f17bc4eaec7470343d216c129e5529c3e06ddeb0e5691779e`；其qualified-evidence SHA256为 `1dc82a65af844abdf9e2287a993ab0efd91b5f0db61d8c7e347c5b2eb1c28ded`。两个旧结果的完整公共接口和实际公共TYPE均已读完；所有qualified材料内可访问的本地精确引用哈希均重新相符。旧完整证明及旧检查没有重审/重跑。

实际TYPE阅读采用可逆的重复子项提取：只把重复且完整的括号表达式各读一次，保留全部实例、宇宙、参数、量词、let值、AE滤子和数学结论；提取后的完整类型和全部定义项分别见两个 `producer*-actual-type-lossless-view.txt`。程序验证展开后与实际TYPE仅规整空白的全文逐字相等。这不是只读词典或接口摘要。181的原实际TYPE文件SHA256为 `1633208cc0646c9dd8d302a27285ad1b242b3173ba6c77dcf4c66e34a3d7c4fd`；175实际TYPE从其已绑定all-owned-actual-metadata的唯一public entry完整取得。

第71–123行以原μ/h/w/α/τ/p及全部原前提调用181。h181是原完整结果：第4项1≤W2、第6项Cenv>0以及七次右投影后的完整原存在谓词都得到正确定位。162–206行h181Threshold保留所有C,d,ν,b,c,Mν、H,κ,G,σ2,σ,K,Kstd,ρ2和最后RhoBound的字面值；唯一替换是展开其既定4*Cenv²*M²。207行N0=Classical.choose h181Threshold，208–252行choose_spec是同一完整谓词，没有借182新结论选择阈值。

任意R≥N0后，260–266行分别是原19项cutoff载体中的第1、2、3、4、6、7、8项；因此C可测、d≥1/2、ν概率及绝对连续、ν(C)=1、ν-a.e.1≤w≤R、ν下L²都已付款。hcutoff由d≥1/2推出，hLamZero明确证明0∈[0,1]。第272行letI instν来自hνprob，没有新外部实例假设。

273–325行以R/hcutoff/0/hLamZero调用175，显式实参依次为μ,h,hh,hh2,hhsymm,hcenter,hprojectionsecond,w,hw,hwone,α,τ,hα,hτ,hwexp,henvelope,R,hcutoff,0,hLamZero。此时尚没有引入后续lam/hLam。175第13项的十二次右投影再左投影，确实给所有原μ可积f的条件可积性和实际限制积分除d公式。取f=F，hwexp正好支付原可积性。没有借未来λ输入付款，也没有以不同原律替换μ。

375–376行在任意合法λ引入后才取181的kernel部分。cutoff结果中十八次右投影取得∀λ；其kernel结果第21项和第22项正好是Cenv*w*w′与Cenv*R²两条AE包络。两个投影所作用的H,κ,G,σ2,σ,K,Kstd都与第368–374行的实际定义相同。

## 完整证明推理

第135–150行先由平方根得aenv≥0及aenv²=Cenv。haenvOne分支使用W2≥1；若aenv<1，(1−aenv)aenv≥0给aenv²≤aenv<1，而2(1+2W2)²≥18，矛盾。源码中的多项式推理也具备这些明确假设。随后aenv>0和aenv^α>0，τ>0支付tauStd>0。

第151–159行只在原μ下hwone满测集使用w≥0和实幂非负，从而τw^α≥0，F≥1。常数1在概率μ下可积，原hwexp已给F可积；积分单调性和μ(Ω)=1给Mexp≥1。没有利用不可积Bochner积分的默认零值。第160–161行的wstd可测及μ下L²分别沿Measurable.const_mul和181原L²取得。

第328–336行在ν-a.e.1≤w≤R集合上得w≥0，使用真实主库Real.mul_rpow得到(aenv*w)^α=aenv^α*w^α。aenv^α>0保证除法抵消，从而tauStd*wstd^α=τw^α及F=Fstd在ν-a.e.成立。可能负w的零测例外没有被当作满足乘幂公式的点。

第337–341行Integrable.congr的方向是Integrable F ν和F=ᵐ[ν]Fstd推出Integrable Fstd ν；积分相等采用同一AE等式的对称方向，再接175的限制积分公式。第342–353行F逐点非负，限制积分≤原Mexp；d≥1/2且Mexp≥0给Mexp≤2*Mexp*d；d>0允许除法，得到统一∫Fstd dν≤2*Mexp。这个常数的全部来源明确。

第354–363行在相同ν满测集，由1≤aenv及aenv≥0把1≤w≤R传为1≤wstd≤aenv*R；ν下L²仍用已付款的w下L²作常数乘法。第364–367行完成这些与λ无关的cutoff结论后，才任取λ。

第377–384行将181第一条AE包络与Cenv*w*w′=(aenv*w)(aenv*w′)合成；第385–390行独立地将第二条与Cenv*R²=(aenv*R)²合成。这两处只是实数环恒等式，不需要逐点w≥0，也不需要把两个不同AE集合逐点等同。每条各保留其正确ν⊗ν滤子和分支点/假设。

## 类型、值、作用域和主库接口覆盖

已完整审查61个冻结条目、22项原输入、22个证明数据绑定（19个公开let的证明局部重现加F、Fstd、N0）、24个额外Prop/内部命令绑定以及25个API实际应用。`source-map.json`中的136个byte半开区间、行定位与实际UTF-8源码均精确匹配，覆盖声明、完整顶层证明块、内部绑定、调用、输入和局部类型变换。

对重复环境，先完整阅读唯一的实际数学内容，再独立按源码顶层命令重建所有先行绑定；对嵌套证明分别显式重建分支向量，核对每一份材料化全文及冻结向量。所有61冻结作用域向量与实际向量去掉允许的新增Prop后顺序相同。没有把正在证明的have加入其自己的环境，没有未来命题流入先前调用；hR/hLam的命令入口与引入后状态区分正确。

独立覆盖文件保留所有唯一完整类型/值、每个实际条目的完整有序作用域向量及环境hash。公开和producer内部的forall、fun和积分局部变量都保持在其完整原表达式内部：g/r/H/G/K/Kstd等函数参数、μ/ν/ν⊗ν积分点、175中∀f接口、所有Measurable/MemLp/Integrable函数项均逐式核对。实际TYPE进一步明确了这些点的类型、度量/范数/测度实例，没有发现自由f/g、捕获或额外结构参数。

需明确两项表示细节。第一，作者已把第144行 `dsimp only [Cenv] at haenvSquare` 记为唯一局部类型变换：反证证明内haenvSquare变为aenv²=2(1+2W2)²，外层仍是aenv²=Cenv；该变换的前环境、源区间及分支结束均已独立核对。第二，源码第70行 `classical` 已有完整CLASSICAL源块，但作者后续“数学绑定向量”没有再次写出这个证明模式命令；本审查在所有后续作用域上显式补记其激活状态。它只提供标准经典推理的elaboration模式，不增加数学前提；没有把这一源级映射当作实际Lean所属常量清单。

主库包SHA256为 `6fafff32648d5b6bb265c7092f9af7269aa10f15cfa41518d783f828599593f0`，对应钉死mathlib `807d3836b165983210ee2ecf3cd28f239436949c`。完整读过Real.lean第1–484行和Integrable.lean第1–131行，包含import/namespace/section/open/variable/instance环境。实际使用的是Real.mul_rpow第476–484行和Integrable.congr第126–128行；包中相邻congr'系列的重复name元数据没有被当作实际调用声明。mul_rpow只需两个非负底数，指数α没有额外限制；Integrable.congr在Ω及其可测空间、ν与实数连续enorm环境下实例化，不需要Ω拓扑。

25个实参及其调用时环境逐一相符：181/175两项producer；sqrt_nonneg、sq_sqrt、rpow_pos_of_pos、mul_rpow；Integrable.congr、integral_congr_ae、setIntegral_le_integral；μ/ν两项MemLp.const_mul、Measurable.const_mul；one_le_exp_iff、integral_mono_ae、div_pos、rpow_nonneg、integrable_const、integral_const、probReal_univ；choose、choose_spec；exp_pos、div_le_iff₀；wstd上下界两项mul_le_mul_of_nonneg_left。非负底数、正分母、原可积性和概率实例均在各自调用前可用。

## 后续资格门

本轮无数学修改建议，源码审查通过。182自身下列材料全部待补：精确源绑定的实际服务器kernel退出、其成功对象hash、同一对象/实际模块所属索引的完整owner清单、每owner完整TYPE、全部非定理完整VALUE、每owner递归公理列表及白名单核对，以及执行前后保护与源对象绑定。名单必须由实际环境及源码所属映射导出，不能因源码只有一个theorem就预设实际owner数。

后续必须在同一独立审稿上下文内完整读这些新增材料，核对源hash不变、完整接口/实例/let/AE语义和实际owner覆盖，才可给qualified裁决。允许公理仅propext、Classical.choice、Quot.sound；不能以静态搜索无禁词代替递归AX。没有第二次Lean重跑或旧证明复审要求；复用父级成功的精确原始证据即可。

本报告的CORRECT是陈述/证明源码层面结论；182机械状态仍PENDING_SERVER_EVIDENCE，qualified=false。请求模型gpt-6.1-sol、请求推理强度xhigh；实际模型/强度及input/cachedInput/output/reasoningSubset遥测未提供，均记录null，不折算订阅比例。
