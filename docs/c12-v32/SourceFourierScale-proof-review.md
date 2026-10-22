# SourceFourierScale 独立完整源与证明审查

STATUS: **CORRECT**

LEAN_STATUS: **LEAN_FULLY_CHECKED（本模块零定义、两个公开定理及全部私有/生成证明；实际既有 server target/audit 已只读核验）**。这不代表完整 Fourier 比较或任何根目标关闭。

审查者未编写本实现或声明提案，未修改源码、scope、其他 owner 文件或共享缓存；本轮只写本票。完整读取最终221行实现、冻结签名、相关原文和已接受接口，并独立核验现有远端记录；未重复运行成功 Lean 目标，也未运行其它 Lean。

## 精确版本

| 对象 | SHA256 |
|---|---|
| SourceFourierScale.lean（10,314字节，221 LF，无CR/BOM） | `5f31eb92eff8ded33b91f55a59a16de4e58cdd7a9e0514d082a2c4932f5feff0` |
| SourceFourierScale-next-scope.md | `5d0afce4726be7a211e934a6bc3ff72e68fc2e622bc091b1e67ad4abff1773ef` |
| SourceFourierScale-declaration-review.md | `cf3a3a7b298d19ab7549d93f0d9f823c3e4c577987c74859da2a3ee3cb9e41c9` |
| SourceFourierScale-author-receipt.md | `58cae129b670e575e1440ac1100ee38197325570060dc3f4d2496cb95ec9170e` |
| 直接 import SourceTruncationBridge.lean | `05321c22d1b2ea178fbc116178af345f4186bfce51011c8242b4ccfd2e0dd7d1` |
| 使用的 TruncationIntegrals.lean | `d7432b7c579c6e6e0d9980af322437941f59f8f670bebd2dd4770f6cfcf1e234` |

本机 source/scope/声明票/作者 receipt 均实测上述哈希。另独立提取冻结两代码块，对实现两个完整 public header 作忽略空白的比较，2/2精确相同；没有多余隐式参数，`autoImplicit false`，没有 premise 改动。实际远端 `pp.all` 两签名逐项确认同一 ν、n、x、ε、条件ρ、raw矩、实际variance、时间区域和 Nat 减法，没有名称遮蔽或编码替换。

远端 `workspaces/source-fourier-scale` 当前 branch 为 `author/source-fourier-scale`，HEAD `3fb0ba0ede60a785bc7ad448756140df868c20f1`，tracked status clean；该 commit 唯一文件是 `Shao/Probability/SourceFourierScale.lean`。metadata 的旧 HEAD 是提交前记录，final.json 与实际 HEAD 已正确补绑定，并非两个源码版本。

## 原文与实际声明

原 main.tex SHA `beb00f718487e36de433175c97f1d500cb48e7a92ce5bd5ad5d62bb132122d06`；supplement.tex SHA `b99f2ac4d2f39dd39772d98a5702b7a923c2f10f8730a08fc1b4cd6bba4742bd`，本轮再次实测。实际读 main 372–392、546–551、622–625，supplement 524–533、2045–2135、2343–2357、2461–2462、3431–3459。

原源用 ξ=X/(σ√n)，故原ν的二矩是1/n，真实条件 law 是 `ρ = cond ν {|z| ≤ ε/(1+x)}`；条件均值μ不必为零。m2与m3是同一ρ的raw二矩与raw绝对三矩，V是其真实方差，γ=m3/V。实现保留原ν均值0及 `n ∫z² = 1`，没有将ρ中心化或把V换成m2，也不要求原ν全局第三矩。

第一声明从原输入门推出全部九项：m3>0、γ>0、`sqrt(m2)m2 ≤ m3`、m2≤γ²、γ≤2h、`(3/4)nm3 ≤ γ ≤ 2nm3`、nm3≤2r以及γ≤4r，其中h=ε/(1+x)、r=R_n(0)。第二声明另给实际源时间区域 `L2γ² ≤ ((n−i:ℕ):ℝ)m2`、i≤n、L2≥20，推出真实剩余长度及bias/variance输入，不假定目标长度或OddPower差界。

原文D3的严格预算及更小ε支付本票的弱预算和0<ε≤1/2；本票认证较宽弱门下的这两个标量结论，不把弱门称为完整D3。γ尺度和剩余长度的原文方向、常数与依赖未改变。

## 全部证明体

**私有 `sf_raw_lyapunov`（15–41行）：正确。** ρ概率，h2/h3是实际raw积分的真可积性。m2≥0由平方非负得，令b=√m2≥0、b²=m2。逐点非负式

`(|z|−b)²(2|z|+b) = 2|z|³−3b z²+b³ ≥ 0`

给 `3b z² ≤ 2|z|³+b³`。两边以h2.const_mul、h3.const_mul、概率常数可积性明确供应 `integral_mono`；积分常数确为b³，未利用不可积时默认0。代入b³=bm2得bm2≤m3。这个helper允许m2=0，本身不假设严格正性、均值0或第四矩。

**私有 `sf_variance_ratio`（43–52行）：正确。** 从V=m2−μ²得V≤m2。若m2>2V，正N给N(m2−2V)>0；而精确scaled variance identity使它等于Nμ²−NV≤1/4−1/2<0，矛盾，故m2≤2V。N>0是调用处由已接受n≥64推得，没有对未知零数消去或偷加方差比较。此证明足够支付公开2V和4V结论，未声称额外公开更强比值。

**`sourceTruncation_gamma_bounds`（54–159行）：正确。**

1. a=1+x≥1，h=ε/a≥0。实际 sample_size 给n≥64，从而n>0。law_data为完全相同的ρ给概率实例、AE闭cutoff、真实h2/h3；variance_bounds给同ρ的V=m2−μ²、V>0、nμ²≤1/4及1/2≤nV≤4/3。没有新概率或V正性输入。
2. 私有ratio得0<V≤m2≤2V，故m2>0。raw Lyapunov给m3≥√m2 m2>0，随后γ>0。由√m2 V≤√m2 m2≤m3及V>0得√m2≤γ；对非负双方平方才得m2≤γ²，顺序合法。
3. AE cutoff逐点给 `|z|³ = |z| z² ≤ h z²`；两边真可积，故m3≤h m2≤2hV，除V>0得到γ≤2h。AE支撑未误作全域逐点前提。
4. γV=m3的除法取消显式用V≠0，重排给γ(nV)=nm3。以γ≥0乘nV上下界，准确推出(3/4)nm3≤γ≤2nm3。没有颠倒4/3与3/4，没有对m3、r或预算取倒数。
5. paid_moments给nm3≤2R_n(x)/a³；`truncationBudget_scale_one_le`在t=0、c=a≥1取上半，精确是R_n(x)≤a³R_n(0)。a³>0保护分母，所以nm3≤2r，再给γ≤4r。此路线与原文直接截断付款是同对象的合法替代，不使用原ν全局三矩。

**`sourceTruncation_oddPower_scale_inputs`（161–219行）：正确。**

1. 沿用同一固定ρ，并调用上一公开结果给γ>0和m2≤γ²。ell直接定义为Nat n−i；非负实cast乘矩比较后，真实hT给 `L2γ² ≤ ell*m2 ≤ ell*γ²`。
2. 若L2>ell，正γ²使(L2−ell)γ²>0，与上式矛盾。因此L2≤(ell:ℝ)。L2≥20经实序与精确Nat cast得到6≤ell；ell≤n由自然截断减法成立。hi虽非这一步所需，仍保留源时间指标i≤n；未提前把Nat减法换成实n−i。
3. 重新使用同原输入的n>0及variance数据，ratio给m2≤2V；V>0再合法放宽至4V。没有在第二声明中假设该目标。
4. 同ρ的实际漂移付款为n|μ|≤2R/(ε²a)。ε>0、a≥1保护分母；ε≤1/2给2ε≤a，乘非负ε²并结合R≤ε³/8，得到2R≤ε²a/8。故n|μ|≤1/8≤1。此步不借η0或未证Λ支付，也没有把条件μ置0。

## 边界与消费限制

n=0与原归一化不相容；本证明还由旧桥实际导出n≥64。空future i=n给ell=0，与L2≥20、γ>0和hT不相容，因此由源区域本身排除，绝非仅凭大n得剩余长度。hT取等号允许，例如声明票给出的n=4096、ν公平±1/64、x=0、ε=1/2与ell=L2=20正好满足闭时间边界；本实现的序/cast未删除它。

x=0、ε=1/2、预算取等号、原子及非中心条件ρ均保留。Dirac/零V由旧输入门排除，V>0与γ>0均是实际结论。h3仅针对真实条件ρ，helper的所有积分有可积性；不存在用默认积分0满足原题的路径。

旧 SourceTruncationBridge 另给ρ概率/h3、V>0和3/4≤nm2；新第二条给同ρ/n/ell的长度、bias、m2≤4V，足以供应既接受OddPower相应标量输入。OddPower频率仍须另满足该真实γ的闭strip。第二条没有证明T<L2γ²区域、频率域、完整噪声或任何Fourier差界。

## 既有机械证据的独立只读核验

本轮通过当前broker作两次只读记录核验：读取现有JSON、实际audit源/完整输出、对象和source哈希，并作Git读取；没有发射Lean或写远端文件。`check02.json`实际exit0，5.363012172281742秒，stdout/stderr和check02.log均空，source前后均为冻结5f31…；目标命令使用指定4核且真正发射该新module对象。实际olean为851656字节，SHA `181f3e96c2cde028a900a0d7c167ca7e521e1a19b28ac97427b9530e6433ab8b`。

`audit01.json`实际exit0，5.366872431710362秒，stderr空；其stdout哈希与实际45807字节完整日志一致。已读实际audit源，按**owner module**遍历全部导入Shao常量，不按声明namespace、public或root-name过滤；每项实际 `Lean.collectAxioms` 拒绝标准三公理外项。脚本的最低数量门是target≥4，但本票另从完整实际日志独立解析确认：169条唯一DEPENDENCY_DECL、7条唯一TARGET_DECL，无遗漏/重复，全部白名单；169**包含**target7，另有162个前驱，不能误记额外169。

7个target常量全部为theorem，恰为2 public +2 private +3 generated：

```text
Shao.sourceTruncation_gamma_bounds
Shao.sourceTruncation_oddPower_scale_inputs
_private.Shao.Probability.SourceFourierScale.0.Shao.sf_raw_lyapunov
_private.Shao.Probability.SourceFourierScale.0.Shao.sf_variance_ratio
Shao.sourceTruncation_gamma_bounds._proof_1_1
Shao.sourceTruncation_oddPower_scale_inputs._proof_1_1
Shao.sourceTruncation_oddPower_scale_inputs._proof_1_2
```

两public实际 `pp.all` 类型完整读取，实际公理为propext、Classical.choice、Quot.sound；private与generated亦全部审计。独立本地public header比较2/2吻合，完整源码禁用token扫描零命中；没有def/axiom/unsafe/native_decide/sorry/admit。

| 现有server工件（work/source-fourier-scale/） | 实测SHA256 |
|---|---|
| check02.json | `3436086967d69e50103190a19f05545640be153e53126e3946d27ed65f1adeb5` |
| check02.log（0字节） | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| Audit.lean（与本地audit源相同） | `073123c1bc5a16e7178a7e74aab52aee7f2d3b4b482d249ffbe3432b339f03b2` |
| audit01.json | `fe749a9d0baf82786417cf2567f24502e6be8ea8366ceefd1862e1006678b317` |
| audit01.stdout | `77c2287af5f61d1ef6373b9e1a9804ae32cc0f780e8ba3cb7cd5c2ea03d4f797` |
| metadata.json | `b4eb2813ead973061106da267316d3d84c9ec7f4cb9f95ceff8b3b7a9dc25e9b` |
| final.json | `54b7ff9ac6518bbaecf4cbb159912fd5c7925a15a69dee57c68855046212ff0e` |

记录绑定固定Lean4.36.0-rc1、compiler commit `c9afcddf514a6772bd4d649f7cfc04eff0b9f15e`；实际lean-toolchain文本/哈希 `d581a24b57a4ae9e0b2132ca8ac7cc3ac336a9fc2751fe6b29414e2d434d54c4`，manifest哈希 `40e8e3385f2b0c8ae56fa9de6947301472379cb62eeb83247944827c38b8af6e`。实际Mathlib HEAD与manifest/metadata均为 `807d3836b165983210ee2ecf3cd28f239436949c`，tracked diff空；没有为审查重跑版本命令。

完整10文件project closure的当前source均与metadata一致。9个前驱还逐项与已接受base `dfd521e6ed80b37c7e0b4280395daf1f7c1ec881` 的Git blob比较相同，并与本地已接受library哈希逐项一致；metadata中的两个旧bridge、根import、public manifest及两pins共6项也实际与base原字节相同。SourceClockBridge的 `ced48edd…` 被保留但未导入本模块。没有将缓存对象存在当作源审查替代。

## 最终裁决

未发现关键数学、形式声明或机械绑定缺口。接受上述冻结源码的完整两个标量桥及其全部helper；root可进行根import/两public manifest和整库集成门。作者receipt中的independent PENDING由本票补齐，作者票不被当作自我认证。

完整噪声K/Ξ及导数、各频区/时间求和、复杂倾斜、Fourier反演、平滑与去平滑、C1/C2及所有其他完整根仍OPEN。本票不修改既有SourceTruncationBridge、SourceClockBridge、OddPower或任何原源条件。
