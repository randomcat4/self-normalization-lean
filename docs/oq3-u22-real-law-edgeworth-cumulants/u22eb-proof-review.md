STATUS: CORRECT

JUSTIFICATION: 已完整读取并独立核对 EB213 的 248 行最终源、两个完整冻结公共头、四个声明内 let 值、全部三个实际所属 TYPE、零非 theorem VALUE、既有成功内核/同首次对象递归公理审计和两个旧输入的完整接口。冻结范围内证明完整，没有发现关键缺口。此裁决只接受真实投影矩的指数到多项式误差桥，不扩大为实际特征函数误差、原六阶 Edgeworth 展开或原 OQ3 B/D 根目标闭合。

## 审核身份与精确范围

- 审核者：fresh 独立非作者上下文 `/root/oq3_eb213_final_review`；分派模型/推理强度 `gpt-6.1-sol/xhigh`，未切换模型、未派生子上下文。
- 使用 `math-theorem` 的独立验缝协议，未使用 math-ultra。依据当前 AGENTS 的 OQ3 明确恢复条款和 `coordination/resource-reallocation-20261027/OQ3-RESUMPTION-PHASE-40.json`；不沿用已撤销的 OQ3 暂停条款。
- 唯一写入职责为本报告。未修改源、冻结、其他报告或协调状态；未运行本地/服务器 Lean、未写服务器、未重放旧证明/成功检查。
- 完整新源为 `drafts/oq3/u22eb-source.lean:1–248`。下文“源 Lx”均指这份精确文件的 1 基行号。
- 来源完整阅读范围为只读 `C:/game/shao/current/oq3/proofs/r2/report.md:1–158`（含第 1、2 节）和 `C:/game/shao/current/oq3/verdict.md:1–58`。旧 DJ195/EA212 只消费完整公共接口及全部接口内 let 值并核对精确合格绑定；没有重读其旧证明或旧审核报告。

## 精确字节与旧证据复用

以下 SHA256 均由本次本地只读计算核对。新源为 UTF-8、11519 字节、248 LF、0 CR；冻结为 2254 字节、39 LF、0 CR。提取源中两个 theorem 的完整头，只去掉各自末尾 ` := by`、按原空行拼接并去掉文件末尾空白后，与冻结文本逐字符一致；四个声明内 let 均包含在该比较中。

| 工件 | SHA256 |
| --- | --- |
| 新源 `u22eb-source.lean` | `0db2e043da2169510061ea6863a28289b1b3ff79ea414467e90d568193c1c8d2` |
| 冻结 `u22eb-frozen-declaration.lean.txt` | `9a4606e638838e502ab669fe74dc57bb53f48cb56533ad7a1794d95f62d25f65` |
| 范围 `two-hundred-thirteenth-unit-scope.md` | `901313a697e9407d3df88a9978fef245562f3a74cb632405e4963da7571693a4` |
| 全实际类型 `u22eb-actual-types.txt`（2456 字节/41 LF） | `5cb17f101e49f768a4b00662cc2d9f7c7e3107c6062d48693f0480b39a5d1500` |
| 服务器收据 `u22eb-receipt.json` | `17fd28cf932e2cf7f299b2124be4b7935e0155191e5661552dc4ef7092958542` |
| 审计源码 `u22eb-Audit.lean` | `8157d7afab6493d8d8c9f077aa1e6bc330652ab994902cdb8534d977f3be609a` |
| 审计记录 `u22eb-audit-record.json` | `c8e52901a5eadf63918e1286da9c9e518d577c0ab8563cb784f590bce28f075e` |
| 构建历史 `u22eb-build-history.json` | `6f00433599d47db0bf2d0093cf1474e43934a017dd952050bb740fa89a83b3d9` |
| 合格输入绑定 `coordination/handoffs/20261024/oq3-handoff.json` | `b384f7df697f09c404497d28affb6780be966193a6dd2834b4b2333fead0469e` |
| 来源 `report.md` | `572e74aa9c12e2771f5543a5709a2807666eeea0a4076e7a3263e5c7bcf87f55` |
| 来源 `verdict.md` | `fd0a5732845aa96ab1725e6d1e52676502092e49d2c00225ce1fde26ac06f3b5` |

旧输入的 source/type/receipt/review 文件实际哈希全部与 handoff 的选定合格字段一致；旧收据保留其写成时的 `AUTHOR_PASS_PENDING_FRESH_COMPLETE_REVIEW` 文本，后续独立审核完成与合格状态从 handoff 精确记录复用，不据此重跑旧证明。

| 输入 | 已核对的精确绑定 |
| --- | --- |
| DJ195 `PairProjectionAbsoluteMoments` | source `19cc0b3b4d191ad64745541503822fbb85bfaebf094229995b5d914e009713f9`；TYPE `a710ed7aeec4232fc3e0502dd3e4f545d408a888d0bb340a1042cce3c500da9d`（10 LF）；receipt `220ec0bac89061d4160c65ca462cb01a575a55f812f158ac53befeae706edd9f`；旧独立 review `3dc8928583aa782d48378d2e0334364025bad27dac1b1bf2c1820a512e6779aa`；首次 O `488fc0f7d3f5f9a5bc488d2ec3942b5e726182dedfabb83d5b64fc6e2238dc1d`。 |
| EA212 `ImaginaryRealExponentialQuadraticError` | source `242616bff5479661e3f510156ae458608ac80ff12c8370bbab59a09ab8413304`；TYPE `c0ebf7e7d218a21ecca2750526c14f6ec6c55eba543185d8e53dbb9a52f49144`（6 LF）；receipt `72b15e4fa37a6ff5a354b407dfecf241e2a7b3ce2de52d124c4a986638f3952f`；旧独立 review `82a267009bb1789157f46309d905b60fec4b74f30fae5903bb26f486cd35892c`；首次 O `f4d3ff1992769f056fe3d014d8ad23d8e062b7b6a0be3e39a4ef51b42c78b4ca`；handoff `COMPLETE_QUALIFIED`、reviewer completed/stopped。 |

DJ195 完整消费的接口是：任意 measure、任意自然数 m，若真实二维欧氏径向 m 次幂可积，则 `f y := |u*y 0+v*y 1|^m` 可积，真实积分非负，且积分至多 `r^m` 乘真实径向矩。唯一接口 let `f` 已完整消费，未把 `Fin 2 → ℝ` 的其他范数替成欧氏半径。EA212 没有 let/额外前提；完整接口对所有实 b,c 给出

`‖exp(b*I+c) − (1+b*I−b²/2+c)‖ ≤ (exp 1+4)|b|³+(exp 1+2)|c||b|+c² exp|c|`。

## 自然来源到精确声明

原 `report.md` 第 1 节定义实际倾斜律、均值/协方差，第 2 节 L83–87 定义实际标准化 `Y_theta` 与 iid 和 `Z_n,theta`；L133–134 的原目标是直到 `n^-3` 的二维六阶 Edgeworth 符号测度。本单元只实现其低频展开的一段代数/积分承重桥。

源 L8–15 的第一个声明对任意二维 measure 和任意自然数 m 证明真实带符号投影幂的 Bochner 可积性与真实积分的绝对值界，不预设该带符号投影幂可积。源 L28–57 的第二个声明只有同一族 `law i` 的三、四阶真实径向可积性和统一积分上界四项前提；没有任意误差函数、自由系数、特征函数近似、高斯衰减或相容性前提。

四个 statement let 的完整值逐项检查如下。

1. `m3 i u v`（源 L38–39）是同一 `law i` 下 `(u*y 0+v*y 1)^3` 的真实积分。
2. `m4 i u v`（源 L40–41）是同一 `law i` 下同一投影的四次幂真实积分。
3. `Qn`（源 L42–45）恰为 `−S/2 − I*m3/(6√n) + (m4−3S²)/(24n)`。减项 `3S²` 在积分外，没有被错误地积分成质量倍数。
4. `Pn`（源 L46–50）恰为 `exp(−S/2) [1−I*m3/(6√n)+((m4−3S²)/24−m3²/72)/n]`；真实平方修正为 `−m3²/(72n)`。

两个矩函数不是独立自由参数；`Qn/Pn` 也不是可任意选择的参数。全部绑定到声明内给出的真实积分。同样，本引理允许一般 measure，未声称此一般 measure 已中心化、协方差已标准化或 `exp Qn` 已等于实际特征函数；这些识别由实际来源消费者承担。其较一般的 measure 量词使当前纯指数桥成立，不把概率识别偷偷当成前提。

## 完整证明逐段复核

**真实投影积分，源 L16–26。** 记 `L(y)=u*y0+v*y1`、`R(y)=sqrt(y0²+y1²)`、`r=sqrt(u²+v²)`。DJ195 给出 `|L|^m` 可积及其积分界。`L^m` 连续，因而几乎处处强可测；点态 `‖L^m‖=|L^m|=|L|^m` 使 `Integrable.mono'` 得到带符号幂可积。随后

`|∫L^m| ≤ ∫|L^m| = ∫|L|^m ≤ r^m ∫R^m`。

因此实际 Bochner 积分没有依赖不可积函数的总化约定。m=0、u=v=0 均在声明和证明中覆盖。

**统一常数和量词，源 L58–94。** 取

`A=|M3|+1, B=|M4|+4, a=exp 1+4, d=exp 1+2, C=a A³+d B A+B²+1, delta=min(1,1/(8B))`。

所有需要的常数严格为正，`0<delta≤1`，且 `B delta≤1/8`（L65–78）。见证 C、delta 先在 L78 构造，再于 L79 引入所有 n、`hn`、i、u、v 和半径约束；C、delta 实际仅依赖 M3/M4，不依赖 n/index/frequency。L80–94 设置 `S=u²+v², r=√S, s=√n, b=−m3/(6s), c=(m4−3S²)/(24n)`，并从 n≥1 得到 `s>0, s²=n, s≥1, s≤n, n*s>0`。没有在 n=0 除法上取得估计。

**实际系数界，源 L95–134。** 第一个新定理与各自 hI/hM 给出 `|m3|≤A r³`、`|m4|≤|M4|r⁴`。用 `S²=r⁴`、三角不等式和 B 的定义得到 `|m4−3S²|≤B r⁴`（L107–113）。除以严格正的 `6s`、`24n` 后，舍弃有利的 1/6、1/24，得到 `|b|s≤A r³`、`|c|n≤B r⁴`。这两项界来自真实矩，而非额外假设。

**半径吸收，源 L135–150。** 由 `r≤delta*s` 平方并用 `delta²≤delta` 得 `r²≤delta*n`。于是

`|c|n ≤ B r⁴ = (B r²)r² ≤ B delta r² n ≤ S n/8`。

以 n>0 消去 n，确得 `|c|≤S/8`。没有要求 b 小，也没有把 c 的小性作为声明前提。

**三个误差幂与分母，源 L151–172。** `s²=n` 使

`|b|³(n*s)=(|b|s)³≤A³r⁹`；

`|c||b|(n*s)=(|c|n)(|b|s)≤BA r⁷`；

`c²(n*s)≤c²n²=(|c|n)²≤B²r⁸`，其中第三式唯一额外放大使用 `s≤n` 和 c²n≥0。

因此三项均具有同一 `n√n` 分母；r 的幂依次为 9、7、8，没有丢失边界小频幂次。

**高斯权重，源 L173–188。** 设 `H=exp(−S/2)>0`、`G=exp(−S/8)>0`。由 S≥0 得 H≤G；由 `|c|≤S/8` 得 `−S/2+|c|≤−3S/8≤−S/8`，故 `H exp|c|≤G`。将非负项分别相乘得到

`H [a|b|³+d|c||b|+c² exp|c|] ≤ [a|b|³+d|c||b|+c²] G`。

**统一多项式常数，源 L189–210。** C 同时支配 `a A³, d B A, B²`，三个 r 幂非负，所以由前述三项界推出

`[a|b|³+d|c||b|+c²] (n*s) ≤ C(r⁷+r⁸+r⁹)`。

这也覆盖 r=0；没有只为 r≥1 证明较弱结论。

**实际多项式识别与结尾，源 L211–245。** L211–213 给出复数域中 s,n 非零及 `s²=n`；L214–217 的 hQ 精确展开 `Qn=−S/2+bI+c`。L218–226 的 hP 使用 `b²/2=m3²/(72n)`，所以 `Pn=exp(−S/2)(1+bI−b²/2+c)`，符号、24、72 和所有实/复强制转换均与冻结值一致。L227–235 由复指数加法公式提取因子，且其范数恰为 H。L236–245 完整调用 EA212 的全局 b,c 结论，依次应用高斯吸收、统一多项式界、严格正分母，得到冻结的

`‖exp(Qn)−Pn‖ ≤ C(r⁷+r⁸+r⁹)/(n√n) exp(−S/8)`。

**边界与隐含条件。** n=1、零频率、m=0、零/非概率 measure 及空索引类型不要求额外分支；可积性或量词保证相应语义。M3/M4 无须额外非负前提，A/B 的绝对值使见证始终有效。证明中没有概率独立性、中心化或协方差前提被暗中调用；它们属于后续实际 CF 绑定，不属于本指数桥。源全文扫描 `sorry/admit/axiom/unsafe/native_decide` 均为零。

## 全部实际 TYPE、let、VALUE 与递归公理覆盖

已完整阅读以下 41 LF 实际类型输出；逐项覆盖 2 个公共 theorem、1 个生成 theorem。公开两个类型与冻结两个完整头一致，四个 let 全部出现在第二个公开类型中；源 L59–64、L80–84、L173–174 的全部证明内 let 也已在上文推导中逐一核对。

```text
DECL Shao.OQ3.uniform_pair_moment_edgeworth_exponential_error
TYPE ∀ {ι : Type u_1} (law : ι → MeasureTheory.Measure (Fin 2 → ℝ)) (M3 M4 : ℝ),
  (∀ (i : ι), MeasureTheory.Integrable (fun y => √(y 0 ^ 2 + y 1 ^ 2) ^ 3) (law i)) →
    (∀ (i : ι), ∫ (y : Fin 2 → ℝ), √(y 0 ^ 2 + y 1 ^ 2) ^ 3 ∂law i ≤ M3) →
      (∀ (i : ι), MeasureTheory.Integrable (fun y => √(y 0 ^ 2 + y 1 ^ 2) ^ 4) (law i)) →
        (∀ (i : ι), ∫ (y : Fin 2 → ℝ), √(y 0 ^ 2 + y 1 ^ 2) ^ 4 ∂law i ≤ M4) →
          have m3 := fun i u v => ∫ (y : Fin 2 → ℝ), (u * y 0 + v * y 1) ^ 3 ∂law i;
          have m4 := fun i u v => ∫ (y : Fin 2 → ℝ), (u * y 0 + v * y 1) ^ 4 ∂law i;
          have Qn := fun i n u v =>
            -↑(u ^ 2 + v ^ 2) / 2 - Complex.I * ↑(m3 i u v) / (6 * ↑√↑n) +
              ↑(m4 i u v - 3 * (u ^ 2 + v ^ 2) ^ 2) / (24 * ↑n);
          have Pn := fun i n u v =>
            Complex.exp (-↑(u ^ 2 + v ^ 2) / 2) *
              (1 - Complex.I * ↑(m3 i u v) / (6 * ↑√↑n) +
                ↑((m4 i u v - 3 * (u ^ 2 + v ^ 2) ^ 2) / 24 - m3 i u v ^ 2 / 72) / ↑n);
          ∃ C delta,
            0 < C ∧
              0 < delta ∧
                delta ≤ 1 ∧
                  ∀ (n : ℕ),
                    1 ≤ n →
                      ∀ (i : ι) (u v : ℝ),
                        √(u ^ 2 + v ^ 2) ≤ delta * √↑n →
                          ‖Complex.exp (Qn i n u v) - Pn i n u v‖ ≤
                            C * (√(u ^ 2 + v ^ 2) ^ 7 + √(u ^ 2 + v ^ 2) ^ 8 + √(u ^ 2 + v ^ 2) ^ 9) / (↑n * √↑n) *
                              Real.exp (-(u ^ 2 + v ^ 2) / 8)
AXIOMS [propext, Classical.choice, Quot.sound]
KIND theorem
DECL Shao.OQ3.pair_projection_signed_moment_bound
TYPE ∀ (law : MeasureTheory.Measure (Fin 2 → ℝ)) (m : ℕ),
  MeasureTheory.Integrable (fun y => √(y 0 ^ 2 + y 1 ^ 2) ^ m) law →
    ∀ (u v : ℝ),
      MeasureTheory.Integrable (fun y => (u * y 0 + v * y 1) ^ m) law ∧
        |∫ (y : Fin 2 → ℝ), (u * y 0 + v * y 1) ^ m ∂law| ≤
          √(u ^ 2 + v ^ 2) ^ m * ∫ (y : Fin 2 → ℝ), √(y 0 ^ 2 + y 1 ^ 2) ^ m ∂law
AXIOMS [propext, Classical.choice, Quot.sound]
KIND theorem
DECL Shao.OQ3.uniform_pair_moment_edgeworth_exponential_error._simp_1_1
TYPE ∀ {M : Type u_2} [inst : Monoid M] (a : M) (m n : ℕ), (a ^ m) ^ n = a ^ (m * n)
AXIOMS []
KIND theorem
```

生成项 `_simp_1_1` 是任意 Monoid 上的幂乘指数恒等式，无新增数学前提，递归公理为空；其类型已完整检查。`all_owned=all_theorems=3`、`non_theorem_values=0`，所以不存在未覆盖的非 theorem 定义 VALUE、opaque/foreign-prefix 所属值或私有定义。没有输出庞大的 theorem proof value。

完整读过的 `u22eb-Audit.lean:1–47` 先确认两个冻结名称都是 theorem，再遍历环境的实际 module-owner（非仅名称前缀），拒绝新 axiom，逐项调用 `Lean.collectAxioms` 并白名单检查，打印全部 TYPE、theorem KIND 和所有 defn VALUE，最后检查两个目标数与非空 owner。实际输出三个声明全部为 theorem，与记录/收据一致；两公共 theorem 的传递公理恰为 `propext, Classical.choice, Quot.sound`，生成项为空。记录修复仅移除了 `AXIOMS []` 解析所得空 token；实际 Lean 审计未重跑。此修复不增删数学依赖。

## 既有服务器机械证据与失败保留

本次复用精确服务器成功收据，不把本报告的只读检查描述成新的 Lean 执行。项目钉死 `Lean 4.36.0-rc1 / mathlib 807d3836b165983210ee2ecf3cd28f239436949c / shared-v34`。成功 native03 记录为 `RC0, 23.378566477447748s`；源 SHA 与本审核源一致。首次原始 O 为 `9171846c823c6d71daf10eb19df5c1d55575392735e44beb756b65896def8ce2`、1851536 字节；同原始 O 的全 owner 审计 `RC0, 5.818529320880771s`。native 日志 SHA `c62a1b9ca514e737283ccc94f767ebddf5d88804244f5ae60b3df4535e9abb2f`/398 字节，审计日志 SHA `7eb80461d1b2f1931d201683c2c8a1d35b145a43a9d5f3e36480039480084edb`/2708 字节。

收据与审计记录的所有共享字段一致；收据中的完整构建历史与 `u22eb-build-history.json` 一致。native01 为 SHA `90daa24f6088e7b87c7ebec6b06007f51223e60cbb13395d63babb909874c645`、226 LF、RC1，日志 SHA `23ce8f6b3cc6dfa62cde1580a0a87dc02acb9255f8f2980ef6d18c5022d2ab2b`；native02 为 SHA `ab69c57732d2779dcce280e027af5ef915ace0fccb8ad79acaeca646d3457065`、247 LF、RC1，日志 SHA `33265299e69e9208ca3e2bfdfa8c05ae4205432aef59d165872e5afe8a5b79b0`。这些失败未被计为通过，源/全日志保留在服务器 `runs/oq3/u22eb-20261027`；最终完整证明未暴露需要另读失败全日志的未解决风险，本审核未复制全日志或重放失败。

三次 native 与同 O 审计收据均使用 phase40 的 OQ3 CPU36–39/44–47、native `-M8192 -j4`。审计/构建所记 `phase39_memory.py` 的内部旧 phase 标签只是复用相同准入公式，外层 `resourcePhase=ROOT_OQ56_OQ3_40` 与明确恢复资源条款一致；不是对已暂停旧 OQ3 或 C12 的误激活。本次审核没有执行资源变更。

## 接受边界与后续消费者义务

当前两项冻结 theorem 可按精确 source/O/审计证据接受，属于完整 checked 的本单元。后续消费者仍必须把 DY210 的实际 `PhiScaled^n → exp Qn` 误差与本桥合成，并保留 DZ211 的完整 SAME single E/真实 product-map rho 数据包；本文件没有消费或重证该完整数据包，不能据本审核略去它。

原 strict `0<beta<2/5`、p54 修复、真实标准化律绑定、累积量/CGF 导数识别、全频控制、反演/去平滑、外区原概率估计和 newrho/Laplace 重建均不被本二阶多项式替代。原报告第 2 节的 Angst–Poly 外部定理归属、verdict 的 Song 说明及既有其他来源归属原样保留；本单元不裁决外部定理的全部历史/适用范围，不宣称历史首次或根级新颖性。原 OQ3 B/D 根目标保持 OPEN，既有反例证据保持有效。

审核完成：STATUS `CORRECT`。本报告写者已完成并停止；释放本报告独占写入职责，未持有源写入、服务器执行或后续消费者作者权限。
