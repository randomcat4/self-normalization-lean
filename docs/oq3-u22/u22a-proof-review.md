# OQ3 U22a 独立完整审查

## 不可改写的盲译前缀

本前缀在读取当前证明、单元范围、作者回执及证明说明前写入。首个数学输入仅为 `u22a-actual-types.txt`：49 行，3109 字节，SHA256 `4c6d4ab35fb2f7e24be183aeab1e3c7b30d90a6a54aeec6c0691e598d4094c7a`。此处记录新鲜独立的量词、语义、边界和待核疑点；其后只能追加审查结果，不能改写本前缀。审查者承担完整 source-to-statement、数学证明、实际 TYPE 及传递公理审查；不作新颖性裁决。

### 实际 TYPE 原文（全部四项）

```text
DECL _private.Shao.OQ3.QuadraticTiltCumulants.0.Shao.OQ3.quadratic_tilt_projection_interior
TYPE ∀ (mu : MeasureTheory.Measure ℝ) [MeasureTheory.IsProbabilityMeasure mu] (theta d : ℝ × ℝ),
  theta ∈ interior (Shao.Probability.bivariateMGFDomain mu fun x => (x, x ^ 2)) →
    0 ∈
      interior
        (ProbabilityTheory.integrableExpSet (fun x => d.1 * x + d.2 * x ^ 2)
          (mu.tilted fun x => theta.1 * x + theta.2 * x ^ 2))
AXIOMS [propext, Classical.choice, Quot.sound]
DECL Shao.OQ3.open_domain_quadratic_tilt_directional_cumulants
TYPE ∀ (mu : MeasureTheory.Measure ℝ) [MeasureTheory.IsProbabilityMeasure mu],
  ∀ theta ∈ interior (Shao.Probability.bivariateMGFDomain mu fun x => (x, x ^ 2)),
    have nu := mu.tilted fun x => theta.1 * x + theta.2 * x ^ 2;
    have means := ![∫ (x : ℝ), x ∂nu, ∫ (x : ℝ), x ^ 2 ∂nu];
    have D := Shao.OQ3.parabolaCovariance nu;
    MeasureTheory.IsProbabilityMeasure nu ∧
      MeasureTheory.MemLp (fun x => x) 2 nu ∧
        MeasureTheory.MemLp (fun x => x ^ 2) 2 nu ∧
          ∀ (d : ℝ × ℝ),
            have F := fun x => d.1 * x + d.2 * x ^ 2;
            have f := fun t =>
              Real.log (∫ (x : ℝ), Real.exp ((theta.1 + t * d.1) * x + (theta.2 + t * d.2) * x ^ 2) ∂mu);
            0 ∈ interior (ProbabilityTheory.integrableExpSet F nu) ∧
              MeasureTheory.MemLp F 2 nu ∧
                (∀ (k : ℕ), MeasureTheory.Integrable (fun x => F x ^ k) nu) ∧
                  HasDerivAt f (d.1 * means 0 + d.2 * means 1) 0 ∧
                    HasDerivAt (deriv f) (d.1 ^ 2 * D 0 0 + 2 * d.1 * d.2 * D 0 1 + d.2 ^ 2 * D 1 1) 0
AXIOMS [propext, Classical.choice, Quot.sound]
DECL _private.Shao.OQ3.QuadraticTiltCumulants.0.Shao.OQ3.quadratic_tilt_variance_eq
TYPE ∀ (nu : MeasureTheory.Measure ℝ) [MeasureTheory.IsProbabilityMeasure nu],
  MeasureTheory.MemLp (fun x => x) 2 nu →
    MeasureTheory.MemLp (fun x => x ^ 2) 2 nu →
      ∀ (a b : ℝ),
        ProbabilityTheory.variance (fun x => a * x + b * x ^ 2) nu =
          a ^ 2 * Shao.OQ3.parabolaCovariance nu 0 0 + 2 * a * b * Shao.OQ3.parabolaCovariance nu 0 1 +
            b ^ 2 * Shao.OQ3.parabolaCovariance nu 1 1
AXIOMS [propext, Classical.choice, Quot.sound]
DECL Shao.OQ3.quadratic_tilt_mgf_identity
TYPE ∀ (mu : MeasureTheory.Measure ℝ) [MeasureTheory.IsProbabilityMeasure mu] (theta d : ℝ × ℝ),
  (theta ∈ Shao.Probability.bivariateMGFDomain mu fun x => (x, x ^ 2)) →
    have nu := mu.tilted fun x => theta.1 * x + theta.2 * x ^ 2;
    have F := fun x => d.1 * x + d.2 * x ^ 2;
    have Z := fun p => ∫ (x : ℝ), Real.exp (p.1 * x + p.2 * x ^ 2) ∂mu;
    MeasureTheory.IsProbabilityMeasure nu ∧
      0 < Z theta ∧
        ∀ (t : ℝ),
          (MeasureTheory.Integrable (fun x => Real.exp (t * F x)) nu ↔
              (theta.1 + t * d.1, theta.2 + t * d.2) ∈ Shao.Probability.bivariateMGFDomain mu fun x => (x, x ^ 2)) ∧
            ProbabilityTheory.mgf F nu t = Z (theta.1 + t * d.1, theta.2 + t * d.2) / Z theta
AXIOMS [propext, Classical.choice, Quot.sound]
```

### 逐项独立盲译

1. **私有 `quadratic_tilt_projection_interior`。** 对任意实数上的概率测度 `mu`、任意二维实参数 `theta` 与任意方向 `d`，若 `theta` 属于抛物线随机向量 `(x,x²)` 的真实二维矩母函数积分域的内部，则对指数倾斜测度 `nu = mu.tilted (theta₁x+theta₂x²)`，标量随机变量 `F=d₁x+d₂x²` 的指数可积参数集以 `0` 为内点。内部应为现有乘积拓扑与实拓扑的内部，不能把沿某条线的可积性冒充二维内部。该项没有有界性、中心化、原子数、非退化性或正定性前提；也没有要求 `d≠0`。

2. **公开 `open_domain_quadratic_tilt_directional_cumulants`。** 对任意 `mu` 概率测度及其真实二维积分域任意内点 `theta`，定义上述实际倾斜测度、均值向量 `(∫x dnu,∫x² dnu)` 与 `D=parabolaCovariance nu`。结论首先是 `nu` 真为概率测度，`x` 和 `x²` 均属 `L²(nu)`；随后对每个实方向 `d`，`F` 的指数可积集在零附近含开邻域，`F∈L²(nu)`，每个自然数 `k` 的 `F^k` 都真正可积。若 `f(t)=log∫exp((theta₁+td₁)x+(theta₂+td₂)x²)dmu`，则 `f` 在零的一阶导数为 `d₁ E_nu x+d₂ E_nu x²`，而 `deriv f` 在零的导数为 `d₁²D₀₀+2d₁d₂D₀₁+d₂²D₁₁`。这是每条固定参数线上的两个 `HasDerivAt`，实际 TYPE 没有宣称完整二元 Fréchet Hessian 或局部均值逆。

3. **私有 `quadratic_tilt_variance_eq`。** 对任意实数上的概率测度 `nu`，只要 `x,x²∈L²(nu)`，则对全部 `a,b∈ℝ`，`a x+b x²` 的方差等于由 `parabolaCovariance nu` 的三个矩阵元组成的二次型 `a²D₀₀+2abD₀₁+b²D₁₁`。不能偷用零均值；必须核对 `D` 确是中心化协方差矩阵，方差与各乘积积分的展开具有实际可积性。允许协方差奇异、点质量、`a=b=0`。

4. **公开 `quadratic_tilt_mgf_identity`。** 对任意概率测度 `mu`、任意 `theta,d∈ℝ²`，仅假设 `theta` 属真实二维积分域（不要求内点）。令 `Z(p)=∫exp(p₁x+p₂x²)dmu`，则 `nu` 是概率测度、`Z(theta)>0`；对所有实数 `t`，`exp(tF)` 在 `nu` 下可积，当且仅当 `theta+td` 属于原二维积分域；并且标量矩母函数等于 `Z(theta+td)/Z(theta)`。这里量词是全部 `t`，比值恒等式没有另写域内条件，故须按 Lean 实值积分在不可积情形的全定义约定审查，不能把它误译为域外有限的经典矩母函数。正分母只由基点条件保证，不能假设所有 `t` 都在域内。

### 盲译阶段的边界与核疑点

- 以上四项均保留任意实概率分布，特别是非中心、无界和退化分布；内部假设只出现在第 1、2 项。`d=0` 与自然幂 `k=0` 必须保留，域外导数没有被声明。
- 尚未读定义：需核对 `bivariateMGFDomain` 是实际指数积分有限/可积域、`tilted` 是归一化指数倾斜、`parabolaCovariance` 的真实中心化定义。若命名与定义不符，以上意图解释应判为语义缺口，而非回写此前缀。
- 第 4 项须把倾斜测度的真实积分变换与双向可积性分开验证，并覆盖不可积处实值积分归零的语义；不得仅以形式指数恒等式或分母非零代替。
- 第 1、2 项须由二维内点与连续参数线得到一维 `0` 内点，再调用真实矩母函数/累积量母函数接口推出矩及导数，不能把所需光滑性藏进假设。
- 第 2 项 `HasDerivAt (deriv f)` 中 `deriv` 本身是全定义运算；需特别检查证明先取得合法邻域内 `f` 与真实累积量母函数的关系，并在邻域转移其一阶导函数，避免用不可微点的默认导数值制造空洞二阶陈述。
- 四份 AXIOMS 行目前只是输入声称的标准三公理；必须在数学审查后核对完整声明覆盖与来源绑定，不能代替逐义审查。

<!-- BLIND_PREFIX_END：此标记及此前所有字节冻结。 -->


## 独立数学与实际 TYPE 审查（先于机械证据）

本节完成时尚未读取作者 receipt、build-history、audit-record、Audit 源或环境变更记录。已完整逐行读完当前 165 行实现及 56 行冻结范围；只读原来源 R2 `report.md` 38–60、83–92 和 `root-contract.md` 第 2、4 节。未读作者的后续证明计划、domination notes、其他 next/future 文件或旧审查票。冻结前缀的完整字节 SHA256 为 `f4640f12f3bf615fb2c9adda1d1de33b6c4f513561c70e4e46d2afd6ea6a7b55`。

### 定义、原意与声明覆盖

- `library/Shao/Probability/BivariateLegendre.lean` 20–22 将二维域定义为字面的 `Integrable (exp (theta₁(W x)₁+theta₂(W x)₂)) mu`，不是自定义 caller 许可集；取 `W x=(x,x²)` 后与本模块的指数完全相同。24–27 的域内 `bivariateLogMGF` 正是同一实值积分的对数。
- `library/Shao/OQ3/RegularCovariance.lean` 20–24 的矩阵对角元分别是 `Var(x)`、`Var(x²)`，两个非对角元是 `Cov(x,x²)`。这里确为中心化协方差矩阵。该文件后续某些其他引理的有界假设没有进入此定义或本模块任何声明。
- pinned Mathlib `Tilted.lean` 42–43 的 `Measure.tilted` 是以 `ofReal(exp(g(x))/∫exp(g)dmu)` 为密度的实际测度；在 `Z(theta)>0` 后，这与 R2 的 `exp(theta·W-K(theta))` 密度一致。不是一个自由选择的概率测度。`IntegrableExpMul.lean` 112–113、`Basic.lean` 122–127 分别确认一维真实指数可积域、真实 mgf 和真实 cgf 的字面定义。
- 冻结范围的两个公开完整签名与源文件 11–23、84–104 的签名逐义一致，实际输出中的 `have`/源中的 `let` 仅为展开显示差异。私有声明另有且仅有两个，分别承担拓扑域和方差展开；盲译逐项覆盖了它们。没有把公开二阶方向结论误称为完整 Hessian。
- 原来源 R2 41–45、50–60 要求同一实际律的 K、倾斜均值/协方差，并在参数的开邻域保证有限；根契约第 2 节明确禁止域外积分默认零充当 K 的定义。当前辅助结论在任意概率律下证明这一局部承重关系，因此无须继承原根的中心化、鞍点、正定、WC 等条件；这属于一般局部引理，绝非删掉原根条件后宣称原根成立。R2 83–92 的白化/统一 WC 消费者和根契约第 4 节的完整充分修复均未在本单元被证明。

### 公开积分比与可积等价：源 11–52

令 `g(x)=theta₁x+theta₂x²`，`F(x)=d₁x+d₂x²`。源 28 从真实二维域直接取得 `hf : Integrable (exp∘g) mu`，不是一个目标性假设。原测度为概率测度，故非零；Mathlib `Tilted.lean` 126–136 在这个精确 `hf` 下给出倾斜概率，`integral_exp_pos hf` 给出有限实数 `Z(theta)>0`。所以此处不会触发 `tilted_of_not_integrable` 的零测度回退。

源 32–43 用 `integrable_tilted_iff hf` 将 `exp(tF)` 在真实倾斜律下的可积性等价为 `exp(g)·exp(tF)` 在原律下可积；所核 API `Tilted.lean` 293–309 没有额外的有界、中心化或非退化条件。随后点态 `exp(g) exp(tF)=exp((theta+td)·W)` 由 `exp_add` 与实数环恒等式证明，因此确是双向等价，不是只证一边或只比较已可积的两项。

源 44–52 使用 Mathlib 236–249 的无条件 `integral_exp_tilted`，然后用同一指数环恒等式得到全部实数 `t` 的比值。全 `t` 陈述忠实于 Lean 的实值 Bochner 积分：域外两侧的对应指数积分均不可积，实积分值为零，等式仍成立；它不提供域外有限 mgf 或域外可微性。公开结果同时给出了可积等价，后续只在真可积邻域使用比值。正分母没有被当作“所有移点均可积”的依据。

### 私有投影内部：源 54–67

源 60 在基点取得已证积分比/可积等价；61–63 证明连续映射 `L(t)=(theta₁+td₁,theta₂+td₂)` 在 `0` 收敛到 `theta`。由于 `theta` 位于真实二维域内部，其内部是 `theta` 的邻域；65 将此邻域沿连续参数线拉回，66–67 通过已证双向可积等价转成 `t∈integrableExpSet F nu`。最后 `mem_interior_iff_mem_nhds` 正确给出 `0` 是该一维集的内点。没有用二维域内一条线的存在性倒推二维内部；也不需要非零方向。

### 矩、均值与方差：源 69–82、106–128

源 108 建立真实 `nu` 的概率实例，然后 109–115 用两个坐标方向 `(1,0)`、`(0,1)` 的已证零内点及 Mathlib `IntegrableExpMul.lean` 526–534 得到 `x,x²∈L²(nu)`。对任意 `d`，122–124 得到 `F∈L²(nu)`，157 则调用 518–522 的全自然幂可积定理。这里的 `Integrable` 本身要求绝对可积，因此不是奇次幂的条件收敛，也没有为原始未倾斜 `mu` 添加高阶矩。

源 125–128 的期望线性化在 `integral_add` 前分别用 `h1.const_mul`、`h2.const_mul` 和概率测度下 `2≥1` 推出真实 `L¹`；两个均值因此是普通有限期望。它没有将不可积积分的默认零值当作线性运算。

私有方差恒等式先持有两个坐标 `L²`，源 79 用 `variance_fun_add (h1.const_mul a) (h2.const_mul b)`，再用方差二次缩放、协方差左右线性缩放和环整理。核对的 pinned API 是 `Variance.lean` 207–209、272–274 和 `Covariance.lean` 136–140；`Covariance.lean` 44–45 是真正的中心化积积分，54–66 的矩差公式明确通过两个 `L²` 保证乘积和均值各项可积。矩阵定义正好给出本目标的三个系数。既未用 `E x=0`，也未要求矩阵正定或可逆。

### 真实 cgf 导数及局部转移：源 129–162

1. 由真实 `h0`，源 129 用 Mathlib `MGFAnalytic.lean` 171–175 得到真实 `cgf F nu` 在零解析；130–133 用 201–202 的 `deriv_cgf_zero` 及 `nu` 为概率（总质量一）取得 `HasDerivAt cgf (E_nu F) 0`。不是把目标一阶导数当作输入。
2. 源 134–139 用 204–238 的真实二阶 cgf 公式。零点时 `exp(0·F)=1`、`mgf F nu 0=1`，该式化为 `E_nu F²-(E_nu F)²`。最后精确调用 `variance_eq_sub hF` 的反向等式；已核对 `Variance.lean` 226–228 的必要前提正是概率实例和本处已取得的 `F∈L²`。实值方差原本是 evariance 的 `toReal`，有 `L²` 后才是有限的真实方差，故此步没有利用无穷方差被 `toReal` 置零。
3. 源 140–141 从 cgf 在零解析推出其导函数在零解析，再取得 `HasDerivAt (deriv cgf) (Var_nu F) 0`。pinned `FDeriv/Analytic.lean` 468–471 的 `AnalyticAt.deriv` 正是该接口，既非仅有形式 `deriv` 值相等，也非未经证明的光滑性。
4. 源 143–153 先限制到一维真积分域内部的零邻域。每个该邻域内的 `t` 都先经公开可积等价取得移点的真实指数可积性，并由 `integral_exp_pos` 取得 `Z(theta+td)>0`；基点的正性来自公开定理。只有这时才用 `Real.log_div`，得到 `f =ᶠ[𝓝0] (log Z(theta)+cgf F nu)`。所以不存在域外 `log 0` 参与导数推导的步骤。
5. 源 154–156 的 `heq.deriv` 是导函数在整个零邻域最终相等，而非只在单点相等；pinned `Deriv/Basic.lean` 651–652 明确由局部相等推出局部导函数相等。常数项导数消失。158–162 分别用 611–613 的 `EventuallyEq.hasDerivAt_iff` 将两个真实 `HasDerivAt` 转回 `f` 与 `deriv f`，再以已证均值线性化及私有方差恒等式得到声明中的精确值。这同时消除了盲译时对全定义 `deriv` 的疑虑。

### 量词、边界及剩余范围

- `mu` 是任意实概率测度，两个公开定理均无 bounded/centering/atom/WC/SPD 假设；内部假设只按冻结签名出现在方向累积量定理及其私有投影。任意非中心或无界测度，只要实际域条件成立，证明同样适用。若内部为空，第二定理不声称存在参数点。
- `d=0` 时参数线常值、`F=0`、一阶和二阶值均零；所有步骤仍成立，没有除以方向系数。`k=0` 是 `F^0=1`，其可积性由真倾斜概率保证。点质量和奇异协方差允许存在；不需要求逆。`theta` 仅在域内而非内部时，只应用第一公开定理，不主张导数。
- 全部四项实际 TYPE 均已逐义覆盖；两个 private 不是遗漏目标。源中仅有定义展开、测度积分/拓扑/解析标准 API 和实数环整理，没有隐藏新数学前提。
- 本模块只闭合任意真实倾斜律的矩与固定方向一、二阶累积量子依赖。所有方向的二阶导数并不能单凭本定理宣称二元完整 Fréchet Hessian；该桥、局部均值逆、根 B 的统一谱/矩/WC/Song/胞/Laplace/远层概率以及原 B/C/D 根继续按根记录开放。本报告不作新颖性或最优性判断。

数学与完整实际 TYPE 审查结论：未发现关键数学缺口。接下来仅核对已有源绑定机械证据与执行环境，不重新执行任何 Lean、Audit、probe 或 smoke。


## 既有机械证据、来源绑定与环境审计

本节只读检查既有工件；没有重新运行 Lean、Audit、probe 或 smoke。完整读取并解析指定的 receipt、build-history、audit-record、Audit 源、audit-environment、environment-change、branch-created 和九项 prerequisite 字典；分支历史只取必要字段，没有将 80 个旧分支展开作额外数学依赖。下列本机/服务器当前源与已保存 source-05、actual-types 工件的字节与哈希一致：

| 工件 | 行/字节 | SHA256 |
| --- | --- | --- |
| `QuadraticTiltCumulants.lean` | 165 / 9143 | `ea105db471a073ac5eca67b4f94ff986766fd3fe3685790fb4859497da49289a` |
| `eighty-second-unit-scope.md` | 56 / 5102 | `595ac5ff0515ec6f66fe525083f6f22158699435084d2f3092b1957ea5a28122` |
| `u22a-actual-types.txt` | 49 / 3109 | `4c6d4ab35fb2f7e24be183aeab1e3c7b30d90a6a54aeec6c0691e598d4094c7a` |
| `u22a-receipt.json` | 9192 字节 | `7bd854e26f30ff1cfe3dd35d0308c76e1b4b2c8807a45d682ac71a5c22b55455` |
| `u22a-Audit.lean` | 1893 字节 | `d5d6c2baf84389ccf0d2514be61fcf22f87b8bec98fcf57cd726a8653ee1db8c` |

### 首次成功、失败分母和告警

已直接只读查看服务器本单元保存的五份完整 build log，并核对其散列与 build-history；不是仅采信作者总结。01、02 均在第 1 行 import 失败，缺少本线原库根下已接受公共 `Shao.Probability.BivariateLegendre.olean`。02 追加正式 v43 作为尾部 fallback 后仍失败，因为 Lean 先选择 `Shao` 包根，原根遮蔽尾部路径；这不是成功构建或部分成功。

03 将精确 accepted v43 库根置于首位后，才真正进入证明 elaboration，出现可积命题等价目标误用 `funext`、连续性收敛目标化简、已无目标以及导数局部等式转移的实际类型错误。04 已修掉其他错误，仍有一项常数加 cgf 的 `HasDerivAt` 匹配错误。01–04 全部保留为 `COMPLETE_FAILURE`，没有计为已检查的证明。

05 是当前完整源第一次 `COMPLETE_SUCCESS`：退出码 0，4.683392856 秒，日志 358 字节，SHA256 `151f6225bdbae002bbc9724609efa9710d060c8fa3a0887c432c1b15c92f52c5`。仅有源 108 的 `letI` 风格告警；告警不涉及声明、数学假设或内核证明。成功后未为清除此风格告警改动证明或重跑成功源。

首次 actual-owner Audit 退出码 0，5.072118338 秒；保存日志 3223 字节，SHA256 `aadcfcc4bc732ff25c88fca8cb64e6784bf7f8cf14fab44d301d810fbe79a995`，无 error 行。没有重复成功源或成功 Audit。所有历史检查回执均为 CPU14–17、Lean 原生内存 8192 MiB、j4、`autoImplicit=false`；沿用项目固定 Lean `4.36.0-rc1` / mathlib `807d3836b165983210ee2ecf3cd28f239436949c`，没有更换 pins 或弱化证明设置。

### 实际所有声明和传递公理

独立读完 Audit 源，其逻辑先核对两个冻结公开名字存在且为 theorem，再遍历环境实际模块 owner 等于 `Shao.OQ3.QuadraticTiltCumulants` 的所有常量，而不是仅审 caller 事先给出的公开清单。它拒绝 owner 下新 axiom，对每项调用 `Lean.collectAxioms` 并拒绝白名单外传递公理，同时打印完整实际 TYPE。`pp.deepTerms=true` 与充足打印步数保证当前 49 行四项实际输出没有省略号；本审查完整阅读和盲译了全部输出。

保存 audit log 的实际 footer 为：公开定义 0、冻结公开 theorem 2、全部 theorem 4、全部 declaration 4、`U22A_AXIOM_GATE PASS`。四项恰是前缀列出的两个公开、两个私有声明，generated 为 0；每项实际传递公理均为 `[propext, Classical.choice, Quot.sound]`。`u22a-audit-record.json` 与 receipt 的 source/audit/log 哈希及成功回执相互一致。当前源另经定向文本检查，无 `sorry`、`admit`、新增 `axiom`、`unsafe` 或 `native_decide`。

因此本报告复用的是当前精确完整源的既有服务器内核及传递公理证据，并补上本次新鲜独立完整语义/证明审查；不是对旧版成功记录套用新源，也不是以标准三公理标签替代数学审查。

### 必要环境变化的诚实记录

- accepted 基线为 `/root/rivermind-data/shao-lean-20261021/workspaces/integration-bearing-v43`，HEAD `d80ba2a19fca34aa6e5dd765d6091900fe0c09c4`，tree `0c08fa33511931678c7187754b6bb2926358cafc`。本轮只读 `git rev-parse` 核对这两个值。03–05 的完整 source 检查将该已接受库根放在首位；当前源的全部 Shao imports 均是该基线中的已接受模块，不需要导入本线尚未整合的其他新模块。
- owner Audit 必须读取本线新生成的 `QuadraticTiltCumulants.olean`，不能让基线包根覆盖它。执行记录为此使用一个可复用的 `/root/rivermind-data/shao-lean-20261021/runs/oq3/accepted-source-view`，将精确 accepted baseline 与本线当前新对象呈现为统一 Shao 根。这是真实的执行环境调整，不能称为原先未变的导入环境。
- 本轮定向只读核对新模块的视图项确为符号链接，精确指向 `/root/rivermind-data/shao-lean-20261021/workspaces/lead-oq3/.lake/build/lib/lean/Shao/OQ3/QuadraticTiltCumulants.olean`；`RegularCovariance.olean` 视图项指向正式 v43 对象；`Shao/Probability` 父项是指向正式 v43 对应目录的符号链接，故 `BivariateLegendre.olean` 也从该基线解析。三个对象均存在。manifest 记录全视图只有目录元数据与符号链接，本轮未扫描或重哈希稳定缓存。
- 此调整不复制二进制缓存、不写共享 cache、不替换旧对象，不改变 frozen imports、模型假设或 pins。它先解决 01/02 的真实 import 失败，再让 Audit 实际读到当前新模块。成功源、Audit 源、actual TYPE 的已核哈希与所选新对象路径组成了本单元绑定证据。
- 九项小 Shao header prerequisite 字典 canonical SHA256 独立重算为 `59ea9801649fb93ac8aa5061495db13080513cfd552247d8ecb3b83ee0d9f12a`，与指定正式 v43 的字典绑定一致；没有重新扫描全部旧库或重哈希旧对象。字典文件 SHA256 为 `da208fb78c0680511b98cea0b7ceef0718e787105061f790192b48215ac2a62b`。
- 当前本线新 branch 为 `feat/oq3-quadratic-tilt-cumulants`，只读观察 HEAD/tree 同为上述 accepted v43；branch-created 记录保留 80 个旧 owned refs。当前新模块尚未 commit/PR。本票只接受精确源内容及其证据，不将此误报为 PR 已发布、已合并或 PR173 已验收。

### 独立性、权限和最终范围

审查任务按 `gpt-6.1-sol / xhigh / fresh` 派发，作者与本审查上下文分离。首数学输入为全部实际 TYPE；盲译前缀在任何当前证明或作者说明进入上下文前落盘。后续数学审查先完成，机械记录后读，未借助旧审查票或作者 future/证明计划替代判断。未使用 math-ultra，未 spawn，未发跨线程消息。

本任务唯一写入文件是 `drafts/oq3/u22a-proof-review.md`；全部其他本机文件只读，全部服务器调用是 CPU14–17 上轻量读取/API 源阅读、日志读取、符号链接定向检查与只读 Git 身份查询。没有运行 Lean/Audit/build/probe/smoke，没有改源码、scope、receipt、历史票、状态、注册表、cache、pins 或任何远端文件。冻结前缀 7676 字节 SHA256 仍为 `f4640f12f3bf615fb2c9adda1d1de33b6c4f513561c70e4e46d2afd6ea6a7b55`。

接受范围严格限定于 SHA256 `ea105db471a073ac5eca67b4f94ff986766fd3fe3685790fb4859497da49289a` 的 `Shao.OQ3.QuadraticTiltCumulants` 全部四项声明。它真实证明了任意实际概率律的域内倾斜概率、正分割函数、全参数线积分比/可积等价、域内部点的坐标与方向矩以及两项标量导数。完整 Fréchet Hessian、局部均值逆、B 分析链及 Song/胞/Laplace/远层概率，原 B/C/D 根和其他根按原记录继续开放；本报告不作新颖性裁决。

STATUS: CORRECT
