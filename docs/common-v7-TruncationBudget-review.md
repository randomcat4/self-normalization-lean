# TruncationBudget 独立盲审

STATUS: CORRECT

本报告整理此前已经完成的独立盲审。审查对象为 `drafts/c12/TruncationBudget.lean`，当时核实的 SHA256 为：

`70cf7e33d458b847ea94cfa5bd8dce59a9dc3cb0ef632140a0f55fca8ded71bd`

此次仅将既有审查写入报告，没有重验或修改源码。原审查先重译全部声明，再审查证明；未运行 Lean，未执行构建或传递公理审计。因此 `CORRECT` 是源码数学裁决，不是内核认证。

## 全部定义与实际量词

唯一的定义是第24行：对任意实数 \(z\)，

\[
F(z)=\operatorname{truncationF}(z)=z^2\min(|z|,1).
\]

文件共有15个公开定理，所有标量均为实数：

| 行 | 定理 | 实际声明 |
|---|---|---|
| 26 | `truncationF_nonneg` | 任意 \(z\)，\(0\le F(z)\) |
| 29 | `truncationF_neg` | 任意 \(z\)，\(F(-z)=F(z)\) |
| 32 | `continuous_truncationF` | \(F:\mathbb R\to\mathbb R\) 连续 |
| 37 | `truncationF_of_abs_le_one` | \(|z|\le1\Rightarrow F(z)=|z|^3\) |
| 43 | `truncationF_of_one_le_abs` | \(1\le|z|\Rightarrow F(z)=z^2\) |
| 47 | `truncationF_le_sq` | 任意 \(z\)，\(F(z)\le z^2\) |
| 54 | `truncationF_le_rpow` | 任意 \(z,p\)，\(2\le p\le3\Rightarrow F(z)\le\operatorname{Real.rpow}(|z|,p)\) |
| 69 | `truncationF_scale_le_one` | 任意 \(c,z\)，\(0\le c\le1\Rightarrow c^3F(z)\le F(cz)\le c^2F(z)\) |
| 97 | `truncationF_scale_one_le` | 任意 \(c,z\)，\(1\le c\Rightarrow c^2F(z)\le F(cz)\le c^3F(z)\) |
| 125 | `truncationF_mono_abs` | 任意 \(z,w\)，\(|z|\le|w|\Rightarrow F(z)\le F(w)\) |
| 133 | `truncationF_mono_scale` | 任意 \(a,b,z\)，\(0\le a\le b\Rightarrow F(az)\le F(bz)\) |
| 140 | `truncationF_scaled_decomposition` | 任意 \(a,z\)，\(a>0\Rightarrow F(az)=a^3|z|^3\mathbf1_{\{|z|\le1/a\}}+a^2z^2\mathbf1_{\{1/a<|z|\}}\) |
| 159 | `truncationF_tail_one` | 任意 \(a,z\)，\(a>0\Rightarrow a|z|\mathbf1_{\{1/a<|z|\}}\le F(az)\) |
| 174 | `truncationF_tail_two` | 任意 \(a,z\)，\(a>0\Rightarrow a^2z^2\mathbf1_{\{1/a<|z|\}}\le F(az)\) |
| 181 | `truncationF_truncated_three` | 任意 \(a,z\)，\(a>0\Rightarrow a^3|z|^3\mathbf1_{\{|z|\le1/a\}}\le F(az)\) |

表中的指标写法等价于源码的 `if ... then ... else 0`，没有积分或几乎处处限定。两个缩放定理的双界在源码中是合取。

## 实指数与零尺度边界

第54行的 \(p\) 是真正的实数指数，不是自然数指数的占位写法。闭区间 \(2\le p\le3\) 包含两个端点：

- 当 \(|z|\le1\)，\(|z|^3\le |z|^p\)，使用小于等于一的非负基底上指数次序反向的性质。
- 当 \(1\le|z|\)，\(|z|^2\le |z|^p\)，使用大于等于一的基底上指数单调的性质。
- 当 \(z=0\)，\(p\ge2>0\)，所以 \(F(0)=0\) 且 \(\operatorname{Real.rpow}(0,p)=0\)。没有 \(0^0\) 或负基底实幂问题。

第69行确实允许 \(c=0\)，此时两个界和中项均为零；证明没有除以尺度。\(c=1\) 时上下缩放界均为等号。第97行要求 \(c\ge1\)，不声称覆盖零尺度。第133行也覆盖 \(a=0\) 及 \(0\le b\) 的情形。

所有含倒数截点 \(1/a\) 的四个定理都明确要求 \(a>0\)，没有将这些结论扩展到 \(a=0\)。

## 截断和指标方向

\(|z|=1\) 时，小区间和大区间公式均适用且值同为一。缩放分解严格采用

\[
\text{保留小区间 } |z|\le1/a,
\qquad
\text{尾区间 } 1/a<|z|.
\]

因此当 \(|z|=1/a\) 时，截断三次项等于 \(F(az)=1\)，尾一次、尾二次指标项均为零。边界没有重复计入或遗漏。\(z=0\) 时各对应矩核均为零。

尾一次和尾二次的不等式是“对应尾核不超过 \(F(az)\)”；截断三次的不等式是“对应小区间三次核不超过 \(F(az)\)”。没有将尾区间与保留区间互换，也没有反转预算控制方向。

## 源码证明审查

- **第26–51行**：非负性、偶性、连续性及分段公式均由平方、绝对值和 `min` 的对应性质得到。\(F\le z^2\) 正确使用非负平方因子与 \(\min(|z|,1)\le1\)。
- **第56–66行**：按 \(|z|\le1\) 分支，分别调用实幂的指数反向/同向单调性。小基底分支的正指数条件由 \(p\ge2\) 保证，零基底没有被遗漏。
- **第72–94行**：当 \(0\le c\le1\)，以
  \(c\min(|z|,1)\le\min(c|z|,1)\le\min(|z|,1)\)
  及非负因子 \(c^2z^2\) 得到下缩放双界。无严格正尺度步骤。
- **第100–123行**：当 \(c\ge1\)，相应使用
  \(\min(|z|,1)\le\min(c|z|,1)\le c\min(|z|,1)\)，方向正确。
- **第127–137行**：平方及 `min` 对非负绝对值的单调性，以及乘积比较所需的非负因子均有明确依据。
- **第144–156行**：由 \(a>0\) 将 \(|z|\le1/a\) 或 \(1/a<|z|\) 转为缩放基底的小/大区间，乘除方向正确；互补指标给出精确分解。
- **第161–171行**：尾区间中令 \(u=a|z|\ge1\)，正确得到 \(u\le u^2=F(az)\)。非尾区间左侧为零，使用 \(F\ge0\)。
- **第176–185行**：分别丢弃精确分解中另一个非负项，得到尾二次和截断三次核的界，使用的非负性完整。

未发现关键数学缺口。源码未见 `sorry`、`admit`、新增 `axiom` 或 `unsafe`。

## 裁决范围

这个文件没有定义 \(R_n\) 或任何概率测度，也没有证明期望、积分、矩有限性、预算的测度层连续性、严格增长或极限。它给出的是上表完整列出的点态实分析输入。该范围说明不将其提升为概率预算定理。

原裁决保持为 **CORRECT（源码数学审查）**；本报告整理不增加机械验证结论。
