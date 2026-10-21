# RetentionEvent 独立盲审

STATUS: CORRECT

本裁决是源码数学审查，不是 Lean 内核认证。未运行本机或服务器 Lean，未读取作者检查回执，也未把范围文件中的成功叙述作为证明证据。

## 审查对象与阶段

- 文件：`drafts/c12/RetentionEvent.lean`。
- 指定并核实的 SHA256：`e27ec2b7f94d55cba013b1cc578dafba25b0056172a6d5c930eb62228c59bb43`。
- 第一阶段只读取全部声明及唯一选择器的定义体，先向协调者提交独立重译；第二阶段读取 `RetentionEvent-scope.md` 比对冻结范围；最后才读取证明正文。
- 复用已经接收的 `ConditionalIID` 审查，不重验旧依赖。没有读取原论文或作者回执。
- 仅创建本报告，没有修改证明、范围或其他参与者的工作。

## 第一阶段：全部声明重译

### 唯一定义：第18–21行

对任意自然数 \(n\)、任意类型 \(\Omega\)、任意族 \(X:\mathrm{Fin}\,n\to\Omega\to\mathbb R\)、任意集合 \(B\subseteq\mathbb R\) 及任意 \(\omega\)，定义

\[
G_B(\omega)=\operatorname{retentionSet}(X,B,\omega)
=\{i\in\mathrm{Fin}\,n:X_i(\omega)\in B\}.
\]

它记录好/保留指标。定义是实际 `Finset.univ.filter`，没有概率、可测性或正长度条件；允许 \(n=0\)。`noncomputable` 与 `classical` 用于一般集合成员资格的选择，不改变集合内容。

### 四个公开定理

1. **第24–47行 `retentionSet_eq_event`**。对上述任意 \(X,B\) 和任意固定有限集合 \(s\subseteq\mathrm{Fin}\,n\)，有精确事件等式
   \[
   \{\omega:G_B(\omega)=s\}
   =\bigcap_i X_i^{-1}\!\left(\begin{cases}B&i\in s,\\B^c&i\notin s.\end{cases}\right).
   \]
   无可测性、概率、非空或正质量条件。这是集合相等，不是几乎处处相等、概率相等或单向包含。
2. **第50–54行 `retentionSet_compl`**。对任意 \(X,B,\omega\)，
   \[
   G_{B^c}(\omega)=G_B(\omega)^c.
   \]
   右边是相对于全部 \(\mathrm{Fin}\,n\) 的有限补集。没有可测性或概率前提。
3. **第59–68行 `measurableSet_retentionSet_eq`**。若 \(\Omega\) 为可测空间，每个 \(X_i\) 可测且 \(B\) 可测，则对每个固定 \(s\)，集合 \(\{\omega:G_B(\omega)=s\}\) 可测。没有为有限集合值域额外规定可测结构，也没有 iid 或正质量条件。
4. **第72–89行 `iid_retained_cond_retentionSet_eq`**。全称量化自然数 \(n\)、可测空间 \(\Omega\)、概率测度 \(\mu\) 于 \(\Omega\) 与 \(\nu\) 于 \(\mathbb R\)，以及 \(X\)。假设每个 \(X_i\) 可测、整个有限族在 \(\mu\) 下相互独立、每个 \(X_i\) 在 \(\mu\) 下的律为 \(\nu\)；固定 \(s\) 满足 \(|s|>0\)，固定 \(B\) 可测，固定事件 \(A_s=\{\omega:G_B(\omega)=s\}\) 满足 \(\mu A_s\ne0\)。令 \(e_s\) 为原索引的递增枚举、\(Y_r=X_{e_s(r)}\)，结论精确为
   \[
   \nu B\ne0\quad\land\quad
   (Y_r)_r\text{ 在 }\operatorname{cond}(\mu,A_s)\text{ 下相互独立}
   \]
   以及对每个 \(r\in\mathrm{Fin}|s|\)，
   \[
   \operatorname{IdentDistrib}
   (Y_r,\operatorname{id}_{\mathbb R},
   \operatorname{cond}(\mu,A_s),\operatorname{cond}(\nu,B)).
   \]
   条件测度均为已有的真实归一化限制测度。共同好集质量非零是输出，不是额外假设。

## 第二阶段：冻结范围与源语义比对

一项定义和四个公共定理的名称、量词、前提及合取输出与 `RetentionEvent-scope.md` 完全一致。没有增加非空选择器、无原子性、矩、中心化或正能量条件。没有把好集选择器命名为坏集。

依照 scope 规定的源语义，原坏指标集为

\[
J(\omega)=G_{B^c}(\omega)=G_B(\omega)^c.
\]

因此对每个固定坏集合 \(I\)，有限补集的对合性给出

\[
\{\omega:J(\omega)=I\}
=\{\omega:G_B(\omega)=I^c\}.
\]

所以应用条件 iid 定理时应代入保留集合 \(s=I^c\)，而不是 \(s=I\)。对应的混合条件精确为：\(i\notin I\) 时观测在 \(B\) 内，\(i\in I\) 时观测在 \(B^c\) 内。已证明的点态补集恒等式足以推出这个转换；冻结 API 没有要求再加一个单独的事件转换定理。

若取闭好集合 \(B=\{z:|z|\le h\}\)，则

\[
B^c=\{z:h<|z|\}.
\]

取 \(h=1/x\) 即得到 scope 所述闭保留/严格删除约定。等号全部归好集，不需要假设边界没有原子。模块本身保留任意 \(B\) 的一般形式，没有暗中加入或删除数值阈值条件。

## 第三阶段：证明审查

### 精确模式事件

**第29–39行**先对每个样本作集合外延，再把指标分成 \(i\in s\) 和 \(i\notin s\)。由选择器等于 \(s\)，分别取得真实选择器的成员资格和非成员资格；展开实际滤集恰好得到 \(X_i\in B\) 或 \(X_i\notin B\)。

**第40–47行**反向逐指标使用同样划分，以有限集合外延性恢复选择器等于 \(s\)。两个方向都覆盖所有坐标，没有只证明“保留坐标在好集”而漏掉“删除坐标在补集”。

### 补集与可测性

**第52–54行**逐指标展开有限补集与滤集，得到 \(X_i\in B^c\iff X_i\notin B\)，正好是所需补集恒等式。

**第62–68行**先重写为完整混合坐标事件，再用有限指标交的可测性；每项由 \(X_i\) 可测及 \(B\) 或 \(B^c\) 可测得到。它证明的是固定纤维事件的可测性，不需要随机有限集合值域的额外接口。

### 条件 iid

**第87–89行**将真实模式事件在质量假设和目标条件测度中一并重写为同一个混合坐标事件，随后直接应用已审查的 `iid_retained_cond_coordinate_event`。全部 iid、可测性、非空保留与正质量参数原样传入；既没有更换条件事件，也没有新增条件独立假设。

保留坐标仍由固定的 `Shao.retainedIndex s` 递增枚举。没有根据样本重新排列，也没有在原始测度 \(\mu\) 下声称随机保留族 iid。

## 零长度与空保留边界

- \(n=0\) 时选择器恒为空，任何 \(\mathrm{Finset}(\mathrm{Fin}\,0)\) 也只能为空；其固定模式事件为全集，右侧为空指标交，同样是全集。
- 此时有限补集恒等式为 \(\varnothing=\varnothing\)，可测性定理也仍成立。
- 对任意正长度也允许固定 \(s=\varnothing\) 的事件恒等式和可测性定理。
- 最后的 iid 推论单独要求 \(|s|>0\)，因此不覆盖空保留或零长度。这个限制恰当，因为结论还要从实际保留坐标推导 \(\nu B\ne0\)。
- \(\mu A_s\ne0\) 在概率测度下就是严格正且有限的事件质量；实际条件测度因此是概率测度。没有把零质量模式当作归一化的条件概率律使用。

## 裁决限度

未发现关键数学缺口或冻结范围偏移。没有新增 `sorry`、`admit`、`axiom`、`unsafe` 或 `native_decide`。该模块没有声称随机长度的无条件 iid、删除数量的二项律、条件矩估计或后续尾界。

本次没有运行 Lean 或传递公理审计；以上 `CORRECT` 仅为声明、范围与源码证明的独立数学裁决。
