# OQ3-U11a：自适应正质量尾预算与先见证后限尾

冻结候选v1，PROPOSED；未实现。拟文件 `Shao/OQ3/AdaptiveTailBudget.lean`，导入已审 `Shao.OQ3.SummableAtoms`（使用既有实数可和/有限前缀语义，不修改共享模块），namespace Shao.OQ3，noncomputable section。

来源R1 report.md SHA256 `3473d34ff20bd0d334b9ef3ea3c3ee167fba4d5cc3a742849820ce54d639e662`，484–550，特别515–541。这里只证明可数正尾预算的兼容性及其带见证选择的因果接口，不假定本身已经有LLT、常数差、连续性或产品TV。

F(J,past)是第J阶段仅依赖已选前缀past:Fin J→ℝ的正尾预算；允许它任意快速缩小且依赖完整前缀。只有正且总质量<eps的合法前缀需要F>0。实际Lean索引r0对应源r1；阶段J保留r0,…,r(J−1)，所以未来尾恰为Σ_k r(J+k)，并不遗漏下一项rJ。

## 待冻结导出声明

```lean
theorem exists_positive_mass_with_adaptive_tail_caps (eps : ℝ) (heps : 0 < eps)
    (F : (J : ℕ) → (Fin J → ℝ) → ℝ)
    (hF : ∀ (J : ℕ) (past : Fin J → ℝ),
      (∀ i, 0 < past i) → (∑ i, past i) < eps → 0 < F J past) :
  ∃ r : ℕ → ℝ, (∀ j, 0 < r j) ∧ Summable r ∧ (∑' j, r j) < eps ∧
    ∀ J : ℕ, (∑' k, r (J + k)) < F J (fun i : Fin J => r i.val)

theorem exists_positive_mass_with_adaptive_and_fixed_tail_caps (eps : ℝ) (heps : 0 < eps)
    (F : (J : ℕ) → (Fin J → ℝ) → ℝ)
    (hF : ∀ (J : ℕ) (past : Fin J → ℝ),
      (∀ i, 0 < past i) → (∑ i, past i) < eps → 0 < F J past)
    (a : ℕ → ℝ) (ha : ∀ J, 0 < a J) :
  ∃ r : ℕ → ℝ, (∀ j, 0 < r j) ∧ Summable r ∧ (∑' j, r j) < eps ∧
    ∀ J : ℕ, (∑' k, r (J + k)) < F J (fun i : Fin J => r i.val) ∧
      (∑' k, r (J + k)) < a J

theorem exists_witness_first_positive_mass_with_tail_caps (eps : ℝ) (heps : 0 < eps)
    (W : (J : ℕ) → (Fin J → ℝ) → ℕ → Prop)
    (hW : ∀ (J : ℕ) (past : Fin J → ℝ),
      (∀ i, 0 < past i) → (∑ i, past i) < eps → ∃ n : ℕ, W J past n)
    (cap : (J : ℕ) → (Fin J → ℝ) → ℕ → ℝ)
    (hcap : ∀ (J : ℕ) (past : Fin J → ℝ),
      (∀ i, 0 < past i) → (∑ i, past i) < eps →
      ∀ n : ℕ, W J past n → 0 < cap J past n) :
  ∃ chooseN : (J : ℕ) → (Fin J → ℝ) → ℕ,
    (∀ (J : ℕ) (past : Fin J → ℝ),
      (∀ i, 0 < past i) → (∑ i, past i) < eps → W J past (chooseN J past)) ∧
    ∃ r : ℕ → ℝ, (∀ j, 0 < r j) ∧ Summable r ∧ (∑' j, r j) < eps ∧
      ∀ J : ℕ, (∑' k, r (J + k)) <
        cap J (fun i : Fin J => r i.val) (chooseN J (fun i : Fin J => r i.val))
```

## 语义与实现门

零定义、三目标。首项必须给同一条完整r的所有阶段尾控制，不是每个J各选一条r，也不预先把F当成不依赖前缀的固定数列。每个有限前缀和严格小于eps由全r非负、总和<eps继承，故后续应用hF的合法门真实满足；不能先用hF于未证明合法的临时前缀。

首项实现须严格证明所有有限前缀属于同一最终r、每项严格正、真实Summable、总质量严格小于eps和每个完整未来尾的界；不能只证下一项小、有限尾小或各阶段分别存在。独立审查需先确认任意自适应F在这些准确前提下的兼容性。

第二项用min(F,a_J)同时保留全部自适应与固定正要求。源可选加强(14a)的Q_J^(-J)>0属于a_J的一种输入，本单元不直接宣称已完成所有多项式弱Cramer失败。

第三项把chooseN这个只依赖有限前缀的完整选择函数放在最终r之前，并在全部合法前缀上验证W。于是后续正尾预算依赖的n已经从当前有限模型选出，不能回头看到未来r后修改该见证。W与cap为显式输入，hW可包含有限阶段LLT给出的任意样本量增长/相位/常数差要求；当前结论不证明hW、不给n_J单调性或误差发散。完整相应的LLT、相位返回、产品TV和常数连续性仍需另证并给出实际cap>0，才可应用此接口。

这是实数序列兼容性，不是三角阵概率极限，也未量化任何随n改变的最终P。之后把这条r代入同一p/q/eps源族，可得到固定律；该组合与根A闭合不在本单元。所有根A/B/C/D保持OPEN。
