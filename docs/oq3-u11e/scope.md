# OQ3-U11e：实际源族上的先见证后未来质量预算

冻结候选v1，PROPOSED；尚未实现。拟文件 `Shao/OQ3/SourceTransferBudgets.lean`，导入 `Shao.OQ3.AdaptiveTailBudget`、`Shao.OQ3.CorrectedScaleContinuity`、`Shao.OQ3.SampleChangeOfMeasure`，namespace Shao.OQ3，open MeasureTheory，open scoped Matrix，noncomputable section。

来源R1 report.md SHA256 `3473d34ff20bd0d334b9ef3ea3c3ee167fba4d5cc3a742849820ce54d639e662`，499–550，特别531–537。把U11a抽象尾预算真正实例化到源族27–30：固定同一p/q/eps，前缀确定有限概率律与正修正常数，n见证选定后取正cap，最后才构造同一全正可和r。显式W/hW仍是尚未证明的有限阶段分析见证输入；本单元不将其存在性记作LLT/尖点/相位见证已实现。

## 冻结候选声明

```lean
theorem exists_source_transfer_caps :
  ∃ (p : Fin 4 → ℝ) (q eps : ℝ),
    (∀ i, 0 < p i) ∧ 1 < q ∧ q < 103 / 100 ∧ 0 < eps ∧
    (constraintMatrix sourceEll) *ᵥ p = constraintTarget q ∧
    (∀ (r : ℕ → ℝ), (∀ j, 0 < r j) → Summable r → (∑' j, r j) < eps →
      (∀ i, 0 < limitingBase sourceEll p r i) ∧
      ∀ J : ℕ, ∀ i, 0 < finiteBase sourceEll p r J i) ∧
    ∀ (eta : ℕ → ℝ), (∀ J, 0 < eta J) →
      ∃ cap : (J : ℕ) → (Fin J → ℝ) → ℕ → ℝ,
        (∀ (J : ℕ) (u : Fin J → ℝ),
          (∀ i, 0 < u i) → (∑ i, u i) < eps → ∀ n : ℕ, 0 < cap J u n) ∧
        ∀ (J : ℕ) (u : Fin J → ℝ),
          (∀ i, 0 < u i) → (∑ i, u i) < eps → ∀ (n : ℕ) (r : ℕ → ℝ),
          (∀ j, 0 < r j) → Summable r → (∑' j, r j) < eps →
          (∀ i : Fin J, r i.val = u i) → (∑' j, r (J + j)) < cap J u n →
            |normalizedTailCoefficient sourceEll q (limitingMass sourceEll p r) n -
              normalizedTailCoefficient sourceEll q (finiteMass sourceEll p r J) n| < eta J ∧
            |correctedInverseScale sourceEll q (atomicMeasure (limitingMass sourceEll p r)) -
              correctedInverseScale sourceEll q (atomicMeasure (finiteMass sourceEll p r J))| < eta J

theorem exists_source_mass_with_witness_and_transfer :
  ∃ (p : Fin 4 → ℝ) (q eps : ℝ),
    (∀ i, 0 < p i) ∧ 1 < q ∧ q < 103 / 100 ∧ 0 < eps ∧
    (constraintMatrix sourceEll) *ᵥ p = constraintTarget q ∧
    ∀ (eta : ℕ → ℝ), (∀ J, 0 < eta J) →
      ∀ (W : (J : ℕ) → (Fin J → ℝ) → ℕ → Prop),
        (∀ (J : ℕ) (u : Fin J → ℝ),
          (∀ i, 0 < u i) → (∑ i, u i) < eps → ∃ n : ℕ, W J u n) →
        ∃ chooseN : (J : ℕ) → (Fin J → ℝ) → ℕ,
          (∀ (J : ℕ) (u : Fin J → ℝ),
            (∀ i, 0 < u i) → (∑ i, u i) < eps → W J u (chooseN J u)) ∧
          ∃ r : ℕ → ℝ, (∀ j, 0 < r j) ∧ Summable r ∧ (∑' j, r j) < eps ∧
            IsProbabilityMeasure (originalMeasure sourceEll (limitingMass sourceEll p r)) ∧
            (Integrable (fun x : ℝ => x) (originalMeasure sourceEll (limitingMass sourceEll p r)) ∧
              (∫ x : ℝ, x ∂originalMeasure sourceEll (limitingMass sourceEll p r)) = 0) ∧
            ∀ J : ℕ,
              W J (fun i : Fin J => r i.val) (chooseN J (fun i : Fin J => r i.val)) ∧
              |normalizedTailCoefficient sourceEll q (limitingMass sourceEll p r)
                  (chooseN J (fun i : Fin J => r i.val)) -
                normalizedTailCoefficient sourceEll q (finiteMass sourceEll p r J)
                  (chooseN J (fun i : Fin J => r i.val))| < eta J ∧
              |correctedInverseScale sourceEll q (atomicMeasure (limitingMass sourceEll p r)) -
                correctedInverseScale sourceEll q (atomicMeasure (finiteMass sourceEll p r J))| < eta J
```

零定义、两公开目标。原始参数p/q/eps在eta/W/chooseN/r/J/n之前取得；W可依赖固定有限前缀与n，但不是未定完整r。第二目标中chooseN在r之前且在每个合法前缀上满足W，原律P由之后的同一r一次固定，所有J共用。

预计从sourceStarter选择p/q，并用exists_uniform_finite_radius与exists_limiting_radius取同一eps，允许非负可和的内部零延拓作为有限参考。每个合法u:Fin J→ℝ可先作零延拓r0，其真实Summable与总和=有限u和须证明；该r0不是最终全正r。统一finite半径给四旧质量严格正，有限约束与U11d source_atomic_corrected_radicand_pos给该参考的正radicand。因此U11d先取独立于未来r的scale cap。

对任意已给n，令K_n=sqrt(2*pi*n)*exp(11sourceEll*n)*n*C(sourceEll)≥0，另取eta J/(K_n+1)>0，cap取两者min。未来质量非负时K_n*T≤(K_n+1)*T；cap严格尾界遂给严格eta误差，n=0亦无除零。normalized比较实际消费U9b最终真实原律系数误差，scale比较消费U11d同前缀cap；不把两个实际law的指数率当成相等。

第二目标使用U11a的witness-first positive mass构造，先以hW选择chooseN再按实际cap构造同一全正r。需要由总质量<eps和非负可和证明每个有限前缀和<eps，才能合法调用hW与cap；不能把合法前缀门省掉。原律概率/中心化从该同一p/q/r的真实极限四约束HasSum与正质量取得，不依赖另一个可能采用不同p/q/eps的存在性族。

本单元只消除(27)–(30)预算与抽象正质量递归之间的接口缺口；hW仍明确待实际有限阶段LLT、尖点常数差和相位/样本增长见证提供。没有(31)发散结论、O(n^-1/2)反例根闭合、全局唯一鞍点或新颖性主张。根A/B/C/D保持OPEN。
