# Genuine finite Spitzer producer declaration freeze

Root has fully read the candidate declarations, source contract and entire proof route. Root approves the complete FINITE-layer public definitions and seven theorem heads below, every literal parameter/type/value. Only sections 1–3 are frozen for production now. Sections 4–5 remain a future candidate, not accepted or silently assumed.

Author: `/root/common_spitzer_author`, gpt-6.1-sol/xhigh. Own ONLY new `Shao/Probability/SpitzerFinite.lean` and `drafts/c12-spitzer-producer-candidate/`; private implementation helpers are permitted and require full actual-owned audit. Root activates the released server worktree `common-cone-derivatives-v44` on frozen parent `4f562ddb57e2cf695291db5da38aadfd2c0fbb7d`. Preserve all existing untracked source/helpers and other owners' edits. Commit only the new owned production source.

Exact candidate bindings:
- `candidate-declarations.md`: `66da3b6ff329a1f33def94c10dcc48c2322f0db201592cdd342730bea83b6974`
- `source-contract.md`: `4dfa91e06d237e56943d72789fb4be5cebbcc3de17f43310d4bdd39caee5d383`
- `proof-route.md`: `2d89d05c6c6b040b54c7f17e1b57c64d1747fe27e22c333b24fe19f33eb751cf`

The genuine finite target is `finite_spitzer_cut_identity` for ALL real paths, including ties and repeated/zero increments, with no supplied cycle identity, recurrence, probability SP, CDF, symmetry or atomless condition. Generic distinct disjoint subset means may occur only inside the deterministic proof and must be actually eliminated by proved density/continuity. The marked equivalence must have a true inverse and prove the actual maximum decomposition; sample-dependent permutations must never be claimed iid-preserving. n=0, singleton rotations and marker at block endpoint are included.

The declared route is mathematically substantive but NOT implemented/verified/accepted. Do not report lower finite rotation or face lemmas as probability Spitzer, survival, second-moment, OQ4 or C1/C2 root completion. No external citation becomes a new axiom. Preserve classical attribution (Spitzer; Abramson–Pitman 3214 construction).

All Lean/heavy server only under root CPU10–13, root-heavy.lock, pinned versions and -M8192 -j4 -DautoImplicit=false. New sources UTF8 LF write_bytes before first source gate. No local Lean. No sorry/admit/new axiom/unsafe/native_decide. Preserve exact original direct Lean exit immediately, source/object hashes and full actual-owned types/definition values/private/generated recursive axioms. Author/reviewer separation and fresh complete independent review remain mandatory. Qualified unchanged predecessors are reused, not recompiled/reviewed again.

## Complete frozen finite layer

```lean
import Shao.Probability.MeasurablePath
import Mathlib.Data.Fintype.Perm
import Mathlib.Analysis.SpecialFunctions.Exp
import Lean.Elab.Tactic.Omega

noncomputable section
```

```lean
def reorder {n : ℕ} (a : Shao.Path n) (σ : Equiv.Perm (Fin n)) :
    Shao.Path n := fun i => a (σ i)

def head {n : ℕ} (a : Shao.Path n) (k : ℕ) (hk : k ≤ n) :
    Shao.Path k :=
  fun i => a ⟨i.val, Nat.lt_of_lt_of_le i.is_lt hk⟩

def tail {n : ℕ} (a : Shao.Path n) (k : ℕ) (hk : k ≤ n) :
    Shao.Path (n - k) :=
  fun i => a ⟨k + i.val, by omega⟩

def subsetMean {n : ℕ} (a : Shao.Path n) (u : Finset (Fin n)) : ℝ :=
  (∑ i ∈ u, a i) / (u.card : ℝ)

def DistinctDisjointMeans {n : ℕ} (a : Shao.Path n) : Prop :=
  ∀ u v : Finset (Fin n), u.Nonempty → v.Nonempty →
    Disjoint u v → subsetMean a u ≠ subsetMean a v

def wordSum {n : ℕ} (a : Shao.Path n) (w : List (Fin n)) : ℝ :=
  (w.map a).sum

def wordMean {n : ℕ} (a : Shao.Path n) (w : List (Fin n)) : ℝ :=
  wordSum a w / (w.length : ℝ)

def rotateWord {α : Type*} (w : List α) (r : ℕ) : List α :=
  w.drop r ++ w.take r

def StrictBelowChord {n : ℕ} (a : Shao.Path n) (w : List (Fin n)) : Prop :=
  w ≠ [] ∧ ∀ j : ℕ, 0 < j → j < w.length →
    wordSum a (w.take j) < (j : ℝ) * wordMean a w

def FaceDecomposition {n : ℕ} (a : Shao.Path n)
    (σ : Equiv.Perm (Fin n)) (B : List (List (Fin n))) : Prop :=
  B.flatten = List.ofFn (fun i : Fin n => σ i) ∧
    (∀ w ∈ B, StrictBelowChord a w) ∧
    B.Pairwise (fun u v => wordMean a v < wordMean a u)
```

```lean
theorem head_prefixSum {n : ℕ} (a : Shao.Path n) (k : ℕ) (hk : k ≤ n)
    (j : ℕ) (hj : j ≤ k) :
    Shao.prefixSum (head a k hk) j = Shao.prefixSum a j

theorem exists_distinctDisjointMeans_direction (n : ℕ) :
    ∃ v : Shao.Path n, DistinctDisjointMeans v

theorem dense_distinctDisjointMeans (n : ℕ) :
    Dense {a : Shao.Path n | DistinctDisjointMeans a}

theorem exists_unique_rotation_strictBelowChord {n : ℕ} (a : Shao.Path n)
    (ha : DistinctDisjointMeans a) (w : List (Fin n))
    (hw : w.Nodup) (hne : w ≠ []) :
    ∃! r : Fin w.length, StrictBelowChord a (rotateWord w r.val)

theorem exists_unique_faceDecomposition {n : ℕ} (a : Shao.Path n)
    (ha : DistinctDisjointMeans a) (σ : Equiv.Perm (Fin n)) :
    ∃! B : List (List (Fin n)), FaceDecomposition a σ B

theorem exists_marked_cut_equiv {n : ℕ} (a : Shao.Path n)
    (ha : DistinctDisjointMeans a) :
    ∃ e : (Fin n × Equiv.Perm (Fin n)) ≃ (Fin n × Equiv.Perm (Fin n)),
      ∀ p : Fin n × Equiv.Perm (Fin n),
        Shao.maxWithZero (reorder a p.2) =
          max (Shao.prefixSum (reorder a (e p).2) ((e p).1.val + 1)) 0 +
            Shao.maxWithZero
              (tail (reorder a (e p).2) ((e p).1.val + 1) (by omega))
```

```lean
theorem finite_spitzer_cut_identity (n : ℕ) (a : Shao.Path n) (L : ℝ) :
    (n : ℝ) *
        (∑ σ : Equiv.Perm (Fin n),
          Real.exp (-Shao.maxWithZero (reorder a σ) / L)) =
      ∑ k : Fin n, ∑ σ : Equiv.Perm (Fin n),
        Real.exp (-max (Shao.prefixSum (reorder a σ) (k.val + 1)) 0 / L) *
          Real.exp
            (-Shao.maxWithZero
              (tail (reorder a σ) (k.val + 1) (by omega)) / L)
```
