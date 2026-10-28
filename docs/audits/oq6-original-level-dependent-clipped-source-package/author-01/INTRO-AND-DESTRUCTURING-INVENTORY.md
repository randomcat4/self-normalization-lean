# Unit251 introduced and destructured source bindings

This is a source-level lexical inventory, not an elaborated all-owned TYPE/VALUE report. Every let/have's full source text is in SOURCE-INVENTORY.json and SOURCE-INVENTORY.md. Types below are the public API head under the written substitutions, without inferred extra premises.

## Frozen introduction (lines105-106; main theorem scope through276)

The29 names g,r,v,rho,P,N,W,V,D,J,Ddelete,Jdelete,A,Adelete,B,Bdelete,d,e,Tclip,s,Tphysical,ξ0,cap,S,Sdelete,fullTest,deletedTest,I,sourceCost are the exact29 frozen lets at lines29-64. Their full types and RHS are inventory entries1-29. The original theorem parameters Ω,mΩ,μ,IsProbabilityMeasure μ,h,hh,hh2,hhsymm,hcenter,hprojectionsecond,n,hn,z,hz,hwindow remain the frozen parameters at lines17-28.

## Compact public API destruction (lines137-142; scope through149)

RHS is the single public call actual_normalized_compact_clipped_observables μ h hh hh2 hhsymm hcenter hprojectionsecond n hn 0 (le_refl0) (by norm_num)512 hC0.

The following are its exact result components under these definitions:

- hW0 : Measurable W
- hV0 : Measurable V
- hD0 : Measurable D
- hJ0 : Measurable J
- hA0 : Measurable A
- _hB10 : Measurable (studentizerClipBudget n r 512 rho 1)
- hs20 : Measurable (centeredSq n g r)
- hs0 : Measurable s
- hd0 : Measurable d
- _he10 : Measurable (clippedCenteredDelta n g r 512 rho 1)
- _hTclip10 : Measurable (clippedCenteredStatistic n g r 512 rho 1)
- hTphysical0 : Measurable Tphysical
- hVzero0 : MeasurableSet {ζ : Fin n → Ω | V ζ=0}
- hszero0 : MeasurableSet {ζ : Fin n → Ω | s ζ=0}
- _hpositive10 : ∀ ζ : Fin n → Ω, (1 / 2 : ℝ) ≤ 1 + clippedCenteredDelta n g r 512 rho 1 ζ
- _hzero10 : ∀ ζ : Fin n → Ω, V ζ = 0 → d ζ = 0 ∧ clippedCenteredDelta n g r 512 rho 1 ζ = 0 ∧ clippedCenteredStatistic n g r 512 rho 1 ζ = 0
- hdeletes0 : the complete coordinate conjunction written immediately below.

For unambiguous complete types, spaces in the displayed Lean block are literal function application:

```lean
hdeletes0 :
  ∀ i : Fin n,
    Measurable (fun ζ : Fin n → Ω =>
      min (|g (ζ i)| / N) (1 / (1 + (0 : ℝ)))) ∧
    Measurable (fun ζ : Fin n → Ω => Ddelete ζ i) ∧
    Measurable (fun ζ : Fin n → Ω => Jdelete ζ i) ∧
    Measurable (fun ζ : Fin n → Ω => Adelete ζ i) ∧
    Measurable (fun ζ : Fin n → Ω =>
      studentizerClipBudgetDeleted n r 512 rho 1 ζ i) ∧
    Measurable (fun ζ : Fin n → Ω =>
      min (|g (ζ i)| / N) (1 / (1 + (0 : ℝ))) *
        (|A ζ - Adelete ζ i| + 0 *
          |studentizerClipBudget n r 512 rho 1 ζ -
            studentizerClipBudgetDeleted n r 512 rho 1 ζ i|)) ∧
    ∃ E0 : ({j : Fin n // j ≠ i} → Ω) → ℝ × ℝ × ℝ,
      Measurable E0 ∧ ∀ ζ : Fin n → Ω,
        (Ddelete ζ i, Jdelete ζ i,
          studentizerClipBudgetDeleted n r 512 rho 1 ζ i) =
            E0 (fun j : {j : Fin n // j ≠ i} => ζ j.val)
```

The unused fixed1 components do not contribute to any current-z statement or fee.

## Nested old-coordinate destruction (lines145-149)

i : Fin n is introduced at145, scope to149. RHS at146 is hdeletes0 i. _hcap0,hDdelete0,hJdelete0,hAdelete0,_hBdelete10,_hdeletedTest0 are the six measurable components, in their complete order above after specializing i. E0 has type ({j : Fin n // j≠i}→Ω)→ℝ×ℝ×ℝ; hE0 : Measurable E0; hE0factor is the universally quantified final triple equality above. Only the second/third/fourth measurable components and E0/hE0/hE0factor are retained into hshared.

## Shared-result destruction (lines150-152; scope through276)

RHS is hshared, whose full type and complete proof RHS are inventory entry37. hW,hV,hD,hJ,hA,_hs2,hs,hd,hTphysical,hVzero,hszero have exactly the first11 component types in hshared. hdeletes is its complete last universal coordinate component:

```lean
hdeletes :
  ∀ i : Fin n,
    Measurable (fun ζ : Fin n → Ω => Ddelete ζ i) ∧
    Measurable (fun ζ : Fin n → Ω => Jdelete ζ i) ∧
    Measurable (fun ζ : Fin n → Ω => Adelete ζ i) ∧
    ∃ E0 : ({j : Fin n // j ≠ i} → Ω) → ℝ × ℝ × ℝ,
      Measurable E0 ∧ ∀ ζ : Fin n → Ω,
        (Ddelete ζ i, Jdelete ζ i,
          studentizerClipBudgetDeleted n r 512 rho 1 ζ i) =
            E0 (fun j : {j : Fin n // j ≠ i} => ζ j.val)
```

## Current-coordinate destruction and local arguments (lines197-247)

i : Fin n is introduced at197, scope to247. RHS at198 is hdeletes i. hDdelete,hJdelete,hAdelete are its first three measurable statements specialized at i. E0,hE0,hE0factor are exactly its existential witness and facts specialized at i. The five fully typed local data pdel,Dret,Jret,Bret,E and every hDret/hJret/hBret/hE/hDfactor/hJfactor/hBfactor/hzξ0/hcap/hBdelete/hdeletedTest are inventory entries47-62, full RHS and coordinates included. ζ : Fin n→Ω at244 is the arbitrary sample for the final triple equality, scope to247.

## Other introduced proof arguments

- hsym proof at113: o y : Ω, scope to116.
- habs parameters at117: f : (Fin n→Ω)→ℝ and hf : Measurable f; scope to119.
- hξ0 at120: i : Fin n; local fact body only.
- hglobal at174: ζ : Fin n→Ω; local fact body only.
- hzero at178: ζ : Fin n→Ω and hζ : V ζ=0; local fact body only.
- hphysicalzero at181: ζ : Fin n→Ω and hζ : s ζ=0; scope to184.
- hDfactor/hJfactor/hBfactor at216/218/220: ζ : Fin n→Ω; their own local bodies only.
- hgeometry at257: hgeom : (1+rho)*z<=N, scope through263.
- first geometric branch at259: ζ : Fin n→Ω, hGood : ζ∈projectionGood n g z and hLower : -(1/2 : ℝ)<=d ζ, scope through261.

No introduced argument strengthens the frozen model. The geometric arguments occur only under the frozen explicit implication.
