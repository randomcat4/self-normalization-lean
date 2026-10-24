# Unit 124: the actual Brownian interval absorption kernel

Author C12 lead 01a16c4c-25a6-7740-a10e-12635a13edae. math-theorem only, independent full final review pending. Unit numbering is unrelated to the original 124 unified mechanism, which is not a prerequisite. Original read-only supplement.tex SHA256 b99f2ac4d2f39dd39772d98a5702b7a923c2f10f8730a08fc1b4cd6bba4742bd, full4192–4398, motivates the actual surviving endpoint density divided by the free density. Units122/123 pay the actual physical density and arbitrary terminal-set disintegration; this unit constructs its genuine measurable finite kernel so the remaining analytic image identity can be stated against an actual subprobability transition kernel.

All seven complete public heads, imports/context and the complete sole transparent definition actualIntervalKernel were frozen at SHA ea23678f932068b8852cc1f27b3ef7e2668c4bab83d5278f8b0586dfe6710978 before separate implementation. No private source heads. No assumption or frozen context/value/head changes. UTF-8 no BOM LF source throughout.

## Complete proof route

The full actualIntervalKernel value is `(Kernel.const R volume).withDensity (fun y z => ENNReal.ofReal (gaussianPDFReal y T z * intervalCompletion (bridgeLaw B P) a y T z))`. Its definition is total for arbitrary B,P,a,T. Native Kernel.withDensity uses the stated density when jointly measurable and zero otherwise; all results here impose an actual standard Brownian hypothesis and T≠0, then explicitly prove the joint measurability and identify the stated row. No zero-time transition claim is made.

1. The actual bridge completion is jointly continuous in both real start and endpoint for fixed positive time and arbitrary real wall parameter. This is proved from the actual upper/lower positive-part formulas, not by an invalid appeal to separate continuity alone. At fixed (y,z), split the interval-probability increment through I(y,z'). The first increment is bounded by the actual upper/lower start increments at the varying endpoint z'; both halfline probabilities are jointly continuous by their exact exponential formulas. The second increment tends to zero by the qualified actual endpoint continuity. A three-term nonnegative squeeze proves the genuine joint limit. This covers exterior starts/endpoints and walls as well as interiors.

2. Multiplying by the true physical free Gaussian density preserves joint continuity for T>0. Composition with ENNReal.ofReal is therefore jointly measurable.

3. Apply the exact native Kernel.withDensity_apply theorem with that actual measurability proof. The row is the genuine Lebesgue withDensity measure for the displayed nonnegative density. No independently supplied row or kernel law is assumed. The new standard WithDensity object was already cached; no missing standard object or old project producer was built.

4. On every measurable terminal set A, withDensity_apply gives the nonnegative Lebesgue integral. Unit123 genuine integrability and the actual probability bounds ensure ofReal_integral_eq_lintegral_ofReal applies without an infinity/toReal convention. Unit123's exact actual physical disintegration identifies this value with ENNReal.ofReal of the actual strict survival plus terminal-A probability. There is no uncountable-survival measurability assumption on an arbitrary original source probability space; its real probability is already handled by the actual almost-everywhere path-copy construction in unit123.

5. Taking toReal gives the exact row real-probability equality because actual probability is nonnegative. At A=univ, the genuine probability bound ≤1 gives the kernel mass bound ≤1. The native IsFiniteKernel exists_univ_le field is then witnessed by the uniform constant1. Thus every row is a subprobability measure with a uniform finite kernel bound. No row is renormalized.

## Original execution and review evidence

Pinned Lean4.36.0-rc1/mathlib807d3836b165983210ee2ecf3cd28f239436949c/shared-v34 unchanged. Only this leaf is kernel-checked remotely with C12 flock, CPUs14–17, -M8192 -j4. Attempt001 is preserved: Pi.sub_apply/Function.comp_def and the exact point of ContinuousAt required explicit elaboration, and the order-add helper needed its correct argument orientation. Attempt002 fixes only those proof expressions and passes with style/check-out warnings only. Full frozen context/heads/value unchanged. No local Lean, cache mutation, old source recompilation, full project build, root import or merge.

The successful established owner/recursive collectAxioms audit selects every module owner via env.getModuleIdxFor?. Actual9 owners comprise8theorems (7public,0private source,1generated) and1definition; all use only propext, Classical.choice, Quot.sound. Complete actual type and full definition-value streams are reconstructed from the original audit log without elision. Successful gates are not replayed. Standard primary WithDensity definition/proofs and actual native Bochner nonnegative integral conversion were read before authoring; independent reviewer verifies consumed interfaces, complete source, all actual owners and full value against exact bytes.

## Scope and unpaid dependency

The actual finite kernel and density measure are now explicit, but their equality with the analytic image/Dirichlet heat kernel is not proved. The exact original hImage interface and unconditional hSmall/C12 roots remain OPEN. No semigroup, heat PDE, eigenmode moment identity, or unconditional source root is inferred from finite mass alone. Existing p54 repairs/classical external attribution preserved; OQ3 remains paused; no other lane acceptance is adjudicated.
