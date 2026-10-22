# v35: actual Brownian first-term asymptotic

This closes the requested actual Brownian first-term shared obligation, on top of v34 fullXi and actual BrownianB1. The four new modules preserve exact author commit6bc709e196e0b8348120651a42e0718ba1b9baa7 and the frozen M/G/S declarations.

For the given actual IsBrownianReal B P, probability B P hB is the real probability of the measurable version of sup_[0,1]|B_t|, equal to the actual full weak strip event. firstTerm x is exactly (4/pi)*exp(-(pi^2/8)/x^2). The actual_brownian_firstTerm_envelope theorem bounds |probability/firstTerm-1| by the accepted absolute constant times exp(-pi^2/x^2) for0<x<1. actual_brownian_firstTerm proves the original epsilon-delta ratio limit1; actual_brownian_eventually_positive derives eventual probability and ratio positivity. No arbitrary survival function or desired probability/functional-CLT/no-atom premise is assumed.

The dependency chain is fully paid: M proves actual finite Rademacher maximal/coarse inequalities by finite polynomial first-crossing recursion; G proves actual finite product-to-Brownian-grid convergence by characteristic functions/finite-dimensional Levy and then the dyadic-to-continuous probability limit; S combines accepted finite spectral envelopes with these actual comparisons in the ordered limits m, then d, then epsilon, then x. The first-term conclusion does not assert an exact Brownian spectral series or a separately constructed canonical Brownian probability space.

Root source/object/aggregate, all public theorem coverage, all owned private/generated transitive axioms and module coverage PASS at2026-10-22T16:13:11Z. Fournew modules/eightpublictheorems/eightpublicdefs/171ownedconstants. Totals256productionmodules,1747publictheorems,2853namespace theoremconstants includinggenerated,4759ownedconstants. Original252sourcefiles and1029baselineobjectfiles unchanged. Fixed Lean4.36.0-rc1/mathlib807d3836b165983210ee2ecf3cd28f239436949c. Whitelist onlypropext/Classical.choice/Quot.sound.

The public-manifest generator previously matched only column-zero headers; one frozen public theorem has a leading space. Root preserved every Lean byte and changed whitespace handling from rstrip to strip. The new manifest was checked to preserve all1739oldpublicnames and add exactly the eight frozen targets; independent bounded manifest review accompanies the three full M/G/S reviews. All eight targets are additionally theorem/axiom checked by the whole-library gate.

M frozen source has existing mixedCRLF and terminalblank; initial Git whitespace classification failed only on that formatting. A per-command cr-at-eol,-blank-at-eof classification accepted the preserved sourcebytes. No mathematical assumption, sourcebyte, compilerflag or audit whitelist was weakened. Full diagnostic history staysserveronly. Review publication normalizes CRLF and terminal blank lines only, with before/after hashes; original review files are preserved.

All heavy work serveronly, rootCPU10–13 oneLeanprocessatonce/-M8192-j4-autoImplicitfalse. Otherlanescontinue14–25; externaluserPID143204CPU0–9/80GiB untouched. Sharedcacheunchanged; newimportsuseprivateoverlay.

S3/S4/S5 and the full OQ4 root remain separate downstream obligations. Full C1/C2 still needs Xi/K derivatives, high-frequency damping, inversion, summations and desmoothing. Other original roots are not expanded by this shared result.

All three fresh M/G/S fullproofverdicts CORRECT with no requiredfixes; bounded independentmanifestreview alsoCORRECT. Exactsources are accepted as an assembled chain with the completed rootgate, so the full shared Brownian first-term obligation is CLOSED.
