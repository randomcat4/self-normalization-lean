# Original clipped expectation fees

Qualified exact source and first original object. The final independent review is [available here](OQ6-original-clipped-expectation-fees-machine-review.md). Root intake and integration are separate.

`Shao.OQ6.OriginalClippedExpectationFees.actual_quadratic_clipped_expectation_fees` supplies the four actual expectation fees and their combined polynomial budget from the original p51 S13/S14 construction. It uses the literal original sample size in the full and deleted residual/statistical budgets. The actual fully tilted law and the partially weighted deletion integrals remain distinct in the statement.

The model is the measurable symmetric centered jointly L2 kernel h under a probability law, with projection second moment exactly1. Let g be the actual projection, r=h-g-g, rho=sqrt(E r²), sigma=1+rho, N=sqrt(n), and C=exp(1/2). The public range is n>=4, 1<=y<=N/(2C), C0>=0. No mixed or fourth moment, zero-boundary-mass, atomlessness, or standard-Borel premise is added.

The law Pa is the actual tilt of the original product law P0 by sum_i(a*g_i-(a*g_i)²/2), where a=y/N. With m=E exp(a*g-(a*g)²/2), the normalization is I=m^n. The deletion weight R_i is exp(sum_{j!=i} phi_j)/I, including the extra m^-1 relative to a normalized (n-1)-coordinate tilt. Its cap is min(|a*g_i|,1). The full D/J and deleted Ddel/Jdel are the named original-n definitions from qualified212. Both studentizer budgets are their named full/deleted definitions with the same original n; B=C0*(sigma*y/N+J/(sigma*y*N)).

The fees and returned component bounds are:

- fD=y*E_Pa|D| <= 8*C²*rho*y*(1+y²)/N.
- fB=y²*E_Pa B <= C0*(sigma*y³+56*C⁴*rho²*y*(1+y²)/sigma)/N.
- fDdel=sum_i E_P0[R_i*cap_i*||D|-|Ddel_i||] <= 4*sqrt(2)*C*rho*(1+y)²/N.
- fBdel=y*sum_i E_P0[R_i*cap_i*|B-Bdel_i|] <= 96*C²*C0*rho²*(1+y)²/(sigma*N).

Consequently, with K=256*C⁴*(1+C0), the actual sum of the four fees is at most K*(1+rho+rho²)*(1+y)³/N. The statement also proves that Pa is a probability law and supplies genuine L1 for |D| and B under Pa and both deletion-cost integrands under P0. Totalized integrals are not used as substitutes for integrability. The boundary cases rho=0, C0=0, and y=1 are retained; no proof divides by rho or C0.

## Proof and inherited evidence

The proof consumes the already qualified public interfaces of212 (literal original-n definitions/identities),213 (actual fully tilted rho/rho² moments), and214 (rho-sensitive R-weighted continuous-cap deletion moments). Their source-bound qualifications and original producer objects are reused without rebuilding, rechecking leaf axioms, or commissioning another complete old proof review.

The new private scalar helper combines four explicit bounds. The public proof transports the actual budget through the affine J term, transfers genuine L1, identifies the deletion difference by the nonnegative coefficient q=C0/(sigma*y*N), and applies the scalar helper. The combined coefficient16+153*C0 is bounded by256*(1+C0).

The declaration/data freeze predates implementation. Complete independent source-to-statement/proof/data/producer-interface coverage of the original433LF source is composed with the same reviewer's exact one-line affected-proof review. Native01 failed at line403 because the additive inequality was written in the reverse syntactic order. The repair changes only that line by5bytes, replacing add_le_add_left with add_le_add(le_refl _)(...). Both declarations, the entire preamble, all63 lexical data lets, and all68 ordinary have/haveI facts remain unchanged. The original failed source and receipt are retained as failure evidence.

## Exact server evidence

Final source: SHA256 `3c11927ca08a6861bb325962a3baf6a818cc9d1366f2f6174d67edccc9bd59ee`,19679B/433LF, UTF-8 without BOM, LF only, one final LF.

Native02 actual exit0; zero errors and12 source warnings. Its receipt SHA256 is `363dabd37f43a95c03229f1b32a1fe9f46dddcb22b4b30df5cb7f5e9b6ab7b56`.

The first original object is SHA256 `beb74878e3dbd5b9ee1731c22a2e6d3340fe8cd8ec10823e4482fc78e65f32d0`,2615840B,mtime_ns1793038721078039158. The import-only all-owner audit uses that same object with unchanged bytes/hash/mtime; its receipt SHA256 is `410da2dab13eaa29ab6819baf2ccba13c4308e292115d5a38ed5effa7325d4bf`,actual exit0.

Ownership is derived from the actual module index across all constants, without a namespace filter. There are19 actual owned constants, all theorems, with821 complete TYPE lines and0 non-theorem VALUE lines. This includes the generated residualStatisticDDeleted.eq_1 and residualEnergyJDeleted.eq_1 in the OQ5.P51 namespace. Recursive axiom occurrences are propext19, Classical.choice7, Quot.sound7; no other axiom occurs. The structured TYPE/JSON/count blocks reconstruct the69416B audit stdout exactly.

The strict outer wrappers remain false: the established134B mathlib-local-changes stderr warning and the source warnings are retained. Actual Lean and audit exits are both0. FIRSTEMPTY is null and is not a returned runner field. Preserved accepted SHA references checked by current bytes/ns are distinguished from newly enrolled full-SHA records; the evidence does not describe the whole protection set as freshly rehashed.

All Lean and axiom commands ran on the designated server under phase ROOT_OQ56_38, CPU52-55, the OQ56 lock, -M8192 -j4, one own heavy command at a time. All owned processes ended naturally; own Lean/heavy/inflight/pendingExternal are0. No local Lean, original-object rebuild, old accepted producer replay, shared-cache write, or merge was performed.

## Scope

This is a source-faithful S13/S14 expectation-fee milestone. It does not prove the random-interval theorem application, S11, general S15, DC, any complete original OQ56 root theorem, or a novelty claim. The source p51 is an UNCERTIFIED_REPAIR_CANDIDATE and attributes external ingredients to Shao-Zhou(2016), arXiv:1405.1218v5. Inherited p54 repair boundaries and external-result attribution remain explicit. Original C1/C2 assigned completion is independent of this OQ56 milestone; OQ3 remains separately PAUSED_BY_USER.
