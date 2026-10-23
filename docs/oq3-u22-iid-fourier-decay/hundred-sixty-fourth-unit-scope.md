# OQ3 unit164 CE — exact normalized frequency scale and strict-threshold cubic cutoff damping
Exact complete declarations and ALL statement let values frozen BEFORE implementation. Module Shao.OQ3.NormalizedIIDPairFrequencyDecay. Import ONLY Shao.OQ3.NormalizedIIDPairCharacteristic. Namespace Shao.OQ3; open MeasureTheory ProbabilityTheory; scoped Topology BigOperators; noncomputable section. THREE public theorems zero definitions.

Source critical Fourier power ledger: derive the exact Euclidean length of frequency/sqrt n and its threshold equivalence; rewrite actual normalizedsum weak-Cramer bound as exp(-c*n^(1+beta/2)*Euclideanlength^(-beta)); then for the WHOLE actual annulus sqrt n*R<Euclideanlength<=n³ derive exp(-c*n^(1-(5/2)beta)) with the positive exponent guaranteed by the retained STRICTbeta<2/5. No desired actualnormalizedsum error/decay premise; input is the genuine one-observation Fourier weak-Cramer inequality on an actual probability law, as supplied later by BU. No moment/atomlessness/density/Hilbert structure or mean0/covI premise needed for this auxiliary high-frequency estimate. Rootstrict0<beta<2/5 remains unchanged; helpers valid atbeta0 do not weaken root assumptions.

```lean
theorem scaled_iid_pair_frequency_length
    (n : ℕ) (hn : 1 ≤ n) (xi eta R : ℝ) :
    Real.sqrt ((xi / Real.sqrt (n : ℝ)) ^ 2 + (eta / Real.sqrt (n : ℝ)) ^ 2) =
      Real.sqrt (xi ^ 2 + eta ^ 2) / Real.sqrt (n : ℝ) ∧
    (R < Real.sqrt ((xi / Real.sqrt (n : ℝ)) ^ 2 + (eta / Real.sqrt (n : ℝ)) ^ 2) ↔
      Real.sqrt (n : ℝ) * R < Real.sqrt (xi ^ 2 + eta ^ 2))

theorem normalized_iid_pair_weak_cramer_power_bound
    (law : Measure (ℝ × ℝ)) [IsProbabilityMeasure law]
    (n : ℕ) (hn : 1 ≤ n) (beta c R : ℝ)
    (hbeta : 0 ≤ beta) (hc : 0 < c) (hR : 0 ≤ R)
    (hWC : ∀ u v : ℝ, R < Real.sqrt (u ^ 2 + v ^ 2) →
      ‖(∫ w : ℝ × ℝ,
        Complex.exp (((u * w.1 + v * w.2 : ℝ) : ℂ) * Complex.I) ∂law)‖ ≤
          1 - c * Real.rpow (Real.sqrt (u ^ 2 + v ^ 2)) (-beta))
    (xi eta : ℝ)
    (hfreq : Real.sqrt (n : ℝ) * R < Real.sqrt (xi ^ 2 + eta ^ 2)) :
    let Q : Measure (Fin n → (ℝ × ℝ)) := Measure.pi (fun _ : Fin n => law)
    let S : (Fin n → (ℝ × ℝ)) → (ℝ × ℝ) := fun z =>
      (Real.sqrt (n : ℝ))⁻¹ • ∑ i : Fin n, z i
    let rho : Measure (ℝ × ℝ) := Q.map S
    ‖(∫ w : ℝ × ℝ,
      Complex.exp (((xi * w.1 + eta * w.2 : ℝ) : ℂ) * Complex.I) ∂rho)‖ ≤
        Real.exp (-c * Real.rpow (n : ℝ) (1 + beta / 2) *
          Real.rpow (Real.sqrt (xi ^ 2 + eta ^ 2)) (-beta))

theorem normalized_iid_pair_weak_cramer_cubic_cutoff_bound
    (law : Measure (ℝ × ℝ)) [IsProbabilityMeasure law]
    (n : ℕ) (hn : 1 ≤ n) (beta c R : ℝ)
    (hbeta : 0 ≤ beta) (hbetaUpper : beta < (2 : ℝ) / 5)
    (hc : 0 < c) (hR : 0 ≤ R)
    (hWC : ∀ u v : ℝ, R < Real.sqrt (u ^ 2 + v ^ 2) →
      ‖(∫ w : ℝ × ℝ,
        Complex.exp (((u * w.1 + v * w.2 : ℝ) : ℂ) * Complex.I) ∂law)‖ ≤
          1 - c * Real.rpow (Real.sqrt (u ^ 2 + v ^ 2)) (-beta))
    (xi eta : ℝ)
    (hfreq : Real.sqrt (n : ℝ) * R < Real.sqrt (xi ^ 2 + eta ^ 2))
    (hcutoff : Real.sqrt (xi ^ 2 + eta ^ 2) ≤ (n : ℝ) ^ 3) :
    let Q : Measure (Fin n → (ℝ × ℝ)) := Measure.pi (fun _ : Fin n => law)
    let S : (Fin n → (ℝ × ℝ)) → (ℝ × ℝ) := fun z =>
      (Real.sqrt (n : ℝ))⁻¹ • ∑ i : Fin n, z i
    let rho : Measure (ℝ × ℝ) := Q.map S
    0 < 1 - (5 / 2 : ℝ) * beta ∧
      ‖(∫ w : ℝ × ℝ,
        Complex.exp (((xi * w.1 + eta * w.2 : ℝ) : ℂ) * Complex.I) ∂rho)‖ ≤
          Real.exp (-c * Real.rpow (n : ℝ) (1 - (5 / 2 : ℝ) * beta))
```

ALL Q/S/rho values are complete above and identical to actual CD normalizediidlaw (ordinaryrealpair with literal coordinate Fourier pairing). The frequency length is always explicit sqrt(xi²+eta²), NOT the pairMAXnorm. No unproved threshold/rpow/n-power rewrite or loss of cutoff endpoints: lowfrequency bound strict, cubicuppercutoff closed. The full annulus can be empty for small n without any omitted case. Constants n,beta,c,R and law keep their exact quantifier order.

Proofplan: n>=1 yieldspositiveNandpositive sqrtN. Divide sum ofcoordinate squares bysqrtN², applysqrt_div andsqrt_sq; lt_div_iff givesexactthreshold. Rpow_div fornonnegative Euclideanlength/sqrtN, rpow_mul using(sqrtN)²=N, rpow_neg andrpow_add give exactNcoefficient. Apply CD's actualFarbound unchanged. Atcubiccutoff, actualfrequencypositive followsfromR>=0 andstrictlowerthreshold; rpow_le_rpow_of_nonpos givesr^-beta>=(N³)^-beta, rpow_natCast_mul/rpow_add identifycombinedNpower asN^(1-5beta/2). Multiplying bynegativec reverses inequality and expmonotonicity givesclaimedupperbound; positivityofexponentisrationalarithmeticfromSTRICTbetaUpper.

CD163 source22120e1075826e4a26411834c4aff8e645dbff2a59b4ed539d5067e0080ac6ca receipt2cfbe8184271b2af0fbbed9f6855a6613b87a65bb76caffe012cb858c7783df8 firstkernel/wholeactual4std3PASS. DIFFERENTfreshNONAUTHOR CDfullreviewACTIVE at freeze; CE cannotqualifyuntilCDreviewqualifies. Primary exactpinnedMathlib807d3836b165983210ee2ecf3cd28f239436949c interfaces read: Real.sqrt_div inAnalysis/Real/Sqrt.lean377, sqrt_sq; Real.rpow_add207,rpow_neg259,rpow_mul414,div_rpow488,rpow_natCast_mul517,rpow_le_rpow_of_nonpos565 inAnalysis/SpecialFunctions/Pow/Real.lean. All positivity/negative-exponent conditionsexplicit. ExactCD/serverhashbindingbeforefirstkernel; no oldproof/checkreplay.

Current active feat/oq3-standardized-cell-comparison e730ce575b5015cf5c86816427673bde6c7c362a tree721b570cdf8c99a29296881f69599ac37a36d09c, PR221 frozenrootintake stackedonPR217. CC162 separateunpublishedqualifiedsource12cfbab4/reportd65da3c8, no sourcechanging. Rootv59 receipt30f1cbf1885bfbd141c23a68844696af992cb4b31eb21afc93b6d912da425ccc checkedcode29c9804c552f0cc494355e6556c112aa3c36c908, acceptedregistryd9956f24/mainb6bdf733 distinct. CPU14–17 max1heavy/nativeM8192/j4/autoImplicitfalse ALLLeanserveronly, onechildlease1. No localLean/cache/package/sharedwrite/math-ultra/newsidebar/crossmessages/sorry/admit/newaxiom/unsafe/native_decide/implemented_by/weakenedsettings. Allactualownersinclgenerated/fulltypes/allvalues requirefreshindependentcompleteproof/semanticreview and recursiveAXstd3; preservefirstPASS exact/allfailures/warnings, no cosmeticedit/replay.

This closes only zeroth-order far-frequency damping on the finite cutoff. It does NOT control derivatives or integrate Fourier errors, prove small/middle frequency estimates, actual signedEdgeworthmeasure/smoothing/inversion or originalprobabilityasymptotic. ActualSongEdgeworth/weightederror/exterior/newrhoLaplace/B-DOPEN, correctedA/boundedC/p54/strictthreshold/externalattribution preserved.
