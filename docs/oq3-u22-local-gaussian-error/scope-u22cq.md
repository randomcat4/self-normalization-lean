# OQ3 unit176 CQ — genuine scalar characteristic quadratic remainder from third absolute moment
Exact TWO complete declarations frozen BEFORE implementation. Module Shao.OQ3.ScalarCharacteristicQuadraticRemainder. Imports Mathlib.Analysis.Complex.Exponential, Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic, Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap, Mathlib.MeasureTheory.Measure.Typeclasses.Probability. Namespace Shao.OQ3; open MeasureTheory; scoped Topology BigOperators; noncomputable section. TWOpublictheorems ZEROdefinitions and ZEROstatement letvalues.

Global imaginary-exponential quadratic remainder with explicit K=exp(1)+4, ALLreal t (no smallnesspremise); split |t|<=1 using actualpinnedcomplexseries remainder and |t|>=1 using genuineunitphasemodulus/trianglebound. Then integrate for actualscalarprobabilitynu with genuineIntegrable x,x²,|x|³ and actualmean0, obtaining actualCF minusrealquadraticsecondmoment polynomial, atALLreal t, normerror<=K |t|³ actualthirdabsolutemoment. No assumedCF/Taylor/errorbound, noexponentialmoment/boundedsupport/atoms/density. AllthreeIntegrablepremises explicitauxiliary andlaterderivedforactualcanonicalprojectionsfromBUcoordinateL2/naturalradialmoments; notnewrootassumptions. OrdinaryProd receivesnoinnerproductinstance. Nextprojection/CovI/uniformmoment specialization andlocalGaussiandamping remainOPEN. ActualEdgeworth/derivatives/Fourierintegrals/weightederror/exterior/newrhoLaplace/originalB-DOPEN; correctedA/boundedC/p54/strictrootbeta/attributionunchanged.

Mathlib-only source; primaryactualshared-v34 source consumed atfixedGitpin807d3836 with currentrootacceptedpackageview. norm_exp_sub_sum_le_norm_mul_exp takesANYcomplexx/n anduppernormx^n*exp(normx), nofactorialclaim; norm_integral_le_of_norm_le requiresgenuineIntegrablebound; integral_ofReal/complex_ofReal andIntegrable.ofReal actualsignatures inspected; integral_sub/add usedonlywithgenuineintegrability. Exactimportobjectavailability/pinbinding beforefirstkernel. Twoearlierboundedreadonlybrokerbusyrequests operation_may_have_started=false, nooperation launched; actualprimaryreadlatercompleted. PublicpinnedGitHubrawsourcewasadvisoryfallback only, actualpackageprimarysignatureverifiedaftercapacityreturned (linepositionsdiffer; do notinferbyteidentity). Rootv60receiptc495f3cd checkedc82108f6/tree1039e99c distinct77df0204/35b781a2; PR225305173d6/tree2480c5d5 frozen. No oldgate/sharedwrite. CP175 freshfullreviewACTIVE atfreeze; CQindependentMathlibonlyandnotinCJ–CPpublicationpacket.

```lean
theorem imaginary_exponential_quadratic_remainder_bound (t : ℝ) :
    ‖Complex.exp ((t : ℂ) * Complex.I) -
      (1 + (t : ℂ) * Complex.I - (t : ℂ) ^ 2 / 2)‖ ≤
        (Real.exp 1 + 4) * |t| ^ 3

theorem probability_characteristic_quadratic_remainder_bound
    (nu : Measure ℝ) [IsProbabilityMeasure nu]
    (h1 : Integrable (fun x : ℝ => x) nu)
    (h2 : Integrable (fun x : ℝ => x ^ 2) nu)
    (h3 : Integrable (fun x : ℝ => |x| ^ 3) nu)
    (hmean : (∫ x : ℝ, x ∂nu) = 0) (t : ℝ) :
    ‖(∫ x : ℝ, Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) ∂nu) -
      (1 - (t : ℂ) ^ 2 * ((∫ x : ℝ, x ^ 2 ∂nu) : ℝ) / 2)‖ ≤
        (Real.exp 1 + 4) * |t| ^ 3 * (∫ x : ℝ, |x| ^ 3 ∂nu)
```
