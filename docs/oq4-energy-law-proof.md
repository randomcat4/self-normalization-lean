# Anonymous proof: actual normalized energy law and finite moment bounds N1

Mathematical version N1-v1, for frozen-energy-tilted-law-v1.md. Complete derivation, awaiting independent verification and Lean implementation. This document does not self-certify independent review. N0 source bd801 and anonymous proof afe5 remain unchanged and are used read-only.

## Objects and explicit hypotheses

Let ν be any Borel probability measure on ℝ, with genuinely integrable x² and |x|³ and ∫x²dν=1. Write β=∫|x|³dν. Fix T≥0, h≥1 and |s|≤T. Use exactly the N0 functions B={|x|≤2h}, w=energyWeight h s, Z=energyNormalizer ν h s, and C_Z(T)=1/8+T/2+exp(4T)T².

Set E=exp(4T), C1=1/4+ET, C2=1/2+2ET, D=(4/3)E,
Cμ=D C1, Cm2=D(C2+T+C_Z), Cm3=D E.

All are finite and nonnegative and depend only on T. Only the mean conclusions additionally assume the original centering equation ∫x dν=0. There are no assumptions of id-integrability, β≥1, Z>0, a numerator estimate, a normalized moment estimate, symmetry, density, bounded support, a fourth/exponential moment, or exact centering after tilting.

## 1. Internal integrability of id and the actual moment lower bound

The pointwise bound |x|≤1+x² and the square integrability assumption under a probability law imply genuine integrability of id and |id| by an integrable majorant. Also 3|x|²≤2|x|³+1 follows from (|x|−1)²(2|x|+1)≥0. Integrating using the genuine square/cube integrabilities gives 3≤2β+1, hence β≥1. This is the already accepted actual moment inequality, not an additional distribution condition. In particular β≥0.

## 2. The actual measure and its probability normalization

Define energyTiltedLaw ν h s by the actual nonnegative density w/Z with respect to ν, for example ν.withDensity(x↦ENNReal.ofReal(w(x)/Z)). This definition depends on ν,h,s only, without T. Totalized real division defines a measure even at non-admissible parameters; all subsequent claims retain the admissible hypotheses above.

N0 supplies actual Borel measurability, nonnegativity, and genuine integrability of w, together with

(3/4)exp(−4T) ≤ Z ≤ E.

Thus Z is finite and strictly positive. Consequently w/Z is Borel, nonnegative and integrable, and its actual integral is Z/Z=1. The withDensity total mass is therefore exactly one, proving IsProbabilityMeasure for the constructed law. Positivity of Z and normalization have been proved from N0, not assumed.

For any Borel A, w1_A is genuinely integrable by restriction of the already integrable weight. The real measure identity is

energyTiltedLaw ν h s .real A = (∫_A w dν)/Z.

It follows from the nonnegative density definition and the true finite integral identity; no infinite-mass division convention is used. Since w=0 on the strict complement D={2h<|x|}, its tilted mass is zero. Hence |x|≤2h almost surely under the tilted law, with the truncation endpoints retained.

Let f be any Borel real function with fw genuinely ν-integrable. Nonnegativity of w gives |f|w=|fw|. Therefore ∫|f|(w/Z)dν=(∫|fw|dν)/Z<∞. The density criterion proves genuine tilted integrability of f, and change of measure gives the exact Bochner identity

∫f d(energyTiltedLaw ν h s) = (∫fw dν)/Z.

This implication is only asserted under the displayed Borel and weighted-integrability hypotheses. It makes no assertion for arbitrary nonintegrable f or for parameter joint kernel measurability.

## 3. Weighted and tilted integrability of the three moment functions

N0 gives 0≤w≤E. The genuine integrability of id from §1, square from the hypotheses and cube from the hypotheses implies respectively

|xw|≤E|x|,   |x²w|≤Ex²,   ||x|³w|≤E|x|³.

All functions are Borel, so these integrable majorants prove actual ν-integrability of all three weighted functions. The change-of-measure interface then proves actual tilted integrability of id, square and absolute cube. This holds without original centering. Closed support is a conclusion about the constructed law, not a restriction on ν.

## 4. Exact exponential difference payment

For any real u with |u|≤4T, the ordinary mean-value theorem applied to the actual exponential gives

|exp(u)−1|≤E|u|.

For u=0 this is equality. Otherwise the slope is exp(ξ) at a ξ between 0 and u; ξ≤4T implies exp(ξ)≤E. Thus the same bound holds for both signs of u. On B, N0's argument bounds give |s x²/h²|≤4T, so

|exp(sx²/h²)−1| ≤ E|s|x²/h² ≤ ET x²/h².

No exponential moment of ν is used: the estimate is confined to the actual closed truncation region.

## 5. Mean numerator, only when the original law is centered

Assume ∫x dν=0. Decompose, with every term genuinely integrable,

∫xw dν = ∫_B x dν + ∫_B x[exp(sx²/h²)−1]dν
= −∫_D x dν + ∫_B x[exp(sx²/h²)−1]dν.

N0's tail first-absolute-moment payment gives |∫_D x dν|≤β/(4h²). The difference estimate gives the pointwise majorant

1_B |x| |exp(sx²/h²)−1| ≤ ET |x|³/h².

This majorant also justifies the correction integral's genuine integrability. Therefore its absolute integral is at most ETβ/h², and

|∫xw dν|≤(1/4+ET)β/h²=C1β/h².

Only this paragraph and its normalized mean consequence use original centering.

## 6. Second and third moment numerators

Using the unit original second moment, the genuine integrable decomposition gives

∫x²w dν−1 = −∫_D x²dν + ∫_B x²[exp(sx²/h²)−1]dν.

The first absolute term is at most β/(2h), by N0. The correction has integrable majorant (ET/h²)1_B x⁴; N0 proves genuine integrability and ∫_B x⁴≤2hβ. Hence

|∫x²w dν−1|≤β/(2h)+(ET/h²)(2hβ)=C2β/h.

For the absolute cube, nonnegativity and w≤E give, with true integrability already proved,

0≤∫|x|³w dν≤Eβ.

No original centering is used here.

## 7. Normalize without losing any constant

The positive N0 lower bound implies

1/Z ≤ [(3/4)exp(−4T)]⁻¹ = (4/3)exp(4T)=D.

Use the exact change-of-measure formula. The mean numerator bound immediately gives

|∫x d(energyTiltedLaw ν h s)|≤D C1β/h²=Cμβ/h²

when the original mean is zero. Likewise the third numerator gives

∫|x|³ d(energyTiltedLaw ν h s)≤D Eβ=Cm3β.

For the second moment it is essential to compare its numerator M2 with Z, not merely with one:

|M2/Z−1|=|M2−Z|/Z≤D(|M2−1|+|Z−1|).

N0's exact expansion and |s|≤T imply

|Z−1|≤T/h²+C_Zβ/h³.

Since h≥1 and the internal moment bound β≥1 gives βh≥1, one has T/h²≤Tβ/h. Also h²≥1 and C_Z≥0 give C_Zβ/h³≤C_Zβ/h. Thus

|Z−1|≤(T+C_Z)β/h.

Combining with §6 yields

|∫x² d(energyTiltedLaw ν h s)−1|
≤D(C2+T+C_Z)β/h=Cm2β/h.

This proves the precise frozen coefficient including both T and C_Z. No height threshold beyond h≥1, no β≤M bound, and no enlarged constant is used.

## Boundaries and scope

At T=0, admissibility forces s=0 and the actual law is the probability-normalized closed truncation, generally different from ν. It retains all original atoms on B, with atom mass exp(sa²/h²)ν.real{a}/Z, and removes the strict complement only. Cases h=1, x=0 and equality |x|=2h remain. All conclusions hold for arbitrary original unbounded support and nonsymmetry.

The tilted mean is controlled but generally nonzero. The second-moment statement is about the raw moment around zero, not unit variance or exact centering. This proves only N1. It proves no log Z precision, E2 linear tilt/exact recentering, E3 path-density identity, E4, K/Kv, B1, BE/SP, random denominator, or complete root theorem. All complete roots remain OPEN.
