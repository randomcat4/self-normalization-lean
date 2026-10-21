# Positivity, inverse powers, and logarithmic error of the free coefficient

Let ν be a Borel probability law on ℝ with the three displayed genuine
integrabilities of y, y², and |y|³, mean zero, and second moment one.
Write β=∫|y|³dν. Fix M≥0 with β≤M and h≥1 with π(1+M)≤h. Throughout,
ρ is the actual free coefficient cosineCoefficient ν (π/(2h)).
No killed-kernel spectral interpretation is made.

The certified cubic coefficient remainder gives, without any extra moment,

    |ρ−(1−π²/(8h²))| ≤ π³M/(48h³).

The threshold implies π≤h and πM≤h. Put q=π²/h². Then 0<q≤1 and
πM/h≤1, so the remainder is at most q/48. In particular it is at most
q/16. The two sides of the absolute-value bound consequently give

    1−q/4 ≤ ρ ≤ 1−q/16.

Since q≤1 and q>0, this proves 3/4≤ρ<1, and in particular ρ>0.

For the inverse powers, put u=1−ρ. We have 0≤u≤q/4 and ρ≥3/4≥1/2.
The elementary logarithm inequality 1−ρ⁻¹≤logρ gives

    −logρ ≤ ρ⁻¹−1 = u/ρ ≤ 2u ≤ q/2.

Multiplication by each nonnegative integer n and monotonicity of exp give

    (ρⁿ)⁻¹ = exp(−n logρ) ≤ exp(π²n/(2h²)).

This includes n=0. If n≤2h², its exponent is at most π². For
m=⌊h²⌋₊, the floor bound m≤h² gives 2m≤2h². Also h²≥1, so
m+1≤h²+1≤2h². Thus both required inverse powers, with exponents m+1
and 2m, are at most exp(π²).

For the logarithmic error, the two elementary logarithm inequalities

    1−ρ⁻¹ ≤ logρ ≤ ρ−1

give a convenient safe quadratic estimate directly:

    |logρ+(1−ρ)|
      = (ρ−1)−logρ
      ≤ (ρ−1)−(1−ρ⁻¹)
      = (1−ρ)²/ρ
      ≤ 2(1−ρ)².

Here only ρ≥1/2 is used in the last comparison. This avoids needing a
logarithmic series remainder. Since 0≤u≤q/4, the quadratic term is at
most q²/8=π⁴/(8h⁴). Combining this with the certified cubic remainder
by the triangle inequality yields

    |logρ+π²/(8h²)|
      ≤ π³M/(48h³)+π⁴/(8h⁴)
      ≤ [π³M/48+π⁴/8]/h³,

where the last step uses h≥1 and positivity of h. Finally, for each
natural N, the expression N logρ+π²N/(8h²) is exactly
N[logρ+π²/(8h²)]. Absolute-value multiplicativity and N≥0 give the
stated bound [π³M/48+π⁴/8]N/h³, including N=0.

All constants are explicit and depend only on the displayed fixed M.
No density, symmetry, fourth moment, bounded increment, or lattice
condition is used. These estimates close only the stated free-coefficient
positivity and finite normalization/logarithmic calculations. B1, O0,
R3/R4, the killed-kernel spectral question, long-time limits, 4/π, and
the root K/Kv/OQ4 claims remain OPEN.
