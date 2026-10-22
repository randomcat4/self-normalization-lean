# Anonymous proof: finite actual log-normalizer error N2

Mathematical version N2-v1 for frozen-energy-log-normalizer-v1.md. Complete derivation awaiting independent verification and Lean implementation. No independent certification is claimed here. Only the fixed actual N0 and the accepted actual third-moment lower bound are dependencies; N1 is not used.

## Objects and exact hypotheses

Let ν be any Borel probability measure on ℝ with genuinely integrable x² and |x|³ and ∫x²dν=1. Define the actual β=∫|x|³dν. Let T≥0, M≥0 and β≤M. For every |s|≤T and every

h≥H(M,T)=2(1+M+T+C_Z(T)M),

use the actual N0 normalizer Z=energyNormalizer ν h s, where C_Z(T)=1/8+T/2+exp(4T)T². Define beforehand

C_log(T)=C_Z(T)+4T²+4C_Z(T)².

Thus the error coefficient depends only on T, while the threshold depends only on M,T. There is no original centering or id-integrability hypothesis, and β≥1 and positivity/closeness of Z are not additional inputs.

## 1. Internal moment and height facts

The accepted actual moment inequality follows by integrating 3|x|²≤2|x|³+1 under the genuine integrabilities and unit second moment. It gives β≥1, hence β≥0. C_Z(T)≥0 from its explicit formula. Put A=T+C_Z(T)M≥0. Since H=2(1+M+A), the height assumption gives

h≥2,   β≤M≤h,   2A≤h.

These inequalities do not add M≥1 as a premise; if M<1, the class is empty as a consequence of β≥1 and β≤M. In particular h>0, h≥1 and h≤h³.

## 2. True normalizer closeness and its interval

N0 establishes actual weight integrability and the actual expansion

|Z−1−s/h²|≤C_Z β/h³.

The triangle inequality and |s|≤T therefore give

|Z−1|≤T/h²+C_Z β/h³.

Since h≥1, β≥0 and β≤M,

T/h²≤T/h,
C_Z β/h³≤C_Z M/h.

Consequently |Z−1|≤A/h≤1/2, using 2A≤h and h>0. Therefore 1/2≤Z≤3/2, and Z>0. These are results about the genuine finite N0 integral. No log of a zero/negative value is ever used, and no assumption that s=0 gives Z=1 is made.

## 3. A two-sided pure logarithm remainder

For every z≥1/2, positivity allows the standard real log inequalities

1−1/z≤log z≤z−1.

Thus log z−(z−1)≤0 and

|log z−(z−1)|=(z−1)−log z
≤(z−1)−(1−1/z)=(z−1)²/z≤2(z−1)².

The calculation uses z≥1/2 and a nonnegative square. It applies equally when z≤1 and when z≥1. Taking z=Z is legitimate by §2, so both signs of s and both signs of the logarithm correction are covered.

## 4. Exact square payment with the coefficient four

Let v=Z−1, a=T/h²≥0 and b=C_Z β/h³≥0. Section 2 gives |v|≤a+b, and (a+b)²≤2a²+2b². Hence

2v²≤4T²/h⁴+4C_Z²β²/h⁶.

No coefficient is enlarged. Internal β≥1 and h≥1 imply βh≥1, so

1/h⁴≤β/h³.

Also β≤M≤h≤h³ and β≥0 imply β²≤βh³. Dividing by h⁶>0 gives

β²/h⁶≤β/h³.

Therefore

2v²≤(4T²+4C_Z²)β/h³.

This is precisely the absorption of β² into the common height threshold. There is no M in the final error coefficient.

## 5. Actual log-normalizer theorem

The exact decomposition is

log Z−s/h² = [log Z−(Z−1)] + [Z−1−s/h²].

Apply the triangle inequality, §3, §4, and N0's actual expansion to obtain

|log Z−s/h²|
≤2(Z−1)²+C_Zβ/h³
≤[C_Z+4T²+4C_Z²]β/h³
=C_log(T)β/h³.

Both C_Z and C_log are fixed functions of T alone; all quantitative assumptions and the threshold remain the frozen expressions. For a fixed law one may choose M=β to obtain the original sufficiently-large-height assertion, without changing the T-only error coefficient.

## Boundaries and scope

T=0 and s=0 are retained. At s=0, Z is the actual closed-cutoff mass, which may be less than one, and the proof pays its nonzero logarithm. Atoms at zero and ±2h, the strict tail complement, arbitrary unbounded support, nonsymmetry and lack of a density are inherited unchanged from N0. No fourth/exponential moment, original center, id-integrability, assumed β≥1, Z-closeness, Z-positivity or desired log bound has entered the hypotheses.

Only N2 is proved. This neither constructs nor certifies N1, nor proves E2 exact linear recentering, E3 path density, E4 energy concentration, B1, BE/SP, K/Kv, random denominator or any complete root theorem. All complete roots remain OPEN.
