# S3-DOM / S3-ALG / S3-MAIN: complete proof for the fixed actual objects

STATUS: PROVED (RELATIVE_TO_FIXED_ACTUAL_S2_AND_ORIGINAL_BROWNIAN_INPUT)
ROLE: ANONYMOUS_MATHEMATICAL_AUTHOR
UNIT_KIND: DERIVED_ASSEMBLY
NEW_RAW_LEAF_INCREMENT: 0
SOURCE_RAW_DENOMINATOR_DELTA: 0
LEAN_STATUS: NOT_RUN
IMPLEMENTATION_AUTHORIZATION: NONE
UPSTREAM_U1_FORMAL_STATUS: PENDING
UPSTREAM_S2_FORMAL_STATUS: OPEN
ACTUAL_BROWNIAN_INTERFACE_OWNER: ROOT
ACTUAL_BROWNIAN_INTERFACE_STATUS: PENDING
S3_S4_S5_SPECTRUM_OQ4_ROOT_STATUS: OPEN

This is an author's mathematical proof of the exact frozen outputs, relative to the fixed actual S2 F0/Q1 outputs and the original actual Brownian leading equivalence. It is not an independent review or a formal certificate. It neither proves those upstream inputs nor declares their formal interfaces closed. No alternative probability law, free error sequence, additional asymptotic premise, or new axiom is introduced.

## 0. Input identity and scope of consumption

All four permitted mathematical inputs were read in full and their original bytes verified:

| Input | Bytes | SHA256 |
| --- | ---: | --- |
| C:/game/shao lean/drafts/oq4/frozen-rademacher-s3-brownian-assembly-v1.md | 14243 | 19f162418e88f7b3ddea57e1c735404f94fd3e50fbd471bfd937eaf93424a71c |
| C:/game/shao lean/drafts/oq4/frozen-rademacher-s2-assembly-v1.md | 8318 | c59971859b432bf312d5c1d65ca82d0a02254c06d4d56833322364f87f69146e |
| C:/game/shao/current/oq4/frozen01.md | 1491 | ea50b9fe0d742cbc9481fb126476ae2a788c7b0ec42d4e60636d757baf7cbc5a |
| C:/game/shao/current/oq4/c01/spectrum01.md | 4306 | b65f9e0c2f9b40a28d092491b479bd20d0b8ee8a9ac940c3c4760cfff7d2670b |

The supplied original source commit is 35d4580b61e22e7145f47730045a09874ef93259. No Git query was made.

Only the actual S2 F0/Q1 outputs are consumed. In particular D -> 1, eventual actual p positivity, and log D -> 0 are outputs of that fixed interface, not added hypotheses about an arbitrary D. No S2 proof was read.

Only the original actual Brownian equivalence

  P_B(U <= x) ~ (4/pi)*exp(-pi^2/(8x^2)), as x decreases to 0,

is consumed, for the same actual U = sup_{0 <= t <= 1}|B_t|. The stronger relative exponential O rate printed in spectrum01.md is not an available input and is never used below.

## 1. Boundary attack before the proof

The following attempted failure modes must be resolved without changing the statement.

1. Early n = 0: F0 retains p = K = 1, the central zero mode, and its 0^0 convention. Ordinary x = h/sqrt(N) and probability logs need not be legal there. A positive-time tail must follow from N/H^2 -> infinity, not from an extra all-index time premise.
2. Small cells m = 1 and m = 2: they cannot be removed to simplify remainders. The proof will consume all-time F0, without altering any remainder or zero mode. Its finite inequalities need only H >= 2 and h >= 1.
3. Weak integer boundary h = m: h must stay unchanged, especially in the Brownian argument and centering. The only threshold comparison used below is H - 1 <= h < H. No strict event or shifted h is introduced.
4. Irregular sequences and parity: neither divergence premise implies monotonicity. Every conjunction of eventual conclusions must use a finite maximum of independently obtained thresholds; parity will not enter.
5. Legality of actual Brownian logs: leading equivalence must itself yield positivity of the actual b_U near 0. Neither a free tail function nor a global positivity assumption is allowed.
6. Strength of the target: an error negligible only after division by N/h^2 would be insufficient. The exact centered difference must be log D - log T_U, with an absolute limit 0.
7. Total functions: Real.log(0) and total Real division cannot substitute for a common positive tail. Total syntax, if used, must eventually equal the already legal ordinary expression.

No counterexample is obtained from these cases. Sections 3-10 establish each required resolution.

## 2. Objects, quantifiers, and fixed relative inputs

Natural numbers include 0. Take arbitrary maps

  m_: N -> N, n_: N -> N, h_: N -> R

satisfying, for every k,

  1 <= m_k,  (m_k : R) <= h_k < (m_k : R) + 1.

Set

  H_k = (m_k : R)+1,
  N_k = (n_k : R),
  t_k = N_k/H_k^2.

The only asymptotic hypotheses are:

  for every real T there is a natural K_H(T) such that
    k >= K_H(T) implies H_k >= T;

  for every real T there is a natural K_t(T) such that
    k >= K_t(T) implies t_k >= T.

Each threshold notation denotes a witness to its displayed existential statement. No monotonicity of the sequences or of the witness choices is required.

Pair means Shao.OQ4.RademacherSpectralPairing and Scalar means Shao.OQ4.RademacherScalarBounds, with their actual fixed S2 meanings. For arbitrary finite m >= 1, weak-cell h, and n in N, let

  H = (m : R)+1, N = (n : R),
  a = Pair.amplitude m, rho = Pair.rho m,
  eps = Pair.epsilon m n = (-1 : R)^(n+m),
  R = Pair.remainder m n,
  u = Scalar.u m, q = (Real.tan u)^2,
  A = a*rho^n.

A is only S2's B_mn under a different letter, to avoid colliding with Brownian B. R is exactly Pair.remainder with its finite normalizedTerm sum and zeroMode/A term. It is not selected as a free error. The same transparent actual definitions are retained:

  u = pi/(4H) = Pair.alpha m 0,
  Scalar.z m = pi/(2H) = Pair.beta m 0,
  a = (1/H)*(cos u/sin u) = Scalar.a m,
  rho = cos(pi/(2H)) = Scalar.rho m.

No Taylor estimate for these functions is used.

Let nu_R = Shao.OQ4.RademacherCosine.law with its fixed probability witness law_isProbabilityMeasure. Retain exactly

  p(n,h) =
    (Measure.pi (fun _ : Fin n => nu_R)).real (@Shao.closedStrip n h),

  K(n,h) =
    @Shao.OQ4.killedMass nu_R law_isProbabilityMeasure h n 0,

  D(m,n,h) = p(n,h)/A.

Thus p is the actual Rademacher product-measure probability of the weak closedStrip event from 0. It is not defined by a spectral sum. Subscripts k always evaluate these same objects at (m_k,n_k,h_k).

Fixed S2 F0 supplies, for every finite allowed m,h,n, including n = 0,

  a > 0, 0 < rho < 1, A > 0,
  p = K,
  p = A*(1+eps*q+R),
  D = K/A = 1+eps*q+R.                             (2.1)

Because A > 0 and D = p/A, multiplying by A gives

  p = A*D.                                        (2.2)

At n = 0, F0 has p = K = 1, preserving the specified central term and 0^0 convention. No finite case is removed.

The chosen sequences satisfy exactly the pointwise domain and the two divergence hypotheses of fixed S2 Q1. We therefore consume its actual conclusions

  D_k -> 1,                                       (2.3)
  eventually D_k > 0, p_k > 0, K_k > 0,            (2.4)
  log(D_k) -> 0 on that positive tail.             (2.5)

For explicit later use, (2.3) means that for each eta > 0 there exists K_2D(eta) with

  k >= K_2D(eta) implies |D_k-1| < eta.             (2.6)

Conclusion (2.5) means that for each e > 0 there exists K_2log(e) with

  k >= K_2log(e) implies D_k > 0 and |log(D_k)| < e. (2.7)

If Q1 presents a logarithmic witness and positivity witness separately, take their finite maximum when choosing K_2log(e). We will also explicitly recover positivity of p and K from (2.2) and (2.6). These are fixed-output applications; they add no premise about D and do not assert U1 or S2 formal closure.

Keep B, U, and P_B exactly as in the original frozen question:

  U = sup_{0 <= t <= 1}|B_t|,
  b_U(x) = P_B(U <= x), for real x.

No coupling or independence relation with the Rademacher law is needed, since only marginal probabilities are compared. Define

  lambda = pi^2/8, c = 4/pi,
  g(x) = c*exp(-lambda/x^2), for x > 0,
  T_U(x) = b_U(x)/g(x), for x > 0.

The given actual Brownian leading equivalence has precisely this normalized consumption:

  for each eta > 0 there exists d_U(eta) > 0 such that
    0 < x < d_U(eta) implies |T_U(x)-1| < eta.      (2.8)

This is the original equivalence for the fixed actual b_U, not a freely instantiable function hypothesis.

For every k use the deterministic main term

  G_k = c*exp(-lambda*N_k/h_k^2).                   (2.9)

If all-index total syntax is desired, use exactly

  xhat_k = h_k/Real.sqrt(N_k),
  W_k = b_U(xhat_k)/G_k.                           (2.10)

Under total Real division, xhat_k = 0 when n_k = 0. This assigns no new value to b_U(0), and gives no ordinary quotient interpretation at zero time. For N_k > 0 write x_k = h_k/sqrt(N_k) in the ordinary sense. The eventual equality xhat_k = x_k will always accompany its use.

## 3. All domain and scale conclusions

For every k the cell domain and cast order give

  H_k >= 2,
  h_k >= (m_k : R) = H_k-1 >= 1,
  0 < h_k < H_k,
  H_k^2 > 0, h_k^2 > 0, N_k >= 0.                 (3.1)

Squaring on positive reals yields h_k^2 < H_k^2. In particular all all-index divisions by h_k^2 and H_k^2 are ordinary and legal.

For any real T and k >= K_H(T+1),

  h_k >= H_k-1 >= (T+1)-1 = T.                    (3.2)

Thus h_k -> infinity, with no requirement that h be monotone.

Let s_k = N_k/h_k^2. Exact field arithmetic and (3.1) give

  s_k-t_k =
    N_k*(H_k^2-h_k^2)/(h_k^2*H_k^2) >= 0.          (3.3)

For every real T, k >= K_t(T) implies s_k >= t_k >= T. Therefore

  N_k/h_k^2 -> infinity.                          (3.4)

This comparison does not replace h by H in a Brownian argument or centering term.

Set

  K_time = K_t(1).                                (3.5)

For every k >= K_time, t_k >= 1. Multiplying by H_k^2 > 0 gives

  N_k >= H_k^2 >= 4 > 0.                          (3.6)

If n_k = 0 its real cast N_k would be 0, contrary to (3.6). A nonzero natural is at least 1, so on this whole tail

  1 <= n_k and N_k > 0.                           (3.7)

This is derived from the given divergence, not added as an all-index hypothesis.

The nonnegative square root satisfies, for N_k > 0,

  sqrt(N_k) > 0 and (sqrt(N_k))^2 = N_k.           (3.8)

Since h_k > 0, x_k > 0 on this tail. Nonzero-denominator field arithmetic gives

  x_k^2 = h_k^2/(sqrt(N_k))^2 = h_k^2/N_k,
  1/x_k^2 = N_k/h_k^2,
  x_k^2 <= H_k^2/N_k = 1/t_k.                     (3.9)

The inequality uses positive N_k and h_k^2 <= H_k^2. The last equality uses N_k != 0 and H_k != 0.

For any d > 0 choose

  K_x(d) = max(K_time, K_t(2/d^2)).                (3.10)

At every k >= K_x(d), t_k >= 1 and t_k >= 2/d^2 > 0. Inverting the latter positive inequality in (3.9) gives

  0 < x_k^2 <= 1/t_k <= d^2/2 < d^2.

Since x_k,d are positive, strict monotonicity of squaring implies x_k < d. Thus, with an explicit threshold,

  for every d > 0 and k >= K_x(d),
  N_k > 0, sqrt(N_k) > 0, 0 < x_k < d.            (3.11)

This is the required positive-side x_k -> 0 for the actual h_k/sqrt(N_k). Also xhat_k = x_k on this tail.

For completeness N_k -> infinity follows without another hypothesis. Given real T, let
K_N(T) = max(K_time,K_H(max(2,T+1))). For k above it,
H_k >= 2 and H_k >= T+1, hence
N_k >= H_k^2 >= H_k >= T+1 > T. This extra scale output is not used as a premise.

## 4. Complete finite deterministic S3-ALG bridges

Fix arbitrary finite m >= 1, weak-cell h, and natural n >= 1. Use the objects H,N,a,rho,A from Section 2, and x = h/sqrt(N). The cast gives N > 0; the cell gives h >= 1 > 0. The square root is positive and squares to N. With r = sqrt(N), the nonzero facts r != 0, N != 0, h != 0 justify

  x^2 = (h/r)^2 = h^2/r^2 = h^2/N,
  1/x^2 = 1/(h^2/N) = N/h^2.                     (4.1)

Also x > 0. This proves all the square, reciprocal, and square-root bridges without using a total-division exceptional value.

Since pi > 0, c = 4/pi > 0 and lambda = pi^2/8 > 0. Since exp(v) > 0 for every real v, g(x) > 0 for every x > 0. Similarly, h_k^2 > 0 at all indices, so (2.9) gives G_k > 0 for every k, including n_k = 0.

The reciprocal bridge gives

  -lambda/x^2 = -lambda*(1/x^2) = -lambda*N/h^2,

and therefore

  g(x) = (4/pi)*exp(-lambda*N/h^2) = G.            (4.2)

For the sequence this holds for all k >= K_time. Thus

  W_k = b_U(xhat_k)/G_k
      = b_U(x_k)/g(x_k)
      = T_U(x_k).                                 (4.3)

Only positive time is needed for this equality; Brownian positivity has not yet been assumed.

We check the natural-power/cast identity explicitly. For every natural n and rho > 0,

  log(rho^n) = (n : R)*log(rho) = N*log(rho).       (4.4)

At n = 0 both sides are 0, since rho^0 = 1 and log(1) = 0. If the identity holds at n, then rho^n > 0 and rho > 0, and

  log(rho^(n+1))
    = log(rho^n*rho)
    = log(rho^n)+log(rho)
    = (n : R)*log(rho)+log(rho)
    = ((n : R)+1)*log(rho)
    = ((n+1 : N) : R)*log(rho).

Positivity of rho^n itself follows by induction: rho^0 = 1 > 0, and a positive product stays positive. This proves (4.4) for natural powers, with N exactly the real cast of the same n, not an independent time or real-power exponent.

Since a > 0 and rho^n > 0, the positive product log identity gives

  log(A) = log(a*rho^n) = log(a)+N*log(rho).        (4.5)

With v = -lambda*N/h^2 and using (4.2), c > 0, exp(v) > 0, and log(exp(v)) = v give

  log(g(x))
    = log(c)+log(exp(v))
    = log(4/pi)-lambda*N/h^2.                      (4.6)

Finally, because pi != 0 and 4 != 0, exact field arithmetic gives

  a/c = a/(4/pi) = a*pi/4 = pi*a/4 > 0.

The positive quotient log identity therefore yields

  log(a)-log(4/pi)
    = log(a)-log(c)
    = log(a/c)
    = log(pi*a/4).                                 (4.7)

Every logarithm in these bridges has a positive argument. None uses log_abs or an exceptional value of Real.log.

## 5. Actual Brownian normalization and local positivity

For any eta > 0 choose the actual Brownian neighborhood d_U(eta) > 0 from (2.8), and set

  K_U(eta) = K_x(d_U(eta)).                        (5.1)

For every k >= K_U(eta), (3.11) gives 0 < x_k < d_U(eta). Hence the actual equivalence yields

  |T_U(x_k)-1| < eta.                              (5.2)

Thus T_U(x_k) -> 1 on the positive-time tail. The exact eventual equality (4.3) proves as well that the total actual ratio W_k -> 1. These conclusions use the actual b_U, not an arbitrary normalized law or free vanishing error.

Choose once

  d_pos = d_U(1/2) > 0.                            (5.3)

For every real x with 0 < x < d_pos, (2.8) implies

  |T_U(x)-1| < 1/2, hence 1/2 < T_U(x) < 3/2.       (5.4)

Since g(x) > 0, multiplying its actual defining quotient gives

  b_U(x) = g(x)*T_U(x) > 0.                        (5.5)

Equations (5.3)-(5.5) prove the required local positivity for the actual Brownian probability and its normalization. They require no global positivity theorem and no information about b_U(0).

Set

  K_Bpos = K_x(d_pos).                             (5.6)

For all k >= K_Bpos, positive time, x_k > 0, b_U(x_k) > 0, and 1/2 < T_U(x_k) < 3/2 hold together. Equation (4.3) then also makes W_k positive.

## 6. The actual Brownian logarithm tends to zero

We first prove an elementary estimate, including its domain:

  if 1/2 <= y <= 3/2, then y > 0 and
  |log(y)| <= 2*|y-1|.                             (6.1)

For y = 1 both sides are 0. If y != 1, the interval with endpoints y and 1 lies in [1/2,3/2], hence entirely in the positive reals. Log is continuous on the closed interval and differentiable on its interior, with derivative 1/z. The mean value theorem gives a z strictly between y and 1 satisfying

  log(y)-log(1) = (y-1)/z.

As z >= 1/2 > 0 and log(1) = 0,

  |log(y)| = |y-1|/z <= 2*|y-1|.

This proves (6.1) from ordinary real analysis; it is not a Brownian error-rate assumption.

For any e > 0 define

  eta_e = min(1/4,e/4) > 0,
  K_Ulog(e) = max(K_Bpos,K_U(eta_e)).              (6.2)

For k >= K_Ulog(e), (5.2) gives
|T_U(x_k)-1| < eta_e <= 1/4, so
3/4 < T_U(x_k) < 5/4. Applying (6.1),

  |log(T_U(x_k))|
    <= 2*|T_U(x_k)-1|
    < 2*eta_e <= e/2 < e.                         (6.3)

Thus

  log(T_U(x_k)) -> 0,                              (6.4)

with ordinary positive log arguments and only the original actual equivalence. If total log(W_k) is written, its eventual equality with log(T_U(x_k)) gives the same limit.

## 7. One common tail for every required positivity statement

From the fixed actual S2 limit choose K_2D(1/2). At every k beyond it,

  |D_k-1| < 1/2, hence D_k > 1/2 > 0.              (7.1)

Since F0 gives A_k > 0 at every k, (2.2) implies p_k = A_k*D_k > 0 there. Since F0 also gives K_k = p_k, K_k > 0 there. This recovers S2's actual positive output directly from its fixed convergence and finite identities; positivity has not been inserted as a new assumption.

Set

  K_pos = max(K_time,K_2D(1/2),K_Bpos).            (7.2)

For every k >= K_pos all the following hold simultaneously:

  1 <= n_k, N_k > 0, sqrt(N_k) > 0, x_k > 0;
  a_k > 0, rho_k > 0, rho_k^n_k > 0, A_k > 0;
  p_k = K_k > 0, D_k > 0;
  G_k = g(x_k) > 0;
  b_U(x_k) > 0, T_U(x_k) > 0, W_k = T_U(x_k) > 0. (7.3)

A quotient of positive reals is positive, so on precisely the same tail,

  p_k/b_U(x_k) > 0,
  K_k/b_U(x_k) > 0,
  D_k = p_k/A_k = K_k/A_k > 0,
  T_U(x_k) = b_U(x_k)/g(x_k) > 0,
  W_k = b_U(xhat_k)/G_k > 0.                       (7.4)

Every quotient among these positive quantities is positive too. In particular D_k/T_U(x_k) > 0; also the exact actual equality W_k = T_U(x_k) gives

  W_k/T_U(x_k) = 1                                (7.5)

on this tail. Thus W and T_U(x_k) both tend to 1, and their eventual quotient is identically 1.

All ordinary logs of p_k, K_k, b_U(x_k), D_k, T_U(x_k), the two actual probability ratios, and pi*a_k/4 are legal on this common tail. This supplies the S3-DOM positive-probability and positive-quotient outputs.

## 8. Exact centered logarithmic identity

Fix k >= K_pos and suppress subscripts within the calculation. By F0, the D definition, and the actual Brownian normalization,

  p = A*D, b_U(x) = g(x)*T_U(x).                   (8.1)

All factors are positive by (7.3). Positive product/quotient log identities, followed by the already checked bridges (4.5)-(4.7), give

  log(p/b_U(x))
    = log(p)-log(b_U(x))

    = log(A)+log(D)-log(g(x))-log(T_U(x))

    = log(a)+N*log(rho)+log(D)
      - [log(4/pi)-lambda*N/h^2] - log(T_U(x))

    = lambda*N/h^2 + N*log(rho)
      + [log(a)-log(4/pi)]
      + log(D)-log(T_U(x))

    = lambda*N/h^2 + N*log(rho)
      + log(pi*a/4)
      + log(D)-log(T_U(x)).                        (8.2)

Define exactly the frozen centering term

  C_k = lambda*N_k/h_k^2
        + N_k*log(rho_k)
        + log(pi*a_k/4).                            (8.3)

Subtracting the identical three terms in (8.2) proves, for every k >= K_pos,

  log(p_k/b_U(x_k))-C_k
    = log(D_k)-log(T_U(x_k)).                       (8.4)

This is an exact identity; no asymptotic cancellation has been suppressed. Every displayed h_k is the original actual h_k. The natural power has been converted using the same-time cast induction (4.4), with no Real.rpow substitution.

Since p_k = K_k at all indices, replacement of the equal numerator in (8.4) gives on the same tail

  log(K_k/b_U(x_k))-C_k
    = log(D_k)-log(T_U(x_k)).                       (8.5)

This is one actual probability identity in two equal notations, not a new process.

## 9. S3-MAIN: all epsilon and threshold quantifiers

Let e > 0. Take K_2log(e/2) from the fixed actual S2 output (2.7), and K_Ulog(e/2) from (6.2). Set

  K_e = max(K_pos,K_2log(e/2),K_Ulog(e/2)).          (9.1)

This is a natural threshold and is at least K_pos. For every k >= K_e, all probability logs are legal, and (8.4) gives

  |log(p_k/b_U(h_k/sqrt(N_k)))
     - [lambda*N_k/h_k^2
        + N_k*log(rho_k)
        + log(pi*a_k/4)]|

    = |log(D_k)-log(T_U(x_k))|

    <= |log(D_k)|+|log(T_U(x_k))|

    < e/2+e/2 = e.                                (9.2)

This is exactly the frozen S3-MAIN conclusion, for the originally arbitrary three sequences. Thresholds may depend on those sequences and on e, as allowed; no convergence rate or extra scale was imposed. Equation (8.5) proves the identical claim with actual K_k in the numerator.

For distinction, the normalized residual ratio D_k/T_U(x_k) tends to 1: on its positive tail it equals exp(log(D_k)-log(T_U(x_k))), so continuity of exp at 0 and the limit just established give exp(0) = 1. This does not claim the uncentered probability ratio tends to 1. In fact (8.2) gives the exact positive-tail equality

  p_k/b_U(x_k) = exp(C_k)*D_k/T_U(x_k).             (9.3)

There is no premise or conclusion C_k -> 0. Therefore no assertion p_k/b_U(x_k) -> 1, or that this uncentered ratio has a finite limit, is made. S3 is precisely a centered logarithmic limit.

## 10. Finite prefixes and the total Real version

All k continue to satisfy the original weak-cell conditions and F0. The proof has not modified h, p, K, R, D, U, or b_U on any prefix. By (3.6)-(3.7) every n_k = 0 is located in the finite natural prefix {k : k < K_time}. No ordinary Brownian-log statement was required on that prefix.

If an all-index formal sequence is wanted, keep the exact xhat from (2.10) and write

  Ehat_k =
    Real.log(p_k/b_U(xhat_k))
    - [lambda*N_k/h_k^2
       + N_k*Real.log(rho_k)
       + Real.log(pi*a_k/4)].                       (10.1)

Total Real operations make (10.1) syntactically defined at every k. They do not establish ordinary probability-log legality there. For each k >= K_pos, xhat_k = x_k, the actual probabilities are strictly positive, and Ehat_k equals the ordinary left side of (8.4). For each e > 0, (9.1) gives |Ehat_k| < e at every k >= K_e. Thus its total-sequence limit follows from the same positive-tail estimates, independently of all early values, without assigning any new b_U value or introducing a free extension F.

Here are explicit witnesses for all required eventual conclusions:

| Output | Witness |
| --- | --- |
| H_k >= T | K_H(T), original hypothesis |
| h_k >= T | K_H(T+1), (3.2) |
| N_k/h_k^2 >= T | K_t(T), (3.3) |
| N_k >= H_k^2, n_k >= 1, N_k > 0, sqrt(N_k) > 0 | K_time = K_t(1) |
| 0 < x_k < d, for every d > 0 | K_x(d), (3.10) |
| |T_U(x_k)-1| < eta and |W_k-1| < eta | K_U(eta), (5.1) |
| Local actual Brownian positivity for every real 0 < x < d_pos | d_pos = d_U(1/2), (5.3)-(5.5) |
| |log(T_U(x_k))| < e | K_Ulog(e), (6.2) |
| Common positivity of actual probabilities and quotients | K_pos, (7.2) |
| Exact centered logarithmic identity | every k >= K_pos |
| Absolute centered-log error < e | K_e, (9.1) |

All K witnesses are natural, and d witnesses are positive reals. Above a finite maximum of natural thresholds, each associated tail condition holds. This accounts for every eventual conjunction. No sequence has been assumed monotone, no all-index n >= 1 was imposed, and no parity, subsequence, N/h^3, DA1, or DA2 condition was used.

The complete quantifier order remains: for every three all-index weak-cell sequences, if H -> infinity and N/H^2 -> infinity, then all S3-DOM / S3-ALG / S3-MAIN outputs above hold. The ordinary and total versions are eventually identical on the explicitly established legal tail.

## 11. Real-analysis tools, lemma status, and outstanding formal gates

Known elementary tools used:

- Order-preserving natural cast, its zero/one/successor identities, and the natural-number zero-or-at-least-one dichotomy.
- Positive multiplication/division, exact nonzero field arithmetic, positive reciprocal inequalities, squares, and square monotonicity on nonnegative reals.
- Nonnegative real sqrt, sqrt(N)^2 = N for N >= 0, and sqrt(N) > 0 for N > 0.
- pi > 0, exp(v) > 0, log(1) = 0, log(exp(v)) = v, and ordinary positive product/quotient log formulas.
- The derivative of log on positive reals and the mean value theorem on a positive closed interval, with the interval checked in Section 6.
- Triangle inequality, finite maxima of tail thresholds, and continuity of exp at 0 for the optional normalized-residual observation.

No specialized unproved inequality is hidden here: no Taylor estimate, no infinite spectral sum bound, and no Brownian exponential relative error rate is used.

| Item | Status of use/proof | Formal boundary |
| --- | --- | --- |
| Actual S2 F0/Q1, including actual D/log D and eventual p positivity | FIXED_RELATIVE_INPUT | actual U1 formal PENDING; S2 formal OPEN |
| Original leading equivalence for actual U and b_U | ORIGINAL_FIXED_RELATIVE_INPUT | actual B/U/probability/tail public interface ROOT-OWNED PENDING |
| Domain, scale, positive time, square-root and positive-side x conclusions | PROVED_HERE, Sections 3-4 | not Lean checked |
| Actual Brownian normalization convergence, local positivity and log convergence | PROVED_HERE from original equivalence, Sections 5-6 | no arbitrary F/law substituted |
| One common positive probability/quotient tail | PROVED_HERE from fixed inputs, Section 7 | not an added assumption |
| Natural-power/cast and exact centered-log identities | PROVED_HERE, Sections 4 and 8 | no real-power substitution |
| S3-MAIN and equal actual K form | PROVED_HERE relative to exactly those inputs, Section 9 | separate verification/formal/acceptance gates remain |
| Stronger Brownian O rate, S4, S5, DA1/DA2, strict/coset variants, general Spectrum/OQ4 | NOT PROVED OR CONSUMED | outside this author's claim |

The relative mathematical proof is complete for the frozen outputs. Faithful actual Brownian public formal objects/tail and actual U1/S2 formal results remain genuine upstream dependencies, not gaps filled by an invented axiom. No Lean, lake, #check, server, Git, network, literature/source search, mathematical experiment, or subagent was used. This author does not supply an independent-review verdict. S3/S4/S5, strict/cosets, Spectrum, and OQ4 root remain OPEN. Derived raw leaf increment and source raw denominator delta are both 0.
