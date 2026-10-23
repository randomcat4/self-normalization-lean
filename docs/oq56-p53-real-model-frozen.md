# Frozen interfaces: actual p53 real model, infinite sample and residual operator

The declarations in this batch were frozen before implementation. The exact source files carry the complete Lean declarations. No mathematical premise, definition body or public theorem type changed after these freezes.

| Unit | Module | Literal definitions | Public theorem types | Frozen contracts SHA256 |
| --- | --- | ---: | ---: | --- |
| 111 | SparseRealModel | 4 | 28 | 231c8a1f6a5618601c5bf90d7f5da3ecf43d07775e815c497ad791a4784b2b4a |
| 112 | SparseRealSample | 3 | 13 | 7b2aab86698a4417575ffb459472959f132aa1ffb074b6b2bea82b59830d41c2 |
| 113 | SparseRealOperator | 2 | 14 | 4a5f7831f8c2731a64cef1127bc43a9601bbd9b15cedca72d78a5491fda62952 |

## Actual real model

The four definitions are the real features G and Z composed with the total population decoder, the real kernel G(u)+G(v)+Z(u)Z(v), and its positive residual Z(u)Z(v). The measure is the previously qualified pushforward of the complete nested population, retaining independent uniform noise and both category/sign pairs.

The 28 public types cover real-feature measurability and full independence; genuine absolute q-moment integrability for every fixed q>0; zero means; G second moment at least 1/3; positive Z second moment under the selection core; Z exponential integrability and its 5/4 bound for 0<tau<=1; symmetric measurable kernel; genuine pair and row integrability; exact row first projection G and zero population mean; literal canonical residual decomposition and degenerate row mean; genuine residual second moment and its exact factorization; actual marginal symmetry and laws.

The exact alpha/core/tau hypotheses are those in the source declarations. In particular the Z-moment and exponential interfaces do not acquire a selection-core premise, while statements consuming G moments or nonzero selection retain theirs. Private transport proofs establish genuine integrability before using integral_map. They do not assume the total decoder is a measurable embedding.

## One fixed infinite real iid sample

The three definitions are the infinite product of the full population measure, the infinite product of the actual real measure, and coordinate evaluation. Full alpha/x/N parameters are fixed before every finite prefix n.

The 13 types assert both probability laws; coordinate measurability and marginal law; full mutual independence; the product law for each distinct ordered pair; both finite-prefix product laws for all natural n, including zero; the two complete infinite encoder/decoder pushforwards; countably simultaneous closed noise support; and the law-specific AE reconstruction identities for whole sequences. No arbitrary-point global inverse is asserted.

## Positive canonical operator on the full real L2 space

The two definitions are actual real Z converted by MemLp.toLp and InnerProductSpace.rankOne over the reals with that same feature in both slots. The observation carrier is real, with the actual sparseRealMeasure.

The 14 types establish feature MemLp; its AE representative; genuine Zf integrability and the integral inner product; its squared norm integral; feature nonzero; genuine residual-row-times-f integrability; the AE integral representation for each L2 input f; output MemLp; self-adjointness; the quadratic square identity and nonnegativity; rank exactly one; and operator nonzero. Alpha>0 suffices for positivity/self-adjointness, while nonzero/rank use the actual selection core.

The integral representation has quantifier order forall f, AE u. It asserts neither a common null set for every f nor global equality of quotient representatives. No fourth moment, finite-dimensional ambient space, global decoder embedding or positive-semidefiniteness of the entire additive kernel is a premise.

P53, OQ6 and RS2 remain OPEN beyond this precise batch scope.
