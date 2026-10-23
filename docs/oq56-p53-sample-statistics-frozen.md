# Frozen interfaces: actual p53 sample statistics, positive denominator and real tails

All declarations were frozen before implementation. The source files contain their complete Lean types and literal definitions. No mathematical assumption, public type or definition changed after freezing.

| Unit | Module | Literal public definitions | Public theorem types | Frozen contracts SHA256 |
| --- | --- | ---: | ---: | --- |
| 114 | SparseSampleStatistics | 7 | 15 | ba22c632205c3581f07f0f996e2ece4dc7b8b0f2e3fa0e75089a67c0c86455cb |
| 115 | SparsePositiveStudentizer | 0 | 4 | 8da71f1b555da0ae148ed967092d8b8d750f005b72934f80d7bad17a40546777 |
| 116 | SparseRealStatistics | 6 | 24 | 5ef895616595c6bfd3873722f057fbbbdde52d2a6fc4df896eeb91e57c8e3e46 |

## Actual finite tuple statistics

The seven definitions retain positive residual pair and erased-row sums, adjusted row b_i=G_i+Z_i(sum Z-Z_i)/(n-2), actual unordered-pair U, the original centered-row jackknife square, its square root R, and total T=sqrt(n)U/R. The fifteen types establish exact residual-row factorization, original row/U decomposition, centered-row and R-squared identities, square nonnegativity, R-squared recovery, the implication zero square implies equal adjusted rows, and measurability. All cancellation statements retain n>=3; measurability and total definitions allow every n. No selection, moment or alpha-positivity premise is needed for this deterministic scope.

## Genuine denominator positivity

The four types prove that the true jackknife-square zero event has measure zero under the actual finite nested product law for n>=3; that the actual R is positive almost everywhere there; that positivity holds for every prefix of the one fixed infinite tuple sample; and that it persists under conditioning on any set E.

The proof conditions on complete label vectors, transports the entire nested product law to noise-vector times labels, and uses the actual independent uniform noise law to make each affine equality section a null singleton. It does not infer a probabilistic result from finite algebra alone. Conditional AE makes no claim that E has positive mass or its conditional measure is normalized.

## Actual real statistics and whole-law tail transport

The six definitions are the real finite U/R-squared/R/T and the actual tuple and real infinite-sample upper-tail probabilities. The twenty-four types cover measurability, four literal decoder statistic identities for every finite real sample, four encoder identities under coordinatewise closed noise support Icc[-1,1], nonnegativity and square recovery, finite/prefix/conditional AE denominator positivity, exact equality of actual whole-sample tail probabilities, and bounds in [0,1].

The finite real kernel is the literal actual tuple kernel composed with the total decoder. This justifies decoder identities without a global inverse assertion. Encoder recovery explicitly retains its support condition. Whole infinite decoder and prefix laws, rather than feature marginals, carry positivity and exact tail events. The separately quantified threshold y does not change the fixed input sequence x. Total division permits tail transport for all n and y, while positivity retains n>=3.

P53, OQ6 and RS2 remain OPEN beyond these exact auxiliary interfaces.
