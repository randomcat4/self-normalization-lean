# Shared retained-sample moments and finite Duhamel identity

Five independently reviewed modules add 29 public theorems. TruncationSampleSize derives the sample-size lower bound from the actual probability law and normalized second moment. RetainedMoments and RetainedSample use the genuine closed-cutoff conditional law and the original H_x = n integral F(x z) budget, including actual mass, first/second/third moments and retained-size/threshold bounds. RetainedVariance proves true centered integrability, positive variance and the actual Lyapunov bound; raw second moments are not relabelled as variance.

LindleyTelescoping defines the real finite-product future kernel and reflection defects. Its eleven theorems prove arbitrary-measurable-test parameter measurability, the bounded-test semigroup, iid future-step law, finite Duhamel identity and the strict positive-energy CDF specialization. Empty paths and boundary atoms are retained, and the maximum comparison uses the proved joint reversal law. No Fourier error estimate or final probability comparison is assumed or claimed.

Each module has a frozen source scope and an independent source-to-statement/proof review under docs/common-v10-<Module>-*.md. Reviewers did not author their reviewed targets. Earlier dependencies retain their existing independent reviews. Historical proposal labels inside scope records are superseded by the explicit freeze and independent acceptance recorded here; mathematical signatures were unchanged.

Root verified the five exact accepted source hashes and ran one combined server build plus the full transitive theorem-axiom audit. All 408 public source theorems were covered; 628 theorem declarations including generated ones use only propext/Classical.choice/Quot.sound. Receipts: verification/receipt-v10.json and verification/declarations-v10.json. Raw logs/cache remain on the server.

All full root theorems remain formally OPEN. The finite Duhamel identity does not establish the Fourier/desmoothing estimates, and moment bounds do not establish a normal-tail comparison.
