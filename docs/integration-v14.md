# Common analytic integration v14

Two source-frozen independently reviewed modules add14 public theorems: QuadraticCharacteristic and GaussianTail. Their source hashes and complete independent statement/final proof reports are in docs/common-v14-*.

QuadraticCharacteristic uses the genuine joint sum/energy characteristic factor and derives its odd derivatives using actual third moments of the supplied law. No centering or independence between A and A² is added. GaussianTail uses the actual standard-normal measure, true integral derivatives, Mills bounds, local tail comparison and deletion comparison, including boundary cases. Whole-power damping, sample Gaussian comparison, Berry–Esseen and full roots remain open.

One combined server build and transitive axiom audit passed:518 public theorems covered,796 theorem declarations including generated helpers audited. Only propext,Classical.choice,Quot.sound are allowed. Earlier accepted source bytes and pinned dependencies are unchanged. No local Lean or redundant accepted-target run. Raw logs remain on server.
