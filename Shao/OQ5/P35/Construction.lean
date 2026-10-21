import Shao.OQ5.P35.FixedLaw
import Shao.OQ5.P35.InfiniteSample
import Shao.OQ5.P35.PopulationKernel
import Shao.OQ5.P35.NoiseMoments
import Shao.OQ5.P35.RealMoments
import Shao.OQ5.P35.KernelMoments
import Shao.OQ5.P35.ProjectionMoments

/-!
# Actual p35 construction and kernel/projection moment premises

One fixed real law, a concrete infinite iid sample, a fixed symmetric Borel
kernel, and its actual Hoeffding moment identities. This aggregate does not
assert the L2 operator-rank theorem, positive Studentizer, rare-event estimates,
or either full tail counterexample conclusion.
-/
