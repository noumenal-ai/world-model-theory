/-
Axiom audit for the World-Model Specification corpus.

`lake env lean ci/Audit.lean` prints the axiom footprint of the headline theorem
of every level. The verification workflow greps this output: a clean corpus
depends only on `propext`, `Classical.choice`, `Quot.sound` (several results use
none), and NOTHING named `sorryAx`.

NOTE ON LAYOUT: these imports assume a single package whose source roots include
both `WMSpec/` and `TLT_Proofs/` (the publish-repo layout). If your lakefile
splits them, run this audit once per package with the matching import subset.
-/
import WMSpec.ForcingTheorem
import WMSpec.BisimMetric
import WMSpec.MixedFamilies
import WMSpec.Flow.FlowArchitecture
import WMSpec.Flow.OscillatorBinding
import TLT_Proofs.NonIdentifiability.ForcingTheorem
import TLT_Proofs.NonIdentifiability.ReadoutCharacterization
import TLT_Proofs.NonIdentifiability.ExecutedWitness
import TLT_Proofs.NonIdentifiability.JepaBoundary

-- L1  readout / McShane characterization
#print axioms TLT.NonIdentifiability.lipschitz_readout_iff
-- L2  the objective invariance calculus (novel exchange constant)
#print axioms WMSpec.mixed_guard_exchange
-- L3  the forcing theorem (both developments)
#print axioms WMSpec.forcing_theorem
#print axioms TLT.NonIdentifiability.isWorldModel_iff_ker_isConforming
-- L4  the metric layer + data-processing inequality
#print axioms WMSpec.bisimMetric_prices_tests
#print axioms WMSpec.fisherRao_mapPMF_le
-- L5  architectures: the admissible-horizon spectrum
#print axioms WMSpec.Flow.kinematic_admissible_iff
#print axioms WMSpec.oscillator_latentStep_iff_int_multiple
-- L6  the executed float32 witness
#print axioms TLT.NonIdentifiability.Executed.no_lipschitz_reading_of_executed_encoder
-- L7  the scoped JEPA boundary, bound to the real objective
#print axioms TLT.NonIdentifiability.JEPA.jepa_predict_cannot_recover_target
#print axioms TLT.NonIdentifiability.JEPA.witness_jepaLoss_computes
