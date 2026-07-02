/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import WMSpec.NoLatentDynamics

/-!
# The oscillator's admissible horizons, in flow vocabulary

The literal-physics binding of the flow stratum: the harmonic oscillator's stroboscopic
dichotomy (`positionLatent_dynamics_iff_stroboscopic`, proved on PhysLean's literal solution
flow) restated as the flow-architecture latent-step predicate, and the admissible set
identified as the integer lattice of half-periods — the middle entry of the spectrum
`{0} ⊂ (π/ω)ℤ ⊂ all`.

`LatentStepAt` is the flow module's predicate, reproduced verbatim (the flow module is
compiled against the design-lab closure, this file against PhysLean's own build; the paste
convention avoids the cross-build olean seam).

**Named obligation (recorded in `world-models/URS.md`):** the `AddAction Time
InitialConditions` packaging needs the flow group law `flow S (t + s) = flow S t ∘ flow S s`;
PhysLean carries no trajectory-composition lemma, so the route is the closed forms
(`trajectory_eq`, `trajectory_velocity`) plus the trigonometric addition formulas — or,
better, an upstream PhysLean lemma via `trajectories_unique`. Deferred, route named.
-/

namespace WMSpec

open ClassicalMechanics HarmonicOscillator Real

/-- Latent step for a single transition map (verbatim core of `WMSpec.Flow.LatentStep`,
specialized to one horizon). -/
def LatentStepAt {S' Z : Type*} (Φ : S' → S') (E : S' → Z) : Prop :=
  ∃ fZ : Z → Z, ∀ s, fZ (E s) = E (Φ s)

variable (S : HarmonicOscillator)

/-- **The oscillator's dichotomy in flow vocabulary**: a latent step for the position-only
encoder exists at horizon `t` iff `t` is stroboscopic. The literal-physics instance of the
master dichotomy. -/
theorem oscillator_latentStep_iff (t : Time) :
    LatentStepAt (flow S t) positionEncoder ↔ sin (S.ω * t) = 0 :=
  positionLatent_dynamics_iff_stroboscopic S t

/-- **The admissible set is the half-period lattice**: latent dynamics for the position
latent exists exactly at integer multiples of `π/ω` — the subgroup `(π/ω)ℤ` of time, the
spectrum's middle entry between kinematics' `{0}` and the quotient-homomorphic `all`. -/
theorem oscillator_latentStep_iff_int_multiple (t : Time) :
    LatentStepAt (flow S t) positionEncoder ↔ ∃ n : ℤ, (n : ℝ) * π = S.ω * t := by
  rw [oscillator_latentStep_iff, Real.sin_eq_zero_iff]

end WMSpec
