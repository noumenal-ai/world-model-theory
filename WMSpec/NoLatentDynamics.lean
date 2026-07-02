/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import WMSpec.EnergyNonRecovery

/-!
# Latent dynamics for the position-only latent exist exactly at stroboscopic times

The dynamics clause of the world-model specification, instantiated on the literal flow of
PhysLean's harmonic oscillator. The state space is `InitialConditions`; the flow at horizon `t`
sends a state to the solution's position and velocity at time `t` (`flow`), grounded by
`flow_zero`. The question the specification asks of a representation: does a latent transition
map exist that commutes with the true flow through the encoder?

For the position-only encoder the answer is a **dichotomy**
(`positionLatent_dynamics_iff_stroboscopic`):

    (∃ f, ∀ IC, f (positionEncoder IC) = positionEncoder (flow S t IC))  ↔  sin (ω t) = 0.

At stroboscopic horizons (`sin (ω t) = 0`, i.e. `t` a half-period multiple) the flow's position
component aliases to `cos (ω t) • x₀`, a function of position alone, and the latent dynamics
exists — the constructed transition is `f z = cos (ω t) • z`, which at those horizons is `± id`.
At every other horizon, two states of equal position and velocities differing by `v` reach
positions differing by `(sin (ω t) / ω) • v ≠ 0`: the collapsed pair separates downstream, and no
transition map — of any regularity — closes the square. A position-only latent of the oscillator
admits **no dynamics law at all** at generic horizons; what looks like a world model at the
sampling times `sin (ω t) = 0` is stroboscopic aliasing.

This is the lumpability clause (specification clause 3) made exact on literal physics: the
encoder's fibers are a congruence for the flow precisely on the stroboscopic set. The abstract
finite-kernel version (P2) has this as its concrete anchor.

Scope: the flow group law `flow S (t+s) = flow S t ∘ flow S s` (via `trajectories_unique`) is a
recorded obligation (`world-models/URS.md`), not needed here.

## References

PhysLean: `InitialConditions.trajectory` and its definitional closed form
`InitialConditions.trajectory_eq` (`cos (ω t) • x₀ + (sin (ω t)/ω) • v₀`),
`trajectory_position_at_zero`, `trajectory_velocity_at_zero`, `HarmonicOscillator.ω_ne_zero`.
-/

namespace WMSpec

open ClassicalMechanics HarmonicOscillator Real

variable (S : HarmonicOscillator)

/-- **The state flow of the oscillator at horizon `t`**: a state (initial position and velocity)
is sent to the solution's position and velocity at time `t`. This is the literal time evolution
of the physical system, read as a map on states. -/
noncomputable def flow (t : Time) (IC : InitialConditions) : InitialConditions :=
  ⟨IC.trajectory S t, Time.deriv (IC.trajectory S) t⟩

/-- The flow at horizon `0` is the identity: the state reading of the solution is grounded at the
initial data. -/
lemma flow_zero (IC : InitialConditions) : flow S 0 IC = IC := by
  ext1
  · exact InitialConditions.trajectory_position_at_zero S IC
  · exact InitialConditions.trajectory_velocity_at_zero S IC

/-- The position latent of the flowed state is the solution's position at the horizon. -/
lemma positionEncoder_flow (t : Time) (IC : InitialConditions) :
    positionEncoder (flow S t IC) = IC.trajectory S t := rfl

/-- **Dichotomy: a position-only latent admits a transition law iff the horizon is
stroboscopic.** A latent map `f` closing the square `f ∘ positionEncoder = positionEncoder ∘
flow S t` exists **iff** `sin (ω t) = 0`. Backward: at stroboscopic horizons the position
component of the flow is `cos (ω t) • x₀`, so `f z = cos (ω t) • z` closes the square. Forward:
otherwise the states `⟨0, 0⟩` and `⟨0, v⟩` (`v ≠ 0`) share a latent while their downstream
positions differ by `(sin (ω t)/ω) • v ≠ 0`, so no `f` exists. -/
theorem positionLatent_dynamics_iff_stroboscopic (t : Time) :
    (∃ f : EuclideanSpace ℝ (Fin 1) → EuclideanSpace ℝ (Fin 1),
        ∀ IC : InitialConditions, f (positionEncoder IC) = positionEncoder (flow S t IC)) ↔
    sin (S.ω * t) = 0 := by
  constructor
  · rintro ⟨f, hf⟩
    by_contra hsin
    set v : EuclideanSpace ℝ (Fin 1) := EuclideanSpace.single 0 1 with hv
    have hvne : v ≠ 0 := by
      rw [hv]
      simp [PiLp.single_eq_zero_iff]
    have e1 : positionEncoder (⟨0, 0⟩ : InitialConditions) = 0 := rfl
    have e2 : positionEncoder (⟨0, v⟩ : InitialConditions) = 0 := rfl
    have h1 := hf ⟨0, 0⟩
    have h2 := hf ⟨0, v⟩
    rw [positionEncoder_flow, e1] at h1
    rw [positionEncoder_flow, e2] at h2
    simp only [InitialConditions.trajectory_eq, smul_zero, add_zero, zero_add] at h1 h2
    -- h1 : f 0 = 0,  h2 : f 0 = (sin (ω t)/ω) • v
    rw [h1] at h2
    exact smul_ne_zero (div_ne_zero hsin S.ω_ne_zero) hvne h2.symm
  · intro hsin
    refine ⟨fun z => cos (S.ω * t) • z, fun IC => ?_⟩
    rw [positionEncoder_flow]
    simp only [InitialConditions.trajectory_eq, positionEncoder]
    rw [hsin]
    simp

/-- **No latent dynamics at any non-stroboscopic horizon.** The citable negative form of the
dichotomy: away from the measure-zero stroboscopic set, a position-only latent of the harmonic
oscillator supports no transition law whatsoever — the world-model square cannot be closed by any
function of the latent. -/
theorem no_positionLatent_dynamics_of_nonstroboscopic (t : Time)
    (h : sin (S.ω * t) ≠ 0) :
    ¬ ∃ f : EuclideanSpace ℝ (Fin 1) → EuclideanSpace ℝ (Fin 1),
        ∀ IC : InitialConditions, f (positionEncoder IC) = positionEncoder (flow S t IC) :=
  fun hex => h ((positionLatent_dynamics_iff_stroboscopic S t).mp hex)

end WMSpec
