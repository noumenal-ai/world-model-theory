/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import Physlib.ClassicalMechanics.HarmonicOscillator.Solution
import Mathlib.Topology.MetricSpace.Lipschitz

/-!
# The conserved energy of the harmonic oscillator is not recoverable from a position-only latent

The world-model specification instantiated on literal formalized physics. The target is not a
hand-rolled stand-in: it is PhysLean's energy functional `HarmonicOscillator.energy`, evaluated on
PhysLean's solution trajectory `InitialConditions.trajectory`, whose conservation is proved
upstream (`energy_conservation_of_equationOfMotion'`; packaged as the closed form
`InitialConditions.trajectory_energy`). The oscillator's phase space is carried by
`InitialConditions` (position `x₀`, velocity `v₀`), on which the solution and its energy are
total functions.

Two results:

* **Fiber collapse kills the readout** (`energy_not_recoverable_from_position`): the position-only
  encoder identifies every pair of states differing only in velocity, and the conserved energy
  separates each such pair with `v ≠ 0`; hence no function of the position latent — of any
  regularity whatsoever — computes the energy of the evolution. Specification clause 1 (separation)
  fails for this encoder, witnessed on the literal conserved quantity.

* **Latent geometry is lower-bounded by the physics** (`worldModel_latent_geometry_bound`): for ANY
  encoder `E` into a pseudometric latent space and ANY `L`-Lipschitz readout of the energy through
  `E`, the latent distance between two states of common position obeys

      (1/2) · m · ‖v‖² ≤ L · dist (E ⟨x₀, 0⟩) (E ⟨x₀, v⟩).

  Reading a conserved quantity at readout budget `L` forces the representation to spend latent
  distance proportional to the energy gap: specification clause 2 (metric domination) made
  quantitative on literal physics. At `v ≠ 0` and `L = 0` the bound is unsatisfiable, recovering
  the fiber-collapse impossibility as the degenerate case.

## Apparatus

`not_factorThrough_of_collapse` and `approx_lipschitz_ineq` are reproduced verbatim from
`TLT_Proofs.NonIdentifiability.{Apparatus, ReadoutCharacterization}` (design-lab `transformers`),
pending package unification of the world-models program; keeping this module self-contained over
`Physlib` avoids a cross-package olean dependency. Obligation recorded in
`world-models/THEORY.md`.

## References

PhysLean (`Physlib/ClassicalMechanics/HarmonicOscillator/{Basic,Solution}.lean`): the oscillator
structure, `energy`, `EquationOfMotion`, `energy_conservation_of_equationOfMotion'`,
`InitialConditions`, `trajectory`, `trajectory_equationOfMotion`, `trajectory_energy`.
-/

namespace WMSpec

/-! ## Apparatus (verbatim from the non-identifiability modules)

Stated before `open ClassicalMechanics HarmonicOscillator`: PhysLean scopes the notation `T`
(the oscillator's period) under that namespace, which would shadow the target binder `T`. -/

/-- Master lemma (verbatim from `TLT.NonIdentifiability.Apparatus`): a target that separates a
pair the encoder collapses does not factor through the encoder. -/
theorem not_factorThrough_of_collapse {S Z W : Type*} (E : S → Z) (T : S → W)
    {s₁ s₂ : S} (hcollapse : E s₁ = E s₂) (hsep : T s₁ ≠ T s₂) :
    ¬ ∃ g : Z → W, ∀ s, T s = g (E s) := by
  rintro ⟨g, hg⟩
  exact hsep (by rw [hg s₁, hg s₂, hcollapse])

/-- Approximate-Lipschitz bound (verbatim from `TLT.NonIdentifiability.Apparatus`): an
`L`-Lipschitz readout forces the target's gaps to be dominated by the latent gaps. -/
theorem approx_lipschitz_ineq {S Z : Type*} [PseudoMetricSpace Z]
    (E : S → Z) (T : S → ℝ) (L : NNReal) (g : Z → ℝ)
    (hg : LipschitzWith L g) (hfac : ∀ s, T s = g (E s)) (s₁ s₂ : S) :
    |T s₁ - T s₂| ≤ (L : ℝ) * dist (E s₁) (E s₂) := by
  have h := hg.dist_le_mul (E s₁) (E s₂)
  rwa [← hfac s₁, ← hfac s₂, Real.dist_eq] at h

/-! ## The literal target: PhysLean's conserved energy as a function of the state -/

open ClassicalMechanics HarmonicOscillator

variable (S : HarmonicOscillator)

/-- **The energy of the evolution from a state.** The literal PhysLean energy functional
`S.energy`, evaluated on the literal solution trajectory of the initial-value problem at the
initial time. By conservation this time-slice is canonical — see `energyOfIC_conserved`. -/
noncomputable def energyOfIC (IC : InitialConditions) : ℝ :=
  S.energy (IC.trajectory S) 0

/-- Closed form of the state energy, from PhysLean's `trajectory_energy` (itself proved via
`energy_conservation_of_equationOfMotion'`). -/
lemma energyOfIC_eq (IC : InitialConditions) :
    energyOfIC S IC = 1 / 2 * (S.m * ‖IC.v₀‖ ^ 2 + S.k * ‖IC.x₀‖ ^ 2) := by
  simp [energyOfIC, InitialConditions.trajectory_energy]

/-- **The time-slice is canonical**: the energy of the solution trajectory is the same at every
time, so `energyOfIC` is the energy of the evolution, not of an arbitrary instant. This is
PhysLean's conservation law, transported to the state reading. -/
lemma energyOfIC_conserved (IC : InitialConditions) (t : Time) :
    S.energy (IC.trajectory S) t = energyOfIC S IC := by
  simp [energyOfIC, InitialConditions.trajectory_energy]

/-! ## The velocity-shedding encoder on the literal phase space -/

/-- The position-only encoder on the oscillator's initial data: keeps `x₀`, sheds `v₀`. The
extremal form of a latent that decodes configuration but not motion. -/
def positionEncoder : InitialConditions → EuclideanSpace ℝ (Fin 1) :=
  fun IC => IC.x₀

/-- The position encoder collapses every velocity fiber: states of common position and arbitrary
velocities are identified. -/
lemma positionEncoder_collapse (x₀ v : EuclideanSpace ℝ (Fin 1)) :
    positionEncoder ⟨x₀, 0⟩ = positionEncoder ⟨x₀, v⟩ := rfl

/-- The conserved energy separates each collapsed pair: the energy gap across a velocity fiber is
exactly the kinetic term `(1/2) · m · ‖v‖²`. -/
lemma energyOfIC_gap (x₀ v : EuclideanSpace ℝ (Fin 1)) :
    energyOfIC S ⟨x₀, v⟩ - energyOfIC S ⟨x₀, 0⟩ = 1 / 2 * S.m * ‖v‖ ^ 2 := by
  rw [energyOfIC_eq, energyOfIC_eq]
  simp only [norm_zero]
  ring

/-! ## Main results -/

/-- **The conserved energy of the harmonic oscillator is not a function of a position-only
latent.** For every position `x₀` and every nonzero velocity `v`, the position encoder collapses
the pair `⟨x₀, 0⟩, ⟨x₀, v⟩` while the conserved energy separates it; hence no readout
`g : Z → ℝ` — linear, Lipschitz, measurable, or arbitrary — satisfies
`energyOfIC = g ∘ positionEncoder`. Specification clause 1, witnessed on the literal conserved
quantity of the literal solution flow. -/
theorem energy_not_recoverable_from_position (x₀ v : EuclideanSpace ℝ (Fin 1)) (hv : v ≠ 0) :
    ¬ ∃ g : EuclideanSpace ℝ (Fin 1) → ℝ,
        ∀ IC : InitialConditions, energyOfIC S IC = g (positionEncoder IC) := by
  have hgap := energyOfIC_gap S x₀ v
  have hnorm : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have hpos : 0 < 1 / 2 * S.m * ‖v‖ ^ 2 :=
    mul_pos (mul_pos (by norm_num) S.m_pos) (pow_pos hnorm 2)
  exact not_factorThrough_of_collapse positionEncoder (energyOfIC S)
    (positionEncoder_collapse x₀ v) (by linarith)

/-- **Latent geometry is lower-bounded by literal physics.** Any encoder `E` supporting an
`L`-Lipschitz readout of the oscillator's conserved energy must place two states of common
position at latent distance at least `(1/2)·m·‖v‖² / L`:

    (1/2) · m · ‖v‖² ≤ L · dist (E ⟨x₀, 0⟩) (E ⟨x₀, v⟩).

The kinetic-energy gap of the collapsed fiber prices the latent geometry of every faithful
representation. With `v ≠ 0` and `L = 0` the inequality is unsatisfiable — the fiber-collapse
impossibility is the degenerate case. Specification clause 2 (metric domination), quantitative,
on the literal conserved quantity. -/
theorem worldModel_latent_geometry_bound {Z : Type*} [PseudoMetricSpace Z]
    (E : InitialConditions → Z) (L : NNReal) (g : Z → ℝ)
    (hg : LipschitzWith L g)
    (hfac : ∀ IC : InitialConditions, energyOfIC S IC = g (E IC))
    (x₀ v : EuclideanSpace ℝ (Fin 1)) :
    1 / 2 * S.m * ‖v‖ ^ 2 ≤ (L : ℝ) * dist (E ⟨x₀, 0⟩) (E ⟨x₀, v⟩) := by
  have h := approx_lipschitz_ineq E (energyOfIC S) L g hg hfac ⟨x₀, v⟩ ⟨x₀, 0⟩
  have hgap := energyOfIC_gap S x₀ v
  have habs : |energyOfIC S ⟨x₀, v⟩ - energyOfIC S ⟨x₀, 0⟩| = 1 / 2 * S.m * ‖v‖ ^ 2 := by
    rw [hgap]
    exact abs_of_nonneg
      (mul_nonneg (mul_nonneg (by norm_num) S.m_pos.le) (pow_nonneg (norm_nonneg v) 2))
  rw [habs] at h
  rwa [dist_comm (E ⟨x₀, 0⟩) (E ⟨x₀, v⟩)]

end WMSpec
