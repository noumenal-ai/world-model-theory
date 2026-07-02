/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import WMSpec.NoLatentDynamics

/-!
# The symmetry-native layer: mismatched invariance at the encoder

The orbit form of the master lemma, and the harmonic-oscillator instance that gives the
stroboscopic dichotomy its matched-invariance reading (companion to the objective-level
matched-invariance theory: an objective whose invariance group contains a broken symmetry of the
data law is blind to it; an *encoder* whose invariance monoid contains a transformation the
target moves supports no readout of that target).

* `not_factorThrough_of_invariance`: if `E ∘ b = E` pointwise (the encoder declares `b`
  nuisance) while `T a ≠ T (b a)` (the target carries `b` as signal), no readout factors `T`
  through `E`. Stated before the physics `open` — PhysLean scopes the notation `T` (period)
  under `HarmonicOscillator` (URS rule: physics namespaces carry notation; open below apparatus).

* `velocityBoost`, `positionEncoder_velocityBoost`: the boost `⟨x₀, v₀⟩ ↦ ⟨x₀, v₀ + v⟩` and the
  position encoder's invariance under it.

* `velocityBoost_breaks_flow`: at every non-stroboscopic horizon the boost moves the
  encoder-viewed transition — the boost is a **broken symmetry** of the flow that the encoder
  treats as nuisance. (At stroboscopic horizons the dichotomy's constructive direction shows the
  symmetry is unbroken for the viewed map: the mismatch vanishes exactly there.)

* `no_dynamics_of_boost_mismatch`: the forward direction of
  `positionLatent_dynamics_iff_stroboscopic`, re-derived through the symmetry layer. Same fact,
  matched-invariance route: the failure of latent dynamics IS an invariance mismatch between the
  encoder and the flow.
-/

namespace WMSpec

/-- **Orbit master lemma (symmetry-native negative layer).** An encoder invariant under a
transformation the target moves supports no readout of that target: `E` has declared `b`
nuisance; `T` carries `b` as signal; the mismatch is fatal for every `g : Z → W`. The master
lemma applied along the `b`-orbit of `a`. -/
theorem not_factorThrough_of_invariance {A Z W : Type*} (E : A → Z) (T : A → W) (b : A → A)
    (hinv : ∀ a, E (b a) = E a) {a : A} (hsep : T a ≠ T (b a)) :
    ¬ ∃ g : Z → W, ∀ x, T x = g (E x) :=
  not_factorThrough_of_collapse E T (hinv a).symm hsep

open ClassicalMechanics HarmonicOscillator Real

variable (S : HarmonicOscillator)

/-- **The velocity boost**: shift the state's velocity by `v`, fixing its position. The
transformation the position-only latent cannot see. -/
def velocityBoost (v : EuclideanSpace ℝ (Fin 1)) :
    InitialConditions → InitialConditions :=
  fun IC => ⟨IC.x₀, IC.v₀ + v⟩

/-- The position encoder is invariant under every velocity boost: the boost is nuisance to the
representation. -/
lemma positionEncoder_velocityBoost (v : EuclideanSpace ℝ (Fin 1)) :
    ∀ IC, positionEncoder (velocityBoost v IC) = positionEncoder IC :=
  fun _ => rfl

/-- **The boost is a broken symmetry of the viewed flow at every non-stroboscopic horizon**: it
moves the encoder's view of the transition at the rest state, by exactly `(sin (ω t)/ω) • v`. -/
lemma velocityBoost_breaks_flow (t : Time) (hsin : sin (S.ω * t) ≠ 0)
    {v : EuclideanSpace ℝ (Fin 1)} (hv : v ≠ 0) :
    positionEncoder (flow S t ⟨0, 0⟩)
      ≠ positionEncoder (flow S t (velocityBoost v ⟨0, 0⟩)) := by
  rw [positionEncoder_flow, positionEncoder_flow]
  simp only [velocityBoost, InitialConditions.trajectory_eq, smul_zero, add_zero, zero_add]
  intro h
  exact smul_ne_zero (div_ne_zero hsin S.ω_ne_zero) hv h.symm

/-- **Latent dynamics fails by invariance mismatch.** At every non-stroboscopic horizon: the
encoder is boost-invariant (`positionEncoder_velocityBoost`), the viewed flow is not
(`velocityBoost_breaks_flow`), so by the orbit master lemma no latent transition map exists.
The forward direction of the stroboscopic dichotomy, derived through the symmetry layer:
"no world model" here IS "mismatched invariance". -/
theorem no_dynamics_of_boost_mismatch (t : Time) (hsin : sin (S.ω * t) ≠ 0)
    {v : EuclideanSpace ℝ (Fin 1)} (hv : v ≠ 0) :
    ¬ ∃ f : EuclideanSpace ℝ (Fin 1) → EuclideanSpace ℝ (Fin 1),
        ∀ IC : InitialConditions, f (positionEncoder IC) = positionEncoder (flow S t IC) := by
  rintro ⟨f, hf⟩
  exact not_factorThrough_of_invariance positionEncoder
    (fun IC => positionEncoder (flow S t IC)) (velocityBoost v)
    (positionEncoder_velocityBoost v)
    (velocityBoost_breaks_flow S t hsin hv)
    ⟨f, fun IC => (hf IC).symm⟩

end WMSpec
