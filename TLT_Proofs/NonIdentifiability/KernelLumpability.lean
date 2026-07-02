/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import Mathlib.Logic.Function.Basic
import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-!
# Latent dynamics exist iff the encoder's collapse is a congruence (lumpability)

The dynamics clause of the world-model specification, made an exact characterization. For an
encoder `E : S → Z` and a dynamics on the state space — deterministic `f : S → S` or a
probabilistic transition kernel `P : S → PMF S` — a latent dynamics closing the world-model
square exists **iff** the encoder's fibers are a congruence for the dynamics:

    ∃ g, g ∘ E = E ∘ f              ↔  E-collapsed pairs stay E-collapsed under f
    ∃ Q, Q (E s) = (P s).map E      ↔  E-collapsed pairs have equal pushforward laws.

The forward directions are the world-model reading of the master lemma: a latent transition map
is a readout of the pushed-forward dynamics, so collapse plus downstream separation kills it. The
converse constructions push the dynamics along `E` by `Function.extend`; the congruence hypothesis
is exactly `Function.FactorsThrough`, and the junk defaults (`id`, `PMF.pure`) make the extension
total with no nonemptiness side conditions.

`latentKernel_unique_on_range` sharpens existence to canonicity: any two latent kernels agreeing
with the pushforward agree on every reachable latent, so *the* latent dynamics is well defined on
`Set.range E` — freedom lives only off the reachable set.

`quotientKernel_iff_congruence` restates the kernel characterization for the quotient map of a
setoid `r`: the quotient carries a transition kernel iff `r` is a `P`-congruence. This is the
exact form the forcing theorem (P3) consumes — bisimilarity will be the greatest such `r`, and
its quotient the coarsest state space carrying a latent dynamics.

## The physics anchor

The deterministic characterization is instantiated on literal physics in
`world-models/WMSpec/NoLatentDynamics.lean`: for PhysLean's harmonic-oscillator flow and the
position-only encoder, the congruence condition holds **iff** `sin (ω t) = 0`
(`positionLatent_dynamics_iff_stroboscopic`) — the stroboscopic dichotomy is this file's
`latentMap_iff_congruence` with its right-hand side computed on the literal solution.
-/

namespace TLT.NonIdentifiability

/-! ## Deterministic dynamics -/

/-- **Latent map iff congruence (deterministic lumpability).** A latent transition map `g`
closing the square `g ∘ E = E ∘ f` exists **iff** the encoder's collapse is a congruence for
`f`: states with equal latents keep equal latents under the dynamics. Construction: push `E ∘ f`
along `E` by `Function.extend` (junk default `id`); the congruence hypothesis is
`Function.FactorsThrough`. -/
theorem latentMap_iff_congruence {S Z : Type*} (E : S → Z) (f : S → S) :
    (∃ g : Z → Z, ∀ s, g (E s) = E (f s)) ↔
    (∀ s₁ s₂, E s₁ = E s₂ → E (f s₁) = E (f s₂)) := by
  constructor
  · rintro ⟨g, hg⟩ s₁ s₂ hE
    rw [← hg s₁, ← hg s₂, hE]
  · intro h
    refine ⟨Function.extend E (fun s => E (f s)) id, fun s => ?_⟩
    exact Function.FactorsThrough.extend_apply (fun a b hab => h a b hab) id s

/-! ## Probabilistic dynamics -/

/-- **Latent kernel iff congruence (probabilistic lumpability).** A latent transition kernel `Q`
with `Q (E s) = (P s).map E` exists **iff** `E`-collapsed states have equal pushforward laws.
The junk default `PMF.pure` keeps the extension total for arbitrary `Z`. -/
theorem latentKernel_iff_congruence {S Z : Type*} (E : S → Z) (P : S → PMF S) :
    (∃ Q : Z → PMF Z, ∀ s, Q (E s) = (P s).map E) ↔
    (∀ s₁ s₂, E s₁ = E s₂ → (P s₁).map E = (P s₂).map E) := by
  constructor
  · rintro ⟨Q, hQ⟩ s₁ s₂ hE
    rw [← hQ s₁, ← hQ s₂, hE]
  · intro h
    refine ⟨Function.extend E (fun s => (P s).map E) PMF.pure, fun s => ?_⟩
    exact Function.FactorsThrough.extend_apply (fun a b hab => h a b hab) PMF.pure s

/-- **The latent dynamics is canonical on reachable latents.** Any two latent kernels realizing
the pushforward agree on `Set.range E`: existence (from `latentKernel_iff_congruence`) upgrades
to uniqueness wherever the latent is realized by a state. -/
theorem latentKernel_unique_on_range {S Z : Type*} (E : S → Z) (P : S → PMF S)
    {Q₁ Q₂ : Z → PMF Z}
    (h₁ : ∀ s, Q₁ (E s) = (P s).map E) (h₂ : ∀ s, Q₂ (E s) = (P s).map E) :
    ∀ z ∈ Set.range E, Q₁ z = Q₂ z := by
  rintro z ⟨s, rfl⟩
  rw [h₁ s, h₂ s]

/-- **Quotient form (for the forcing theorem).** For a setoid `r` on the state space, the
quotient carries a transition kernel commuting with `Quotient.mk r` **iff** `r` is a
`P`-congruence: related states have equal pushforward laws on the quotient. Bisimilarity (P3)
will be the greatest such setoid; its quotient is the coarsest state space carrying a latent
dynamics. -/
theorem quotientKernel_iff_congruence {S : Type*} (r : Setoid S) (P : S → PMF S) :
    (∃ Q : Quotient r → PMF (Quotient r),
        ∀ s, Q (Quotient.mk r s) = (P s).map (Quotient.mk r)) ↔
    (∀ s₁ s₂, r s₁ s₂ → (P s₁).map (Quotient.mk r) = (P s₂).map (Quotient.mk r)) := by
  rw [latentKernel_iff_congruence]
  exact ⟨fun h s₁ s₂ hr => h s₁ s₂ (Quotient.eq.mpr hr),
    fun h s₁ s₂ hmk => h s₁ s₂ (Quotient.eq.mp hmk)⟩

end TLT.NonIdentifiability
