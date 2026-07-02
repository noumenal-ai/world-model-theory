/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import TLT_Proofs.NonIdentifiability.KernelLumpability
import Mathlib.Data.Setoid.Basic
import Mathlib.Order.SetNotation

/-!
# The forcing theorem: world models are exactly the refinements of bisimilarity

The specification of a world model, at the set level, has two clauses: the representation must
*separate* every pair some target distinguishes, and it must *carry a latent dynamics* — a
transition law on latents commuting with the true dynamics through the encoder
(`KernelLumpability`). This file proves that the specification **forces** a canonical state
space: the class of equivalence relations compatible with the specification has a greatest
element — bisimilarity relative to the target family — whose quotient is itself a world model,
and every world model's kernel refines it.

Concretely, for a target family `T : ∀ i, S → W i` (heterogeneous codomains) and a transition
kernel `P : S → PMF S`:

* `IsConforming T P r`: the setoid `r` refines every target's partition and is a `P`-congruence
  (related states have equal pushforward laws on the quotient) — the relational form of the
  specification.
* `IsWorldModel T P E`: the encoder form — `E` separates what the targets separate and some
  latent kernel `Q` satisfies `Q (E s) = (P s).map E`.
* `isConforming_sSup`: conforming setoids are closed under arbitrary suprema. Both clauses close
  for one reason: per-step indistinguishability propagates along equivalence chains
  (`eqvGen_factorsThrough`), with the probabilistic clause transported up the lattice by
  `map_quotient_eq_of_le`.
* `bisimilarity T P`: the supremum of all conforming setoids; `isGreatest_bisimilarity` — it is
  itself conforming, hence the greatest.
* `isWorldModel_iff_ker_isConforming`: **the extension of the specification, computed** — `E` is
  a world model iff `Setoid.ker E` conforms. World-model-hood is a property of the partition the
  encoder induces; nothing else about `E` matters.
* `ker_le_bisimilarity_of_isWorldModel`: every world model refines bisimilarity.
* `isWorldModel_quotientMk_bisimilarity`: the bisimilarity quotient is a world model — the
  coarsest one, by the two preceding results.

No finiteness, countability, or nonemptiness hypotheses anywhere: `PMF` carries the countable
support intrinsically, so the theorem is at Larsen–Skou generality (probabilistic bisimulation
with countable branching over an arbitrary state space), strictly beyond the finite-MDP setting
of the classical lumpability and bisimulation-metric results. The qualitative LTS counterpart of
`bisimilarity`-as-greatest lives in design-lab's cslib (`Cslib.LTS.Bisimilarity`,
`Cslib.CCS.bisimilarity_is_congruence`); this is the probabilistic, target-relative form the
world-model specification requires.

The physics anchor for the dynamics clause is `world-models/WMSpec/NoLatentDynamics.lean`
(the stroboscopic dichotomy); the readout clause's quantitative form is
`ReadoutCharacterization.lean` (McShane).

## References

Larsen–Skou, *Bisimulation through probabilistic testing*, Inf. Comput. 94 (1991); Kemeny–Snell,
*Finite Markov Chains* (lumpability); Givan–Dean–Greig, *Equivalence notions and model
minimization in Markov decision processes*, AIJ 147 (2003); Ferns–Panangaden–Precup,
*Metrics for finite Markov decision processes*, UAI 2004.
-/

namespace TLT.NonIdentifiability

/-! ## The propagation principle -/

/-- **Per-step indistinguishability propagates along equivalence chains.** If each generating
step of a relation leaves `g` unchanged, so does its equivalence closure. This is the engine of
`isConforming_sSup`: both specification clauses are statements of the form `g s₁ = g s₂`, so both
close under `sSup` by this one principle. -/
theorem eqvGen_factorsThrough {α : Sort*} {γ : Sort*} {rel : α → α → Prop} {g : α → γ}
    (h : ∀ a b, rel a b → g a = g b) {a b : α}
    (hab : Relation.EqvGen rel a b) : g a = g b := by
  induction hab with
  | rel a b h' => exact h a b h'
  | refl a => rfl
  | symm a b _ ih => exact ih.symm
  | trans a b c _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- **Quotient-pushforward equality transports up the lattice.** If two states have equal
pushforward laws on the quotient by `r`, they have equal pushforward laws on the quotient by any
coarser `r'`: the coarser quotient map factors through the finer one (definitionally, via
`Quotient.lift`), and `PMF.map` respects the composition. -/
theorem map_quotient_eq_of_le {S : Type*} {r r' : Setoid S} (hle : r ≤ r') (P : S → PMF S)
    {s₁ s₂ : S}
    (h : (P s₁).map (Quotient.mk r) = (P s₂).map (Quotient.mk r)) :
    (P s₁).map (Quotient.mk r') = (P s₂).map (Quotient.mk r') := by
  have hsound : ∀ a b : S, r a b → Quotient.mk r' a = Quotient.mk r' b :=
    fun a b hab => Quotient.eq.mpr (Setoid.le_def.mp hle hab)
  set φ : Quotient r → Quotient r' := Quotient.lift (Quotient.mk r') hsound with hφdef
  have key : ∀ s : S, (P s).map (Quotient.mk r') = ((P s).map (Quotient.mk r)).map φ := by
    intro s
    rw [PMF.map_comp]
    congr 1
  rw [key s₁, key s₂, h]

/-! ## The specification, in relational and encoder form -/

variable {S : Type*} {ι : Type*} {W : ι → Type*}

/-- **The relational form of the world-model specification.** A setoid conforms to the target
family `T` and dynamics `P` when it refines every target's partition (related states are
target-indistinguishable) and is a `P`-congruence (related states have equal pushforward laws on
the quotient — the lumpability condition of `KernelLumpability`). -/
structure IsConforming (T : ∀ i, S → W i) (P : S → PMF S) (r : Setoid S) : Prop where
  refines : ∀ (i : ι) ⦃s₁ s₂ : S⦄, r s₁ s₂ → T i s₁ = T i s₂
  congr : ∀ ⦃s₁ s₂ : S⦄, r s₁ s₂ → (P s₁).map (Quotient.mk r) = (P s₂).map (Quotient.mk r)

/-- **The encoder form of the world-model specification** (set level). `E` separates what the
targets separate, and some latent transition kernel closes the world-model square. The metric
strengthening of the first clause is `ReadoutCharacterization.lipschitz_readout_iff`. -/
structure IsWorldModel (T : ∀ i, S → W i) (P : S → PMF S) {Z : Type*} (E : S → Z) : Prop where
  separates : ∀ (i : ι) ⦃s₁ s₂ : S⦄, E s₁ = E s₂ → T i s₁ = T i s₂
  hasDynamics : ∃ Q : Z → PMF Z, ∀ s, Q (E s) = (P s).map E

variable {T : ∀ i, S → W i} {P : S → PMF S}

/-! ## Closure under suprema, and bisimilarity -/

/-- **Conforming setoids are closed under arbitrary suprema.** The supremum's relation is the
equivalence closure of the union (`Setoid.sSup_eq_eqvGen`); both clauses propagate along chains
by `eqvGen_factorsThrough` — the target clause directly, the congruence clause after
transporting each component's pushforward equality up to the supremum's quotient
(`map_quotient_eq_of_le`, with `le_sSup`). -/
theorem isConforming_sSup {R : Set (Setoid S)} (hR : ∀ r ∈ R, IsConforming T P r) :
    IsConforming T P (sSup R) := by
  have toEqvGen : ∀ {s₁ s₂ : S}, (sSup R) s₁ s₂ →
      Relation.EqvGen (fun x y => ∃ r ∈ R, r x y) s₁ s₂ := by
    intro s₁ s₂ h
    rw [Setoid.sSup_eq_eqvGen] at h
    exact h
  constructor
  · intro i s₁ s₂ h
    refine eqvGen_factorsThrough (g := T i) ?_ (toEqvGen h)
    rintro a b ⟨r, hrR, hrab⟩
    exact (hR r hrR).refines i hrab
  · intro s₁ s₂ h
    refine eqvGen_factorsThrough (g := fun s => (P s).map (Quotient.mk (sSup R))) ?_ (toEqvGen h)
    rintro a b ⟨r, hrR, hrab⟩
    exact map_quotient_eq_of_le (le_sSup hrR) P ((hR r hrR).congr hrab)

/-- **Bisimilarity relative to the target family and dynamics**: the supremum of all conforming
setoids. By `isConforming_sSup` it is itself conforming, hence the greatest conforming setoid. -/
def bisimilarity (T : ∀ i, S → W i) (P : S → PMF S) : Setoid S :=
  sSup {r | IsConforming T P r}

theorem isConforming_bisimilarity : IsConforming T P (bisimilarity T P) :=
  isConforming_sSup fun _ hr => hr

/-- Bisimilarity is the greatest conforming setoid. -/
theorem isGreatest_bisimilarity :
    IsGreatest {r | IsConforming T P r} (bisimilarity T P) :=
  ⟨isConforming_bisimilarity, fun _ hr => le_sSup hr⟩

/-! ## The extension of the specification, computed -/

/-- **A representation is a world model iff its kernel conforms.** World-model-hood is a
property of the partition the encoder induces — nothing else about the encoder matters. Forward:
the latent kernel yields `E`-congruence (`latentKernel_iff_congruence`), which descends to the
kernel quotient through the factoring `Quotient.mk (ker E) = ψ ∘ E`. Backward: the kernel
quotient's congruence ascends to `E`-congruence through `E = φ ∘ Quotient.mk (ker E)`, and the
latent kernel is rebuilt by `latentKernel_iff_congruence`. -/
theorem isWorldModel_iff_ker_isConforming {Z : Type*} (E : S → Z) :
    IsWorldModel T P E ↔ IsConforming T P (Setoid.ker E) := by
  constructor
  · rintro ⟨hsep, hdyn⟩
    have hcong : ∀ s₁ s₂, E s₁ = E s₂ → (P s₁).map E = (P s₂).map E :=
      (latentKernel_iff_congruence E P).mp hdyn
    refine ⟨fun i s₁ s₂ h => hsep i (Setoid.ker_def.mp h), fun s₁ s₂ h => ?_⟩
    have hE : E s₁ = E s₂ := Setoid.ker_def.mp h
    set ψ : Z → Quotient (Setoid.ker E) :=
      Function.extend E (Quotient.mk (Setoid.ker E))
        (fun _ => Quotient.mk (Setoid.ker E) s₁) with hψdef
    have hψ : ∀ s, ψ (E s) = Quotient.mk (Setoid.ker E) s := by
      intro s
      exact Function.FactorsThrough.extend_apply
        (fun a b hab => Quotient.eq.mpr (Setoid.ker_def.mpr hab)) _ s
    have key : ∀ s : S,
        (P s).map (Quotient.mk (Setoid.ker E)) = ((P s).map E).map ψ := by
      intro s
      rw [PMF.map_comp]
      congr 1
      funext s'
      exact (hψ s').symm
    rw [key s₁, key s₂, hcong s₁ s₂ hE]
  · rintro ⟨href, hcong⟩
    refine ⟨fun i s₁ s₂ h => href i (Setoid.ker_def.mpr h), ?_⟩
    rw [latentKernel_iff_congruence]
    intro s₁ s₂ hE
    have h' := hcong (Setoid.ker_def.mpr hE)
    set φ : Quotient (Setoid.ker E) → Z :=
      Quotient.lift E (fun a b hab => Setoid.ker_def.mp hab) with hφdef
    have key : ∀ s : S, (P s).map E = ((P s).map (Quotient.mk (Setoid.ker E))).map φ := by
      intro s
      rw [PMF.map_comp]
      congr 1
    rw [key s₁, key s₂, h']

/-- **Every world model refines bisimilarity.** The forcing direction: the specification admits
no partition coarser than bisimilarity's. -/
theorem ker_le_bisimilarity_of_isWorldModel {Z : Type*} {E : S → Z}
    (h : IsWorldModel T P E) : Setoid.ker E ≤ bisimilarity T P :=
  le_sSup ((isWorldModel_iff_ker_isConforming E).mp h)

/-- **The bisimilarity quotient is a world model.** Existence: the specification is realized by
the canonical quotient — separation from the `refines` clause through `Quotient.eq`, the latent
dynamics from the `congr` clause through `quotientKernel_iff_congruence`. With
`ker_le_bisimilarity_of_isWorldModel`, it is the coarsest world model: the specification forces
the bisimulation quotient. -/
theorem isWorldModel_quotientMk_bisimilarity :
    IsWorldModel T P (Quotient.mk (bisimilarity T P)) := by
  obtain ⟨href, hcong⟩ := (isConforming_bisimilarity (T := T) (P := P))
  exact ⟨fun i s₁ s₂ h => href i (Quotient.eq.mp h),
    (quotientKernel_iff_congruence (bisimilarity T P) P).mpr fun s₁ s₂ hr => hcong hr⟩

end TLT.NonIdentifiability
