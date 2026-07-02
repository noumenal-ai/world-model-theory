/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Group.End
import Mathlib.Algebra.Group.Submonoid.Defs
import Mathlib.Data.Real.Basic

/-!
# Objective-level invariance: blindness and the matched-invariance direction pair

The matched-invariance draft's objective layer, in the rigorous loss-VALUE form. An SSL
objective is a family `L : Θ → X → M → V` (parameters, data, mask/view selector, loss values —
`V` needs only equality for blindness). Its invariance class is

    ObjectiveInvariant L g  ↔  ∀ θ x m, L θ (g x) m = L θ x m.

* `invarianceMonoid`: the invariant transformations form a submonoid of `Function.End X` —
  the formal footprint of the draft's "objective invariance group" (monoid for arbitrary maps;
  the invertible elements give the group).
* `objective_blindness`: draft Theorem 1's rigorous core, loss-value form — an invariant `g`
  makes every loss observable `L θ · m` factor through `g` exactly.
* `not_factorThrough_loss_of_invariance`: the bridge to the encoder layer — a target that moves
  along a `g`-orbit is recoverable from NO loss observable of a `g`-invariant objective. "The
  missing information has been quotiented out", as a factoring impossibility.
* `sum_objective_invariant_of_components` (draft Thm 4, ⊇): componentwise invariance passes to
  every positively-weighted sum objective.
* `components_invariant_of_sum_objective` (draft Thm 4, ⊆, under a NAMED hypothesis): the
  converse requires ruling out cancellation between components. `MonotoneDeviation` — no
  component's value decreases under `g` — is the explicit richness hypothesis this
  formalization adopts; the draft's informal "independent objective components" is exactly the
  gap this hypothesis names. Under it, positive weights force each component invariant.

Scaling note (draft Corollary 2): `ObjectiveInvariant` quantifies over ALL `θ` — enlarging the
parameter class cannot remove a loss-level invariance. That reading is definitional here.
-/

namespace WMSpec

variable {Θ X M V : Type*}

/-- **Objective invariance.** `g` is an invariance of the objective family `L` when the loss
value cannot distinguish `x` from `g x` — for every parameter, sample, and mask. -/
def ObjectiveInvariant (L : Θ → X → M → V) (g : X → X) : Prop :=
  ∀ θ x m, L θ (g x) m = L θ x m

/-- The identity is an objective invariance. -/
lemma objectiveInvariant_id (L : Θ → X → M → V) : ObjectiveInvariant L id :=
  fun _ _ _ => rfl

/-- Objective invariances compose. -/
lemma ObjectiveInvariant.comp {L : Θ → X → M → V} {g h : X → X}
    (hg : ObjectiveInvariant L g) (hh : ObjectiveInvariant L h) :
    ObjectiveInvariant L (g ∘ h) :=
  fun θ x m => (hg θ (h x) m).trans (hh θ x m)

/-- **The invariance monoid of an objective** (the draft's `G_L`): the submonoid of
`Function.End X` consisting of transformations the loss value cannot see. -/
def invarianceMonoid (L : Θ → X → M → V) : Submonoid (Function.End X) where
  carrier := {g | ObjectiveInvariant L g}
  one_mem' := objectiveInvariant_id L
  mul_mem' := fun hg hh => hg.comp hh

/-- **Objective blindness (draft Theorem 1, loss-value form).** For an invariant `g`, every
loss observable factors through `g` exactly: `(L θ · m) ∘ g = L θ · m`. The objective assigns
identical values along every `g`-orbit, for every parameter — this is the rigorous content of
"optimization cannot create a gradient signal for a distinction not present in the objective";
the training-dynamics reading is interpretation, this equation is the theorem. -/
theorem objective_blindness {L : Θ → X → M → V} {g : X → X}
    (hg : ObjectiveInvariant L g) (θ : Θ) (m : M) :
    (fun x => L θ x m) ∘ g = fun x => L θ x m :=
  funext fun x => hg θ x m

/-- Master lemma (verbatim from `TLT.NonIdentifiability.Apparatus`, pending package
unification): a target separating a collapsed pair factors through nothing built on the
collapse. -/
theorem not_factorThrough_of_collapse {S Z W : Type*} (E : S → Z) (T : S → W)
    {s₁ s₂ : S} (hcollapse : E s₁ = E s₂) (hsep : T s₁ ≠ T s₂) :
    ¬ ∃ g : Z → W, ∀ s, T s = g (E s) := by
  rintro ⟨g, hg⟩
  exact hsep (by rw [hg s₁, hg s₂, hcollapse])

/-- **Blindness bridges to the encoder layer.** If the objective is `g`-invariant and a target
`T` moves along some `g`-orbit (`T x ≠ T (g x)`), then no readout of ANY loss observable
recovers `T`: the loss value at any `(θ, m)` is an encoder that has already collapsed the
orbit. Draft Theorem 1's "blind to a distinction made by the data-generating process", as a
factoring impossibility. -/
theorem not_factorThrough_loss_of_invariance {W : Type*} {L : Θ → X → M → V} {g : X → X}
    (hg : ObjectiveInvariant L g) (T : X → W) {x : X} (hsep : T x ≠ T (g x))
    (θ : Θ) (m : M) :
    ¬ ∃ r : V → W, ∀ y, T y = r (L θ y m) :=
  not_factorThrough_of_collapse (fun y => L θ y m) T (hg θ x m).symm hsep

section Matched

variable {k : ℕ}

/-- **Draft Theorem 4, ⊇ direction.** If every component of a weighted-sum objective is
`g`-invariant, so is the sum — for any weights. -/
theorem sum_objective_invariant_of_components
    (C : Fin k → Θ → X → M → ℝ) (lam : Fin k → ℝ) {g : X → X}
    (hC : ∀ j, ObjectiveInvariant (C j) g) :
    ObjectiveInvariant (fun θ x m => ∑ j : Fin k, lam j * C j θ x m) g := by
  intro θ x m
  exact Finset.sum_congr rfl fun j _ => by rw [hC j θ x m]

/-- **Monotone deviation** — the named richness hypothesis for the converse direction: no
component's value decreases when `g` is applied (each guard can only be violated or preserved
by an unmatched transformation, never improved). The draft's informal "independent objective
components" is the role this hypothesis plays: it rules out cancellation between components
inside the sum. -/
def MonotoneDeviation (C : Fin k → Θ → X → M → ℝ) (g : X → X) : Prop :=
  ∀ j θ x m, C j θ x m ≤ C j θ (g x) m

/-- **Draft Theorem 4, ⊆ direction, under `MonotoneDeviation`.** With strictly positive
weights and no component able to decrease under `g`, invariance of the weighted sum forces
invariance of every component: positively-weighted nonnegative deviations summing to zero all
vanish. This is the precise form in which "one guard per broken symmetry removes every spurious
direction" is a theorem rather than a slogan. -/
theorem components_invariant_of_sum_objective
    (C : Fin k → Θ → X → M → ℝ) (lam : Fin k → ℝ) {g : X → X}
    (hlam : ∀ j, 0 < lam j)
    (hmono : MonotoneDeviation C g)
    (hsum : ObjectiveInvariant (fun θ x m => ∑ j : Fin k, lam j * C j θ x m) g) :
    ∀ j, ObjectiveInvariant (C j) g := by
  intro j θ x m
  have hzero : ∑ i : Fin k, lam i * (C i θ (g x) m - C i θ x m) = 0 := by
    have h : ∑ i : Fin k, lam i * C i θ (g x) m = ∑ i : Fin k, lam i * C i θ x m :=
      hsum θ x m
    have hexpand : ∑ i : Fin k, lam i * (C i θ (g x) m - C i θ x m)
        = ∑ i : Fin k, lam i * C i θ (g x) m - ∑ i : Fin k, lam i * C i θ x m := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [hexpand, h, sub_self]
  have hnonneg : ∀ i ∈ Finset.univ, (0:ℝ) ≤ lam i * (C i θ (g x) m - C i θ x m) :=
    fun i _ => mul_nonneg (hlam i).le (sub_nonneg.mpr (hmono i θ x m))
  have heach := (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp hzero j (Finset.mem_univ j)
  rcases mul_eq_zero.mp heach with hl | hd
  · exact absurd hl (hlam j).ne'
  · exact sub_eq_zero.mp hd

end Matched

end WMSpec
