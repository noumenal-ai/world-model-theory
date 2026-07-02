/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import WMSpec.ObjectiveInvariance
import NN.MLTheory.SelfSupervised.JEPA

/-!
# Mask-indexed invariance: the R-expansions forced by the verified JEPA algebra

The four expansions the F5 inspection forced (E1–E4), each with a proof AND an executed
witness on the literal TorchLean-package `jepaLoss`. Classical anchor: Cantwell, *Introduction
to Symmetry Analysis* (CUP 2002) — §1.4 (the covariance principle: the objective must keep its
form under the appropriate transformations), §1.5.2 (invariance of functions under groups;
`ObjectiveInvariant` is its discrete, slot-typed form), §1.3 (discrete symmetry groups — here
monoids of endomorphisms, per slot).

* **E1 — mask-indexed invariance.** `ObjectiveInvariantAt L m g`: invariance AT a mask. The
  global class is the intersection over masks (`objectiveInvariant_iff_forall_at`), and the
  invisibility theorem (`jepaLoss_target_ext`) becomes a worked instance: rewriting unselected
  targets is an invariance at that mask. "The mask chooses what the objective can and cannot
  see" is now a statement about how `invarianceMonoidAt` varies with `m`.
* **Vacuity strata (mini-E3, found by inquiry).** The empty mask constrains nothing:
  `objectiveInvariantAt_nil_of_additive`. The bottom of the mask lattice is invariance-blind —
  the same shape as the constant-guard alarm, one stratum down.
* **E2 — mask-separation richness.** For mask-additive objectives, invariance at every
  singleton mask already forces global invariance (`objectiveInvariant_of_singletons`):
  structural cancellation-exclusion, replacing `MonotoneDeviation` for the JEPA case.
* **E3 — the guard repair.** `constant_guard_invariant` states the alarm as a theorem (a
  constant guard admits EVERY transformation as an invariance — today's contract slot);
  `enrichedObjective` is the repair (guards as functions of the data), and
  `enrichedGuard_nonvacuous` executes a two-point witness showing the repaired slot genuinely
  excludes transformations. Contract-level wiring is the Theorem-4 mini-project's first step.
* **E4 — the mask-symmetry axis.** `MaskInvariant L σ`: transformations of the mask slot;
  `jepaLoss_reverse` gives the worked instance. Temporal asymmetry (causal masks) is a
  statement about which σ are NOT mask-invariances of a matched objective.
-/

namespace WMSpec

open NN.MLTheory.SelfSupervised

variable {Θ X M V : Type*}

/-! ## E1 — invariance at a mask -/

/-- **Invariance at a mask.** `g` is an invariance of the objective AT the view/mask `m`: the
loss value at `m` cannot distinguish `x` from `g x`, for every parameter. The mask-indexed
refinement of `ObjectiveInvariant`. -/
def ObjectiveInvariantAt (L : Θ → X → M → V) (m : M) (g : X → X) : Prop :=
  ∀ θ x, L θ (g x) m = L θ x m

/-- Global objective invariance is exactly invariance at every mask: `G_L = ⋂ₘ G_L(m)`.
The mask-indexed family is the finer object; the draft's `G_L` is its intersection. -/
theorem objectiveInvariant_iff_forall_at (L : Θ → X → M → V) (g : X → X) :
    ObjectiveInvariant L g ↔ ∀ m, ObjectiveInvariantAt L m g :=
  ⟨fun h m θ x => h θ x m, fun h θ x m => h m θ x⟩

/-- **The invariance monoid at a mask**: transformations the loss value at `m` cannot see. -/
def invarianceMonoidAt (L : Θ → X → M → V) (m : M) : Submonoid (Function.End X) where
  carrier := {g | ObjectiveInvariantAt L m g}
  one_mem' := fun _ _ => rfl
  mul_mem' := fun hg hh θ x => (hg θ _).trans (hh θ x)

section Jepa

variable {n : Nat} {Context Target Pred : Type}

/-- The JEPA objective as a slot-typed family: parameters `θ` = (predictor, representation
loss); data `x` = (context view, target view); mask `m` = the selected target indices. The
literal `jepaLoss` of the TorchLean package, re-slotted for invariance analysis. -/
def jepaFamily (n : Nat) (Context Target Pred : Type) :
    ((Context → Fin n → Pred) × (Target → Pred → Nat)) →
    (Context × (Fin n → Target)) → List (Fin n) → Nat :=
  fun θ x m => jepaLoss m x.1 x.2 θ.1 θ.2

/-- **E1 worked instance (the invisibility theorem as a mask-indexed invariance).** Rewriting
the targets OUTSIDE a mask `I` — by any per-index rewrite `r` — is an invariance of the JEPA
objective at `I`: the mask has chosen not to see it. Direct consequence of the verified
`jepaLoss_target_ext`. -/
theorem unselectedRewrite_invariantAt [DecidableEq (Fin n)]
    (I : List (Fin n)) (r : Fin n → Target → Target) :
    ObjectiveInvariantAt (jepaFamily n Context Target Pred) I
      (fun x => (x.1, fun i => if i ∈ I then x.2 i else r i (x.2 i))) := by
  intro θ x
  exact jepaLoss_target_ext I x.1 _ x.2 θ.1 θ.2 (fun i hi => by simp [hi])

/-- **E1 executed witness** (kernel computation on the literal `jepaLoss`, mask `[0]`,
targets rewritten at the unselected index `1`): both sides evaluate to the same loss. -/
theorem witness_unselected_rewrite_executed :
    jepaLoss [(0 : Fin 2)] () (fun _ => false) (fun _ _ => true)
        (fun t p => if t = p then 0 else 1)
      = jepaLoss [(0 : Fin 2)] () (fun i => if i = 1 then true else false)
        (fun _ _ => true) (fun t p => if t = p then 0 else 1) := rfl

/-! ## Vacuity strata (mini-E3): the empty mask constrains nothing -/

/-- For a mask-additive objective the empty mask is invariance-blind: EVERY transformation is
an invariance at `[]`. The bottom stratum of the mask lattice carries no constraint — the
guard-vacuity alarm one level down. -/
theorem objectiveInvariantAt_nil_of_additive {ι : Type*}
    (L : Θ → X → List ι → ℕ)
    (hadd : ∀ θ x I₁ I₂, L θ x (I₁ ++ I₂) = L θ x I₁ + L θ x I₂) (g : X → X) :
    ObjectiveInvariantAt L ([] : List ι) g := by
  intro θ x
  have hz : ∀ y, L θ y [] = 0 := fun y => by
    have h := hadd θ y [] []
    simp only [List.nil_append] at h
    omega
  rw [hz (g x), hz x]

/-! ## E2 — singleton masks generate: structural cancellation-exclusion -/

/-- **Mask-separation richness.** For a mask-additive objective, invariance at every singleton
mask forces invariance at every mask: `i :: I = [i] ++ I` splits any mask, and ℕ-additivity
recombines. The structural alternative to `MonotoneDeviation` — for JEPA the mask family
itself excludes cancellation. -/
theorem objectiveInvariant_of_singletons {ι : Type*}
    (L : Θ → X → List ι → ℕ)
    (hadd : ∀ θ x I₁ I₂, L θ x (I₁ ++ I₂) = L θ x I₁ + L θ x I₂)
    {g : X → X} (hsingle : ∀ i : ι, ObjectiveInvariantAt L [i] g) :
    ObjectiveInvariant L g := by
  intro θ x m
  induction m with
  | nil =>
      have h1 := hadd θ (g x) [] []
      have h2 := hadd θ x [] []
      simp only [List.nil_append] at h1 h2
      omega
  | cons i I ih =>
      have hsplit : ∀ y, L θ y (i :: I) = L θ y [i] + L θ y I :=
        fun y => hadd θ y [i] I
      rw [hsplit (g x), hsplit x, hsingle i θ x, ih]

/-- **E2 executed witness**: mask-additivity of the literal `jepaLoss` on a concrete instance
(`[0,1] = [0] ++ [1]`), computed by the kernel. -/
theorem witness_mask_additivity_executed :
    jepaLoss [(0 : Fin 2), 1] () (fun _ => false) (fun _ _ => true)
        (fun t p => if t = p then 0 else 1)
      = jepaLoss [(0 : Fin 2)] () (fun _ => false) (fun _ _ => true)
          (fun t p => if t = p then 0 else 1)
        + jepaLoss [(1 : Fin 2)] () (fun _ => false) (fun _ _ => true)
          (fun t p => if t = p then 0 else 1) := rfl

/-! ## E3 — the guard repair -/

/-- **The vacuity alarm as a theorem.** A constant guard — the shape of today's contract slot
(`geometryGuard : Nat`, attached as a pre-evaluated value) — admits EVERY transformation as an
invariance. A guard that cannot see the data removes no spurious invariance, so a
guard-intersection theorem over constant guards is vacuously true. -/
theorem constant_guard_invariant (c : V) (g : X → X) :
    ObjectiveInvariant (fun (_ : Θ) (_ : X) (_ : M) => c) g :=
  fun _ _ _ => rfl

/-- **The repair**: a guarded objective whose guard reads the data. This is the enrichment the
Theorem-4 binding requires of the contract's guard slot. -/
def enrichedObjective (Lpred : Θ → X → M → ℕ) (G : X → ℕ) : Θ → X → M → ℕ :=
  fun θ x m => Lpred θ x m + G x

/-- **E3 executed witness (non-vacuity of the repaired slot).** A data-reading guard genuinely
excludes transformations: the two-point guard `x ↦ if x then 1 else 0` on `Bool` is NOT
invariant under negation — the kernel computes the violating pair. -/
theorem enrichedGuard_nonvacuous :
    ¬ ObjectiveInvariant
        (enrichedObjective (fun (_ : Unit) (_ : Bool) (_ : Unit) => 0)
          (fun x => if x then 1 else 0)) not :=
  fun h => Nat.one_ne_zero (h () false ())

end Jepa

/-! ## E4 — the mask-symmetry axis -/

/-- **Mask invariance**: symmetry in the mask/view slot. `σ : M → M` is a mask symmetry of the
objective when relabeling views by `σ` never changes the loss. The third invariance axis
(parameters, data, masks); temporal asymmetry lives here — a causal objective is exactly one
for which time-reversing σ is NOT a mask invariance. -/
def MaskInvariant (L : Θ → X → M → V) (σ : M → M) : Prop :=
  ∀ θ x m, L θ x (σ m) = L θ x m

/-- Mask symmetries form a submonoid of `Function.End M`. -/
def maskInvarianceMonoid (L : Θ → X → M → V) : Submonoid (Function.End M) where
  carrier := {σ | MaskInvariant L σ}
  one_mem' := fun _ _ _ => rfl
  mul_mem' := fun hσ hτ θ x m => (hσ θ x _).trans (hτ θ x m)

section JepaMask

variable {n : Nat} {Context Target Pred : Type}

/-- **E4 worked instance**: `List.reverse` is a mask symmetry of the JEPA objective — the
verified `jepaLoss_reverse`, re-slotted. -/
theorem reverse_maskInvariant :
    MaskInvariant (jepaFamily n Context Target Pred) List.reverse :=
  fun θ x m => jepaLoss_reverse m x.1 x.2 θ.1 θ.2

/-- **E4 executed witness** on a length-2 mask (where `reverse ≠ id`): the kernel computes
equal losses for `[1,0]` and `[0,1]`. -/
theorem witness_reverse_executed :
    jepaLoss [(1 : Fin 2), 0] () (fun _ => false) (fun _ _ => true)
        (fun t p => if t = p then 0 else 1)
      = jepaLoss [(0 : Fin 2), 1] () (fun _ => false) (fun _ _ => true)
        (fun t p => if t = p then 0 else 1) := rfl

end JepaMask

end WMSpec
