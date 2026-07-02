/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import WMSpec.MaskIndexedInvariance

/-!
# Theorem 4 on the repaired contract: matched invariance, characterized

The matched objective in the E3-repaired form — an ℕ-valued predictive branch (the literal
contract/`jepaLoss` type) plus positively-weighted data-reading ℝ-guards:

    L_matched θ x m  =  ↑(L_pred θ x m) + ∑ j, λ_j · G_j x.

The draft's Theorem 4 claims `G_{L_matched} = G_{L_pred} ∩ ⋂_j G_{G_j}`. This file locates the
hypotheses exactly:

* **The pred/guard joint needs NO richness hypothesis** for mask-additive predictive branches
  (`matched_invariance_iff`): the empty mask — last tick's vacuity stratum, inverted into a
  separation tool — zeroes the predictive branch, so matched-invariance at `[]` yields
  guard-sum invariance outright, and predictive invariance follows by subtraction and
  `Nat.cast` injectivity. Unconditional, both directions.
* **Richness is needed only among the guards** (`guards_invariant_of_matched`): splitting the
  invariant guard SUM into per-guard invariance is where cancellation must be excluded —
  positive weights + monotone guards (the named hypothesis, now in its minimal location).
* `matched_invariance_characterization`: the full Theorem 4 under exactly those hypotheses.

Value-type seam (recorded): guards are ℝ-valued for analytic generality (HSIC/MMD/MI
zero-iffs), so ℝ-instance witnesses close by `norm_num` rather than kernel `rfl`; the executed
`rfl` witnesses live on the ℕ/`jepaLoss` side. A ℚ-valued executable-guard variant is the
TorchLean/dyadic plan-edge.
-/

namespace WMSpec

open NN.MLTheory.SelfSupervised

variable {Θ X M : Type*} {k : ℕ}

/-- **The matched objective on the repaired form**: cast-ℕ predictive branch plus
positively-weighted data-reading guards. The formal shape of the draft's
`L_matched = L_pred + ∑ λ_j G_{s_j}`. -/
def matchedObjective (Lpred : Θ → X → M → ℕ) (G : Fin k → X → ℝ) (lam : Fin k → ℝ) :
    Θ → X → M → ℝ :=
  fun θ x m => (Lpred θ x m : ℝ) + ∑ j : Fin k, lam j * G j x

/-- **Theorem 4, ⊇ (unconditional).** Predictive invariance plus per-guard invariance passes
to the matched objective. -/
theorem matchedObjective_invariant_of_components
    {Lpred : Θ → X → M → ℕ} {G : Fin k → X → ℝ} {lam : Fin k → ℝ} {g : X → X}
    (hpred : ObjectiveInvariant Lpred g) (hG : ∀ j x, G j (g x) = G j x) :
    ObjectiveInvariant (matchedObjective Lpred G lam) g := by
  intro θ x m
  simp only [matchedObjective, hpred θ x m]
  congr 1
  exact Finset.sum_congr rfl fun j _ => by rw [hG j x]

section NilSeparation

variable {ι : Type*} {Lpred : Θ → X → List ι → ℕ} {G : Fin k → X → ℝ}
  {lam : Fin k → ℝ} {g : X → X}

/-- **The nil mask separates the guard from the predictive branch.** For a mask-additive
predictive branch, matched-invariance instantiated at the empty mask — where the predictive
loss vanishes — yields invariance of the guard sum, with no hypothesis on the guards. The
vacuity stratum inverted into the separation tool. -/
theorem guardSum_invariant_of_matched
    (hadd : ∀ θ x I₁ I₂, Lpred θ x (I₁ ++ I₂) = Lpred θ x I₁ + Lpred θ x I₂)
    (h : ObjectiveInvariant (matchedObjective Lpred G lam) g) (θ₀ : Θ) (x : X) :
    ∑ j : Fin k, lam j * G j (g x) = ∑ j : Fin k, lam j * G j x := by
  have hz : ∀ y, Lpred θ₀ y [] = 0 := by
    intro y
    have hy := hadd θ₀ y [] []
    simp only [List.nil_append] at hy
    omega
  have h0 : (Lpred θ₀ (g x) [] : ℝ) + ∑ j : Fin k, lam j * G j (g x)
      = (Lpred θ₀ x [] : ℝ) + ∑ j : Fin k, lam j * G j x := h θ₀ x []
  rw [hz (g x), hz x] at h0
  simp only [Nat.cast_zero, zero_add] at h0
  exact h0

/-- **Predictive invariance falls out by subtraction.** Given matched-invariance over a
mask-additive branch, subtract the (already-invariant) guard sum and cancel the `Nat.cast`:
the predictive branch is invariant on its own. No richness hypothesis. -/
theorem pred_invariant_of_matched
    (hadd : ∀ θ x I₁ I₂, Lpred θ x (I₁ ++ I₂) = Lpred θ x I₁ + Lpred θ x I₂)
    (h : ObjectiveInvariant (matchedObjective Lpred G lam) g) :
    ObjectiveInvariant Lpred g := by
  intro θ x m
  have hm : (Lpred θ (g x) m : ℝ) + ∑ j : Fin k, lam j * G j (g x)
      = (Lpred θ x m : ℝ) + ∑ j : Fin k, lam j * G j x := h θ x m
  have hguard := guardSum_invariant_of_matched hadd h θ x
  rw [hguard] at hm
  have hcast : (Lpred θ (g x) m : ℝ) = (Lpred θ x m : ℝ) := add_right_cancel hm
  exact_mod_cast hcast

/-- **Theorem 4 at the pred/guard joint, characterized — no richness hypothesis.** For a
mask-additive predictive branch, the matched objective is `g`-invariant **iff** the predictive
branch is invariant and the guard sum is invariant. Both directions unconditional: the nil
mask does the separation the draft's "independence" was informally invoked for. -/
theorem matched_invariance_iff
    (hadd : ∀ θ x I₁ I₂, Lpred θ x (I₁ ++ I₂) = Lpred θ x I₁ + Lpred θ x I₂) (θ₀ : Θ) :
    ObjectiveInvariant (matchedObjective Lpred G lam) g ↔
    (ObjectiveInvariant Lpred g ∧
      ∀ x, ∑ j : Fin k, lam j * G j (g x) = ∑ j : Fin k, lam j * G j x) := by
  constructor
  · intro h
    exact ⟨pred_invariant_of_matched hadd h,
      fun x => guardSum_invariant_of_matched hadd h θ₀ x⟩
  · rintro ⟨hpred, hsum⟩ θ x m
    simp only [matchedObjective, hpred θ x m, hsum x]

/-- **Richness, in its minimal location: the guard/guard joint.** Splitting the invariant
guard sum into per-guard invariance is where cancellation must be excluded: positive weights
and monotone guards (no guard improves under `g`) force each guard invariant. -/
theorem guards_invariant_of_matched
    (hadd : ∀ θ x I₁ I₂, Lpred θ x (I₁ ++ I₂) = Lpred θ x I₁ + Lpred θ x I₂)
    (hlam : ∀ j, 0 < lam j) (hmono : ∀ j x, G j x ≤ G j (g x))
    (h : ObjectiveInvariant (matchedObjective Lpred G lam) g) (θ₀ : Θ) :
    ∀ j x, G j (g x) = G j x := by
  intro j x
  have hsum := guardSum_invariant_of_matched hadd h θ₀ x
  have hzero : ∑ i : Fin k, lam i * (G i (g x) - G i x) = 0 := by
    have hexpand : ∑ i : Fin k, lam i * (G i (g x) - G i x)
        = ∑ i : Fin k, lam i * G i (g x) - ∑ i : Fin k, lam i * G i x := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [hexpand, hsum, sub_self]
  have hnonneg : ∀ i ∈ Finset.univ, (0:ℝ) ≤ lam i * (G i (g x) - G i x) :=
    fun i _ => mul_nonneg (hlam i).le (sub_nonneg.mpr (hmono i x))
  have heach := (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp hzero j (Finset.mem_univ j)
  rcases mul_eq_zero.mp heach with hl | hd
  · exact absurd hl (hlam j).ne'
  · exact sub_eq_zero.mp hd

/-- **Theorem 4, full characterization (draft form), hypotheses in their minimal locations.**
For a mask-additive predictive branch, positive weights, and monotone guards:

    g ∈ G_{L_matched}  ↔  g ∈ G_{L_pred} ∧ ∀ j, g ∈ G_{G_j}.

The pred/guard separation is unconditional (nil mask); monotonicity is spent only on
splitting the guard sum. -/
theorem matched_invariance_characterization
    (hadd : ∀ θ x I₁ I₂, Lpred θ x (I₁ ++ I₂) = Lpred θ x I₁ + Lpred θ x I₂)
    (hlam : ∀ j, 0 < lam j) (hmono : ∀ j x, G j x ≤ G j (g x)) (θ₀ : Θ) :
    ObjectiveInvariant (matchedObjective Lpred G lam) g ↔
    (ObjectiveInvariant Lpred g ∧ ∀ j x, G j (g x) = G j x) := by
  constructor
  · intro h
    exact ⟨pred_invariant_of_matched hadd h, guards_invariant_of_matched hadd hlam hmono h θ₀⟩
  · rintro ⟨hpred, hG⟩
    exact matchedObjective_invariant_of_components hpred hG

end NilSeparation

section JepaBinding

/-- **The matched JEPA objective**: the literal TorchLean-package `jepaLoss` as the predictive
branch, arbitrary data-reading guards. The object draft Theorem 4 is about, on the verified
loss. -/
def jepaMatched (n : Nat) (Context Target Pred : Type)
    (G : Fin k → (Context × (Fin n → Target)) → ℝ) (lam : Fin k → ℝ) :=
  matchedObjective (jepaFamily n Context Target Pred) G lam

/-- **Theorem 4 on the literal JEPA loss.** `jepaLoss` is mask-additive (`jepaLoss_append`),
so the characterization applies with monotone guards and positive weights — the draft's
Theorem 4, on the verified predictive branch, with the richness hypothesis only at the
guard/guard joint. -/
theorem jepaMatched_invariance_characterization
    {n : Nat} {Context Target Pred : Type}
    {G : Fin k → (Context × (Fin n → Target)) → ℝ} {lam : Fin k → ℝ}
    {g : (Context × (Fin n → Target)) → (Context × (Fin n → Target))}
    (hlam : ∀ j, 0 < lam j) (hmono : ∀ j x, G j x ≤ G j (g x))
    (θ₀ : (Context → Fin n → Pred) × (Target → Pred → Nat)) :
    ObjectiveInvariant (jepaMatched n Context Target Pred G lam) g ↔
    (ObjectiveInvariant (jepaFamily n Context Target Pred) g ∧ ∀ j x, G j (g x) = G j x) :=
  matched_invariance_characterization
    (fun θ x I₁ I₂ => jepaLoss_append I₁ I₂ x.1 x.2 θ.1 θ.2) hlam hmono θ₀

/-- **Executed witness (ℕ side, kernel computation): the nil mask zeroes the literal
`jepaLoss`** — the separation lever exists on the real object. -/
theorem witness_jepa_nil_executed :
    jepaLoss ([] : List (Fin 2)) () (fun _ => false) (fun _ _ => true)
      (fun t p => if t = p then 0 else 1) = 0 := rfl

/-- **Instance witness (ℝ side, `norm_num`): a data-reading guard breaks matched-invariance.**
On the two-point instance, the matched objective with guard `x ↦ if x.2 0 then 1 else 0`
detects the target rewrite that the bare predictive branch (mask `[0]`) cannot see —
Theorem 4's content on a computed example. -/
theorem witness_matched_detects :
    ¬ ObjectiveInvariant
        (matchedObjective (jepaFamily 2 Unit Bool Bool)
          (fun (_ : Fin 1) x => if x.2 0 then (1:ℝ) else 0) (fun _ => 1))
        (fun x => (x.1, fun _ => true)) := by
  intro h
  have h0 := h ((fun _ _ => true), (fun t p => if t = p then 0 else 1))
    ((), fun _ => false) []
  simp [matchedObjective, jepaFamily] at h0

end JepaBinding

end WMSpec
