/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import TLT_Proofs.NonIdentifiability.Apparatus
import NN.MLTheory.SelfSupervised.JEPA

/-!
# JEPA non-identifiability boundary (bound to the real `jepaLoss`)

Binds the collapse/non-identifiability apparatus to the JEPA objective
`NN.MLTheory.SelfSupervised.jepaLoss`, whose predictor has type `predict : Context → Fin n → Pred`
— it reads the *context* (the representation) alone at each target index. Boundary: if the
context-encoder collapses a target-separated pair of inputs, no readout of the context recovers the
target, so the represented target is not a function of the JEPA context and no predictor/decoder
pair (a function of context alone) matches both.

The `witness_jepaLoss_computes` sanity theorem exercises the real `jepaLoss` on the witness types.
The loss-lower-bound form (`jepaLoss > 0` on a collapsed target-separated pair) is a separate,
stronger binding that mentions `jepaLoss` in its conclusion — planned, discussed before building.
-/

open NN.MLTheory.SelfSupervised
open TLT.NonIdentifiability

noncomputable section

namespace TLT.NonIdentifiability.JEPA

/-- **JEPA representation non-identifiability.** If the context-encoder `E` collapses two inputs
(`E i₁ = E i₂`) whose true targets differ (`T i₁ ≠ T i₂`), no readout `g : Context → Target`
recovers the target from the JEPA context. The master lemma at `Z := Context`, `W := Target`. -/
theorem jepa_target_not_identifiable
    {Input Context Target : Type} (E : Input → Context) (T : Input → Target)
    {i₁ i₂ : Input} (hcollapse : E i₁ = E i₂) (hsep : T i₁ ≠ T i₂) :
    ¬ ∃ g : Context → Target, ∀ x, T x = g (E x) :=
  not_factorThrough_of_collapse E T hcollapse hsep

/-- **JEPA predictor boundary (real `predict` shape).** The JEPA predictor
`predict : Context → Fin n → Pred` reads the context alone; at a fixed target index `k` it is
`fun c => predict c k`, and composing any decoder `dec : Pred → Target` gives a context-only readout.
Under encoder collapse on a target-separated pair, no predictor/decoder pair recovers the target at
both inputs. -/
theorem jepa_predict_cannot_recover_target
    {n : Nat} {Input Context Target Pred : Type}
    (E : Input → Context) (T : Input → Target)
    (predict : Context → Fin n → Pred)
    (k : Fin n)
    {i₁ i₂ : Input} (hcollapse : E i₁ = E i₂) (hsep : T i₁ ≠ T i₂) :
    ¬ ∃ dec : Pred → Target, ∀ x, T x = dec (predict (E x) k) := by
  rintro ⟨dec, hdec⟩
  exact jepa_target_not_identifiable E T hcollapse hsep
    ⟨fun c => dec (predict c k), hdec⟩

/-- Phrased with `Function.FactorsThrough`: `T` does not factor through `E` under collapse. -/
theorem jepa_target_not_factorsThrough
    {Input Context Target : Type} (E : Input → Context) (T : Input → Target)
    {i₁ i₂ : Input} (hcollapse : E i₁ = E i₂) (hsep : T i₁ ≠ T i₂) :
    ¬ Function.FactorsThrough T E := by
  intro hft
  exact hsep (hft hcollapse)

/-! ### Concrete non-vacuous witness (A4) -/

/-- Witness context-encoder: collapses both inputs to the one-point context. -/
def witnessE : Fin 2 → Fin 1 := fun _ => 0
/-- Witness true target: the two inputs differ. -/
def witnessT : Fin 2 → Fin 2 := fun x => x
/-- Predictor at the real `predict : Context → Fin n → Pred` shape (`n = 1`, `Pred = Fin 2`). -/
def witnessPredict : Fin 1 → Fin 1 → Fin 2 := fun _ _ => 0

theorem witness_collapse : witnessE 0 = witnessE 1 := by decide
theorem witness_separated : witnessT 0 ≠ witnessT 1 := by decide

theorem jepa_boundary_witness :
    ¬ ∃ g : Fin 1 → Fin 2, ∀ x, witnessT x = g (witnessE x) :=
  jepa_target_not_identifiable witnessE witnessT witness_collapse witness_separated

theorem jepa_boundary_witness_predict :
    ¬ ∃ dec : Fin 2 → Fin 2, ∀ x, witnessT x = dec (witnessPredict (witnessE x) 0) :=
  jepa_predict_cannot_recover_target witnessE witnessT witnessPredict 0
    witness_collapse witness_separated

/-- Sanity check tying the witness types to the actual `jepaLoss`: with a context-alone predictor
disagreeing with the target-at-index, the real objective computes a nonzero loss. -/
def witnessTargetAtIdx : Fin 1 → Fin 2 := fun _ => 1

theorem witness_jepaLoss_computes :
    jepaLoss [0] (witnessE 0) witnessTargetAtIdx witnessPredict
      (fun t p => if t = p then 0 else 1) = 1 := by decide

end TLT.NonIdentifiability.JEPA
