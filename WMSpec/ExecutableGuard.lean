/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import WMSpec.MatchedObjective
import NN.Floats.IEEEExec.RealSemantics

/-!
# The executable guard: matched objectives with kernel-computable float32 guards

Theorem 4's guard slot, made executable. Three layers:

* **The ℚ-reading of executed float32** (`dyadicToRat`, `toRat`): TorchLean's `IEEE32Exec.Dyadic`
  is plain data (`sign/mant/exp`, decidable equality), so the executed value has a computable
  rational reading. `dyadicToRat_cast`/`toRat_cast` prove it agrees with the noncomputable
  ℝ-reading (`dyadicToReal`, `toReal`) under the cast — so witness obligations about executed
  values discharge by kernel `decide` on the decoded data and transport to the ℝ theory by
  `Rat.cast_injective`. (The radix lemma re-proves `TLT.Capacity.neuralBpow_binaryRadix_eq`
  locally, attributed, keeping this module on the built `NN.Floats` closure.)

* **The cast-factored guard** (`spreadQ`, `spreadGuard`): guards of the form `(↑) ∘ Gq` with
  `Gq` computable — the ℝ-typed interface `matchedObjective` requires, with decidable
  invariance. `spreadGuard` is the two-point anti-collapse guard: the absolute spread of the
  two target latents' executed values (the 2-point shadow of a variance/VICReg guard).

* **The Theorem-4 executed story** (`witness_executedGuard_matched_detects`): on the
  one-ULP-adjacent float32 pair, with a collapse-blind predictive branch (`repLoss ≡ 0` — the
  kernel computes both sides' `jepaLoss` to `0` by `rfl`), the matched objective with the
  spread guard DETECTS target collapse, while the bare predictive branch cannot. The guard
  removes exactly the spurious invariance the predictive branch carries, on literal bits.

Reduction note (banked): whole-term `decide` on ℚ-`abs` expressions blocks at the
`Decidable.rec` inside `|·|`; the witness therefore decides only the bit-level decode atoms
(`toDyadic? … = some ⟨…⟩`, the proven pattern) and a literal ℚ equality, with the remaining
steps symbolic.
-/

namespace WMSpec

open NN.MLTheory.SelfSupervised TorchLean.Floats TorchLean.Floats.IEEE754

/-! ## The ℚ-reading of executed float32 -/

/-- Computable rational reading of a decoded float32: `±mant · 2^exp` in ℚ. Mirrors
`IEEE32Exec.dyadicToReal` shape-for-shape. -/
def dyadicToRat (d : IEEE32Exec.Dyadic) : ℚ :=
  (if d.sign then (-1 : ℚ) else 1) * (d.mant : ℚ) * (2 : ℚ) ^ d.exp

/-- Computable rational reading of an executed float32 (`0` on non-finite). -/
def toRat (x : IEEE32Exec) : ℚ :=
  (IEEE32Exec.toDyadic? x).elim 0 dyadicToRat

/-- The binary radix power is `2^e` over ℝ (local, attributed re-proof of
`TLT.Capacity.neuralBpow_binaryRadix_eq`, kept here to stay on the `NN.Floats` closure). -/
lemma neuralBpow_binaryRadix (e : ℤ) : neuralBpow binaryRadix e = (2 : ℝ) ^ e := by
  simp [neuralBpow, binaryRadix, NeuralRadix.toReal]

/-- **The bridge, decoded form**: the ℚ-reading agrees with the ℝ-reading of a decoded value. -/
lemma dyadicToRat_cast (d : IEEE32Exec.Dyadic) :
    ((dyadicToRat d : ℚ) : ℝ) = IEEE32Exec.dyadicToReal d := by
  rw [IEEE32Exec.dyadicToReal, neuralBpow_binaryRadix, dyadicToRat]
  split_ifs <;> push_cast <;> ring

/-- On a decoded value, `toRat` is the dyadic reading. -/
lemma toRat_of_toDyadic {x : IEEE32Exec} {d : IEEE32Exec.Dyadic}
    (hd : IEEE32Exec.toDyadic? x = some d) : toRat x = dyadicToRat d := by
  rw [toRat, hd]
  rfl

/-- On a decoded value, `toReal` is the dyadic reading (via the `@[simp]` hooks of
`RealSemantics`). -/
lemma toReal_of_toDyadic {x : IEEE32Exec} {d : IEEE32Exec.Dyadic}
    (hd : IEEE32Exec.toDyadic? x = some d) :
    IEEE32Exec.toReal x = IEEE32Exec.dyadicToReal d := by
  simp [IEEE32Exec.toReal, IEEE32Exec.toReal?_of_toDyadic?_some hd]

/-- **The bridge, executed-value form**: on finite values the cast ℚ-reading IS the executed
real value. Executed-witness obligations about `toReal` reduce to computation on ℚ. -/
lemma toRat_cast {x : IEEE32Exec} {d : IEEE32Exec.Dyadic}
    (hd : IEEE32Exec.toDyadic? x = some d) :
    ((toRat x : ℚ) : ℝ) = IEEE32Exec.toReal x := by
  rw [toRat_of_toDyadic hd, toReal_of_toDyadic hd, dyadicToRat_cast]

/-! ## The cast-factored anti-collapse guard -/

/-- The computable core: absolute spread of the two target latents' executed values. -/
def spreadQ (x : Unit × (Fin 2 → IEEE32Exec)) : ℚ :=
  |toRat (x.2 0) - toRat (x.2 1)|

/-- **The executable anti-collapse guard**: ℝ-typed (as `matchedObjective` requires),
ℚ-computable core. Zero iff the two target latents decode to the same rational — the 2-point
shadow of a variance guard. -/
def spreadGuard : (Unit × (Fin 2 → IEEE32Exec)) → ℝ :=
  fun x => ((spreadQ x : ℚ) : ℝ)

/-- Cast-transfer: guard equality in ℝ is spread equality in ℚ. -/
lemma spreadGuard_eq_iff (x y : Unit × (Fin 2 → IEEE32Exec)) :
    spreadGuard x = spreadGuard y ↔ spreadQ x = spreadQ y :=
  ⟨fun h => Rat.cast_injective h, fun h => by rw [spreadGuard, spreadGuard, h]⟩

/-! ## The executed Theorem-4 witness on literal bits -/

/-- The one-ULP pair: `1.0` and the next float32 above it. -/
def w : Unit × (Fin 2 → IEEE32Exec) :=
  ((), fun i => if i = 0 then IEEE32Exec.ofBits 0x3F800000 else IEEE32Exec.ofBits 0x3F800001)

/-- Target collapse: overwrite both targets with the first. -/
def collapse : (Unit × (Fin 2 → IEEE32Exec)) → (Unit × (Fin 2 → IEEE32Exec)) :=
  fun x => (x.1, fun _ => x.2 0)

/-- Bit-level decode of `1.0` (kernel `decide`, the proven pattern). -/
lemma w0_toDyadic : IEEE32Exec.toDyadic? (IEEE32Exec.ofBits 0x3F800000)
    = some ⟨false, 8388608, -23⟩ := by decide

/-- Bit-level decode of the next float32 above `1.0`. -/
lemma w1_toDyadic : IEEE32Exec.toDyadic? (IEEE32Exec.ofBits 0x3F800001)
    = some ⟨false, 8388609, -23⟩ := by decide

/-- The two executed latents decode to distinct rationals: mantissas `8388608 ≠ 8388609` at the
common scale `2⁻²³`. Decides only the literal equality; the scale cancels symbolically. -/
lemma toRat_w_ne : toRat (w.2 0) ≠ toRat (w.2 1) := by
  have hw0 : w.2 0 = IEEE32Exec.ofBits 0x3F800000 := rfl
  have hw1 : w.2 1 = IEEE32Exec.ofBits 0x3F800001 := rfl
  rw [hw0, hw1, toRat_of_toDyadic w0_toDyadic, toRat_of_toDyadic w1_toDyadic]
  simp only [dyadicToRat, if_neg Bool.false_ne_true, one_mul]
  intro h
  have hz : ((2 : ℚ) ^ (-23 : ℤ)) ≠ 0 := zpow_ne_zero _ two_ne_zero
  have hmant : ((8388608 : ℕ) : ℚ) = ((8388609 : ℕ) : ℚ) := mul_right_cancel₀ hz h
  exact absurd hmant (by decide)

/-- **Executed: the spread guard detects the collapse.** The collapsed pair has spread `0`;
the ULP pair's spread is nonzero (distinct decoded rationals). -/
theorem witness_collapse_detected : spreadQ (collapse w) ≠ spreadQ w := by
  have hzero : spreadQ (collapse w) = 0 := by
    simp [spreadQ, collapse]
  rw [hzero]
  intro h
  exact toRat_w_ne (sub_eq_zero.mp (abs_eq_zero.mp h.symm))

/-- **The Theorem-4 executed story.** With a collapse-blind predictive branch (`repLoss ≡ 0` —
both sides' `jepaLoss` compute to `0` by `rfl`), the matched objective with the executable
spread guard is moved by the collapse: the guard removes exactly the spurious invariance the
predictive branch carries, on literal float32 bits. -/
theorem witness_executedGuard_matched_detects :
    matchedObjective (jepaFamily 2 Unit IEEE32Exec Unit)
        (fun _ : Fin 1 => spreadGuard) (fun _ => 1)
        ((fun _ _ => ()), (fun _ _ => 0)) (collapse w) [0]
      ≠ matchedObjective (jepaFamily 2 Unit IEEE32Exec Unit)
        (fun _ : Fin 1 => spreadGuard) (fun _ => 1)
        ((fun _ _ => ()), (fun _ _ => 0)) w [0] := by
  have hj1 : jepaFamily 2 Unit IEEE32Exec Unit ((fun _ _ => ()), (fun _ _ => 0))
      (collapse w) [0] = 0 := rfl
  have hj2 : jepaFamily 2 Unit IEEE32Exec Unit ((fun _ _ => ()), (fun _ _ => 0))
      w [0] = 0 := rfl
  simp only [matchedObjective, hj1, hj2, Nat.cast_zero, zero_add, Fin.sum_univ_one, one_mul]
  exact fun h => witness_collapse_detected (Rat.cast_injective h)

end WMSpec
