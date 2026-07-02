/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import TLT_Proofs.NonIdentifiability.Apparatus
import TLT_Proofs.Capacity.Discretization.Float32IsDyadic
import NN.Floats.IEEEExec.RealSemantics

/-!
# Mechanized-empirical witness: no Lipschitz reading of an EXECUTED float32 encoder

The first kernel-sound empirical witness of the collapse/no-reading apparatus in which the encoder
latents are genuine `IEEE32Exec.toReal` values of concrete executed float32 bit-patterns — decoded
through TLT's exact float32→dyadic bridge (`Float32IsDyadic`) to *exact rationals* in ℝ — rather than
declared reals.

Two adjacent binary32 values supply the antecedent:
* `x₁ = ofBits 0x3F800000` (bits of `+1.0`),
* `x₂ = ofBits 0x3F800001` (next representable float above `+1.0`, i.e. `1 + 2⁻²³`).

Their executed decodes are proved kernel-soundly (bit-field extraction by `decide`, the dyadic→ℝ step
by `simp`/`norm_num`) to be exactly `1` and `8388609/8388608 = 1 + 2⁻²³`. So the empirical antecedent
`dist (E s₁) (E s₂) = 2⁻²³` is a **decidable rational fact computed from the executed float32 values**,
not an assumed constant. A target separating the samples by `δ = 1` then exceeds `L·ε = 2⁻²³` for
`L = 1`, and the impossibility corollary yields: no `1`-Lipschitz reading recovers the target from the
executed encoder. No `native_decide`, no opaque `Float`; axiom-clean.

Scope: minimal executed map (two decoded bit-patterns), and the target is a stipulated unit-gap
labelling — the empirical content is entirely encoder-side. Scaling the latents to a literal executed
attention head (`execAttnLit`) and grounding the target is the next step.
-/

open TorchLean.Floats TorchLean.Floats.IEEE754
open TLT.NonIdentifiability

noncomputable section

namespace TLT.NonIdentifiability.Executed

/-- `+1.0` as executed binary32 bits. -/
def x₁ : IEEE32Exec := IEEE32Exec.ofBits 0x3F800000
/-- The next representable binary32 above `+1.0` (i.e. `1 + 2⁻²³`). -/
def x₂ : IEEE32Exec := IEEE32Exec.ofBits 0x3F800001

theorem x₁_finite : IEEE32Exec.isFinite x₁ = true := by decide
theorem x₂_finite : IEEE32Exec.isFinite x₂ = true := by decide

theorem x₁_toDyadic : IEEE32Exec.toDyadic? x₁ =
    some { sign := false, mant := 8388608, exp := -23 } := by decide

theorem x₂_toDyadic : IEEE32Exec.toDyadic? x₂ =
    some { sign := false, mant := 8388609, exp := -23 } := by decide

/-- **Executed real value of `x₁` is exactly `1`** — decoded through the float32→dyadic→ℝ bridge;
kernel-sound (no `native_decide`, no opaque `Float`). -/
theorem x₁_toReal : IEEE32Exec.toReal x₁ = 1 := by
  rw [IEEE32Exec.toReal_eq, x₁_toDyadic]
  simp only [IEEE32Exec.dyadicToReal, TLT.Capacity.neuralBpow_binaryRadix_eq]
  norm_num

/-- **Executed real value of `x₂` is exactly `1 + 2⁻²³ = 8388609/8388608`.** -/
theorem x₂_toReal : IEEE32Exec.toReal x₂ = 8388609 / 8388608 := by
  rw [IEEE32Exec.toReal_eq, x₂_toDyadic]
  simp only [IEEE32Exec.dyadicToReal, TLT.Capacity.neuralBpow_binaryRadix_eq]
  norm_num

/-- Sample space: two samples. -/
abbrev S := Bool

/-- Encoder: latents ARE the executed float32 decodes. -/
def E : S → ℝ := fun b => if b then IEEE32Exec.toReal x₂ else IEEE32Exec.toReal x₁

/-- Target: a labelling separating the two samples by a unit gap. -/
def T : S → ℝ := fun b => if b then 1 else 0

/-- The executed latent gap is exactly `2⁻²³` — a decidable rational fact read off the executed
float32 decodes, not a declared constant. -/
theorem exec_latent_gap : dist (E false) (E true) = 1 / 8388608 := by
  simp only [E, if_true, Real.dist_eq, x₁_toReal, x₂_toReal]
  norm_num

theorem exec_close : dist (E false) (E true) ≤ (1 / 8388608 : ℝ) := by rw [exec_latent_gap]

theorem exec_sep : (1 : ℝ) ≤ |T false - T true| := by simp [T]

theorem exec_gap : ((1 : NNReal) : ℝ) * (1 / 8388608) < 1 := by norm_num

/-- **Executed mechanized-empirical witness.** No `1`-Lipschitz reading `g` recovers the target `T`
from the EXECUTED float32 encoder `E`, whose latents are the exact-rational decodes of the concrete
binary32 bit-patterns `x₁, x₂`. Every antecedent is a kernel-proven fact about the executed values. -/
theorem no_lipschitz_reading_of_executed_encoder :
    ¬ ∃ g : ℝ → ℝ, LipschitzWith 1 g ∧ ∀ s, T s = g (E s) :=
  no_lipschitz_reading_of_gap E T 1 (1 / 8388608) 1 exec_close exec_sep exec_gap

/-- The two executed latents are distinct reals (approximate, not exact, collapse) — so the
impossibility is genuinely quantitative. -/
theorem exec_latents_distinct : E false ≠ E true := by
  simp only [E, if_true, x₁_toReal, x₂_toReal]
  norm_num

end TLT.NonIdentifiability.Executed
