/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
-- Narrow import (not full `Mathlib`): the apparatus needs only Lipschitz/metric/ℝ/NNReal, and
-- pulling `Mathlib.Order.Concept` (via full Mathlib) clashes with `FLT_Proofs.Basic.Concept` in the
-- unified design-lab closure that `ExecutedWitness` reaches through `Float32IsDyadic`.
import Mathlib.Topology.MetricSpace.Lipschitz

/-!
# Non-identifiability apparatus: collapse ⇒ no reading

The reusable core behind the representation-boundary theorems. If a representation map
`E : S → Z` **collapses** a pair that a target functional separates, then the target does not
factor through `E` — hence no probe, planner, success verdict, or predictor built on `E` can
recover it. Two forms:

* **Exact** (`not_factorThrough_of_collapse`): `E s₁ = E s₂` with `T s₁ ≠ T s₂` ⇒ no `g` with
  `T = g ∘ E`. Codomain-generic, no structure on `Z` or `W`.
* **Quantitative** (`approx_lipschitz`, `no_lipschitz_reading_of_gap`): for a real target on a
  pseudometric latent space, an `L`-Lipschitz reading of an `ε`-approximately-collapsing encoder
  cannot open a target gap wider than `L·ε`. This is the form that binds *real* (approximately
  collapsing) executed encoders, whose latents are close but not exactly equal.
-/

noncomputable section

namespace TLT.NonIdentifiability

/-- **Master lemma (exact collapse).** If `E` collapses `s₁, s₂` (`E s₁ = E s₂`) while `T`
separates them (`T s₁ ≠ T s₂`), then `T` does not factor through `E`. No structure on `Z` or `W`. -/
theorem not_factorThrough_of_collapse {S Z W : Type*} (E : S → Z) (T : S → W)
    {s₁ s₂ : S} (hcollapse : E s₁ = E s₂) (hsep : T s₁ ≠ T s₂) :
    ¬ ∃ g : Z → W, ∀ s, T s = g (E s) := by
  rintro ⟨g, hg⟩
  exact hsep (by rw [hg s₁, hg s₂, hcollapse])

/-- Real-valued specialization (`W := ℝ`). -/
theorem not_factorThrough_of_collapse_real {S Z : Type*} (E : S → Z) (T : S → ℝ)
    {s₁ s₂ : S} (hcollapse : E s₁ = E s₂) (hsep : T s₁ ≠ T s₂) :
    ¬ ∃ g : Z → ℝ, ∀ s, T s = g (E s) :=
  not_factorThrough_of_collapse E T hcollapse hsep

/-- Boolean-verdict specialization (`W := Bool`) — the success-criterion form. -/
theorem not_factorThrough_of_collapse_bool {S Z : Type*} (E : S → Z) (T : S → Bool)
    {s₁ s₂ : S} (hcollapse : E s₁ = E s₂) (hsep : T s₁ ≠ T s₂) :
    ¬ ∃ g : Z → Bool, ∀ s, T s = g (E s) :=
  not_factorThrough_of_collapse E T hcollapse hsep

/-- **Sharp inequality.** For any `L`-Lipschitz reading `g` realizing `T = g ∘ E`, the target gap
is controlled by the latent gap: `|T s₁ − T s₂| ≤ L · dist (E s₁) (E s₂)`. -/
theorem approx_lipschitz_ineq {S Z : Type*} [PseudoMetricSpace Z]
    (E : S → Z) (T : S → ℝ) (L : NNReal) (g : Z → ℝ)
    (hg : LipschitzWith L g) (hfac : ∀ s, T s = g (E s)) (s₁ s₂ : S) :
    |T s₁ - T s₂| ≤ (L : ℝ) * dist (E s₁) (E s₂) := by
  have h := hg.dist_le_mul (E s₁) (E s₂)
  rwa [← hfac s₁, ← hfac s₂, Real.dist_eq] at h

/-- **Quantitative obstruction.** `ε`-close latents and a `δ`-separated target force `δ ≤ L·ε`
for any `L`-Lipschitz reading. -/
theorem approx_lipschitz {S Z : Type*} [PseudoMetricSpace Z]
    (E : S → Z) (T : S → ℝ) (L : NNReal) (ε δ : ℝ) {s₁ s₂ : S}
    (hclose : dist (E s₁) (E s₂) ≤ ε) (hsep : δ ≤ |T s₁ - T s₂|)
    (g : Z → ℝ) (hg : LipschitzWith L g) (hfac : ∀ s, T s = g (E s)) :
    δ ≤ (L : ℝ) * ε := by
  have h1 : |T s₁ - T s₂| ≤ (L : ℝ) * dist (E s₁) (E s₂) :=
    approx_lipschitz_ineq E T L g hg hfac s₁ s₂
  have h2 : (L : ℝ) * dist (E s₁) (E s₂) ≤ (L : ℝ) * ε :=
    mul_le_mul_of_nonneg_left hclose (L.coe_nonneg)
  linarith

/-- **Impossibility corollary.** If the target gap strictly exceeds `L·ε` while latents are
`ε`-close, no `L`-Lipschitz reading realizes the target. -/
theorem no_lipschitz_reading_of_gap {S Z : Type*} [PseudoMetricSpace Z]
    (E : S → Z) (T : S → ℝ) (L : NNReal) (ε δ : ℝ) {s₁ s₂ : S}
    (hclose : dist (E s₁) (E s₂) ≤ ε) (hsep : δ ≤ |T s₁ - T s₂|)
    (hgap : (L : ℝ) * ε < δ) :
    ¬ ∃ g : Z → ℝ, LipschitzWith L g ∧ ∀ s, T s = g (E s) := by
  rintro ⟨g, hg, hfac⟩
  have : δ ≤ (L : ℝ) * ε := approx_lipschitz E T L ε δ hclose hsep g hg hfac
  linarith

end TLT.NonIdentifiability
