/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import TLT_Proofs.NonIdentifiability.Apparatus

/-!
# Readout characterization: Lipschitz readability iff metric domination

The specification half of the world-model program made exact. `Apparatus.lean` proves the
*negative* direction: an `L`-Lipschitz readout forces the target's gaps to be dominated by the
latent gaps (`approx_lipschitz_ineq`), so a gap violating the domination kills every readout
(`no_lipschitz_reading_of_gap`). This file closes the loop with the *converse construction*: if the
latent metric dominates the target's gaps, an `L`-Lipschitz readout exists. Together:

    ∃ L-Lipschitz g with T = g ∘ E   ↔   ∀ s₁ s₂, |T s₁ − T s₂| ≤ L · dist (E s₁) (E s₂).

Reading: a representation `E` supports an `L`-Lipschitz readout of a real-valued target `T`
**exactly when** its latent geometry dominates the target's modulus. The domination inequality is
therefore not merely necessary for readability — it *characterizes* it. In the world-model
specification this upgrades clause 2 (metric domination) from a necessary condition to an exact
criterion, at every readout budget `L`.

## Construction (the ⇐ direction)

Domination at zero latent distance forces `T` to identify points `E` identifies, i.e.
`Function.FactorsThrough T E` (`factorsThrough_of_dominated`). Push `T` along `E` by
`Function.extend`; the factoring makes the pushforward well defined on `Set.range E`
(`Function.FactorsThrough.extend_apply`), where domination makes it `L`-Lipschitz
(`LipschitzOnWith.of_dist_le_mul`). McShane's extension for real-valued Lipschitz maps
(`LipschitzOnWith.extend_real`) then extends it from the range to all of `Z` at the same constant.

## Main results

* `factorsThrough_of_dominated`: metric domination forces set-level factoring.
* `lipschitz_readout_iff`: the characterization.
* `no_lipschitz_readout_iff`: the boundary form — no `L`-Lipschitz readout exists **iff** some
  pair's target gap strictly exceeds `L` times its latent gap. The quantitative obstruction is
  exactly equivalent to unreadability; nothing weaker suffices.

## References

McShane, *Extension of range of functions*, Bull. AMS 40 (1934) 837–842 (the real-valued
Lipschitz extension); Whitney, Trans. AMS 36 (1934) (the companion extension theorem). The
Mathlib form is `LipschitzOnWith.extend_real`.
-/

namespace TLT.NonIdentifiability

open Set Function

/-- **Metric domination forces factoring.** If every target gap is bounded by `L` times the
latent gap, then two states with the same latent have the same target value: `T` factors through
`E` at the level of values. This is the well-definedness half of the readout construction, and the
quantitative strengthening of the master lemma's contrapositive. -/
theorem factorsThrough_of_dominated {S Z : Type*} [PseudoMetricSpace Z]
    (E : S → Z) (T : S → ℝ) (L : NNReal)
    (h : ∀ s₁ s₂, |T s₁ - T s₂| ≤ (L : ℝ) * dist (E s₁) (E s₂)) :
    Function.FactorsThrough T E := by
  intro s₁ s₂ hE
  have h0 := h s₁ s₂
  rw [hE, dist_self, mul_zero] at h0
  have habs : |T s₁ - T s₂| = 0 := le_antisymm h0 (abs_nonneg _)
  exact sub_eq_zero.mp (abs_eq_zero.mp habs)

/-- **Readout characterization (McShane iff).** A target `T : S → ℝ` admits an `L`-Lipschitz
readout from the representation `E : S → Z` **iff** the latent metric dominates the target's gaps:

    (∃ g, LipschitzWith L g ∧ ∀ s, T s = g (E s)) ↔ ∀ s₁ s₂, |T s₁ − T s₂| ≤ L · dist (E s₁) (E s₂).

Forward: `approx_lipschitz_ineq`. Converse: extend `T` along `E` (`Function.extend`, well defined
by `factorsThrough_of_dominated`), which is `L`-Lipschitz on `Set.range E` by the domination
hypothesis, then extend to all of `Z` at the same constant by McShane
(`LipschitzOnWith.extend_real`). -/
theorem lipschitz_readout_iff {S Z : Type*} [PseudoMetricSpace Z]
    (E : S → Z) (T : S → ℝ) (L : NNReal) :
    (∃ g : Z → ℝ, LipschitzWith L g ∧ ∀ s, T s = g (E s)) ↔
    (∀ s₁ s₂, |T s₁ - T s₂| ≤ (L : ℝ) * dist (E s₁) (E s₂)) := by
  constructor
  · rintro ⟨g, hg, hfac⟩ s₁ s₂
    exact approx_lipschitz_ineq E T L g hg hfac s₁ s₂
  · intro h
    -- Push `T` along `E`; off the range the default value is irrelevant.
    set g₀ : Z → ℝ := Function.extend E T (fun _ => 0) with hg₀
    have hFT : Function.FactorsThrough T E := factorsThrough_of_dominated E T L h
    have hagree : ∀ s, g₀ (E s) = T s := fun s => hFT.extend_apply (fun _ => 0) s
    -- Domination makes the pushforward `L`-Lipschitz on the range.
    have hlip : LipschitzOnWith L g₀ (Set.range E) := by
      apply LipschitzOnWith.of_dist_le_mul
      rintro z₁ ⟨s₁, rfl⟩ z₂ ⟨s₂, rfl⟩
      rw [hagree s₁, hagree s₂, Real.dist_eq]
      exact h s₁ s₂
    -- McShane: extend from the range to all of `Z` at the same constant.
    obtain ⟨g, hg, hEq⟩ := hlip.extend_real
    refine ⟨g, hg, fun s => ?_⟩
    rw [← hEq (Set.mem_range_self s), hagree s]

/-- **Boundary form of the characterization.** No `L`-Lipschitz readout of `T` from `E` exists
**iff** some pair's target gap strictly exceeds `L` times its latent gap. The quantitative
obstruction of `no_lipschitz_reading_of_gap` is thereby exactly equivalent to unreadability: a
single dominating-gap witness is both sufficient and necessary to rule out every readout at
budget `L`. -/
theorem no_lipschitz_readout_iff {S Z : Type*} [PseudoMetricSpace Z]
    (E : S → Z) (T : S → ℝ) (L : NNReal) :
    (¬ ∃ g : Z → ℝ, LipschitzWith L g ∧ ∀ s, T s = g (E s)) ↔
    (∃ s₁ s₂, (L : ℝ) * dist (E s₁) (E s₂) < |T s₁ - T s₂|) := by
  constructor
  · intro hno
    by_contra hcon
    push Not at hcon
    exact hno ((lipschitz_readout_iff E T L).mpr hcon)
  · rintro ⟨s₁, s₂, hgap⟩ ⟨g, hg, hfac⟩
    exact absurd (approx_lipschitz_ineq E T L g hg hfac s₁ s₂) (not_le.mpr hgap)

end TLT.NonIdentifiability
