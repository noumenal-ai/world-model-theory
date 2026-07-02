/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import ZPM.Probability.FintypePMF.TransferPrinciple
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse

/-!
# The finite Fisher–Rao risk bound

The matched-invariance draft's Theorem 5, bound to ZPM's verified finite-probability layer: for
finite laws `p, q` and any Boolean test, the expectation gap is at most `sin (d_FR(p,q) / 2)`,
where `d_FR = 2 · arccos ∑ √(p·q)` is the Fisher–Rao (spherical/Bhattacharyya) distance on the
finite simplex.

## Convention finding (recorded)

ZPM's `tvDistance` is the ℓ¹ distance `∑ |p − q|` — **twice** the standard total variation the
draft's informal proof uses. Composing the existing transfer hook `expectation_approx_of_tv`
with the Fisher–Rao bound would therefore give the constant `2 · sin(d_FR/2)`. The tight
transfer lemma `boolTest_gap_le_half_tvDistance` (the `∑ (p − q) = 0` positive-part argument)
restores the draft-exact constant. Both transfer routes coexist: the hook for its uniform
family-transfer role, the tight lemma for the sharp constant.

## Main results

* `bhattacharyya`, `fisherRao`: the coefficient `∑ √(p·q)` and the distance `2 · arccos` of it.
* `tvDistance_le_two_sin_half_fisherRao`: the geometric core —
  `∑ |p − q| ≤ 2 √(1 − BC²) = 2 sin(d_FR/2)` via Cauchy–Schwarz on `√p ∓ √q`.
* `boolTest_gap_le_half_tvDistance`: tight transfer, `gap ≤ tvDistance / 2`.
* `finite_fisherRao_risk_bound`: the draft's Theorem 5, exact constant:
  `|E_p f − E_q f| ≤ sin (fisherRao p q / 2)`.
-/

noncomputable section

namespace WMSpec

open ProbabilityTheory.FintypePMF Real Finset

variable {α : Type*} [Fintype α]

/-- **Bhattacharyya coefficient** of two finite laws: `∑ √(p·q)`, the inner product of the
square-root embeddings into the unit sphere. -/
def bhattacharyya (p q : ProbabilityTheory.FintypePMF α) : ℝ :=
  ∑ a : α, Real.sqrt (p.prob a * q.prob a)

/-- **Fisher–Rao distance** on the finite simplex: twice the spherical angle between the
square-root embeddings, `2 · arccos ∑ √(p·q)`. -/
def fisherRao (p q : ProbabilityTheory.FintypePMF α) : ℝ :=
  2 * Real.arccos (bhattacharyya p q)

/-- `sin` of half the Fisher–Rao distance is `√(1 − BC²)`. -/
lemma sin_half_fisherRao (p q : ProbabilityTheory.FintypePMF α) :
    Real.sin (fisherRao p q / 2) = Real.sqrt (1 - bhattacharyya p q ^ 2) := by
  rw [fisherRao, mul_div_cancel_left₀ _ (two_ne_zero), Real.sin_arccos]

/-- Square-root embedding lands on the unit sphere: `∑ (√(p a))² = 1`. -/
private lemma sum_sq_sqrt_prob (p : ProbabilityTheory.FintypePMF α) :
    ∑ a : α, Real.sqrt (p.prob a) ^ 2 = 1 := by
  have h : ∀ a : α, Real.sqrt (p.prob a) ^ 2 = p.prob a :=
    fun a => Real.sq_sqrt (p.prob_nonneg a)
  simp_rw [h]
  exact p.prob_sum_one

/-- The cross term of the square-root embeddings is the Bhattacharyya coefficient. -/
private lemma sum_sqrt_mul_sqrt (p q : ProbabilityTheory.FintypePMF α) :
    ∑ a : α, Real.sqrt (p.prob a) * Real.sqrt (q.prob a) = bhattacharyya p q := by
  show _ = ∑ a : α, Real.sqrt (p.prob a * q.prob a)
  exact Finset.sum_congr rfl fun a _ => (Real.sqrt_mul (p.prob_nonneg a) _).symm

/-- **The geometric core: the ℓ¹ distance is bounded by the spherical chord.**
`∑ |p − q| ≤ 2 √(1 − BC²)`, i.e. `tvDistance ≤ 2 sin(d_FR/2)`. Cauchy–Schwarz applied to
`|√p − √q|` and `√p + √q`, with the sphere identities `∑(√p ∓ √q)² = 2 ∓ 2·BC`. -/
theorem tvDistance_le_two_sin_half_fisherRao (p q : ProbabilityTheory.FintypePMF α) :
    tvDistance p q ≤ 2 * Real.sin (fisherRao p q / 2) := by
  rw [sin_half_fisherRao]
  -- Pointwise factorization |p − q| = |√p − √q| · (√p + √q).
  have hpt : ∀ a : α, |p.prob a - q.prob a|
      = |Real.sqrt (p.prob a) - Real.sqrt (q.prob a)|
        * (Real.sqrt (p.prob a) + Real.sqrt (q.prob a)) := by
    intro a
    have hu2 : Real.sqrt (p.prob a) ^ 2 = p.prob a := Real.sq_sqrt (p.prob_nonneg a)
    have hv2 : Real.sqrt (q.prob a) ^ 2 = q.prob a := Real.sq_sqrt (q.prob_nonneg a)
    have hsum : 0 ≤ Real.sqrt (p.prob a) + Real.sqrt (q.prob a) :=
      add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    have key : (Real.sqrt (p.prob a) - Real.sqrt (q.prob a))
        * (Real.sqrt (p.prob a) + Real.sqrt (q.prob a)) = p.prob a - q.prob a := by
      have expand : (Real.sqrt (p.prob a) - Real.sqrt (q.prob a))
          * (Real.sqrt (p.prob a) + Real.sqrt (q.prob a))
          = Real.sqrt (p.prob a) ^ 2 - Real.sqrt (q.prob a) ^ 2 := by ring
      rw [expand, hu2, hv2]
    calc |p.prob a - q.prob a|
        = |(Real.sqrt (p.prob a) - Real.sqrt (q.prob a))
            * (Real.sqrt (p.prob a) + Real.sqrt (q.prob a))| := by rw [key]
      _ = |Real.sqrt (p.prob a) - Real.sqrt (q.prob a)|
            * (Real.sqrt (p.prob a) + Real.sqrt (q.prob a)) := by
          rw [abs_mul, abs_of_nonneg hsum]
  -- Sphere identity, minus branch: ∑ (√p − √q)² = 2 − 2·BC.
  have hminus : ∑ a : α, (Real.sqrt (p.prob a) - Real.sqrt (q.prob a)) ^ 2
      = 2 - 2 * bhattacharyya p q := by
    have expand : ∀ a : α, (Real.sqrt (p.prob a) - Real.sqrt (q.prob a)) ^ 2
        = Real.sqrt (p.prob a) ^ 2 + Real.sqrt (q.prob a) ^ 2
          - 2 * (Real.sqrt (p.prob a) * Real.sqrt (q.prob a)) := fun a => by ring
    rw [Finset.sum_congr rfl fun a _ => expand a, Finset.sum_sub_distrib,
      Finset.sum_add_distrib, ← Finset.mul_sum, sum_sq_sqrt_prob, sum_sq_sqrt_prob,
      sum_sqrt_mul_sqrt]
    ring
  -- Sphere identity, plus branch: ∑ (√p + √q)² = 2 + 2·BC.
  have hplus : ∑ a : α, (Real.sqrt (p.prob a) + Real.sqrt (q.prob a)) ^ 2
      = 2 + 2 * bhattacharyya p q := by
    have expand : ∀ a : α, (Real.sqrt (p.prob a) + Real.sqrt (q.prob a)) ^ 2
        = Real.sqrt (p.prob a) ^ 2 + Real.sqrt (q.prob a) ^ 2
          + 2 * (Real.sqrt (p.prob a) * Real.sqrt (q.prob a)) := fun a => by ring
    rw [Finset.sum_congr rfl fun a _ => expand a, Finset.sum_add_distrib,
      Finset.sum_add_distrib, ← Finset.mul_sum, sum_sq_sqrt_prob, sum_sq_sqrt_prob,
      sum_sqrt_mul_sqrt]
    ring
  -- Cauchy–Schwarz with the sphere identities substituted.
  have hCS : (∑ a : α, |Real.sqrt (p.prob a) - Real.sqrt (q.prob a)|
        * (Real.sqrt (p.prob a) + Real.sqrt (q.prob a))) ^ 2
      ≤ (2 - 2 * bhattacharyya p q) * (2 + 2 * bhattacharyya p q) := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
      (fun a => |Real.sqrt (p.prob a) - Real.sqrt (q.prob a)|)
      (fun a => Real.sqrt (p.prob a) + Real.sqrt (q.prob a))
    have habs : ∑ a : α, |Real.sqrt (p.prob a) - Real.sqrt (q.prob a)| ^ 2
        = ∑ a : α, (Real.sqrt (p.prob a) - Real.sqrt (q.prob a)) ^ 2 := by
      simp_rw [sq_abs]
    calc (∑ a : α, |Real.sqrt (p.prob a) - Real.sqrt (q.prob a)|
          * (Real.sqrt (p.prob a) + Real.sqrt (q.prob a))) ^ 2
        ≤ (∑ a : α, |Real.sqrt (p.prob a) - Real.sqrt (q.prob a)| ^ 2)
          * ∑ a : α, (Real.sqrt (p.prob a) + Real.sqrt (q.prob a)) ^ 2 := h
      _ = (2 - 2 * bhattacharyya p q) * (2 + 2 * bhattacharyya p q) := by
          rw [habs, hminus, hplus]
  -- tv = the CS left-hand side; take square roots.
  have htv : tvDistance p q = ∑ a : α, |Real.sqrt (p.prob a) - Real.sqrt (q.prob a)|
      * (Real.sqrt (p.prob a) + Real.sqrt (q.prob a)) := by
    show ∑ a : α, |p.prob a - q.prob a| = _
    exact Finset.sum_congr rfl fun a _ => hpt a
  have hnn : 0 ≤ ∑ a : α, |Real.sqrt (p.prob a) - Real.sqrt (q.prob a)|
      * (Real.sqrt (p.prob a) + Real.sqrt (q.prob a)) :=
    Finset.sum_nonneg fun a _ => mul_nonneg (abs_nonneg _)
      (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
  have hle := Real.sqrt_le_sqrt hCS
  rw [Real.sqrt_sq hnn] at hle
  rw [htv]
  refine hle.trans (le_of_eq ?_)
  rw [show (2 - 2 * bhattacharyya p q) * (2 + 2 * bhattacharyya p q)
      = 2 ^ 2 * (1 - bhattacharyya p q ^ 2) by ring,
    Real.sqrt_mul (by positivity) _, Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 2)]

/-- **Tight transfer.** For a Boolean test the expectation gap is at most HALF the ℓ¹ distance:
`|E_p f − E_q f| ≤ tvDistance p q / 2`. Uses `∑ (p − q) = 0`: the gap and its negation are
realized on the test and its complement, so twice the gap is at most the full ℓ¹ mass. Restores
the standard-TV constant that the ℓ¹-convention transfer leaves on the table. -/
theorem boolTest_gap_le_half_tvDistance (p q : ProbabilityTheory.FintypePMF α)
    (f : α → Bool) :
    |boolTestExpectation p f - boolTestExpectation q f| ≤ tvDistance p q / 2 := by
  simp only [boolTestExpectation, trueExpectation]
  have hg01 : ∀ a : α, (0:ℝ) ≤ (if f a then (1:ℝ) else 0)
      ∧ (if f a then (1:ℝ) else 0) ≤ 1 := by
    intro a; by_cases h : f a <;> simp [h]
  have hsum0 : ∑ a : α, (p.prob a - q.prob a) = 0 := by
    rw [Finset.sum_sub_distrib, p.prob_sum_one, q.prob_sum_one, sub_self]
  have hgap : ∑ a : α, p.prob a * (if f a then (1:ℝ) else 0)
      - ∑ a : α, q.prob a * (if f a then (1:ℝ) else 0)
      = ∑ a : α, (p.prob a - q.prob a) * (if f a then (1:ℝ) else 0) := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun a _ => by ring
  -- The complementary test realizes the negated gap.
  have hcompl : ∑ a : α, (p.prob a - q.prob a) * (1 - (if f a then (1:ℝ) else 0))
      = -(∑ a : α, (p.prob a - q.prob a) * (if f a then (1:ℝ) else 0)) := by
    have hsplit : ∑ a : α, (p.prob a - q.prob a) * (1 - (if f a then (1:ℝ) else 0))
        = ∑ a : α, (p.prob a - q.prob a)
          - ∑ a : α, (p.prob a - q.prob a) * (if f a then (1:ℝ) else 0) := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun a _ => by ring
    rw [hsplit, hsum0, zero_sub]
  -- Weighted ℓ¹ bounds for a [0,1]-weight.
  have habs : ∀ h : α → ℝ, (∀ a, 0 ≤ h a ∧ h a ≤ 1) →
      |∑ a : α, (p.prob a - q.prob a) * h a|
        ≤ ∑ a : α, |p.prob a - q.prob a| * h a := by
    intro h hh
    calc |∑ a : α, (p.prob a - q.prob a) * h a|
        ≤ ∑ a : α, |(p.prob a - q.prob a) * h a| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ a : α, |p.prob a - q.prob a| * h a := by
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [abs_mul, abs_of_nonneg (hh a).1]
  have h1 := habs _ hg01
  have h2 := habs (fun a => 1 - (if f a then (1:ℝ) else 0))
    (fun a => ⟨by linarith [(hg01 a).2], by linarith [(hg01 a).1]⟩)
  rw [hcompl, abs_neg] at h2
  -- The two weighted masses add to the full ℓ¹ mass.
  have hadd : ∑ a : α, |p.prob a - q.prob a| * (if f a then (1:ℝ) else 0)
      + ∑ a : α, |p.prob a - q.prob a| * (1 - (if f a then (1:ℝ) else 0))
      = tvDistance p q := by
    rw [← Finset.sum_add_distrib]
    show _ = ∑ a : α, |p.prob a - q.prob a|
    exact Finset.sum_congr rfl fun a _ => by ring
  rw [hgap]
  linarith [h1, h2, hadd]

/-- **The finite Fisher–Rao risk bound** (the matched-invariance draft's Theorem 5, exact
constant): for finite laws and any Boolean test,

    |E_p f − E_q f| ≤ sin (d_FR(p, q) / 2).

Tight transfer (`boolTest_gap_le_half_tvDistance`) composed with the spherical-chord bound
(`tvDistance_le_two_sin_half_fisherRao`). -/
theorem finite_fisherRao_risk_bound (p q : ProbabilityTheory.FintypePMF α) (f : α → Bool) :
    |boolTestExpectation p f - boolTestExpectation q f|
      ≤ Real.sin (fisherRao p q / 2) := by
  have h1 := boolTest_gap_le_half_tvDistance p q f
  have h2 := tvDistance_le_two_sin_half_fisherRao p q
  linarith

end WMSpec
