/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import WMSpec.ForcingTheorem
import WMSpec.FisherRaoFinite

/-!
# The bisimulation metric on the forced quotient, executable on Fisher–Rao

The metric layer over P3: the forced quotient's classes are compared by the Fisher–Rao
distance between their one-step transition laws (`bisimMetric`). Three proved bricks and one
recorded conjecture:

* **The metric exists with no new well-definedness debt**: `quotientDynamics` is already
  lifted, so `bisimMetric c c' := fisherRao (Pq c) (Pq c')` is a genuine function of classes;
  reflexivity (`bisimMetric_self`, via `BC(p,p) = 1` and `arccos 1 = 0`) and symmetry come
  from the Bhattacharyya form.

* **The pricing theorem** (`bisimMetric_prices_tests`): one-step behavioral
  distinguishability between classes — the expectation gap of ANY Boolean class test under
  their transition laws — is at most `sin(bisimMetric/2)`; and bisimilar states have
  IDENTICAL one-step test power (`bisim_zero_one_step_power`). The metric prices exactly what
  the specification says classes may differ by.

* **The data-processing inequality** (`fisherRao_mapPMF_le`): coarse-graining never inflates
  the metric — the Bhattacharyya coefficient increases under every pushforward (per-fiber
  Cauchy–Schwarz), and `arccos` is antitone. This is the finite Chentsov-monotonicity brick:
  the reason a quotient metric built from Fisher–Rao is honest, and the first proved piece of
  the forcing-the-metric story.

* **The conjecture (gated, ChallengeCrown form — recorded, NOT asserted):** (i) the
  Ferns-style discounted fixpoint — `bisimMetric` as the exact one-step layer of the unique
  fixed point `d = max(target gap, γ·W₁(d)(Pq, Pq))` (needs the finite Wasserstein layer);
  (ii) Chentsov uniqueness — any class-metric assignment natural under congruent embeddings
  and monotone under pushforward agrees with a rescaling of Fisher–Rao. Together: P3 forces
  the partition, invariance forces the metric. `world-models/URS.md` carries the gating.
-/

namespace WMSpec

open ProbabilityTheory.FintypePMF

/-! ## Fisher–Rao bricks (general finite laws) -/

section FRBricks

variable {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]

/-- The Bhattacharyya coefficient of a law with itself is `1` (the square-root embedding is
unit-norm). -/
lemma bhattacharyya_self (p : ProbabilityTheory.FintypePMF α) : bhattacharyya p p = 1 := by
  have h : ∀ a : α, Real.sqrt (p.prob a * p.prob a) = p.prob a :=
    fun a => Real.sqrt_mul_self (p.prob_nonneg a)
  rw [bhattacharyya]
  simp_rw [h]
  exact p.prob_sum_one

/-- Fisher–Rao distance of a law to itself is `0`. -/
lemma fisherRao_self (p : ProbabilityTheory.FintypePMF α) : fisherRao p p = 0 := by
  rw [fisherRao, bhattacharyya_self, Real.arccos_one, mul_zero]

/-- The Bhattacharyya coefficient is symmetric. -/
lemma bhattacharyya_comm (p q : ProbabilityTheory.FintypePMF α) :
    bhattacharyya p q = bhattacharyya q p := by
  unfold bhattacharyya
  exact Finset.sum_congr rfl fun a _ => by rw [mul_comm]

/-- Fisher–Rao distance is symmetric. -/
lemma fisherRao_comm (p q : ProbabilityTheory.FintypePMF α) :
    fisherRao p q = fisherRao q p := by
  rw [fisherRao, fisherRao, bhattacharyya_comm]

/-- **Bhattacharyya increases under pushforward** (per-fiber Cauchy–Schwarz): merging states
can only increase the overlap of the square-root embeddings. -/
theorem bhattacharyya_le_mapPMF (g : α → β) (p q : ProbabilityTheory.FintypePMF α) :
    bhattacharyya p q ≤ bhattacharyya (mapPMF g p) (mapPMF g q) := by
  rw [bhattacharyya, ← Finset.sum_fiberwise (s := Finset.univ) (g := g)
    (f := fun a => Real.sqrt (p.prob a * q.prob a))]
  refine Finset.sum_le_sum fun b _ => ?_
  -- Per fiber F: ∑_{a ∈ F} √(p a · q a) ≤ √((∑_F p) · (∑_F q)).
  set F := Finset.univ.filter (fun a => g a = b) with hF
  have hsplit : ∀ a : α, Real.sqrt (p.prob a * q.prob a)
      = Real.sqrt (p.prob a) * Real.sqrt (q.prob a) :=
    fun a => Real.sqrt_mul (p.prob_nonneg a) _
  have hnn : 0 ≤ ∑ a ∈ F, Real.sqrt (p.prob a) * Real.sqrt (q.prob a) :=
    Finset.sum_nonneg fun a _ => mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hsq : (∑ a ∈ F, Real.sqrt (p.prob a) * Real.sqrt (q.prob a)) ^ 2
      ≤ (∑ a ∈ F, p.prob a) * ∑ a ∈ F, q.prob a := by
    have hCS := Finset.sum_mul_sq_le_sq_mul_sq F
      (fun a => Real.sqrt (p.prob a)) (fun a => Real.sqrt (q.prob a))
    have hp : ∑ a ∈ F, Real.sqrt (p.prob a) ^ 2 = ∑ a ∈ F, p.prob a :=
      Finset.sum_congr rfl fun a _ => Real.sq_sqrt (p.prob_nonneg a)
    have hq : ∑ a ∈ F, Real.sqrt (q.prob a) ^ 2 = ∑ a ∈ F, q.prob a :=
      Finset.sum_congr rfl fun a _ => Real.sq_sqrt (q.prob_nonneg a)
    calc (∑ a ∈ F, Real.sqrt (p.prob a) * Real.sqrt (q.prob a)) ^ 2
        ≤ (∑ a ∈ F, Real.sqrt (p.prob a) ^ 2) * ∑ a ∈ F, Real.sqrt (q.prob a) ^ 2 := hCS
      _ = (∑ a ∈ F, p.prob a) * ∑ a ∈ F, q.prob a := by rw [hp, hq]
  have hle := Real.sqrt_le_sqrt hsq
  rw [Real.sqrt_sq hnn] at hle
  calc ∑ a ∈ F, Real.sqrt (p.prob a * q.prob a)
      = ∑ a ∈ F, Real.sqrt (p.prob a) * Real.sqrt (q.prob a) :=
        Finset.sum_congr rfl fun a _ => hsplit a
    _ ≤ Real.sqrt ((∑ a ∈ F, p.prob a) * ∑ a ∈ F, q.prob a) := hle
    _ = Real.sqrt ((mapPMF g p).prob b * (mapPMF g q).prob b) := rfl

/-- **The data-processing inequality for Fisher–Rao**: coarse-graining never increases the
distance. The finite Chentsov-monotonicity brick of the bisimMetric conjecture. -/
theorem fisherRao_mapPMF_le (g : α → β) (p q : ProbabilityTheory.FintypePMF α) :
    fisherRao (mapPMF g p) (mapPMF g q) ≤ fisherRao p q := by
  rw [fisherRao, fisherRao]
  exact mul_le_mul_of_nonneg_left
    (Real.arccos_le_arccos (bhattacharyya_le_mapPMF g p q)) (by norm_num)

end FRBricks

/-! ## The metric on the forced quotient -/

section Metric

variable {S : Type*} [Fintype S] {V : Type*}
variable (𝒯 : Set (S → V)) (P : S → ProbabilityTheory.FintypePMF S)

/-- **The bisimulation metric**: Fisher–Rao distance between the one-step transition laws of
two classes of the forced quotient. Well-definedness is inherited from `quotientDynamics` —
the metric exists BECAUSE the forcing theorem holds. -/
noncomputable def bisimMetric :
    Quotient (bisimilarity 𝒯 P) → Quotient (bisimilarity 𝒯 P) → ℝ :=
  fun c c' => fisherRao (quotientDynamics 𝒯 P c) (quotientDynamics 𝒯 P c')

/-- The metric is reflexive-zero. -/
theorem bisimMetric_self (c : Quotient (bisimilarity 𝒯 P)) :
    bisimMetric 𝒯 P c c = 0 :=
  fisherRao_self _

/-- The metric is symmetric. -/
theorem bisimMetric_comm (c c' : Quotient (bisimilarity 𝒯 P)) :
    bisimMetric 𝒯 P c c' = bisimMetric 𝒯 P c' c :=
  fisherRao_comm _ _

/-- **The pricing theorem**: the one-step behavioral distinguishability of two classes — the
expectation gap of any Boolean class test under their transition laws — is at most
`sin(bisimMetric/2)`. The metric prices exactly the differences the specification permits. -/
theorem bisimMetric_prices_tests (c c' : Quotient (bisimilarity 𝒯 P))
    (f : Quotient (bisimilarity 𝒯 P) → Bool) :
    |boolTestExpectation (quotientDynamics 𝒯 P c) f
      - boolTestExpectation (quotientDynamics 𝒯 P c') f|
      ≤ Real.sin (bisimMetric 𝒯 P c c' / 2) :=
  finite_fisherRao_risk_bound _ _ f

/-- **Bisimilar states have identical one-step test power**: the executable consequence of
the forcing theorem's quotient — no class test distinguishes the futures of bisimilar
states. -/
theorem bisim_zero_one_step_power {a b : S} (hab : bisimilarity 𝒯 P a b)
    (f : Quotient (bisimilarity 𝒯 P) → Bool) :
    boolTestExpectation (quotientDynamics 𝒯 P (Quotient.mk (bisimilarity 𝒯 P) a)) f
      = boolTestExpectation (quotientDynamics 𝒯 P (Quotient.mk (bisimilarity 𝒯 P) b)) f := by
  rw [Quotient.sound hab]

end Metric

end WMSpec
