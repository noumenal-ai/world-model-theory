/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import WMSpec.GuardFamilies
import ZPM.Probability.FintypePMF.TransferPrinciple

/-!
# Mixed guard families, the exchange constant, and the closing of the remaining edges

The one-shot closure of the program's remaining task set, built from the front-loaded model
(see `world-models/URS.md`, genius-simulation tick):

* **The pushforward layer** (`mapPMF`, `boolTestExpectation_mapPMF`) and **zero-power theorem**
  (`blind_tests_zero_power`): a loss-invariant transformation `b ∈ G_L` makes every loss-built
  Boolean test read the SAME expectation on the shifted law `b#P` — even when the shift is
  real (`tvDistance (b#P) P > 0`). With `finite_fisherRao_risk_bound` this brackets the power
  spectrum: general tests are Fisher–Rao-bounded, blind tests are zero-bounded. The draft's
  Theorem 1 conjunction, exact.

* **The mixed objective and the exchange constant** (`mixed_guard_exchange`): data guards and
  law guards under the joint action `(g, h)` separate from the predictive branch via the nil
  mask, but between the two guard FAMILIES exactly a one-dimensional cancellation channel
  survives: invariance forces the data-deviation sum to a constant `c` and the law-deviation
  sum to `−c`. Monotone deviations on both families collapse `c = 0` and full separation
  follows (`mixed_separation_of_monotone`, `mixed_invariance_characterization`).

* **The pushforward-coupled instance** (`mixedPushforward_invariance_characterization`):
  the law slot at `FintypePMF Xd` moved by `mapPMF g` — the same transformation acting on data
  and, by pushforward, on the represented law: the formal home of "guards computed on the
  representation distribution".

* **The MMD reference guard** (`mmdGuard_characterized`): distribution-matching to a reference
  law as a characterized guard (provenance guard), unconditional given a characteristic kernel.

* **The executed n-point witness** (`witness_tensorVar_detects`): the 3-point Tensor
  `[1.0, 1.0+ulp, 1.0]` — using only the two proven bit decodes — has nonvanishing variance
  guard, while the collapsed tensor's guard vanishes (`varQ_const`); symbolic ℚ arithmetic on
  the decoded values, no new `decide` obligations.

* **The lattice form** (`invarianceMonoid_eq_iInf`): `G_L = ⨅ m, G_L(m)` as submonoids.
-/

namespace WMSpec

open ProbabilityTheory.FintypePMF TorchLean.Floats TorchLean.Floats.IEEE754

/-! ## The pushforward layer on the finite probability substrate -/

section Pushforward

variable {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]

/-- **Pushforward of a finite law** along `g`: the mass of `b` is the mass of its fiber. -/
def mapPMF (g : α → β) (p : ProbabilityTheory.FintypePMF α) :
    ProbabilityTheory.FintypePMF β where
  prob := fun b => ∑ a ∈ Finset.univ.filter (fun a => g a = b), p.prob a
  prob_nonneg := fun _ => Finset.sum_nonneg fun a _ => p.prob_nonneg a
  prob_sum_one := by
    rw [Finset.sum_fiberwise]
    exact p.prob_sum_one

/-- **Change of variables** for Boolean tests under the pushforward. -/
theorem boolTestExpectation_mapPMF (g : α → β) (p : ProbabilityTheory.FintypePMF α)
    (f : β → Bool) :
    boolTestExpectation (mapPMF g p) f = boolTestExpectation p (fun a => f (g a)) := by
  simp only [boolTestExpectation, trueExpectation, mapPMF]
  rw [← Finset.sum_fiberwise (s := Finset.univ) (g := g)
    (f := fun a => p.prob a * (if f (g a) then (1:ℝ) else 0))]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun a ha => ?_
  rw [(Finset.mem_filter.mp ha).2]

/-- **Blind tests have zero power** (draft Theorem 1, exact form). If `b` is an objective
invariance, every Boolean test built from a loss observable reads the SAME expectation on the
shifted law `b#P` as on `P` — even when the shift is real. Together with
`finite_fisherRao_risk_bound`: general tests are Fisher–Rao-bounded; loss-blind tests are
zero-bounded. -/
theorem blind_tests_zero_power {Θ M V : Type*} [DecidableEq α]
    {L : Θ → α → M → V} {b : α → α} (hb : ObjectiveInvariant L b)
    (r : V → Bool) (θ : Θ) (m : M) (p : ProbabilityTheory.FintypePMF α) :
    boolTestExpectation (mapPMF b p) (fun a => r (L θ a m))
      = boolTestExpectation p (fun a => r (L θ a m)) := by
  rw [boolTestExpectation_mapPMF]
  congr 1
  funext a
  rw [hb θ a m]

end Pushforward

/-! ## The mixed objective and the exchange constant -/

section Mixed

variable {Θ Xd Yl : Type*} {ι : Type*} {k r : ℕ}

/-- **The mixed objective**: predictive branch on data, one guard family reading data, one
reading laws (or any second space). The joint action moves both slots together. -/
def mixedObjective (Lpred : Θ → Xd → List ι → ℕ)
    (Gd : Fin k → Xd → ℝ) (Gl : Fin r → Yl → ℝ)
    (lam : Fin k → ℝ) (mu : Fin r → ℝ) : Θ → (Xd × Yl) → List ι → ℝ :=
  fun θ xy m => (Lpred θ xy.1 m : ℝ)
    + (∑ j : Fin k, lam j * Gd j xy.1) + (∑ i : Fin r, mu i * Gl i xy.2)

/-- The joint action on the two slots. -/
def jointAction (g : Xd → Xd) (h : Yl → Yl) : Xd × Yl → Xd × Yl :=
  fun xy => (g xy.1, h xy.2)

variable {Lpred : Θ → Xd → List ι → ℕ} {Gd : Fin k → Xd → ℝ} {Gl : Fin r → Yl → ℝ}
  {lam : Fin k → ℝ} {mu : Fin r → ℝ} {g : Xd → Xd} {h : Yl → Yl}

/-- **The exchange constant** (the one-dimensional inter-family channel). For a mask-additive
predictive branch, joint invariance of the mixed objective forces the data-guard deviation sum
to a CONSTANT `c` (independent of the data point) and the law-guard deviation sum to `−c`:
the only cancellation the two families can exchange is a uniform constant. -/
theorem mixed_guard_exchange [Nonempty Yl]
    (hadd : ∀ θ x I₁ I₂, Lpred θ x (I₁ ++ I₂) = Lpred θ x I₁ + Lpred θ x I₂)
    (hinv : ObjectiveInvariant (mixedObjective Lpred Gd Gl lam mu) (jointAction g h))
    (θ₀ : Θ) (x₀ : Xd) :
    ∃ c : ℝ,
      (∀ x, ∑ j : Fin k, lam j * (Gd j (g x) - Gd j x) = c) ∧
      (∀ y, ∑ i : Fin r, mu i * (Gl i (h y) - Gl i y) = -c) := by
  have hz : ∀ y, Lpred θ₀ y [] = 0 := by
    intro y
    have hy := hadd θ₀ y [] []
    simp only [List.nil_append] at hy
    omega
  -- The nil-mask identity: Sd(g x) + Sl(h y) = Sd(x) + Sl(y) for all x, y.
  have key : ∀ x y,
      (∑ j : Fin k, lam j * Gd j (g x)) + (∑ i : Fin r, mu i * Gl i (h y))
      = (∑ j : Fin k, lam j * Gd j x) + (∑ i : Fin r, mu i * Gl i y) := by
    intro x y
    have h0 : (Lpred θ₀ (g x) [] : ℝ)
        + (∑ j : Fin k, lam j * Gd j (g x)) + (∑ i : Fin r, mu i * Gl i (h y))
        = (Lpred θ₀ x [] : ℝ)
        + (∑ j : Fin k, lam j * Gd j x) + (∑ i : Fin r, mu i * Gl i y) :=
      hinv θ₀ (x, y) []
    rw [hz (g x), hz x] at h0
    simp only [Nat.cast_zero, zero_add] at h0
    exact h0
  obtain ⟨y₀⟩ := ‹Nonempty Yl›
  refine ⟨∑ j : Fin k, lam j * (Gd j (g x₀) - Gd j x₀), fun x => ?_, fun y => ?_⟩
  · -- data side: compare the nil identities at (x, y₀) and (x₀, y₀).
    have h1 := key x y₀
    have h2 := key x₀ y₀
    have hexp : ∀ x', ∑ j : Fin k, lam j * (Gd j (g x') - Gd j x')
        = (∑ j : Fin k, lam j * Gd j (g x')) - ∑ j : Fin k, lam j * Gd j x' := by
      intro x'
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [hexp, hexp]
    linarith
  · -- law side: the nil identity at (x₀, y).
    have h1 := key x₀ y
    have hexp : ∑ i : Fin r, mu i * (Gl i (h y) - Gl i y)
        = (∑ i : Fin r, mu i * Gl i (h y)) - ∑ i : Fin r, mu i * Gl i y := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    have hexp' : ∑ j : Fin k, lam j * (Gd j (g x₀) - Gd j x₀)
        = (∑ j : Fin k, lam j * Gd j (g x₀)) - ∑ j : Fin k, lam j * Gd j x₀ := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [hexp, hexp']
    linarith

/-- **Monotone deviations on both families collapse the exchange constant**: `c ≥ 0` from the
data side, `−c ≥ 0` from the law side, so `c = 0` and each family's deviation sum vanishes;
positive weights then force every guard invariant, in both families. -/
theorem mixed_separation_of_monotone [Nonempty Yl]
    (hadd : ∀ θ x I₁ I₂, Lpred θ x (I₁ ++ I₂) = Lpred θ x I₁ + Lpred θ x I₂)
    (hlam : ∀ j, 0 < lam j) (hmu : ∀ i, 0 < mu i)
    (hmond : ∀ j x, Gd j x ≤ Gd j (g x)) (hmonl : ∀ i y, Gl i y ≤ Gl i (h y))
    (hinv : ObjectiveInvariant (mixedObjective Lpred Gd Gl lam mu) (jointAction g h))
    (θ₀ : Θ) (x₀ : Xd) :
    (∀ j x, Gd j (g x) = Gd j x) ∧ (∀ i y, Gl i (h y) = Gl i y) := by
  obtain ⟨c, hcd, hcl⟩ := mixed_guard_exchange hadd hinv θ₀ x₀
  obtain ⟨y₀⟩ := ‹Nonempty Yl›
  have hc0 : 0 ≤ c := by
    have := hcd x₀
    have hterm : ∀ j ∈ Finset.univ, (0:ℝ) ≤ lam j * (Gd j (g x₀) - Gd j x₀) :=
      fun j _ => mul_nonneg (hlam j).le (sub_nonneg.mpr (hmond j x₀))
    have := Finset.sum_nonneg hterm
    linarith [hcd x₀]
  have hc0' : c ≤ 0 := by
    have hterm : ∀ i ∈ Finset.univ, (0:ℝ) ≤ mu i * (Gl i (h y₀) - Gl i y₀) :=
      fun i _ => mul_nonneg (hmu i).le (sub_nonneg.mpr (hmonl i y₀))
    have := Finset.sum_nonneg hterm
    linarith [hcl y₀]
  have hc : c = 0 := le_antisymm hc0' hc0
  constructor
  · intro j x
    have hzero := hcd x
    rw [hc] at hzero
    have hterm : ∀ j' ∈ Finset.univ, (0:ℝ) ≤ lam j' * (Gd j' (g x) - Gd j' x) :=
      fun j' _ => mul_nonneg (hlam j').le (sub_nonneg.mpr (hmond j' x))
    have heach := (Finset.sum_eq_zero_iff_of_nonneg hterm).mp hzero j (Finset.mem_univ j)
    rcases mul_eq_zero.mp heach with hl | hd
    · exact absurd hl (hlam j).ne'
    · exact sub_eq_zero.mp hd
  · intro i y
    have hzero := hcl y
    rw [hc, neg_zero] at hzero
    have hterm : ∀ i' ∈ Finset.univ, (0:ℝ) ≤ mu i' * (Gl i' (h y) - Gl i' y) :=
      fun i' _ => mul_nonneg (hmu i').le (sub_nonneg.mpr (hmonl i' y))
    have heach := (Finset.sum_eq_zero_iff_of_nonneg hterm).mp hzero i (Finset.mem_univ i)
    rcases mul_eq_zero.mp heach with hl | hd
    · exact absurd hl (hmu i).ne'
    · exact sub_eq_zero.mp hd

/-- **The mixed characterization** (Theorem 4, two families, hypotheses in minimal locations):
under mask-additivity, positive weights, and monotone deviations on both families, joint
invariance of the mixed objective is EXACTLY componentwise invariance of the predictive
branch and of every guard in both families. -/
theorem mixed_invariance_characterization [Nonempty Yl]
    (hadd : ∀ θ x I₁ I₂, Lpred θ x (I₁ ++ I₂) = Lpred θ x I₁ + Lpred θ x I₂)
    (hlam : ∀ j, 0 < lam j) (hmu : ∀ i, 0 < mu i)
    (hmond : ∀ j x, Gd j x ≤ Gd j (g x)) (hmonl : ∀ i y, Gl i y ≤ Gl i (h y))
    (θ₀ : Θ) (x₀ : Xd) :
    ObjectiveInvariant (mixedObjective Lpred Gd Gl lam mu) (jointAction g h) ↔
    (ObjectiveInvariant Lpred g ∧ (∀ j x, Gd j (g x) = Gd j x)
      ∧ (∀ i y, Gl i (h y) = Gl i y)) := by
  constructor
  · intro hinv
    obtain ⟨hGd, hGl⟩ := mixed_separation_of_monotone hadd hlam hmu hmond hmonl hinv θ₀ x₀
    refine ⟨?_, hGd, hGl⟩
    intro θ x m
    obtain ⟨y₀⟩ := ‹Nonempty Yl›
    have h0 := hinv θ (x, y₀) m
    simp only [mixedObjective, jointAction] at h0
    have hd : ∑ j : Fin k, lam j * Gd j (g x) = ∑ j : Fin k, lam j * Gd j x :=
      Finset.sum_congr rfl fun j _ => by rw [hGd j x]
    have hl : ∑ i : Fin r, mu i * Gl i (h y₀) = ∑ i : Fin r, mu i * Gl i y₀ :=
      Finset.sum_congr rfl fun i _ => by rw [hGl i y₀]
    rw [hd, hl] at h0
    have hcast : (Lpred θ (g x) m : ℝ) = (Lpred θ x m : ℝ) := by linarith
    exact_mod_cast hcast
  · rintro ⟨hpred, hGd, hGl⟩ θ xy m
    simp only [mixedObjective, jointAction, hpred θ xy.1 m]
    congr 1
    · congr 1
      exact Finset.sum_congr rfl fun j _ => by rw [hGd j xy.1]
    · exact Finset.sum_congr rfl fun i _ => by rw [hGl i xy.2]

end Mixed

/-! ## The pushforward-coupled instance: the same `g` on data and on the represented law -/

/-- **The mixed characterization along the representation's pushforward**: the law slot is the
finite law space over the data, moved by `mapPMF g` — guards computed on the representation
distribution, formally. Direct instance of `mixed_invariance_characterization` at
`Yl := FintypePMF Xd`, `h := mapPMF g`. -/
theorem mixedPushforward_invariance_characterization
    {Θ Xd : Type*} {ι : Type*} {k r : ℕ} [Fintype Xd] [DecidableEq Xd] [Nonempty Xd]
    {Lpred : Θ → Xd → List ι → ℕ} {Gd : Fin k → Xd → ℝ}
    {Gl : Fin r → ProbabilityTheory.FintypePMF Xd → ℝ}
    {lam : Fin k → ℝ} {mu : Fin r → ℝ} {g : Xd → Xd}
    (hadd : ∀ θ x I₁ I₂, Lpred θ x (I₁ ++ I₂) = Lpred θ x I₁ + Lpred θ x I₂)
    (hlam : ∀ j, 0 < lam j) (hmu : ∀ i, 0 < mu i)
    (hmond : ∀ j x, Gd j x ≤ Gd j (g x))
    (hmonl : ∀ i P, Gl i P ≤ Gl i (mapPMF g P))
    (θ₀ : Θ) (x₀ : Xd) :
    ObjectiveInvariant (mixedObjective Lpred Gd Gl lam mu) (jointAction g (mapPMF g)) ↔
    (ObjectiveInvariant Lpred g ∧ (∀ j x, Gd j (g x) = Gd j x)
      ∧ (∀ i P, Gl i (mapPMF g P) = Gl i P)) := by
  haveI : Nonempty (ProbabilityTheory.FintypePMF Xd) :=
    ⟨{ prob := fun a => if a = x₀ then 1 else 0
       prob_nonneg := fun a => by by_cases h : a = x₀ <;> simp [h]
       prob_sum_one := by rw [Finset.sum_ite_eq' Finset.univ x₀ (fun _ => (1:ℝ))]; simp }⟩
  exact mixed_invariance_characterization hadd hlam hmu hmond hmonl θ₀ x₀

/-! ## The MMD reference guard (provenance guard) -/

section MMDGuard

set_option linter.unusedSectionVars false

open MeasureTheory RKHS

variable {Xt : Type*} [TopologicalSpace Xt] [MeasurableSpace Xt] [OpensMeasurableSpace Xt]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable [SecondCountableTopology H]
variable [RKHS ℝ H Xt ℝ]
variable [BoundedKernel H (X := Xt)]

/-- **The MMD reference guard is a characterized guard**: its value at a law `P` is the squared
MMD to the reference `Q₀`, and it names exactly the distribution-matching property `P = Q₀`
(provenance/source-matching), unconditionally given a characteristic kernel. The uniform
`CharacterizedGuard.transport` applies. -/
noncomputable def mmdGuard_characterized (hchar : IsCharacteristic (H := H) (X := Xt))
    (Q₀ : Measure Xt) : CharacterizedGuard (Measure Xt) where
  val := fun P => mmdSq (H := H) P Q₀
  Pr := fun P => P = Q₀
  zero_iff := fun P => mmdSq_zero_iff hchar P Q₀

end MMDGuard

/-! ## The executed n-point Tensor witness (no new decodes) -/

section TensorWitness

open Spec

/-- Scaled variance of a constant family vanishes: the collapse side of the n-point witness,
in general. -/
lemma varQ_const {n : ℕ} (c : ℚ) : varQ (fun _ : Fin n => c) = 0 := by
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring_nf

/-- The 3-point literal tensor `[1.0, 1.0 + ulp, 1.0]` — built from the two PROVEN bit
decodes only. -/
def t3 : Tensor IEEE32Exec (.dim 3 .scalar) :=
  .dim (fun i => .scalar (if i = 1 then IEEE32Exec.ofBits 0x3F800001
    else IEEE32Exec.ofBits 0x3F800000))

/-- The collapsed 3-point tensor: every entry the first. -/
def t3collapsed : Tensor IEEE32Exec (.dim 3 .scalar) :=
  .dim (fun _ => .scalar (IEEE32Exec.ofBits 0x3F800000))

/-- **Executed n-point witness**: the variance guard vanishes on the collapsed tensor and is
nonzero on the literal `[1.0, 1.0+ulp, 1.0]` — detected through the ℚ-read decoded values
(`3·1 ≠ 3 + 2⁻²³`), with no new `decide` obligations. -/
theorem witness_tensorVar_detects :
    tensorVarGuard t3collapsed = 0 ∧ tensorVarGuard t3 ≠ 0 := by
  constructor
  · rw [tensorVarGuard]
    rw [show (fun i => toRat (t3collapsed.vecGet i))
        = fun _ : Fin 3 => toRat (IEEE32Exec.ofBits 0x3F800000) from rfl]
    rw [varQ_const]
    norm_num
  · rw [tensorVarGuard]
    intro hcast
    have hq : varQ (fun i : Fin 3 => toRat (t3.vecGet i)) = 0 := by
      exact_mod_cast hcast
    have hall := (varQ_eq_zero_iff _).mp hq 0
    have h0 : toRat (t3.vecGet 0) = 1 := by
      rw [show t3.vecGet 0 = IEEE32Exec.ofBits 0x3F800000 from rfl, toRat_ofBits_one]
    have hsum : ∑ j : Fin 3, toRat (t3.vecGet j) = 3 + (2:ℚ) ^ (-23 : ℤ) := by
      rw [Fin.sum_univ_three,
        show t3.vecGet 0 = IEEE32Exec.ofBits 0x3F800000 from rfl,
        show t3.vecGet 1 = IEEE32Exec.ofBits 0x3F800001 from rfl,
        show t3.vecGet 2 = IEEE32Exec.ofBits 0x3F800000 from rfl,
        toRat_ofBits_one, toRat_ofBits_ulp]
      ring
    rw [h0, hsum] at hall
    norm_num at hall

end TensorWitness

/-! ## The lattice form of the mask intersection -/

/-- **`G_L = ⨅ₘ G_L(m)`, as submonoids**: the global invariance monoid is the infimum of the
mask-indexed family — the mask lattice's shadow on the invariance side, in the order-theoretic
form the forcing theorem (P3) will consume. -/
theorem invarianceMonoid_eq_iInf {Θ X M V : Type*} (L : Θ → X → M → V) :
    invarianceMonoid L = ⨅ m : M, invarianceMonoidAt L m := by
  ext g
  simp only [Submonoid.mem_iInf]
  exact objectiveInvariant_iff_forall_at L g

end WMSpec
