/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import WMSpec.ExecutableGuard
import NN.Spec.Core.Tensor.Core
import ZPM.Analysis.InnerProductSpace.HSIC.ZeroIff
import ZPM.InformationTheory.MutualInformation.ZeroIffProduct

/-!
# Guard families: characterized guards, executable and analytic

The compound closure of the three guard plan-edges. The unifying object surfaced by their
joint seam: a **characterized guard** is a (value, property, zero-iff) triple — the guard's
value vanishes exactly where the property it names holds. The transport theorem is uniform:
value-invariance under `g` transports the named property along `g`. The two families then
differ only in their witness tier:

* **Executable guards** (data-level, ℚ-cored): the n-point scaled-variance guard `varQ` (no
  division — `∑ (n·vᵢ − Σv)²`, same zero locus as variance) with its own zero-iff
  (`varQ_eq_zero_iff`), Tensor-typed via the literal `Tensor.vecGet`, plus the ℚ-read executed
  values of the witness layer (`toReal_ofBits_one`, `toReal_ofBits_ulp`, `executed_gap_eq`) —
  the `norm_num`→`decide` retrofit of the executed-witness pattern.
* **Analytic guards** (measure-level, ℝ-native): HSIC and MMD are characterized guards
  unconditionally given a characteristic kernel (`hsicGuard_transport`); mutual information is
  characterized only under per-point side conditions (`miGuard_transport` carries absolute
  continuity and finite KL at BOTH points) — a scope finding: the MI guard "enforces the
  symmetry it names" only along transformations preserving those conditions.

Domain finding (recorded): executable guards read DATA (`Unit × (Fin n → IEEE32Exec)`,
`Tensor`), analytic guards read LAWS (`Measure (α × β)`). A matched objective mixing them
lives at two `X`'s connected by the representation's pushforward; the mixed-family composite
is the named next obligation, not silently identified.
-/

namespace WMSpec

open TorchLean.Floats TorchLean.Floats.IEEE754

/-! ## The characterized guard and the uniform transport theorem -/

/-- **A characterized guard**: a guard value together with the property its zero locus names.
Every guard in the matched-objective story — executable or analytic — is one of these. -/
structure CharacterizedGuard (X' : Type*) where
  /-- The guard value. -/
  val : X' → ℝ
  /-- The property the guard names. -/
  Pr : X' → Prop
  /-- The characterization: the guard vanishes exactly where the property holds. -/
  zero_iff : ∀ x, val x = 0 ↔ Pr x

/-- **Uniform transport**: if a transformation preserves a characterized guard's values, it
transports the named property both ways. "The guard enforces the symmetry it names," as one
theorem for every guard family. -/
theorem CharacterizedGuard.transport {X' : Type*} (Gc : CharacterizedGuard X')
    {g : X' → X'} (hinv : ∀ x, Gc.val (g x) = Gc.val x) (x : X') :
    Gc.Pr (g x) ↔ Gc.Pr x := by
  rw [← Gc.zero_iff, ← Gc.zero_iff, hinv]

/-! ## Executable family: the n-point scaled-variance guard -/

/-- **Scaled variance on ℚ** (division-free): `∑ i, (n·vᵢ − Σⱼvⱼ)²`. Same zero locus as the
variance; exactly computable. The n-point generalization of `spreadQ`. -/
def varQ {n : ℕ} (v : Fin n → ℚ) : ℚ :=
  ∑ i : Fin n, ((n : ℚ) * v i - ∑ j : Fin n, v j) ^ 2

/-- The scaled-variance zero-iff: the guard vanishes exactly when every point sits at the
scaled mean — the anti-collapse property, characterized. -/
theorem varQ_eq_zero_iff {n : ℕ} (v : Fin n → ℚ) :
    varQ v = 0 ↔ ∀ i, (n : ℚ) * v i = ∑ j : Fin n, v j := by
  constructor
  · intro h i
    have hnonneg : ∀ j ∈ Finset.univ, (0:ℚ) ≤ ((n : ℚ) * v j - ∑ k : Fin n, v k) ^ 2 :=
      fun j _ => sq_nonneg _
    have heach := (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp h i (Finset.mem_univ i)
    have hzero := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp heach
    exact sub_eq_zero.mp hzero
  · intro h
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [sub_eq_zero.mpr (h i)]
    exact zero_pow (by norm_num)

open Spec in
/-- **The Tensor-typed executable guard**: scaled variance of a literal TorchLean vector's
executed values, through the ℚ-reading. ℝ-typed interface, computable core. -/
def tensorVarGuard {n : ℕ} : Tensor IEEE32Exec (.dim n .scalar) → ℝ :=
  fun t => ((varQ (fun i => toRat (t.vecGet i)) : ℚ) : ℝ)

open Spec in
/-- The Tensor variance guard is a characterized guard: it names exactly the anti-collapse
property of the executed values. -/
def tensorVarCharacterized (n : ℕ) :
    CharacterizedGuard (Tensor IEEE32Exec (.dim n .scalar)) where
  val := tensorVarGuard
  Pr := fun t => ∀ i, (n : ℚ) * toRat (t.vecGet i) = ∑ j : Fin n, toRat (t.vecGet j)
  zero_iff := fun t => by
    rw [tensorVarGuard, show ((0:ℝ) = ((0:ℚ):ℝ)) by norm_num]
    exact ⟨fun h => (varQ_eq_zero_iff _).mp (Rat.cast_injective h),
      fun h => by rw [(varQ_eq_zero_iff _).mpr h]⟩

/-! ## The ℚ-read executed values (the `norm_num`→`decide` retrofit) -/

/-- The ℚ-read value of the bits of `1.0`: mantissa `2²³` at scale `2⁻²³`. -/
theorem toRat_ofBits_one : toRat (IEEE32Exec.ofBits 0x3F800000) = 1 := by
  rw [toRat_of_toDyadic w0_toDyadic, dyadicToRat]
  norm_num

/-- The ℚ-read value of the next float32 above `1.0`: exactly `1 + 2⁻²³`. -/
theorem toRat_ofBits_ulp : toRat (IEEE32Exec.ofBits 0x3F800001) = 1 + (2 : ℚ) ^ (-23 : ℤ) := by
  rw [toRat_of_toDyadic w1_toDyadic, dyadicToRat]
  norm_num

/-- The executed value of the bits of `1.0`, through the ℚ-reading. -/
theorem toReal_ofBits_one :
    IEEE32Exec.toReal (IEEE32Exec.ofBits 0x3F800000) = 1 := by
  rw [← toRat_cast w0_toDyadic, toRat_ofBits_one]
  norm_num

/-- The executed value of the next float32 above `1.0`: exactly `1 + 2⁻²³`. -/
theorem toReal_ofBits_ulp :
    IEEE32Exec.toReal (IEEE32Exec.ofBits 0x3F800001) = 1 + (2 : ℝ) ^ (-23 : ℤ) := by
  rw [← toRat_cast w1_toDyadic, toRat_ofBits_ulp]
  push_cast
  norm_num

/-- **The executed one-ULP gap, in ℝ, via the ℚ-reading**: the two decoded values differ by
exactly `2⁻²³`. The witness layer's gap statement, re-proved through the computable bridge. -/
theorem executed_gap_eq :
    IEEE32Exec.toReal (IEEE32Exec.ofBits 0x3F800001)
      - IEEE32Exec.toReal (IEEE32Exec.ofBits 0x3F800000) = (2 : ℝ) ^ (-23 : ℤ) := by
  rw [toReal_ofBits_one, toReal_ofBits_ulp]
  ring

/-! ## Analytic family: the zero-iff guards -/

section Analytic

open MeasureTheory RKHS

variable {Xt : Type*} [TopologicalSpace Xt] [MeasurableSpace Xt] [OpensMeasurableSpace Xt]
variable {Yt : Type*} [TopologicalSpace Yt] [MeasurableSpace Yt] [OpensMeasurableSpace Yt]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable [SecondCountableTopology H]
variable [RKHS ℝ H (Xt × Yt) ℝ]
variable [BoundedKernel H (X := Xt × Yt)]

omit [TopologicalSpace Xt] [OpensMeasurableSpace Xt] [TopologicalSpace Yt]
  [OpensMeasurableSpace Yt] [SecondCountableTopology H] [BoundedKernel H] in
/-- **HSIC transport** (unconditional given a characteristic kernel): a transformation of
joint laws preserving the HSIC value transports independence both ways. The HSIC guard
enforces the symmetry it names. -/
theorem hsicGuard_transport
    (hchar : IsCharacteristic (H := H) (X := Xt × Yt))
    (g : Measure (Xt × Yt) → Measure (Xt × Yt))
    (hinv : ∀ P, hsicDef (H := H) (g P) = hsicDef (H := H) P) (P : Measure (Xt × Yt)) :
    ((g P) = ((g P).map Prod.fst).prod ((g P).map Prod.snd)) ↔
      (P = (P.map Prod.fst).prod (P.map Prod.snd)) := by
  rw [← hsicDef_zero_iff_independent (H := H) hchar, ← hsicDef_zero_iff_independent (H := H) hchar,
    hinv P]

/-- **MI transport is CONDITIONAL** (the scope finding): the mutual-information guard
transports independence only along transformations that preserve its side conditions —
absolute continuity of the joint w.r.t. the product of marginals, and finite KL — at BOTH
points. The zero-iff is hypothesis-bearing, so "enforces the symmetry it names" is too. -/
theorem miGuard_transport {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β]
    (g : Measure (α × β) → Measure (α × β))
    (hinv : ∀ P, InformationTheory.mutualInformationReal (g P)
      = InformationTheory.mutualInformationReal P)
    (P : Measure (α × β)) [IsProbabilityMeasure P] [IsProbabilityMeasure (g P)]
    (hac : P.AbsolutelyContinuous ((P.map Prod.fst).prod (P.map Prod.snd)))
    (hfin : InformationTheory.klDiv P ((P.map Prod.fst).prod (P.map Prod.snd)) ≠ ⊤)
    (hac' : (g P).AbsolutelyContinuous (((g P).map Prod.fst).prod ((g P).map Prod.snd)))
    (hfin' : InformationTheory.klDiv (g P)
      (((g P).map Prod.fst).prod ((g P).map Prod.snd)) ≠ ⊤) :
    ((g P) = ((g P).map Prod.fst).prod ((g P).map Prod.snd)) ↔
      (P = (P.map Prod.fst).prod (P.map Prod.snd)) := by
  rw [← InformationTheory.mutualInformationReal_eq_zero_iff_product (g P) hac' hfin',
    ← InformationTheory.mutualInformationReal_eq_zero_iff_product P hac hfin, hinv P]

end Analytic

end WMSpec
