/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import Mathlib.GroupTheory.GroupAction.Defs
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Ring
import Mathlib.Data.Finite.Prod
import Mathlib.Data.Fintype.Pigeonhole

/-!
# Flow architectures: the admissible-horizon laws and the executable warmup

The physics-architectures mini-project's flow stratum. A flow is an additive action of time
on states (`AddAction T S` — Mathlib's grammar, no bespoke axioms); an encoder `E : S → Z`
admits a latent step at horizon `t` iff `E ∘ (t +ᵥ ·)` factors through `E`
(`latentStep_iff_factorsThrough` — the master dichotomy; L2b's stroboscopic iff is the
harmonic-oscillator instance).

**The structure laws:**
* `admissibleHorizons E : AddSubmonoid T` — the horizons admitting latent dynamics always
  form a submonoid of time (0 by `zero_vadd`; sums by composing factorizations along
  `add_vadd`).
* `admissibleSubgroup` — for FINITE state spaces and group time, they form a subGROUP: a
  pigeonhole period `k • t ≡ id` on the finite function space gives
  `(-t) +ᵥ x = ((k-1) • t) +ᵥ x`, so the negative horizon rides the forward ones
  (`AddSubmonoid.nsmul_mem`). No permutation theory needed.
* `shift_collapse_not_neg_closed` — finiteness is NECESSARY: on ℤ with the
  collapse-nonnegatives encoder, `+1` is admissible and `−1` is not; the admissible set is a
  genuine submonoid-not-subgroup. The hypothesis is non-vacuous, proved.

**The architecture** (`FlowWorldModel`): an encoder, a DECLARED horizon submonoid, and a step
whose `commutes` field is the flow-correctness certificate — admissibility of every declared
horizon is DERIVED (`FlowWorldModel.horizons_admissible`), not assumed. The executable warmup
instance (`blockModel`): the shift flow on `ZMod 6` with the two-block encoder — the discrete
shadow of the oscillator's half-period aliasing. Kernel `decide` computes the dichotomy on the
literal dynamics (`three_mem_block`, `one_not_mem_block`), and the parity step's additive law
splits into a cast-hom step plus a finite `decide` core.

**The kinematics corollary** (`kinematic_admissible_iff`): for the free-kinematic flow
`t +ᵥ (x, v) = (x + t·v, v)` and the position-only encoder, the admissible set is exactly
`{0}` — aliasing NEVER rescues a velocity-shedding latent. The spectrum of predicted
architectures: kinematics `{0}` ⊂ oscillator `(π/ω)ℤ` (L2b) ⊂ quotient-homomorphic `all` —
one submonoid law, three physics classes.
-/

namespace WMSpec.Flow

open Function

/-! ## The master dichotomy and the submonoid law -/

section Dichotomy

variable {T S Z : Type*} [AddMonoid T] [AddAction T S]

/-- A latent step exists at horizon `t`: some map on the latent space closes the square with
the flow. -/
def LatentStep (E : S → Z) (t : T) : Prop :=
  ∃ fZ : Z → Z, ∀ s, fZ (E s) = E (t +ᵥ s)

/-- **The master dichotomy**: a latent step at horizon `t` exists iff the flowed reading
factors through the encoder. L2b's stroboscopic iff is the oscillator instance; every flow
classification below is an instance of this equivalence. -/
theorem latentStep_iff_factorsThrough [Nonempty S] (E : S → Z) (t : T) :
    LatentStep E t ↔ Function.FactorsThrough (fun s => E (t +ᵥ s)) E := by
  constructor
  · rintro ⟨fZ, hf⟩ a b hab
    simp only []
    rw [← hf a, ← hf b, hab]
  · intro hft
    refine ⟨Function.extend E (fun s => E (t +ᵥ s))
      (fun _ => E (t +ᵥ Classical.arbitrary S)), fun s => ?_⟩
    exact hft.extend_apply _ s

/-- **The submonoid law**: the admissible horizons of ANY encoder against ANY flow form an
additive submonoid of time. Zero: the identity flow factors trivially. Sums: factorizations
compose along `add_vadd`. -/
def admissibleHorizons (E : S → Z) : AddSubmonoid T where
  carrier := {t | Function.FactorsThrough (fun s => E (t +ᵥ s)) E}
  zero_mem' := by
    intro a b hab
    simp only [zero_vadd]
    exact hab
  add_mem' := by
    intro s t hs ht a b hab
    simp only [add_vadd]
    exact hs (ht hab)

/-- Membership unfolds to the factorization property. -/
theorem mem_admissibleHorizons {E : S → Z} {t : T} :
    t ∈ admissibleHorizons E ↔ Function.FactorsThrough (fun s => E (t +ᵥ s)) E :=
  Iff.rfl

end Dichotomy

/-! ## The subgroup upgrade under finiteness -/

section Subgroup

variable {T S Z : Type*} [AddGroup T] [AddAction T S] [Finite S]

/-- **Pigeonhole period**: on a finite state space, every horizon has a positive multiple
acting as the identity — the map `n ↦ ((n • t) +ᵥ ·)` into the finite function space
collides, and group cancellation extracts the period. -/
lemma exists_period (t : T) : ∃ k : ℕ, 0 < k ∧ ∀ x : S, (k • t) +ᵥ x = x := by
  obtain ⟨m, n, hmn, heq⟩ :=
    Finite.exists_ne_map_eq_of_infinite (fun n : ℕ => fun x : S => (n • t) +ᵥ x)
  rcases lt_or_gt_of_ne hmn with h | h
  · refine ⟨n - m, Nat.sub_pos_of_lt h, fun x => ?_⟩
    have happ : (m • t) +ᵥ x = (n • t) +ᵥ x := congrFun heq x
    have hsplit : (n : ℕ) = m + (n - m) := by omega
    rw [hsplit, add_nsmul, add_vadd] at happ
    have := congrArg (fun u => (-(m • t)) +ᵥ u) happ
    simpa [← add_vadd, neg_add_cancel, zero_vadd] using this.symm
  · refine ⟨m - n, Nat.sub_pos_of_lt h, fun x => ?_⟩
    have happ : (n • t) +ᵥ x = (m • t) +ᵥ x := (congrFun heq x).symm
    have hsplit : (m : ℕ) = n + (m - n) := by omega
    rw [hsplit, add_nsmul, add_vadd] at happ
    have := congrArg (fun u => (-(n • t)) +ᵥ u) happ
    simpa [← add_vadd, neg_add_cancel, zero_vadd] using this.symm

/-- On `T` the local left-successor law `(n+1) • a = a + n • a` (kept general — no
commutativity of time assumed). -/
private lemma nsmul_succ_left (n : ℕ) (a : T) : (n + 1) • a = a + n • a := by
  induction n with
  | zero => simp
  | succ n ih =>
      conv_lhs => rw [succ_nsmul, ih]
      conv_rhs => rw [succ_nsmul]
      exact add_assoc _ _ _

/-- **Negative horizons ride the forward ones**: on a finite state space, if `t` is
admissible then so is `−t` — the period identity turns `(-t) +ᵥ ·` into `((k-1) • t) +ᵥ ·`,
which is admissible by submonoid closure. -/
theorem neg_mem_admissible (E : S → Z) {t : T} (ht : t ∈ admissibleHorizons E) :
    -t ∈ admissibleHorizons E := by
  obtain ⟨k, hk, hper⟩ := exists_period (S := S) t
  have key : ∀ x : S, (-t) +ᵥ x = ((k - 1) • t) +ᵥ x := by
    intro x
    have h1 : (-t) +ᵥ x = (-t) +ᵥ ((k • t) +ᵥ x) := by rw [hper x]
    rw [h1, ← add_vadd]
    have hk1 : k = (k - 1) + 1 := (Nat.succ_pred_eq_of_pos hk).symm
    have harith : -t + k • t = (k - 1) • t := by
      conv_lhs => rw [hk1]
      rw [nsmul_succ_left, neg_add_cancel_left]
    rw [harith]
  have hmem : (k - 1) • t ∈ admissibleHorizons E :=
    AddSubmonoid.nsmul_mem (admissibleHorizons E) ht (k - 1)
  intro a b hab
  simp only [key a, key b]
  exact hmem hab

/-- **The subgroup law**: for finite state spaces and group time, the admissible horizons
form an additive subgroup. -/
def admissibleSubgroup (E : S → Z) : AddSubgroup T :=
  { admissibleHorizons E with
    neg_mem' := fun ht => neg_mem_admissible E ht }

end Subgroup

/-! ## Finiteness is necessary: the submonoid-not-subgroup counterexample -/

section Counterexample

/-- The collapse-nonnegatives encoder on ℤ. -/
def collapseEncoder : ℤ → ℤ := fun z => if z < 0 then z else 0

/-- `+1` is admissible for the shift flow against the collapse encoder. -/
theorem one_mem_collapse : (1 : ℤ) ∈ admissibleHorizons (T := ℤ) collapseEncoder := by
  intro a b hab
  simp only [collapseEncoder, vadd_eq_add] at *
  split_ifs at hab ⊢ <;> omega

/-- `−1` is NOT admissible: the collapse forgets exactly the information the backward shift
needs. The admissible set of an infinite state space can be a genuine
submonoid-not-subgroup — the finiteness hypothesis of `admissibleSubgroup` is necessary. -/
theorem neg_one_not_mem_collapse :
    (-1 : ℤ) ∉ admissibleHorizons (T := ℤ) collapseEncoder := by
  intro h
  have h01 : collapseEncoder 0 = collapseEncoder 1 := by
    simp [collapseEncoder]
  have := h h01
  simp only [vadd_eq_add, collapseEncoder] at this
  norm_num at this

end Counterexample

/-! ## The architecture: flow-correctness as a type -/

/-- **A flow world model**: an encoder, a DECLARED horizon submonoid, and a latent step whose
`commutes` field certifies flow-correctness on every declared horizon. Admissibility of the
declared horizons is a theorem (`horizons_admissible`), not a field — the certificate cannot
be circular. -/
structure FlowWorldModel (T S Z : Type*) [AddMonoid T] [AddAction T S] where
  /-- The encoder. -/
  encode : S → Z
  /-- The declared horizons at which the latent dynamics is claimed. -/
  horizons : AddSubmonoid T
  /-- The latent step. -/
  step : T → Z → Z
  /-- The flow-correctness certificate: the square commutes on every declared horizon. -/
  commutes : ∀ t ∈ horizons, ∀ s, step t (encode s) = encode (t +ᵥ s)

/-- Every declared horizon of a flow world model is genuinely admissible: the certificate
implies the factorization. -/
theorem FlowWorldModel.horizons_admissible {T S Z : Type*} [AddMonoid T] [AddAction T S]
    (M : FlowWorldModel T S Z) {t : T} (ht : t ∈ M.horizons) :
    t ∈ admissibleHorizons M.encode := by
  intro a b hab
  simp only []
  rw [← M.commutes t ht a, ← M.commutes t ht b, hab]

/-! ## The executable warmup: the block model on `ZMod 6` -/

section BlockModel

/-- The shift flow of ℤ on `ZMod 6` (the discrete rotation — the finite shadow of the
oscillator phase flow). -/
local instance : AddAction ℤ (ZMod 6) where
  vadd := fun t x => (t : ZMod 6) + x
  zero_vadd := fun x => by
    show ((0 : ℤ) : ZMod 6) + x = x
    simp
  add_vadd := fun s t x => by
    show ((s + t : ℤ) : ZMod 6) + x = (s : ZMod 6) + ((t : ZMod 6) + x)
    push_cast
    rw [add_assoc]

/-- The two-block encoder: which half of the cycle. -/
def blockEncoder : ZMod 6 → Bool := fun x => decide (x.val < 3)

/-- **Executed dichotomy, admissible side**: horizon `3` (the half-period) is admissible —
kernel `decide` over the literal finite dynamics. -/
theorem three_mem_block : (3 : ℤ) ∈ admissibleHorizons (T := ℤ) blockEncoder := by
  show ∀ a b : ZMod 6, blockEncoder a = blockEncoder b →
    blockEncoder ((3 : ℤ) +ᵥ a) = blockEncoder ((3 : ℤ) +ᵥ b)
  decide

/-- **Executed dichotomy, inadmissible side**: horizon `1` is not — the blocks shear. -/
theorem one_not_mem_block : (1 : ℤ) ∉ admissibleHorizons (T := ℤ) blockEncoder := by
  show ¬ ∀ a b : ZMod 6, blockEncoder a = blockEncoder b →
    blockEncoder ((1 : ℤ) +ᵥ a) = blockEncoder ((1 : ℤ) +ᵥ b)
  decide

/-- The parity core of the block step, closed by kernel `decide` over `ZMod 2 × Bool`. -/
private lemma parity_core : ∀ (a b : ZMod 2) (z : Bool),
    xor (xor z (decide (b = 1))) (decide (a = 1)) = xor z (decide (a + b = 1)) := by
  decide

/-- **The executable block architecture**: declared horizons = the submonoid generated by the
half-period, step = block swap by the parity of `t/3` (read through the cast hom `ℤ → ZMod 2`);
`commutes` proved by closure induction with a `decide` base and the `parity_core`. The
warmup's flow-correct world model, literal and type-checked. -/
noncomputable def blockModel : FlowWorldModel ℤ (ZMod 6) Bool where
  encode := blockEncoder
  horizons := AddSubmonoid.closure {(3 : ℤ)}
  step := fun t z => xor z (decide ((t : ZMod 2) = 1))
  commutes := by
    intro t ht
    induction ht using AddSubmonoid.closure_induction with
    | mem t htm =>
        simp only [Set.mem_singleton_iff] at htm
        subst htm
        decide
    | zero => decide
    | add s t _ _ ihs iht =>
        intro x
        have hcast : ((s + t : ℤ) : ZMod 2) = (s : ZMod 2) + (t : ZMod 2) := by push_cast; ring
        calc xor (blockEncoder x) (decide (((s + t : ℤ) : ZMod 2) = 1))
            = xor (blockEncoder x) (decide ((s : ZMod 2) + (t : ZMod 2) = 1)) := by rw [hcast]
          _ = xor (xor (blockEncoder x) (decide ((t : ZMod 2) = 1)))
                (decide ((s : ZMod 2) = 1)) := (parity_core _ _ _).symm
          _ = xor (blockEncoder ((t : ℤ) +ᵥ x)) (decide ((s : ZMod 2) = 1)) := by rw [iht x]
          _ = blockEncoder ((s : ℤ) +ᵥ ((t : ℤ) +ᵥ x)) := ihs ((t : ℤ) +ᵥ x)
          _ = blockEncoder ((s + t : ℤ) +ᵥ x) := by rw [← add_vadd]

end BlockModel

/-! ## The kinematics corollary -/

section Kinematics

/-- Kinematic phase: position and velocity. A dedicated carrier so the kinematic flow's
action cannot collide with Mathlib's componentwise product action (a real ambiguity the
kernel caught: `ℝ × ℝ` already carries `t +ᵥ (x, v) = (t + x, t + v)`). -/
structure Kin where
  /-- position -/
  x : ℝ
  /-- velocity -/
  v : ℝ

/-- The free-kinematic flow: `t +ᵥ ⟨x, v⟩ = ⟨x + t·v, v⟩` (PhysLean's `FreeParticle` binding
is the named literal-physics obligation; the flow law here is exact). -/
instance : AddAction ℝ Kin where
  vadd := fun t p => ⟨p.x + t * p.v, p.v⟩
  zero_vadd := fun p => by
    show Kin.mk (p.x + 0 * p.v) p.v = p
    rw [zero_mul, add_zero]
  add_vadd := fun s t p => by
    show Kin.mk (p.x + (s + t) * p.v) p.v = Kin.mk ((p.x + t * p.v) + s * p.v) p.v
    congr 1
    ring

/-- **The kinematics corollary**: for the free-kinematic flow and the position-only encoder,
the admissible set is exactly `{0}` — aliasing never rescues a velocity-shedding latent. The
anti-stroboscopic extreme of the spectrum (oscillator: `(π/ω)ℤ`; quotient-homomorphic
encoders: everything). -/
theorem kinematic_admissible_iff (t : ℝ) :
    t ∈ admissibleHorizons (T := ℝ) Kin.x ↔ t = 0 := by
  constructor
  · intro h
    by_contra ht
    have hcol : Kin.x ⟨0, 0⟩ = Kin.x ⟨0, 1⟩ := rfl
    have happ := h hcol
    have h1 : Kin.x (t +ᵥ (⟨0, 0⟩ : Kin)) = 0 := by
      show (0 : ℝ) + t * 0 = 0
      ring
    have h2 : Kin.x (t +ᵥ (⟨0, 1⟩ : Kin)) = t := by
      show (0 : ℝ) + t * 1 = t
      ring
    simp only [] at happ
    rw [h1, h2] at happ
    exact ht happ.symm
  · rintro rfl
    exact (admissibleHorizons Kin.x).zero_mem

end Kinematics

end WMSpec.Flow
