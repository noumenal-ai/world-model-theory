/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import WMSpec.MixedFamilies

/-!
# The forcing theorem: bisimilarity is the greatest spec-satisfying congruence

P3, the world-model specification's apex. On a finite state space with probabilistic dynamics
`P : S → FintypePMF S` and a target family `𝒯`:

* the 𝒯-refining `P`-congruences (`SpecCongruences`) have a GREATEST element — `bisimilarity`,
  their lattice supremum, which is itself a member (`bisim_mem`, the crux: Larsen–Skou
  union-of-bisimulations in finite form, one `EqvGen` chain induction carried by the
  saturation lemma);
* the quotient by bisimilarity satisfies the specification: every target descends
  (`quotientTarget`), and the dynamics descends to the quotient with a DEFINITIONALLY
  commuting square (`quotientDynamics_mk` is `rfl`) — the latent dynamics of specification
  clause 3, existing by construction rather than assumption;
* every spec-satisfying encoder refines bisimilarity (`specEncoder_ker_le`), and the
  bisimulation classification factors through ANY spec-satisfying representation
  (`bisim_classification_factors` — the `Function.extend`/`FactorsThrough` idiom of the
  McShane tick, aimed at the quotient map): every world model, whatever its latent space,
  already computes the causal states.

Design notes (from the front-loaded model, `world-models/URS.md` P3 tick): the congruence
property is stated QUOTIENT-FREE — equal mass on every saturated `Finset` — so bisimilarity's
definition never mentions its own classes; saturation is symmetric by construction (sophism
guard S6); membership is the headline theorem, not a hypothesis (guard S1); the quotient
dynamics is `Quotient.lift`ed, forcing the well-definedness proof (guard S2); coarseness is a
factorization statement, not cardinality talk (guard S3).
-/

namespace WMSpec

open ProbabilityTheory.FintypePMF

section Forcing

variable {S : Type*} [Fintype S] {V : Type*}

/-- Mass a finite law assigns to a `Finset` of states. -/
def classMass (p : ProbabilityTheory.FintypePMF S) (C : Finset S) : ℝ :=
  ∑ s ∈ C, p.prob s

/-- A `Finset` is saturated for a setoid when membership is invariant along the relation
(symmetric formulation — sophism guard S6). -/
def Saturated (r : Setoid S) (C : Finset S) : Prop :=
  ∀ a b, r a b → (a ∈ C ↔ b ∈ C)

/-- The relation refines the target family: related states carry equal target values
(`r ≤ ker T` for every `T ∈ 𝒯`; orientation pinned once — sophism guard S4). -/
def Refining (𝒯 : Set (S → V)) (r : Setoid S) : Prop :=
  ∀ T ∈ 𝒯, ∀ a b, r a b → T a = T b

/-- **Quotient-free probabilistic congruence**: related states give equal mass to every
`r`-saturated `Finset`. The classes never appear in the definition — they arrive later as
theorems. -/
def DynCong (P : S → ProbabilityTheory.FintypePMF S) (r : Setoid S) : Prop :=
  ∀ a b, r a b → ∀ C : Finset S, Saturated r C → classMass (P a) C = classMass (P b) C

/-- The spec-satisfying congruences: refine the targets, respect the dynamics. -/
def SpecCongruences (𝒯 : Set (S → V)) (P : S → ProbabilityTheory.FintypePMF S) :
    Set (Setoid S) :=
  {r | Refining 𝒯 r ∧ DynCong P r}

/-- **Bisimilarity relative to `(𝒯, P)`**: the supremum of the spec-satisfying congruences.
That it is itself one is the forcing theorem's crux (`bisim_mem`). -/
def bisimilarity (𝒯 : Set (S → V)) (P : S → ProbabilityTheory.FintypePMF S) : Setoid S :=
  sSup (SpecCongruences 𝒯 P)

omit [Fintype S] in
/-- **The saturation lemma** (the unification carrying both closure proofs): a `Finset`
saturated for the supremum is saturated for every member. -/
lemma Saturated.of_mem {F : Set (Setoid S)} {r : Setoid S} (hr : r ∈ F) {C : Finset S}
    (hC : Saturated (sSup F) C) : Saturated r C :=
  fun a b hab => hC a b (Setoid.le_def.mp (le_sSup hr) hab)

/-- **The crux: bisimilarity is itself a spec-satisfying congruence** (membership, not just
an upper bound — sophism guard S1). Both closure properties go by one `EqvGen` chain
induction: each chain step preserves target values (its member refines) and preserves the
mass of the FIXED sup-saturated set (its member is a congruence, and the set is saturated for
it by the saturation lemma). Larsen–Skou's union of bisimulations, finite form. -/
theorem bisim_mem (𝒯 : Set (S → V)) (P : S → ProbabilityTheory.FintypePMF S) :
    bisimilarity 𝒯 P ∈ SpecCongruences 𝒯 P := by
  constructor
  · intro T hT a b hab
    have hab' : Relation.EqvGen (fun x y => ∃ r ∈ SpecCongruences 𝒯 P, r x y) a b := by
      rw [bisimilarity, Setoid.sSup_eq_eqvGen] at hab
      exact hab
    clear hab
    induction hab' with
    | rel x y h =>
        obtain ⟨r, hrF, hrxy⟩ := h
        exact hrF.1 T hT x y hrxy
    | refl x => rfl
    | symm x y _ ih => exact ih.symm
    | trans x y z _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  · intro a b hab C hC
    have hC' : Saturated (sSup (SpecCongruences 𝒯 P)) C := hC
    have hab' : Relation.EqvGen (fun x y => ∃ r ∈ SpecCongruences 𝒯 P, r x y) a b := by
      rw [bisimilarity, Setoid.sSup_eq_eqvGen] at hab
      exact hab
    clear hab hC
    induction hab' with
    | rel x y h =>
        obtain ⟨r, hrF, hrxy⟩ := h
        exact hrF.2 x y hrxy C (Saturated.of_mem hrF hC')
    | refl x => rfl
    | symm x y _ ih => exact ih.symm
    | trans x y z _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- Every spec-satisfying congruence lies below bisimilarity: greatest, given membership. -/
theorem le_bisimilarity {𝒯 : Set (S → V)} {P : S → ProbabilityTheory.FintypePMF S}
    {r : Setoid S} (hr : r ∈ SpecCongruences 𝒯 P) : r ≤ bisimilarity 𝒯 P :=
  le_sSup hr

/-- **A spec-satisfying encoder**: one whose kernel refines the targets and respects the
dynamics — specification clauses 1 and 3 at the level of the induced equivalence. -/
def SpecEncoder (𝒯 : Set (S → V)) (P : S → ProbabilityTheory.FintypePMF S)
    {Z : Type*} (E : S → Z) : Prop :=
  Setoid.ker E ∈ SpecCongruences 𝒯 P

/-- Every spec-satisfying encoder refines bisimilarity. -/
theorem specEncoder_ker_le {𝒯 : Set (S → V)} {P : S → ProbabilityTheory.FintypePMF S}
    {Z : Type*} {E : S → Z} (hE : SpecEncoder 𝒯 P E) :
    Setoid.ker E ≤ bisimilarity 𝒯 P :=
  le_sSup hE

/-- **The universal factorization** (coarseness as structure, not cardinality — sophism guard
S3): the bisimulation classification factors through EVERY spec-satisfying representation.
Whatever latent space a world model uses, it already computes the causal states. The
`Function.extend`/`FactorsThrough` idiom, aimed at the quotient map. -/
theorem bisim_classification_factors [Nonempty S]
    {𝒯 : Set (S → V)} {P : S → ProbabilityTheory.FintypePMF S}
    {Z : Type*} {E : S → Z} (hE : SpecEncoder 𝒯 P E) :
    ∃ φ : Z → Quotient (bisimilarity 𝒯 P),
      ∀ s, Quotient.mk (bisimilarity 𝒯 P) s = φ (E s) := by
  have hft : Function.FactorsThrough (Quotient.mk (bisimilarity 𝒯 P)) E := by
    intro a b hab
    exact Quotient.sound (Setoid.le_def.mp (specEncoder_ker_le hE) (Setoid.ker_def.mpr hab))
  exact ⟨Function.extend E (Quotient.mk (bisimilarity 𝒯 P))
      (fun _ => Quotient.mk (bisimilarity 𝒯 P) (Classical.arbitrary S)),
    fun s => (hft.extend_apply _ s).symm⟩

/-! ## The quotient satisfies the specification -/

section QuotientSpec

variable (𝒯 : Set (S → V)) (P : S → ProbabilityTheory.FintypePMF S)

/-- Targets descend to the bisimulation quotient (specification clause 1 for the quotient). -/
def quotientTarget {T : S → V} (hT : T ∈ 𝒯) :
    Quotient (bisimilarity 𝒯 P) → V :=
  Quotient.lift T (fun a b hab => (bisim_mem 𝒯 P).1 T hT a b hab)

/-- The descended target reads the original on representatives — definitionally. -/
theorem quotientTarget_mk {T : S → V} (hT : T ∈ 𝒯) (s : S) :
    quotientTarget 𝒯 P hT (Quotient.mk (bisimilarity 𝒯 P) s) = T s := rfl

noncomputable instance : DecidableEq (Quotient (bisimilarity 𝒯 P)) :=
  Classical.decEq _

noncomputable instance : Fintype (Quotient (bisimilarity 𝒯 P)) :=
  Fintype.ofSurjective (Quotient.mk (bisimilarity 𝒯 P)) Quotient.mk_surjective

/-- Local extensionality for finite laws: equal mass functions, equal laws. -/
lemma FintypePMF.ext' {α : Type*} [Fintype α] {p q : ProbabilityTheory.FintypePMF α}
    (h : ∀ a, p.prob a = q.prob a) : p = q := by
  cases p
  cases q
  congr 1
  exact funext h

/-- The fiber of a quotient class under `Quotient.mk` is bisimilarity-saturated. -/
lemma fiber_saturated (c : Quotient (bisimilarity 𝒯 P)) :
    Saturated (bisimilarity 𝒯 P)
      (Finset.univ.filter (fun s => Quotient.mk (bisimilarity 𝒯 P) s = c)) := by
  intro a b hab
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [Quotient.sound hab]

/-- **The dynamics descends** (specification clause 3 for the quotient): the pushforward of
the step law along the quotient map is well defined on classes — the congruence property is
exactly its well-definedness. -/
noncomputable def quotientDynamics :
    Quotient (bisimilarity 𝒯 P) → ProbabilityTheory.FintypePMF (Quotient (bisimilarity 𝒯 P)) :=
  Quotient.lift (fun a => mapPMF (Quotient.mk (bisimilarity 𝒯 P)) (P a)) (by
    intro a b hab
    refine FintypePMF.ext' fun c => ?_
    show classMass (P a) _ = classMass (P b) _
    exact (bisim_mem 𝒯 P).2 a b hab _ (fiber_saturated 𝒯 P c))

/-- **The commuting square is definitional**: the quotient dynamics of a class is the
pushforward of the state dynamics — the latent transition law exists by construction. -/
theorem quotientDynamics_mk (a : S) :
    quotientDynamics 𝒯 P (Quotient.mk (bisimilarity 𝒯 P) a)
      = mapPMF (Quotient.mk (bisimilarity 𝒯 P)) (P a) := rfl

end QuotientSpec

/-- **The forcing theorem** (P3, packaged): bisimilarity is a spec-satisfying congruence,
it is the greatest one, and every spec-satisfying encoder refines it. With
`quotientTarget`/`quotientDynamics` (the quotient satisfies the spec) and
`bisim_classification_factors` (every world model computes the causal states), this is the
positive theory's apex: what survives the specification is exactly the bisimulation
quotient. -/
theorem forcing_theorem (𝒯 : Set (S → V)) (P : S → ProbabilityTheory.FintypePMF S) :
    bisimilarity 𝒯 P ∈ SpecCongruences 𝒯 P ∧
    (∀ r ∈ SpecCongruences 𝒯 P, r ≤ bisimilarity 𝒯 P) ∧
    (∀ {Z : Type*} (E : S → Z), SpecEncoder 𝒯 P E → Setoid.ker E ≤ bisimilarity 𝒯 P) :=
  ⟨bisim_mem 𝒯 P, fun _ hr => le_bisimilarity hr, fun _ hE => specEncoder_ker_le hE⟩

end Forcing

end WMSpec
