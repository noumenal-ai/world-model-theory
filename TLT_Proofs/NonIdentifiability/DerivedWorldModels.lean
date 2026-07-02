/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import TLT_Proofs.NonIdentifiability.ForcingTheorem

/-!
# Derived world models: the specification computes the architecture

Two consequences of the forcing theorem that together change what "building a world model"
means for a system with declared targets.

**Objective-independence.** The two clauses of the specification are independent, and neither is
supplied by a predictive training objective alone. The collapsed (constant) encoder satisfies the
dynamics clause for *every* dynamics — `hasDynamics_const`: predictive consistency is compatible
with total collapse, so the dynamics clause cannot certify a representation — yet it fails the
specification the moment any target separates any pair (`not_isWorldModel_const`). In the other
direction, the canonical world model `isWorldModel_quotientMk_bisimilarity` (ForcingTheorem) is a
quotient construction carrying no predictive-training structure whatsoever. Separation is
target-supplied; dynamics-compatibility is congruence-supplied; the specification is indifferent
to how a representation was produced.

**Derivation.** For a deterministic dynamics under which every declared target is conserved, the
specification stops being a constraint and becomes a computation
(`bisimilarity_pureKernel_of_conserved`):

    bisimilarity 𝒯 (pureKernel f) = Setoid.ker (fun s i => T i s),

the joint-invariant kernel — and the induced latent dynamics on the forced quotient is the
**identity** (`pureKernel_map_quotientMk_of_conserved`). The coarsest world model of a
conservative system is the chart of its conserved quantities, with trivial dynamics: the latent
space, the encoder, and the transition law are *derived* from the declared physics, not designed
and then validated. The physics instantiation (PhysLean harmonic oscillator, target = the literal
conserved energy, dynamics = the literal flow) is the recorded next objective in
`world-models/URS.md`.

## References

Noether, *Invariante Variationsprobleme* (1918) — invariants as the canonical coordinates of a
conservative system; Larsen–Skou (1991), Givan–Dean–Greig (2003) as in `ForcingTheorem`.
-/

namespace TLT.NonIdentifiability

variable {S : Type*} {ι : Type*} {W : ι → Type*}

/-- A deterministic dynamics, read as a probabilistic transition kernel. -/
noncomputable def pureKernel (f : S → S) : S → PMF S := fun s => PMF.pure (f s)

variable {T : ∀ i, S → W i}

/-! ## Objective-independence -/

/-- **Predictive consistency admits total collapse.** The constant encoder carries a latent
dynamics for *every* transition kernel: the dynamics clause of the specification is satisfiable
with zero information retained, so it cannot by itself certify a representation. -/
theorem hasDynamics_const (P : S → PMF S) :
    ∃ Q : PUnit → PMF PUnit,
      ∀ s, Q ((fun _ => PUnit.unit) s) = (P s).map (fun _ => PUnit.unit) :=
  ⟨fun _ => PMF.pure PUnit.unit, fun s => (PMF.map_const (P s) PUnit.unit).symm⟩

/-- **The collapsed encoder is not a world model once anything is at stake.** If any target
separates any pair of states, the constant encoder — despite carrying a latent dynamics for every
kernel (`hasDynamics_const`) — fails the specification. Separation is supplied by the targets,
never by dynamics-consistency. -/
theorem not_isWorldModel_const (P : S → PMF S) {i : ι} {s₁ s₂ : S}
    (hsep : T i s₁ ≠ T i s₂) :
    ¬ IsWorldModel T P (fun _ => PUnit.unit) := by
  rintro ⟨hsepE, -⟩
  exact hsep (hsepE i rfl)

/-! ## The derivation theorem -/

/-- **The joint-invariant kernel conforms for conserved targets.** If every target is conserved
by the dynamics, the relation "equal on all targets" refines every target (trivially) and is a
congruence: conservation transports joint-target equality through the flow, so pure pushforwards
agree on the quotient. -/
theorem isConforming_ker_targets_of_conserved {f : S → S}
    (hcons : ∀ (i : ι) (s : S), T i (f s) = T i s) :
    IsConforming T (pureKernel f) (Setoid.ker (fun s i => T i s)) := by
  constructor
  · intro i s₁ s₂ h
    exact congrFun (Setoid.ker_def.mp h) i
  · intro s₁ s₂ h
    show (PMF.pure (f s₁)).map _ = (PMF.pure (f s₂)).map _
    rw [PMF.pure_map, PMF.pure_map]
    refine congrArg PMF.pure (Quotient.eq.mpr (Setoid.ker_def.mpr ?_))
    funext i
    rw [hcons i s₁, hcons i s₂]
    exact congrFun (Setoid.ker_def.mp h) i

/-- **The derivation theorem.** For a deterministic dynamics under which every declared target is
conserved, bisimilarity **equals** the joint-invariant kernel: the specification computes the
forced state space of a conservative system to be exactly the chart of its invariants. One
inclusion is the `refines` clause of bisimilarity; the other is
`isConforming_ker_targets_of_conserved` with `le_sSup`. -/
theorem bisimilarity_pureKernel_of_conserved {f : S → S}
    (hcons : ∀ (i : ι) (s : S), T i (f s) = T i s) :
    bisimilarity T (pureKernel f) = Setoid.ker (fun s i => T i s) := by
  refine le_antisymm ?_ (le_sSup (isConforming_ker_targets_of_conserved hcons))
  rw [Setoid.le_def]
  intro x y h
  refine Setoid.ker_def.mpr (funext fun i => ?_)
  exact isConforming_bisimilarity.refines i h

/-- **The derived latent dynamics of a conservative system is the identity.** On the forced
quotient, the pushforward of the deterministic dynamics is the point mass at the state's own
class: conserved targets cannot move, so the canonical world model's transition law is trivial.
Together with `bisimilarity_pureKernel_of_conserved`: latent space, encoder, and transition law
of the coarsest world model are all computed from the declared targets and dynamics. -/
theorem pureKernel_map_quotientMk_of_conserved {f : S → S}
    (hcons : ∀ (i : ι) (s : S), T i (f s) = T i s) (s : S) :
    (pureKernel f s).map (Quotient.mk (bisimilarity T (pureKernel f))) =
      PMF.pure (Quotient.mk (bisimilarity T (pureKernel f)) s) := by
  have hrel : (bisimilarity T (pureKernel f)) (f s) s := by
    rw [bisimilarity_pureKernel_of_conserved hcons]
    exact Setoid.ker_def.mpr (funext fun i => hcons i s)
  show (PMF.pure (f s)).map _ = _
  rw [PMF.pure_map]
  exact congrArg PMF.pure (Quotient.eq.mpr hrel)

end TLT.NonIdentifiability
