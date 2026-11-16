import Tengoku.Ulmstheorem.Lib.PGroups.Socle

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Ulm invariants

For a prime p and a reduced abelian p-group G, the **Ulm invariant** at ordinal α is
  f_G(α) = dim_{ℤ/pℤ} (P_α / P_{α+1}),
where `P_α = G[p] ∩ p^α·G = pSocleAt p α`.

We also keep the raw filtration quotient `G_α / G_{α+1}` available as
`layerQuotient` / `layerInvariant`; this is useful auxiliary data, but it is
not the classical Ulm invariant used in Ulm's theorem.

## Main definitions

- `layerQuotient p α G` : the quotient group `(p^α·G) / (p^(α+1)·G)`
- `layerInvariant p α G` : the cardinal rank of `layerQuotient` as a `ℤ/pℤ`-module
- `ulmQuotient p α G` : the quotient group `P_α / P_{α+1}`
- `ulmInvariant p α G` : the cardinal rank of `ulmQuotient` as a `ℤ/pℤ`-module
- `ulmLength p G` : the least ordinal α with `p^α·G = 0`  (exists for reduced groups)

## References
- Fuchs, "Abelian Groups", Chapter 11, §1
- Kaplansky, "Infinite Abelian Groups", Theorem 14
-/
namespace Tengoku.Ulmstheorem end Tengoku.Ulmstheorem open Tengoku.Ulmstheorem
open Ordinal Cardinal

variable (p : ℕ) [hp : Fact p.Prime]

/-! ### The raw filtration quotient `G_α / G_{α+1}` -/

/-- The quotient `G_α / G_{α+1}`. This is useful auxiliary filtration data, but
it is not the classical Ulm invariant.-/
noncomputable def _root_.Tengoku.Ulmstheorem.layerQuotient {G : Type*} [AddCommGroup G] (α : Ordinal) :
    Type _ :=
  (ulmSubgroup p α (G := G)) ⧸
    ((ulmSubgroup p (Order.succ α) (G := G)).comap
      (ulmSubgroup p α (G := G)).subtype)

noncomputable instance {G : Type*} [AddCommGroup G] (α : Ordinal) :
    AddCommGroup (layerQuotient p α (G := G)) := by
  unfold layerQuotient
  infer_instance

/-! ### The classical Ulm quotient `P_α / P_{α+1}` -/

/-- `P_(α+1)` as a `ZMod p`-submodule of `P_α`.-/
noncomputable def _root_.Tengoku.Ulmstheorem.ulmDenSubmodule {G : Type*} [AddCommGroup G] (α : Ordinal) :
    Submodule (ZMod p) (pSocleAt p α (G := G)) :=
  AddSubgroup.toZModSubmodule p (pSocleAt_succ_subgroupOf p α)

/-- The classical Ulm quotient at `α`: `P_α / P_{α+1}`.-/
abbrev _root_.Tengoku.Ulmstheorem.ulmQuotient {G : Type*} [AddCommGroup G] (α : Ordinal) :
    Type _ :=
  (pSocleAt p α (G := G)) ⧸ ulmDenSubmodule p α

/-- The classical Ulm invariant `f_G(α) = dim_{ℤ/pℤ}(P_α / P_{α+1})`.-/
noncomputable def _root_.Tengoku.Ulmstheorem.ulmInvariant {G : Type*} [AddCommGroup G]
    (α : Ordinal) : Cardinal :=
  Module.rank (ZMod p) (ulmQuotient p α (G := G))

/-! ### Hill, marked-graded, and overhang invariants -/

section RelativeInvariants

variable {G : Type*} [AddCommGroup G]

/-- The marked-graded denominator
`P_(α+1) + (S ∩ P_α)`, viewed as a subgroup of `P_α`.-/
noncomputable def _root_.Tengoku.Ulmstheorem.markedGradedDen (S : AddSubgroup G) (α : Ordinal) :
    AddSubgroup (pSocleAt p α (G := G)) :=
  (pSocleAt p (Order.succ α) ⊔ (S ⊓ pSocleAt p α)).comap
    (pSocleAt p α).subtype

/-- The marked-graded denominator as a `ZMod p`-submodule of `P_α`.-/
noncomputable def _root_.Tengoku.Ulmstheorem.markedGradedSubmodule (S : AddSubgroup G) (α : Ordinal) :
    Submodule (ZMod p) (pSocleAt p α (G := G)) :=
  AddSubgroup.toZModSubmodule p (markedGradedDen p S α)

/-- The marked-graded socle space
`P_α / (P_(α+1) + (S ∩ P_α))`.-/
abbrev _root_.Tengoku.Ulmstheorem.markedGradedQuotient (S : AddSubgroup G) (α : Ordinal) : Type _ :=
  (pSocleAt p α (G := G)) ⧸ markedGradedSubmodule p S α

/-- The rank of the marked-graded socle space
`dim_(ZMod p) P_α / (P_(α+1) + (S ∩ P_α))`.-/
noncomputable def _root_.Tengoku.Ulmstheorem.markedGradedInvariant (S : AddSubgroup G) (α : Ordinal) : Cardinal :=
  Module.rank (ZMod p) (markedGradedQuotient p S α)

/-- The Fuchs/Walker Hill denominator
`P_α ∩ (S + G_(α+1))`, viewed inside `P_α`.-/
noncomputable def _root_.Tengoku.Ulmstheorem.hillDen (S : AddSubgroup G) (α : Ordinal) :
    AddSubgroup (pSocleAt p α (G := G)) :=
  (pSocleAt p α ⊓ (S ⊔ ulmSubgroup p (Order.succ α))).comap
    (pSocleAt p α).subtype

/-- The Hill denominator as a `ZMod p`-submodule of `P_α`.-/
noncomputable def _root_.Tengoku.Ulmstheorem.hillSubmodule (S : AddSubgroup G) (α : Ordinal) :
    Submodule (ZMod p) (pSocleAt p α (G := G)) :=
  AddSubgroup.toZModSubmodule p (hillDen p S α)

/-- The Fuchs/Walker Hill (relative Ulm) space
`P_α / (P_α ∩ (S + G_(α+1)))`.-/
abbrev _root_.Tengoku.Ulmstheorem.hillQuotient (S : AddSubgroup G) (α : Ordinal) : Type _ :=
  (pSocleAt p α (G := G)) ⧸ hillSubmodule p S α

/-- The Fuchs/Walker Hill invariant. Its nonzero classes are exactly the
order-`p`, exact-height-`α` elements proper with respect to `S`.-/
noncomputable def _root_.Tengoku.Ulmstheorem.hillInvariant (S : AddSubgroup G) (α : Ordinal) : Cardinal :=
  Module.rank (ZMod p) (hillQuotient p S α)

/-- BCM's "relative Ulm" terminology names the same quotient as the
Fuchs/Walker Hill invariant.-/
noncomputable abbrev _root_.Tengoku.Ulmstheorem.relativeUlmDen (S : AddSubgroup G) (α : Ordinal) :=
  hillDen p S α

noncomputable abbrev _root_.Tengoku.Ulmstheorem.relativeUlmSubmodule (S : AddSubgroup G) (α : Ordinal) :=
  hillSubmodule p S α

abbrev _root_.Tengoku.Ulmstheorem.relativeUlmQuotient (S : AddSubgroup G) (α : Ordinal) :=
  hillQuotient p S α

noncomputable abbrev _root_.Tengoku.Ulmstheorem.relativeUlmInvariant (S : AddSubgroup G) (α : Ordinal) :=
  hillInvariant p S α

/-- The marked-graded denominator is contained in the Hill denominator.
@isnad1 id=le.0h4v.s8.d9bd87a820fd from=translated src=- shape=6655074b vocab=b554fb99
-/
lemma _root_.Tengoku.Ulmstheorem.markedGradedSubmodule_le_hillSubmodule (S : AddSubgroup G) (α : Ordinal) :
    markedGradedSubmodule p S α ≤ hillSubmodule p S α := by
  intro x hx
  change (x : G) ∈ pSocleAt p α ⊓ (S ⊔ ulmSubgroup p (Order.succ α))
  change (x : G) ∈
    pSocleAt p (Order.succ α) ⊔ (S ⊓ pSocleAt p α) at hx
  refine ⟨x.property, ?_⟩
  have hle :
      pSocleAt p (Order.succ α) ⊔ (S ⊓ pSocleAt p α) ≤
        S ⊔ ulmSubgroup p (Order.succ α) := by
    apply sup_le
    · intro y hy
      exact AddSubgroup.mem_sup_right hy.2
    · intro y hy
      exact AddSubgroup.mem_sup_left hy.1
  exact hle hx

/-- The ordinary Ulm denominator `P_(α+1)` is contained in the Hill denominator.
@isnad1 id=le.0h4v.s8.b8f8e64d6c31 from=translated src=- shape=bc165838 vocab=fce8cecb
-/
lemma _root_.Tengoku.Ulmstheorem.ulmDenSubmodule_le_hillSubmodule (S : AddSubgroup G) (α : Ordinal) :
    ulmDenSubmodule p α ≤ hillSubmodule p S α := by
  intro x hx
  change (x : G) ∈ pSocleAt p α ⊓ (S ⊔ ulmSubgroup p (Order.succ α))
  change (x : G) ∈ pSocleAt p (Order.succ α) at hx
  exact ⟨x.property, AddSubgroup.mem_sup_right hx.2⟩

/-- The subspace of the ordinary Ulm layer occupied by the marked subgroup `S`.-/
noncomputable def _root_.Tengoku.Ulmstheorem.relativeOccupiedSubmodule (S : AddSubgroup G) (α : Ordinal) :
    Submodule (ZMod p) (ulmQuotient p α (G := G)) :=
  (hillSubmodule p S α).map (ulmDenSubmodule p α).mkQ

/-- Quotienting the ordinary Ulm layer by its occupied subspace gives the
relative Ulm space.-/
noncomputable def _root_.Tengoku.Ulmstheorem.occupiedQuotientEquivRelative (S : AddSubgroup G) (α : Ordinal) :
    (ulmQuotient p α (G := G) ⧸ relativeOccupiedSubmodule p S α) ≃ₗ[ZMod p]
      hillQuotient p S α :=
  Submodule.quotientQuotientEquivQuotient
    (ulmDenSubmodule p α) (hillSubmodule p S α)
    (ulmDenSubmodule_le_hillSubmodule p S α)

/-- The BCM overhang, as the kernel subspace inside the marked-graded quotient.
This ordinal-indexed definition extends BCM's finite-level construction.-/
noncomputable def _root_.Tengoku.Ulmstheorem.overhangSubmodule (S : AddSubgroup G) (α : Ordinal) :
    Submodule (ZMod p) (markedGradedQuotient p S α) :=
  (hillSubmodule p S α).map (markedGradedSubmodule p S α).mkQ

/-- The dimension of the BCM overhang space.-/
noncomputable def _root_.Tengoku.Ulmstheorem.overhangInvariant (S : AddSubgroup G) (α : Ordinal) : Cardinal :=
  Module.rank (ZMod p) (overhangSubmodule (p := p) S α)

/-- The canonical quotient map from the marked-graded space onto the Hill space.-/
noncomputable def _root_.Tengoku.Ulmstheorem.markedGradedToHill (S : AddSubgroup G) (α : Ordinal) :
    markedGradedQuotient p S α →ₗ[ZMod p] hillQuotient p S α :=
  Submodule.factor (markedGradedSubmodule_le_hillSubmodule p S α)

end RelativeInvariants

/-! ### Ulm length -/

/-- The Ulm length of a reduced p-group: the least ordinal α at which p^α·G = 0.
    For countable reduced p-groups this is a countable ordinal.-/
noncomputable def _root_.Tengoku.Ulmstheorem.ulmLength {G : Type*} [AddCommGroup G] (_hred : IsReducedPGroup p G) :
    Ordinal.{0} :=
  sInf {α : Ordinal.{0} | ulmSubgroup p α (G := G) = ⊥}

namespace Tengoku.Ulmstheorem.ulmLength

variable {G : Type*} [AddCommGroup G] (hred : IsReducedPGroup p G)

omit hp in
/-- The set `{α | p^α·G = 0}` is nonempty for a reduced p-group.
@isnad1 id=ex.1h2v.s5.02c8c08ee8de from=translated src=- shape=b0eb717f vocab=6165ddc0
-/
lemma exists_zero (hred' : IsReducedPGroup p G) :
    ∃ α : Ordinal.{0}, ulmSubgroup p α (G := G) = ⊥ := by
  exact hred'.reduced

end Tengoku.Ulmstheorem.ulmLength

/-! ### Ulm sequence as a function ℕ → Cardinal (for successor-length groups) -/

/-- For groups of Ulm length `ω·γ + n`, the tail Ulm invariants are those at
`ω·γ`, `ω·γ+1`, ..., `ω·γ+(n-1)`.-/
noncomputable def _root_.Tengoku.Ulmstheorem.tailInvariants {G : Type*} [AddCommGroup G]
    (γ : Ordinal) (n : ℕ) : Fin n → Cardinal :=
  fun k ↦ ulmInvariant p (ω * γ + k.1) (G := G)
-- Tengoku: root names of this library moved to Tengoku.Ulmstheorem so they do not collide with other libraries (generated)
