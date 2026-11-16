import Tengoku.Ulmstheorem.Lib.PGroups.Morphisms
import Tengoku.Ulmstheorem.Lib.PGroups.Socle

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Pure subgroups and height-preserving partial maps

This file contains the basic hard-direction infrastructure for Ulm's theorem:
ordinal height, p-order, purity, and height-preserving maps on subgroups.
-/
namespace Tengoku.Ulmstheorem end Tengoku.Ulmstheorem open Tengoku.Ulmstheorem
open Ordinal

universe u

variable (p : ℕ)
variable {G : Type u} [AddCommGroup G]
variable {H : Type u} [AddCommGroup H]

/-- The ordinal Ulm height of an element.-/
noncomputable def _root_.Tengoku.Ulmstheorem.ulmHeight (x : G) : WithTop Ordinal.{0} :=
  ⨆ (α : Ordinal.{0}) (_ : x ∈ ulmSubgroup p α (G := G)), (α : WithTop Ordinal.{0})

/-- `x` is proper with respect to `S` when its height is maximal in the coset `x + S`.-/
def _root_.Tengoku.Ulmstheorem.IsProper (S : AddSubgroup G) (x : G) : Prop :=
  ∀ s : S, ulmHeight p x ≥ ulmHeight p (x + s)

/-- In a reduced `p`-group, every nonzero element has an attained ordinal
Ulm height.

Reducedness supplies a stage missing the element.  The least such stage
cannot be zero or a limit stage, so it is a successor `α+1`; minimality then
puts the element in `G_α` but not in `G_(α+1)`.
@isnad1 id=ex.2h3v.s6.edf473d85722 from=translated src=- shape=d0650e1a vocab=cbf785e3
-/
lemma _root_.Tengoku.Ulmstheorem.exists_ulmHeight_eq_of_ne_zero [Fact p.Prime]
    (hG : IsReducedPGroup p G) {x : G} (hx0 : x ≠ 0) :
    ∃ α : Ordinal.{0},
      x ∈ ulmSubgroup p α (G := G) ∧
      x ∉ ulmSubgroup p (Order.succ α) (G := G) := by
  obtain ⟨γ, hγ⟩ := hG.reduced
  have hxγ : x ∉ ulmSubgroup p γ (G := G) := by
    rw [hγ]
    simpa using hx0
  obtain ⟨δ, hδmin⟩ :=
    exists_minimal_of_wellFoundedLT
      (fun β : Ordinal.{0} ↦ x ∉ ulmSubgroup p β (G := G)) ⟨γ, hxγ⟩
  rcases Ordinal.zero_or_succ_or_isSuccLimit δ with hδ0 | ⟨α, rfl⟩ | hδlim
  · subst δ
    exact False.elim (hδmin.1 (by simp))
  · refine ⟨α, ?_, hδmin.1⟩
    by_contra hxα
    exact hδmin.not_prop_of_lt (Order.lt_succ α) hxα
  · have hnotall :
        ¬ ∀ β < δ, x ∈ ulmSubgroup p β (G := G) := by
      simpa [mem_ulmSubgroup_limit_iff p hδlim x] using hδmin.1
    push Not at hnotall
    obtain ⟨β, hβδ, hxβ⟩ := hnotall
    exact False.elim (hδmin.not_prop_of_lt hβδ hxβ)

/-- Height-preserving map between full groups.-/
def _root_.Tengoku.Ulmstheorem.IsHeightPreserving (φ : G →+ H) : Prop :=
  ∀ (x : G) (α : Ordinal.{0}),
    x ∈ ulmSubgroup p α (G := G) ↔ φ x ∈ ulmSubgroup p α (G := H)

/-- Height-preserving map between subgroups `A ≤ G` and `B ≤ H`.-/
def _root_.Tengoku.Ulmstheorem.IsHeightPresOn {A : AddSubgroup G} {B : AddSubgroup H} (φ : A →+ B) : Prop :=
  ∀ (a : A) (α : Ordinal.{0}),
    (a : G) ∈ ulmSubgroup p α (G := G) ↔ (φ a : H) ∈ ulmSubgroup p α (G := H)

/-- The `p`-order of an element: the least `n` such that `p^n • x = 0`,
or `⊤` if no such `n` exists.-/
noncomputable def _root_.Tengoku.Ulmstheorem.pOrder (x : G) : ℕ∞ :=
  ⨅ (n : ℕ) (_ : p ^ n • x = 0), (n : ℕ∞)

/--
@isnad1 id=eq.0h2v.s5.d6e1c7396508 from=translated src=- shape=a06f9591 vocab=f8d27599
-/
@[simp] lemma _root_.Tengoku.Ulmstheorem.pOrder_zero : pOrder p (0 : G) = 0 :=
  le_antisymm (iInf_le_of_le 0 <| iInf_le_of_le (by simp) le_rfl) bot_le

/-- A subgroup is `p`-pure if divisibility by powers of `p` seen in the ambient
group is already witnessed internally.-/
def _root_.Tengoku.Ulmstheorem.IsPure (A : AddSubgroup G) : Prop :=
  ∀ (n : ℕ) (x : A), (x : G) ∈ pPow p n (G := G) → x ∈ pPow p n (G := A)

/-- An isotype subgroup is one whose induced Ulm filtration agrees with the
ambient filtration on every element. This is stronger than purity, and it is
the right hypothesis for ambient/intrinsic height equality.-/
def _root_.Tengoku.Ulmstheorem.IsIsotype (A : AddSubgroup G) : Prop :=
  ∀ (x : A) (α : Ordinal.{0}),
    (x : G) ∈ ulmSubgroup p α (G := G) ↔ x ∈ ulmSubgroup p α (G := A)

/--
@isnad1 id=ispure.0h2v.s4.17ece487b1cb from=translated src=- shape=67b1b787 vocab=517fd944
-/
lemma _root_.Tengoku.Ulmstheorem.IsPure_bot : IsPure p (⊥ : AddSubgroup G) :=
  fun _ _ _ ↦ ⟨0, Subsingleton.elim _ _⟩

/--
@isnad1 id=ispure.0h2v.s4.9ff2c25eb085 from=translated src=- shape=67b1b787 vocab=9a564bcb
-/
lemma _root_.Tengoku.Ulmstheorem.IsPure_top : IsPure p (⊤ : AddSubgroup G) := fun _ _ hx ↦ by
  obtain ⟨y, hy⟩ := hx
  exact ⟨⟨y, by simp⟩, Subtype.ext hy⟩

/--
@isnad1 id=injectiv.2h4v.s6.6e7a496d8fc9 from=translated src=- shape=5de4333b vocab=04f3660c
-/
lemma Tengoku.Ulmstheorem.IsHeightPreserving.injective [Fact p.Prime] (hred : IsReducedPGroup p G)
    {φ : G →+ H} (hφ : IsHeightPreserving p φ) :
    Function.Injective φ := by
  intro x y hxy
  rcases hred.reduced with ⟨α, hα⟩
  have hmem : x - y ∈ ulmSubgroup p α (G := G) :=
    (hφ (x - y) α).mpr (by simp [hxy])
  rw [hα] at hmem
  exact sub_eq_zero.mp (AddSubgroup.mem_bot.mp hmem)

/--
@isnad1 id=injectiv.2h6v.s9.ea507f609a60 from=translated src=- shape=2a8078d8 vocab=5142af9f
-/
lemma Tengoku.Ulmstheorem.IsHeightPresOn.injective [Fact p.Prime] (hred : IsReducedPGroup p G)
    {A : AddSubgroup G} {B : AddSubgroup H} {φ : A →+ B} (hφ : IsHeightPresOn p φ) :
    Function.Injective φ := by
  intro x y hxy
  apply Subtype.ext
  rcases hred.reduced with ⟨α, hα⟩
  have hmem : (((x - y : A) : A) : G) ∈ ulmSubgroup p α (G := G) :=
    (hφ (x - y) α).mpr (by simp [hxy])
  rw [hα] at hmem
  exact sub_eq_zero.mp (AddSubgroup.mem_bot.mp hmem)

/-- If `a` is in a subgroup but `b` is not, their sum is not in the subgroup.
Useful for the ultrametric argument in the extension theorem.
@isnad1 id=not.2h4v.s6.cab95cd00d7b from=translated src=- shape=b1dff413 vocab=c3edaa58
-/
lemma _root_.Tengoku.Ulmstheorem.not_mem_of_mem_of_not_mem_add {S : AddSubgroup G} {a b : G}
    (ha : a ∈ S) (hb : b ∉ S) : a + b ∉ S :=
  fun hab ↦ hb (by simpa using S.sub_mem hab ha)
-- Tengoku: root names of this library moved to Tengoku.Ulmstheorem so they do not collide with other libraries (generated)
