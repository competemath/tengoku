/-
Copyright (c) 2026 Palalansoukî. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Palalansoukî
-/
module

public import Tengoku.LeanPool.LeanPool.Incompleteness.Foundation.IntProp.Formula
public import Tengoku

/-! # Substitution -/

@[expose] public section

namespace LO
namespace IntProp

/-- Imported declaration from the Incompleteness formalization. -/
abbrev Substitution (α) := α → (Formula α)

/-- Imported declaration from the Incompleteness formalization. -/
abbrev _root_.LO.IntProp.Substitution.id {α} : Substitution α := fun a => .atom a

namespace Formula

variable {φ ψ : Formula α} {s : Substitution α}

/-- Imported declaration from the Incompleteness formalization. -/
def subst (s : Substitution α) : Formula α → Formula α
  | atom a  => (s a)
  | ⊥       => ⊥
  | φ ⋏ ψ   => φ.subst s ⋏ ψ.subst s
  | φ ⋎ ψ   => φ.subst s ⋎ ψ.subst s
  | φ ==> ψ   => φ.subst s ==> ψ.subst s

/-- Imported declaration from the Incompleteness formalization. -/
notation:80 φ "⟦" s "⟧" => Formula.subst s φ

/--
@isnad1 id=eq.0h3v.s4.342552e7ca50 from=translated src=- shape=38405f78 vocab=614c596b
-/
@[simp] lemma subst_atom {a} : (.atom a)⟦s⟧ = s a := rfl

/--
@isnad1 id=eq.0h2v.s4.89156744242f from=translated src=- shape=45d5be01 vocab=25206f89
-/
@[simp] lemma subst_bot : ⊥⟦s⟧ = ⊥ := rfl

/--
@isnad1 id=eq.0h2v.s4.2f6cce2de7b5 from=translated src=- shape=45d5be01 vocab=687edde4
-/
@[simp] lemma subst_top : ⊤⟦s⟧ = ⊤ := rfl

/--
@isnad1 id=eq.0h4v.s5.8f8b41f98c81 from=translated src=- shape=1bab1856 vocab=ca2cbc3e
-/
@[simp] lemma subst_imp : (φ ==> ψ)⟦s⟧ = φ⟦s⟧ ==> ψ⟦s⟧ := rfl

/--
@isnad1 id=eq.0h3v.s5.90d4e6a038a8 from=translated src=- shape=16faf886 vocab=c2c05647
-/
@[simp] lemma subst_neg : (∼φ)⟦s⟧ = ∼(φ⟦s⟧) := rfl

/--
@isnad1 id=eq.0h4v.s5.f1f1732ead85 from=translated src=- shape=1bab1856 vocab=f6b8b647
-/
@[simp] lemma subst_and : (φ ⋏ ψ)⟦s⟧ = φ⟦s⟧ ⋏ ψ⟦s⟧ := rfl

/--
@isnad1 id=eq.0h4v.s5.01fba37e8c25 from=translated src=- shape=1bab1856 vocab=77928812
-/
@[simp] lemma subst_or : (φ ⋎ ψ)⟦s⟧ = φ⟦s⟧ ⋎ ψ⟦s⟧ := rfl

/--
@isnad1 id=eq.0h4v.s5.2700b2adbba5 from=translated src=- shape=1bab1856 vocab=360756ba
-/
@[simp] lemma subst_iff : (φ <=> ψ)⟦s⟧ = (φ⟦s⟧ <=> ψ⟦s⟧) := rfl

end Formula

/--
@isnad1 id=eq.0h2v.s3.fb368a85dec2 from=translated src=- shape=ff24a7f5 vocab=879db962
-/
@[simp] lemma subst_id {φ : Formula α} :
    φ⟦.id⟧ = φ := by induction φ using Formula.rec' <;> simp_all;

/-- Imported declaration from the Incompleteness formalization. -/
def _root_.LO.IntProp.Substitution.comp (s₁ s₂ : Substitution α) : Substitution α :=
  fun a => (s₁ a)⟦s₂⟧
/-- Imported declaration from the Incompleteness formalization. -/
infixr:80 " ∘ " => Substitution.comp

/--
@isnad1 id=eq.0h4v.s4.eada3dc56551 from=translated src=- shape=f0aafd19 vocab=a83108d1
-/
@[simp]
lemma subst_comp {s₁ s₂ : Substitution α} {φ : Formula α} : φ⟦s₁ ∘ s₂⟧ = φ⟦s₁⟧⟦s₂⟧ := by
  induction φ using Formula.rec' <;> simp_all [Substitution.comp];

/-- Imported declaration from the Incompleteness formalization. -/
class SubstitutionClosed (S : Set (Formula α)) where
  closed : ∀ φ ∈ S, (∀ s : Substitution α, φ⟦s⟧ ∈ S)

end IntProp
end LO
