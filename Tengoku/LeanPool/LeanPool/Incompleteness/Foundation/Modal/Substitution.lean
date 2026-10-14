/-
Copyright (c) 2026 Palalansoukî. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Palalansoukî
-/
module

public import Tengoku.LeanPool.LeanPool.Incompleteness.Foundation.Modal.Formula

/-! # Substitution -/

@[expose] public section

namespace LO
namespace Modal

/-- Imported declaration from the Incompleteness formalization. -/
abbrev Substitution (α) := α → (Formula α)

/-- Imported declaration from the Incompleteness formalization. -/
abbrev _root_.LO.Modal.Substitution.id {α} : Substitution α := fun a => .atom a

namespace Formula

variable {φ ψ : Formula α} {s : Substitution α}

/-- Imported declaration from the Incompleteness formalization. -/
def subst (s : Substitution α) : Formula α → Formula α
  | atom a  => (s a)
  | ⊥       => ⊥
  | □φ      => □(φ.subst s)
  | φ ==> ψ   => φ.subst s ==> ψ.subst s

/-- Imported declaration from the Incompleteness formalization. -/
notation:80 φ "⟦" s "⟧" => Formula.subst s φ

/--
@isnad1 id=eq.0h3v.s4.eba4f0208920 from=translated src=- shape=38405f78 vocab=ae39fe8a
-/
@[simp] lemma subst_atom {a} : (.atom a)⟦s⟧ = s a := rfl

/--
@isnad1 id=eq.0h2v.s5.476bb09c14c3 from=translated src=- shape=45d5be01 vocab=affbb884
-/
@[simp] lemma subst_bot : ⊥⟦s⟧ = ⊥ := rfl

/--
@isnad1 id=eq.0h4v.s5.7f680cf8e28a from=translated src=- shape=1bab1856 vocab=0fe2647c
-/
@[simp] lemma subst_imp : (φ ==> ψ)⟦s⟧ = φ⟦s⟧ ==> ψ⟦s⟧ := rfl

/--
@isnad1 id=eq.0h3v.s5.852ffad8f945 from=translated src=- shape=16faf886 vocab=accbdb1c
-/
@[simp] lemma subst_neg : (∼φ)⟦s⟧ = ∼(φ⟦s⟧) := rfl

/--
@isnad1 id=eq.0h4v.s5.b5095d0d740d from=translated src=- shape=1bab1856 vocab=b5b940da
-/
@[simp] lemma subst_and : (φ ⋏ ψ)⟦s⟧ = φ⟦s⟧ ⋏ ψ⟦s⟧ := rfl

/--
@isnad1 id=eq.0h4v.s5.def9dc20651b from=translated src=- shape=1bab1856 vocab=fe2f3e95
-/
@[simp] lemma subst_or : (φ ⋎ ψ)⟦s⟧ = φ⟦s⟧ ⋎ ψ⟦s⟧ := rfl

/--
@isnad1 id=eq.0h4v.s5.43439ef91ec3 from=translated src=- shape=1bab1856 vocab=8bd7e1ef
-/
@[simp] lemma subst_iff : (φ <=> ψ)⟦s⟧ = (φ⟦s⟧ <=> ψ⟦s⟧) := rfl

/--
@isnad1 id=eq.0h3v.s5.7729ab2cc563 from=translated src=- shape=16faf886 vocab=c0759bd0
-/
@[simp] lemma subst_box : (□φ)⟦s⟧ = □(φ⟦s⟧) := rfl

/--
@isnad1 id=eq.0h4v.s5.b2f3bdd660fc from=translated src=- shape=1e9a9645 vocab=ba99c081
-/
@[simp] lemma subst_multibox : (□^[n]φ)⟦s⟧ = □^[n](φ⟦s⟧) := by
  induction n with
  | zero => rfl
  | succ n ih => simp [ih]

/--
@isnad1 id=eq.0h3v.s5.b4f16af3ab0f from=translated src=- shape=16faf886 vocab=f22806bd
-/
@[simp] lemma subst_dia : (◇φ)⟦s⟧ = ◇(φ⟦s⟧) := rfl

/--
@isnad1 id=eq.0h4v.s5.b8e87718b7b5 from=translated src=- shape=1e9a9645 vocab=f1ef765b
-/
@[simp] lemma subst_multidia : (◇^[n]φ)⟦s⟧ = ◇^[n](φ⟦s⟧) := by
  induction n with
  | zero => rfl
  | succ n ih => simp [ih]

end Formula

/--
@isnad1 id=eq.0h2v.s3.49c2fa85fe24 from=translated src=- shape=ff24a7f5 vocab=d2f4c44b
-/
@[simp] lemma subst_id {φ : Formula α} :
    φ⟦.id⟧ = φ := by induction φ using Formula.rec' <;> simp_all;

/-- Imported declaration from the Incompleteness formalization. -/
def _root_.LO.Modal.Substitution.comp (s₁ s₂ : Substitution α) : Substitution α :=
  fun a => (s₁ a)⟦s₂⟧
/-- Imported declaration from the Incompleteness formalization. -/
infixr:80 " ∘ " => Substitution.comp

/--
@isnad1 id=eq.0h4v.s4.84f198161af8 from=translated src=- shape=f0aafd19 vocab=760d7939
-/
@[simp]
lemma subst_comp {s₁ s₂ : Substitution α} {φ : Formula α} : φ⟦s₁ ∘ s₂⟧ = φ⟦s₁⟧⟦s₂⟧ := by
  induction φ using Formula.rec' <;> simp_all [Substitution.comp];

/-- Imported declaration from the Incompleteness formalization. -/
class SubstitutionClosed (S : Set (Formula α)) where
  closed : ∀ φ ∈ S, (∀ s : Substitution α, φ⟦s⟧ ∈ S)

end Modal
end LO
