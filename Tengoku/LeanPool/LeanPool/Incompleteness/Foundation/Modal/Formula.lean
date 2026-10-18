/-
Copyright (c) 2026 Palalansoukî. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Palalansoukî
-/
module

public import Tengoku.LeanPool.LeanPool.Incompleteness.Foundation.Logic.HilbertStyle.Lukasiewicz
public import Tengoku.LeanPool.LeanPool.Incompleteness.Foundation.Modal.LogicSymbol

/-! # Formula -/

@[expose] public section
open scoped LO.Axioms LO.Dia LO.Entailment


namespace LO
namespace Modal

/-- Imported declaration from the Incompleteness formalization. -/
inductive Formula (α : Type u) : Type u where
  | atom   : α → Formula α
  | falsum : Formula α
  | imp    : Formula α → Formula α → Formula α
  | box    : Formula α → Formula α
  deriving DecidableEq

namespace Formula

/-- Imported declaration from the Incompleteness formalization. -/
abbrev neg (φ : Formula α) : Formula α := imp φ falsum

/-- Imported declaration from the Incompleteness formalization. -/
abbrev verum : Formula α := imp falsum falsum

/-- Imported declaration from the Incompleteness formalization. -/
abbrev top : Formula α := imp falsum falsum

/-- Imported declaration from the Incompleteness formalization. -/
abbrev or (φ ψ : Formula α) : Formula α := imp (neg φ) ψ

/-- Imported declaration from the Incompleteness formalization. -/
abbrev and (φ ψ : Formula α) : Formula α := neg (imp φ (neg ψ))

/-- Imported declaration from the Incompleteness formalization. -/
abbrev dia (φ : Formula α) : Formula α := neg (box (neg φ))

variable {α : Type u}

instance : BasicModalLogicalConnective (Formula α) where
  tilde := neg
  arrow := imp
  wedge := and
  vee := or
  top := verum
  bot := falsum
  box := box
  dia := dia

instance : LukasiewiczAbbrev (Formula α) where
  top := rfl
  neg := rfl
  or := rfl
  and := rfl
instance : DiaAbbrev (Formula α) := ⟨rfl⟩

section «lp_section_1»

variable [ToString α]

/-- Imported declaration from the Incompleteness formalization. -/
def toStr : Formula α → String
  -- | ⊤       => "\\top"
  | ⊥       => "\\bot"
  | atom a  => "{" ++ toString a ++ "}"
  | □φ      => "\\Box " ++ toStr φ
  -- | ◇φ      => "\\Diamond " ++ toStr φ
  | φ ==> ψ   => "\\left(" ++ toStr φ ++ " \\to " ++ toStr ψ ++ "\\right)"
  -- | φ ⋏ ψ   => "\\left(" ++ toStr φ ++ " \\land " ++ toStr ψ ++ "\\right)"
  -- | φ ⋎ ψ   => "\\left(" ++ toStr φ ++ " \\lor "   ++ toStr ψ ++ "\\right)"

instance : Repr (Formula α) := ⟨fun t _ => toStr t⟩

instance : ToString (Formula α) := ⟨toStr⟩

instance : Coe α (Formula α) := ⟨atom⟩

end «lp_section_1»

/--
@isnad1 id=eq.0h1v.s5.29aa80fe9d18 from=translated src=- shape=899c32bf vocab=500f24a6
-/
@[simp] lemma neg_bot : ∼(⊥ : Formula α) = ⊤ := rfl

/--
@isnad1 id=eq.0h3v.s4.623013f6dc70 from=translated src=- shape=c90f15fe vocab=f57f013d
-/
lemma or_eq (φ ψ : Formula α) : or φ ψ = φ ⋎ ψ := rfl

/--
@isnad1 id=eq.0h3v.s4.dd6b0e571880 from=translated src=- shape=c90f15fe vocab=3b1b8b06
-/
lemma and_eq (φ ψ : Formula α) : and φ ψ = φ ⋏ ψ := rfl

/--
@isnad1 id=eq.0h3v.s4.fda17e4eb678 from=translated src=- shape=c90f15fe vocab=5e27601c
-/
lemma imp_eq (φ ψ : Formula α) : imp φ ψ = φ ==> ψ := rfl

/--
@isnad1 id=eq.0h2v.s4.f153477b9b1c from=translated src=- shape=c2b6d1b2 vocab=24992fc8
-/
lemma neg_eq (φ : Formula α) : neg φ = ∼φ := rfl

/--
@isnad1 id=eq.0h2v.s4.db9a0999dc4c from=translated src=- shape=c2b6d1b2 vocab=eeb0928b
-/
lemma box_eq (φ : Formula α) : box φ = □φ := rfl

/--
@isnad1 id=eq.0h2v.s4.4c65b040c9e7 from=translated src=- shape=c2b6d1b2 vocab=567032ca
-/
lemma dia_eq (φ : Formula α) : dia φ = ◇φ := rfl

/--
@isnad1 id=eq.0h3v.s5.ec026032a61b from=translated src=- shape=8067ab0c vocab=c72a2bd5
-/
lemma iff_eq (φ ψ : Formula α) : φ <=> ψ = (φ ==> ψ) ⋏ (ψ ==> φ) := rfl

/--
@isnad1 id=eq.0h1v.s4.b9f986d7e8e5 from=translated src=- shape=a92aae16 vocab=fe405507
-/
lemma falsum_eq : (falsum : Formula α) = ⊥ := rfl

/--
@isnad1 id=iff.0h5v.s5.d3a72d0ffef0 from=translated src=- shape=356e8d20 vocab=419bb852
-/
@[simp] lemma and_inj (φ₁ ψ₁ φ₂ ψ₂ : Formula α) :
    φ₁ ⋏ φ₂ = ψ₁ ⋏ ψ₂ ↔ φ₁ = ψ₁ ∧ φ₂ = ψ₂ := by
  simp[Wedge.wedge]

/--
@isnad1 id=iff.0h5v.s5.389dba343a01 from=translated src=- shape=356e8d20 vocab=b5f3218c
-/
@[simp] lemma or_inj (φ₁ ψ₁ φ₂ ψ₂ : Formula α) :
    φ₁ ⋎ φ₂ = ψ₁ ⋎ ψ₂ ↔ φ₁ = ψ₁ ∧ φ₂ = ψ₂ := by
  simp[Vee.vee]

/--
@isnad1 id=iff.0h5v.s5.502e725b8d96 from=translated src=- shape=356e8d20 vocab=767c1570
-/
@[simp] lemma imp_inj (φ₁ ψ₁ φ₂ ψ₂ : Formula α) :
    φ₁ ==> φ₂ = ψ₁ ==> ψ₂ ↔ φ₁ = ψ₁ ∧ φ₂ = ψ₂ := by
  simp[Arrow.arrow]

/--
@isnad1 id=iff.0h3v.s5.6434943c2262 from=translated src=- shape=af747b6b vocab=0b89db95
-/
@[simp] lemma neg_inj (φ ψ : Formula α) : ∼φ = ∼ψ ↔ φ = ψ := by simp [NegAbbrev.neg];

/-
instance : ModalDeMorgan (Formula α) where
  verum := rfl
  falsum := rfl
  and := by simp
  or := by simp
  imply := by simp[imp_eq]
  neg := by simp
  dia := by simp
  box := by simp
-/

/-- Formula complexity -/
def complexity : Formula α → ℕ
| atom _  => 0
| ⊥       => 0
| φ ==> ψ   => max φ.complexity ψ.complexity + 1
| □φ   => φ.complexity + 1

/-- Max numbers of `□` -/
def degree : Formula α → Nat
  | atom _ => 0
  | ⊥ => 0
  | φ ==> ψ => max φ.degree ψ.degree
  | □φ => φ.degree + 1

/--
@isnad1 id=eq.0h2v.s4.904f3e90f4b7 from=translated src=- shape=b04106a2 vocab=2cfaa721
-/
@[simp] lemma degree_neg (φ : Formula α) :
    degree (∼φ) = degree φ := by
  induction φ <;> simp_all [degree]
/--
@isnad1 id=eq.0h3v.s5.54b7a05b48fb from=translated src=- shape=9e579978 vocab=7d2d1074
-/
@[simp] lemma degree_imp (φ ψ : Formula α) :
    degree (φ ==> ψ) = max (degree φ) (degree ψ) := by
  simp [degree]

/-- Imported declaration from the Incompleteness formalization. -/
@[elab_as_elim]
def cases' {C : Formula α → Sort w}
    (hfalsum : C ⊥)
    (hatom : ∀ a : α, C (atom a))
    (himp     : ∀ (φ ψ : Formula α), C (φ ==> ψ))
    (hbox    : ∀ (φ : Formula α), C (□φ))
    : (φ : Formula α) → C φ
  | ⊥       => hfalsum
  | atom a  => hatom a
  | □φ      => hbox φ
  | φ ==> ψ   => himp φ ψ

/-- Imported declaration from the Incompleteness formalization. -/
@[elab_as_elim]
def rec' {C : Formula α → Sort w}
  (hfalsum : C ⊥)
  (hatom : ∀ a : α, C (atom a))
  (himp    : ∀ (φ ψ : Formula α), C φ → C ψ → C (φ ==> ψ))
  (hbox    : ∀ (φ : Formula α), C φ → C (□φ))
  : (φ : Formula α) → C φ
  | ⊥      => hfalsum
  | atom a => hatom a
  | φ ==> ψ  => himp φ ψ (rec' hfalsum hatom himp hbox φ) (rec' hfalsum hatom himp hbox ψ)
  | □φ     => hbox φ (rec' hfalsum hatom himp hbox φ)

section «lp_section_2»

variable [DecidableEq α]

/-- Imported declaration from the Incompleteness formalization. -/
def hasDecEq : (φ ψ : Formula α) → Decidable (φ = ψ) := fun _ _ => inferInstance
instance : DecidableEq (Formula α) := hasDecEq

end «lp_section_2»

/-- Imported declaration from the Incompleteness formalization. -/
def isBox : Formula α → Bool
  | box _ => true
  | _  => false

end Formula

/-- Imported declaration from the Incompleteness formalization. -/
abbrev FormulaSet (α) := Set (Formula α)

/-- Imported declaration from the Incompleteness formalization. -/
abbrev FormulaFinset (α) := Finset (Formula α)

namespace Formula

variable {φ ψ χ : Formula α}

/-- Imported declaration from the Incompleteness formalization. -/
@[elab_as_elim]
def casesNeg [DecidableEq α] {C : Formula α → Sort w}
    (hfalsum : C ⊥)
    (hatom : ∀ a : α, C (atom a))
    (hneg    : ∀ φ : Formula α, C (∼φ))
    (himp    : ∀ (φ ψ : Formula α), ψ ≠ ⊥ → C (φ ==> ψ))
    (hbox    : ∀ (φ : Formula α), C (□φ))
    : (φ : Formula α) → C φ
  | ⊥       => hfalsum
  | atom a  => hatom a
  | □φ      => hbox φ
  | ∼φ      => hneg φ
  | φ ==> ψ  => if e : ψ = ⊥ then e ▸ hneg φ else himp φ ψ e

/-- Imported declaration from the Incompleteness formalization. -/
@[elab_as_elim]
def recNeg [DecidableEq α] {C : Formula α → Sort w}
    (hfalsum : C ⊥)
    (hatom : ∀ a : α, C (atom a))
    (hneg    : ∀ φ : Formula α, C (φ) → C (∼φ))
    (himp    : ∀ (φ ψ : Formula α), ψ ≠ ⊥ → C φ → C ψ → C (φ ==> ψ))
    (hbox    : ∀ (φ : Formula α), C (φ) → C (□φ))
    : (φ : Formula α) → C φ
  | ⊥       => hfalsum
  | atom a  => hatom a
  | □φ      => hbox φ (recNeg hfalsum hatom hneg himp hbox φ)
  | ∼φ      => hneg φ (recNeg hfalsum hatom hneg himp hbox φ)
  | φ ==> ψ  =>
    if e : ψ = ⊥
    then e ▸ hneg φ (recNeg hfalsum hatom hneg himp hbox φ)
    else himp φ ψ e (recNeg hfalsum hatom hneg himp hbox φ) (recNeg hfalsum hatom hneg himp hbox
      ψ)

section «lp_section_3»

/-- Imported declaration from the Incompleteness formalization. -/
def negated : Formula α → Bool
  | ∼_ => True
  | _  => False

/--
@isnad1 id=eq.0h2v.s4.0d7296621054 from=translated src=- shape=613ace56 vocab=be530fdd
-/
@[simp] lemma negated_def : (∼φ).negated := by simp [negated]

/--
@isnad1 id=iff.0h3v.s5.32f1d2664139 from=translated src=- shape=f47a33bb vocab=71049c94
-/
@[simp]
lemma negated_imp : (φ ==> ψ).negated ↔ (ψ = ⊥) := by
  simp [negated];
  split;
  · simp_all [Formula.imp_eq]; rfl;
  · simp_all [Formula.imp_eq]; simpa;

/--
@isnad1 id=iff.0h2v.s5.0eef0684b4a8 from=translated src=- shape=f301b4fa vocab=be530fdd
-/
lemma negated_iff : φ.negated ↔ ∃ ψ, φ = ∼ψ := by
  classical
  induction φ using Formula.casesNeg with
  | himp => simp [negated_imp, NegAbbrev.neg];
  | _ => simp [negated]

/--
@isnad1 id=iff.0h2v.s5.5b209f3cf55e from=translated src=- shape=6b76a6d9 vocab=be530fdd
-/
lemma not_negated_iff : ¬φ.negated ↔ ∀ ψ, φ ≠ ∼ψ := by
  classical
  induction φ using Formula.casesNeg with
  | himp => simp [negated_imp, NegAbbrev.neg];
  | _ => simp [negated]

/-- Imported declaration from the Incompleteness formalization. -/
@[elab_as_elim]
def recNegated [DecidableEq α] {C : Formula α → Sort w}
    (hfalsum : C ⊥)
    (hatom : ∀ a : α, C (atom a))
    (hneg    : ∀ φ : Formula α, C (φ) → C (∼φ))
    (himp    : ∀ (φ ψ : Formula α), ¬(φ ==> ψ).negated → C φ → C ψ → C (φ ==> ψ))
    (hbox    : ∀ (φ : Formula α), C (φ) → C (□φ))
    : (φ : Formula α) → C φ
  | ⊥       => hfalsum
  | atom a  => hatom a
  | □φ      => hbox φ (recNegated hfalsum hatom hneg himp hbox φ)
  | ∼φ      => hneg φ (recNegated hfalsum hatom hneg himp hbox φ)
  | φ ==> ψ  => by
    by_cases e : ψ = ⊥
    · exact e ▸ hneg φ (recNegated hfalsum hatom hneg himp hbox φ)
    · refine himp φ ψ ?_ (recNegated hfalsum hatom hneg himp hbox φ) (recNegated hfalsum hatom
      hneg himp hbox ψ)
      · simpa [negated_imp]

end «lp_section_3»

section «lp_section_4»

variable [Encodable α]
open Encodable

/-- Imported declaration from the Incompleteness formalization. -/
def toNat : Formula α → ℕ
  | atom a  => (Nat.pair 0 <| encode a) + 1
  | ⊥       => (Nat.pair 1 0) + 1
  | □φ      => (Nat.pair 2 <| φ.toNat) + 1
  | φ ==> ψ   => (Nat.pair 3 <| φ.toNat.pair ψ.toNat) + 1

end «lp_section_4»

end Formula

end Modal
end LO
