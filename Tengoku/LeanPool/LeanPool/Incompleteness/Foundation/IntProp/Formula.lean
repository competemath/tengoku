/-
Copyright (c) 2026 Palalansoukî. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Palalansoukî
-/
module

public import Tengoku.LeanPool.LeanPool.Incompleteness.Foundation.Logic.LogicSymbol
public import Tengoku

/-! # Formula -/

@[expose] public section

namespace LO
namespace IntProp

/-- Imported declaration from the Incompleteness formalization. -/
inductive Formula (α : Type u) : Type u
  | atom   : α → Formula α
  | falsum : Formula α
  | and    : Formula α → Formula α → Formula α
  | or     : Formula α → Formula α → Formula α
  | imp    : Formula α → Formula α → Formula α
  deriving DecidableEq

namespace Formula

/-- Imported declaration from the Incompleteness formalization. -/
abbrev neg {α : Type u} (φ : Formula α) : Formula α := imp φ falsum

/-- Imported declaration from the Incompleteness formalization. -/
abbrev verum {α : Type u} : Formula α := imp falsum falsum

instance : LogicalConnective (Formula α) where
  tilde := neg
  arrow := imp
  wedge := and
  vee := or
  top := verum
  bot := falsum

instance : LO.NegAbbrev (Formula α) := by tauto;

section «lp_section_1»

variable [ToString α]

/-- Imported declaration from the Incompleteness formalization. -/
def toStr : Formula α → String
  | ⊤       => "\\top"
  | ⊥       => "\\bot"
  | atom a  => "{" ++ toString a ++ "}"
  | ∼φ      => "\\lnot " ++ toStr φ
  | φ ⋏ ψ   => "\\left(" ++ toStr φ ++ " \\land " ++ toStr ψ ++ "\\right)"
  | φ ⋎ ψ   => "\\left(" ++ toStr φ ++ " \\lor "  ++ toStr ψ ++ "\\right)"
  | φ ==> ψ   => "\\left(" ++ toStr φ ++ " \\rightarrow " ++ toStr ψ ++ "\\right)"

instance : Repr (Formula α) := ⟨fun t _ => toStr t⟩
instance : ToString (Formula α) := ⟨toStr⟩

end «lp_section_1»

/--
@isnad1 id=iff.0h5v.s5.d895747b1592 from=translated src=- shape=356e8d20 vocab=c5698735
-/
@[simp] lemma and_inj (φ₁ ψ₁ φ₂ ψ₂ : Formula α) :
    φ₁ ⋏ φ₂ = ψ₁ ⋏ ψ₂ ↔ φ₁ = ψ₁ ∧ φ₂ = ψ₂ := by simp[Wedge.wedge]

/--
@isnad1 id=iff.0h5v.s5.b6ed4a27c7cc from=translated src=- shape=356e8d20 vocab=0c4df813
-/
@[simp] lemma or_inj (φ₁ ψ₁ φ₂ ψ₂ : Formula α) :
    φ₁ ⋎ φ₂ = ψ₁ ⋎ ψ₂ ↔ φ₁ = ψ₁ ∧ φ₂ = ψ₂ := by simp[Vee.vee]

/--
@isnad1 id=iff.0h5v.s5.26ebf3f5551b from=translated src=- shape=356e8d20 vocab=1e8d47a2
-/
@[simp] lemma imp_inj (φ₁ ψ₁ φ₂ ψ₂ : Formula α) :
    φ₁ ==> φ₂ = ψ₁ ==> ψ₂ ↔ φ₁ = ψ₁ ∧ φ₂ = ψ₂ := by simp[Arrow.arrow]

/--
@isnad1 id=iff.0h3v.s5.8f8134597752 from=translated src=- shape=af747b6b vocab=10e6ee17
-/
@[simp] lemma neg_inj (φ ψ : Formula α) : ∼φ = ∼ψ ↔ φ = ψ := by simp[Tilde.tilde]

/--
@isnad1 id=eq.0h2v.s5.3c2f603d2a71 from=translated src=- shape=672fb964 vocab=0f24ae1b
-/
lemma neg_def (φ : Formula α) : ∼φ = φ ==> ⊥ := rfl

/--
@isnad1 id=eq.0h1v.s5.dd271699ed94 from=translated src=- shape=75fde5cb vocab=0a04c803
-/
lemma top_def : (⊤ : Formula α) = ⊥ ==> ⊥ := rfl

/--
@isnad1 id=eq.0h3v.s5.97a4f720ee37 from=translated src=- shape=8067ab0c vocab=38900fc2
-/
lemma iff_def (φ ψ : Formula α) : φ <=> ψ = (φ ==> ψ) ⋏ (ψ ==> φ) := by rfl

/-- Imported declaration from the Incompleteness formalization. -/
def complexity : Formula α → ℕ
| atom _  => 0
| ⊥       => 0
| φ ==> ψ  => max φ.complexity ψ.complexity + 1
| φ ⋏ ψ   => max φ.complexity ψ.complexity + 1
| φ ⋎ ψ   => max φ.complexity ψ.complexity + 1

/--
@isnad1 id=eq.0h1v.s4.acb676cd8092 from=translated src=- shape=d9710dfd vocab=a70cb60f
-/
@[simp] lemma complexity_bot : complexity (⊥ : Formula α) = 0 := rfl

/--
@isnad1 id=eq.0h2v.s4.50f9b3fe35ca from=translated src=- shape=d0dfd432 vocab=932417ad
-/
@[simp] lemma complexity_atom (a : α) : complexity (atom a) = 0 := rfl

/--
@isnad1 id=eq.0h3v.s5.de561ceecc45 from=translated src=- shape=85137ebf vocab=85b8a981
-/
@[simp] lemma complexity_imp (φ ψ : Formula α) :
    complexity (φ ==> ψ) = max φ.complexity ψ.complexity + 1 :=
  rfl
/--
@isnad1 id=eq.0h3v.s5.ed286f47e84f from=translated src=- shape=8fb0926f vocab=db37d416
-/
@[simp] lemma complexity_imp' (φ ψ : Formula α) :
    complexity (imp φ ψ) = max φ.complexity ψ.complexity + 1 :=
  rfl

/--
@isnad1 id=eq.0h3v.s5.42c76aaca3cc from=translated src=- shape=85137ebf vocab=ca0884f7
-/
@[simp] lemma complexity_and (φ ψ : Formula α) :
    complexity (φ ⋏ ψ) = max φ.complexity ψ.complexity + 1 :=
  rfl
/--
@isnad1 id=eq.0h3v.s5.dfb4356cbcc7 from=translated src=- shape=8fb0926f vocab=72aace89
-/
@[simp] lemma complexity_and' (φ ψ : Formula α) :
    complexity (and φ ψ) = max φ.complexity ψ.complexity + 1 :=
  rfl

/--
@isnad1 id=eq.0h3v.s5.01dfa94f9684 from=translated src=- shape=85137ebf vocab=451f5a39
-/
@[simp] lemma complexity_or (φ ψ : Formula α) :
    complexity (φ ⋎ ψ) = max φ.complexity ψ.complexity + 1 :=
  rfl
/--
@isnad1 id=eq.0h3v.s5.e9dfaf3e8f36 from=translated src=- shape=8fb0926f vocab=5eb5f1da
-/
@[simp] lemma complexity_or' (φ ψ : Formula α) :
    complexity (or φ ψ) = max φ.complexity ψ.complexity + 1 :=
  rfl

/-- Imported declaration from the Incompleteness formalization. -/
@[elab_as_elim]
def cases' {C : Formula α → Sort w}
    (hfalsum : C ⊥)
    (hatom : ∀ a : α, C (atom a))
    (himp    : ∀ (φ ψ : Formula α), C (φ ==> ψ))
    (hand    : ∀ (φ ψ : Formula α), C (φ ⋏ ψ))
    (hor     : ∀ (φ ψ : Formula α), C (φ ⋎ ψ))
    : (φ : Formula α) → C φ
  | ⊥       => hfalsum
  | atom a  => hatom a
  | φ ==> ψ   => himp φ ψ
  | φ ⋏ ψ   => hand φ ψ
  | φ ⋎ ψ   => hor φ ψ

/-- Imported declaration from the Incompleteness formalization. -/
@[elab_as_elim]
def rec' {C : Formula α → Sort w}
  (hfalsum : C ⊥)
  (hatom : ∀ a : α, C (atom a))
  (himp    : ∀ (φ ψ : Formula α), C φ → C ψ → C (φ ==> ψ))
  (hand    : ∀ (φ ψ : Formula α), C φ → C ψ → C (φ ⋏ ψ))
  (hor     : ∀ (φ ψ : Formula α), C φ → C ψ → C (φ ⋎ ψ))
  : (φ : Formula α) → C φ
  | ⊥       => hfalsum
  | atom a  => hatom a
  | φ ==> ψ  => himp φ ψ (rec' hfalsum hatom himp hand hor φ) (rec' hfalsum hatom himp hand hor ψ)
  | φ ⋏ ψ   => hand φ ψ (rec' hfalsum hatom himp hand hor φ) (rec' hfalsum hatom himp hand hor ψ)
  | φ ⋎ ψ   => hor φ ψ (rec' hfalsum hatom himp hand hor φ) (rec' hfalsum hatom himp hand hor ψ)

section «lp_section_2»

variable [DecidableEq α]

/-- Imported declaration from the Incompleteness formalization. -/
def hasDecEq : (φ ψ : Formula α) → Decidable (φ = ψ) := fun _ _ => inferInstance

instance : DecidableEq (Formula α) := hasDecEq

end «lp_section_2»

section «lp_section_3»

variable [Encodable α]
open Encodable

/-- Imported declaration from the Incompleteness formalization. -/
def toNat : Formula α → ℕ
  | ⊥       => (Nat.pair 0 0) + 1
  | atom a  => (Nat.pair 1 <| encode a) + 1
  | φ ==> ψ   => (Nat.pair 2 <| φ.toNat.pair ψ.toNat) + 1
  | φ ⋏ ψ   => (Nat.pair 3 <| φ.toNat.pair ψ.toNat) + 1
  | φ ⋎ ψ   => (Nat.pair 4 <| φ.toNat.pair ψ.toNat) + 1

end «lp_section_3»

end Formula

/-- Imported declaration from the Incompleteness formalization. -/
abbrev FormulaSet (α : Type u) := Set (Formula α)

/-- Imported declaration from the Incompleteness formalization. -/
abbrev FormulaFinset (α : Type u) := Finset (Formula α)

end IntProp
end LO
