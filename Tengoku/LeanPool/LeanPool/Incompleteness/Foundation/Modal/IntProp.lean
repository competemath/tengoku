/-
Copyright (c) 2026 Palalansoukî. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Palalansoukî
-/
module

public import Tengoku.LeanPool.LeanPool.Incompleteness.Foundation.IntProp.Formula
public import Tengoku.LeanPool.LeanPool.Incompleteness.Foundation.Modal.Formula

/-! # IntProp -/

@[expose] public section

namespace LO
namespace IntProp

/-- Imported declaration from the Incompleteness formalization. -/
def _root_.LO.IntProp.Formula.toModalFormula : Formula α → Modal.Formula α
  | .atom a => Modal.Formula.atom a
  | ⊥ => ⊥
  | φ ==> ψ => (toModalFormula φ) ==> (toModalFormula ψ)
  | φ ⋏ ψ => (toModalFormula φ) ⋏ (toModalFormula ψ)
  | φ ⋎ ψ => (toModalFormula φ) ⋎ (toModalFormula ψ)
/-- Imported declaration from the Incompleteness formalization. -/
postfix:75 "ᴹ" => Formula.toModalFormula

namespace Formula
namespace toModalFormula

/--
@isnad1 id=eq.0h1v.s4.0737415c31df from=translated src=- shape=1014f1d5 vocab=9b48fbe1
-/
@[simp] lemma def_top : (⊤ : Formula α)ᴹ = ⊤ := by rfl

/--
@isnad1 id=eq.0h1v.s4.621471ec2775 from=translated src=- shape=1014f1d5 vocab=04f531e3
-/
@[simp] lemma def_bot : (⊥ : Formula α)ᴹ = ⊥ := by rfl

/--
@isnad1 id=eq.0h2v.s3.a32bea329fa3 from=translated src=- shape=eca97296 vocab=e71b44de
-/
@[simp] lemma def_atom (a : α) : (atom a)ᴹ = .atom a := by rfl

/--
@isnad1 id=eq.0h2v.s5.d976d4a028ab from=translated src=- shape=f2ef64f4 vocab=01b49575
-/
@[simp] lemma def_not (φ : Formula α) : (∼φ)ᴹ = ∼(φᴹ) := by rfl

/--
@isnad1 id=eq.0h3v.s5.c3f73ddaeecb from=translated src=- shape=b6f46340 vocab=33df0732
-/
@[simp] lemma def_imp (φ ψ : Formula α) : (φ ==> ψ)ᴹ = (φᴹ) ==> (ψᴹ) := by rfl

/--
@isnad1 id=eq.0h3v.s5.5a5767af0dfd from=translated src=- shape=b6f46340 vocab=63dbac25
-/
@[simp] lemma def_and (φ ψ : Formula α) : (φ ⋏ ψ)ᴹ = (φᴹ) ⋏ (ψᴹ) := by rfl

/--
@isnad1 id=eq.0h3v.s5.c3aaecf651e0 from=translated src=- shape=b6f46340 vocab=dd9fc03c
-/
@[simp] lemma def_or (φ ψ : Formula α) : (φ ⋎ ψ)ᴹ = (φᴹ) ⋎ (ψᴹ) := by rfl

end toModalFormula
end Formula

end IntProp
end LO

namespace LO
namespace Modal

/-- Imported declaration from the Incompleteness formalization. -/
def _root_.LO.Modal.Formula.toPropFormula (φ : Formula α) (_ : φ.degree = 0 :=
  by simp_all [Formula.degree, Formula.degree_neg, Formula.degree_imp]) :
    IntProp.Formula α :=
  match φ with
  | .atom a => IntProp.Formula.atom a
  | ⊥ => ⊥
  | φ ==> ψ => φ.toPropFormula ==> ψ.toPropFormula
/-- Imported declaration from the Incompleteness formalization. -/
postfix:75 "ᴾ" => Formula.toPropFormula

end Modal
end LO
