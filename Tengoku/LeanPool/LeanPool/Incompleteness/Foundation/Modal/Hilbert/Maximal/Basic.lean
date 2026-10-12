/-
Copyright (c) 2026 Palalansoukî. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Palalansoukî
-/
module

public import Tengoku.LeanPool.LeanPool.Incompleteness.Foundation.IntProp.Hilbert.WellKnown
public import Tengoku.LeanPool.LeanPool.Incompleteness.Foundation.Modal.Hilbert.WellKnown
public import Tengoku.LeanPool.LeanPool.Incompleteness.Foundation.Modal.IntProp

/-! # Basic -/

@[expose] public section

namespace LO
namespace Modal

variable {α} [DecidableEq α]

namespace Formula

/-- Imported declaration from the Incompleteness formalization. -/
def TrivTranslation : Formula α → Formula α
  | .atom a => atom a
  | □φ => φ.TrivTranslation
  | ⊥ => ⊥
  | φ ==> ψ => (φ.TrivTranslation) ==> (ψ.TrivTranslation)
/-- Imported declaration from the Incompleteness formalization. -/
postfix:75 "ᵀ" => TrivTranslation

namespace TrivTranslation

@[simp] lemma degree_zero : φᵀ.degree = 0 := by induction φ <;> simp [TrivTranslation, degree, *];

@[simp]
lemma back : φᵀᴾᴹ = φᵀ := by
  induction φ using rec' with
  | himp => simp [TrivTranslation, toPropFormula, *];
  | hbox => simp [TrivTranslation, *];
  | _ => rfl;

end TrivTranslation

/-- Imported declaration from the Incompleteness formalization. -/
def VerTranslation : Formula α → Formula α
  | atom a => atom a
  | □_ => ⊤
  | ⊥ => ⊥
  | φ ==> ψ => (φ.VerTranslation) ==> (ψ.VerTranslation)
/-- Imported declaration from the Incompleteness formalization. -/
postfix:75 "ⱽ" => VerTranslation

namespace VerTranslation

@[simp]
lemma degree_zero : φⱽ.degree = 0 := by
  induction φ using rec' with
  | himp => simp [VerTranslation, *];
  | _ => rfl;

@[simp] lemma back : φⱽᴾᴹ = φⱽ := by
  induction φ using rec' with
  | himp => simp [VerTranslation, toPropFormula, *];
  | _ => rfl;

end VerTranslation

end Formula

open Entailment
open Formula (TrivTranslation VerTranslation)

namespace Hilbert

namespace Triv

lemma iff_trivTranslated : (Hilbert.Triv) ⊢! φ <=> φᵀ := by
  induction φ using Formula.rec' with
  | hbox φ ih =>
    apply iff_intro!;
    · exact imp_trans''! axiomT! (and₁'! ih)
    · exact imp_trans''! (and₂'! ih) axiomTc!
  | himp _ _ ih₁ ih₂ => exact imp_replace_iff! ih₁ ih₂;
  | _ => apply iff_id!

end Triv

namespace Ver

lemma iff_verTranslated : (Hilbert.Ver) ⊢! φ <=> φⱽ := by
  induction φ using Formula.rec' with
  | hbox =>
    apply iff_intro!;
    · exact imply₁'! verum!
    · exact imply₁'! (by simp)
  | himp _ _ ih₁ ih₂ => exact imp_replace_iff! ih₁ ih₂;
  | _ => apply iff_id!

end Ver

end Hilbert

end Modal
end LO
