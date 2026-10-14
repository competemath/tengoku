/-
Copyright (c) 2026 Palalansoukî. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Palalansoukî
-/
module

public import Tengoku.LeanPool.LeanPool.Incompleteness.Foundation.Modal.Kripke.Basic

/-! # FiniteFrame -/

@[expose] public section

namespace LO
namespace Modal

namespace Kripke

/-- Imported declaration from the Incompleteness formalization. -/
structure FiniteFrame extends Frame where
  [world_finite : Finite toFrame.World]

instance {F : FiniteFrame} : Finite F.World := F.world_finite

/-- Imported declaration from the Incompleteness formalization. -/
def _root_.LO.Modal.Kripke.Frame.toFinite (F : Frame) [Finite F.World] : FiniteFrame where
  toFrame := F

/-- Imported declaration from the Incompleteness formalization. -/
abbrev FiniteFrameClass := Set FiniteFrame

/-- Imported declaration from the Incompleteness formalization. -/
def _root_.LO.Modal.Kripke.FrameClass.restrictFinite (C : FrameClass) : FiniteFrameClass := { F :
    FiniteFrame | F.toFrame ∈ C }

/-- Imported declaration from the Incompleteness formalization. -/
def _root_.LO.Modal.Kripke.FiniteFrameClass.toFrameClass (C : FiniteFrameClass) :
    FrameClass :=
  C.image (·.toFrame)

instance : Coe (FiniteFrameClass) (FrameClass) := ⟨FiniteFrameClass.toFrameClass⟩

/-- Imported declaration from the Incompleteness formalization. -/
abbrev reflexivePointFrame : FiniteFrame where
  World := Unit
  Rel := fun _ _ => True

/-- Imported declaration from the Incompleteness formalization. -/
abbrev irreflexivePointFrame : FiniteFrame where
  World := Unit
  Rel := fun _ _ => False

end Kripke

namespace Formula
namespace Kripke

/-- Imported declaration from the Incompleteness formalization. -/
def ValidOnFiniteFrame (F : Kripke.FiniteFrame) (φ : Formula ℕ) := F.toFrame ⊧ φ

namespace ValidOnFiniteFrame

instance semantics :
    Semantics (Formula ℕ) (Kripke.FiniteFrame) :=
  ⟨fun F ↦ Formula.Kripke.ValidOnFiniteFrame F⟩

variable {F : Kripke.FiniteFrame}

/--
@isnad1 id=iff.0h2v.s4.19f4d26f277e from=translated src=- shape=d962512f vocab=b63b0ac9
-/
@[simp] protected lemma models_iff : F ⊧ φ ↔ Kripke.ValidOnFiniteFrame F φ := iff_of_eq rfl

/--
@isnad1 id=iff.0h2v.s5.d8b856c6b153 from=translated src=- shape=c6fec093 vocab=5f474904
-/
lemma models_set_iff : F ⊧* Φ ↔ ∀ φ ∈ Φ, F ⊧ φ := by simp [Semantics.realizeSet_iff];

/--
@isnad1 id=realize.0h1v.s4.c5ab5715b13b from=translated src=- shape=75b9ccd3 vocab=9b8d4137
-/
protected lemma top_def : F ⊧ ⊤ := by simp [ValidOnFiniteFrame];

/--
@isnad1 id=not.0h1v.s4.ef8a8349a8d5 from=translated src=- shape=6fb7f272 vocab=c5c1f78f
-/
protected lemma bot_def : ¬F ⊧ ⊥ := by simp [ValidOnFiniteFrame];

/--
@isnad1 id=iff.0h2v.s5.6a945462b102 from=translated src=- shape=240946cf vocab=f8ad95a2
-/
lemma iff_not_exists_valuation : (¬F ⊧ φ) ↔ (∃ V : Kripke.Valuation F.toFrame, ¬(⟨F.toFrame, V⟩ :
    Kripke.Model) ⊧ φ) :=
  ValidOnFrame.iff_not_exists_valuation

alias ⟨exists_valuation_of_not, not_of_exists_valuation⟩ := iff_not_exists_valuation

/--
@isnad1 id=iff.0h2v.s5.e57fd56589db from=translated src=- shape=cc55c75d vocab=327294ed
-/
lemma iff_not_exists_valuation_world : (¬F ⊧ φ) ↔ (∃ V : Kripke.Valuation F.toFrame, ∃ x :
    (⟨F.toFrame, V⟩ :
    Kripke.Model).World, ¬Satisfies _ x φ) :=
  ValidOnFrame.iff_not_exists_valuation_world

alias ⟨exists_valuation_world_of_not, not_of_exists_valuation_world⟩ :=
  iff_not_exists_valuation_world

end ValidOnFiniteFrame

/-- Imported declaration from the Incompleteness formalization. -/
def ValidOnFiniteFrameClass (C : Kripke.FiniteFrameClass) (φ : Formula ℕ) := C.toFrameClass ⊧ φ

namespace ValidOnFiniteFrameClass

protected instance semantics :
    Semantics (Formula ℕ) (Kripke.FiniteFrameClass) :=
  ⟨fun C ↦ Kripke.ValidOnFrameClass C⟩

variable {C : Kripke.FiniteFrameClass}

/--
@isnad1 id=iff.0h2v.s4.c540800caf5d from=translated src=- shape=63d62e0b vocab=321f63b6
-/
@[simp] protected lemma models_iff : C ⊧ φ ↔ Formula.Kripke.ValidOnFrameClass C φ := iff_of_eq rfl

/--
@isnad1 id=iff.0h2v.s5.81cd04f76a99 from=translated src=- shape=1c137132 vocab=4ac1fd38
-/
lemma iff_not_exists_frame : (¬C ⊧ φ) ↔ (∃ F ∈ C, ¬F ⊧ φ) := by
  have h := ValidOnFrameClass.iff_not_exists_frame (φ := φ) (C := C.toFrameClass);
  rw [show (¬C ⊧ φ) = (¬C.toFrameClass ⊧ φ) from rfl, h];
  simp [Kripke.FiniteFrameClass.toFrameClass, ValidOnFiniteFrame];

alias ⟨exists_frame_of_not, not_of_exists_frame⟩ := iff_not_exists_frame

end ValidOnFiniteFrameClass

end Kripke
end Formula

namespace Kripke

namespace FiniteFrameClass

/-- Imported declaration from the Incompleteness formalization. -/
class DefinedBy (C : Kripke.FiniteFrameClass) (Γ : Set (Formula ℕ)) where
  defines : ∀ F, F ∈ C ↔ (∀ φ ∈ Γ, F ⊧ φ)

/-- Imported declaration from the Incompleteness formalization. -/
class FiniteDefinedBy (C Γ) extends FiniteFrameClass.DefinedBy C Γ where
  finite : Set.Finite Γ

/-- Imported declaration from the Incompleteness formalization. -/
abbrev DefinedByFormula (C) (φ : Formula ℕ) := FiniteFrameClass.DefinedBy C {φ}

/--
@isnad1 id=definedb.1h2v.s4.b27ec423a155 from=translated src=- shape=ab8af8f8 vocab=0b2e0160
-/
lemma definedByFormula_of_iff_mem_validate (h : ∀ F, F ∈ C ↔ F ⊧ φ) : DefinedByFormula C φ := by
  constructor;
  simpa;

/--
@isnad1 id=definedb.0h4v.s5.c9421361c99e from=translated src=- shape=35291cc0 vocab=7f0616af
-/
instance definedBy_inter
  (C₁ Γ₁) [h₁ : DefinedBy C₁ Γ₁]
  (C₂ Γ₂) [h₂ : DefinedBy C₂ Γ₂]
  : DefinedBy (C₁ ∩ C₂) (Γ₁ ∪ Γ₂) := ⟨by
  rintro F;
  constructor
  · rintro ⟨hF₁, hF₂⟩;
    rintro φ (hφ₁ | hφ₂);
    · exact h₁.defines F |>.mp hF₁ _ hφ₁;
    · exact h₂.defines F |>.mp hF₂ _ hφ₂;
  · intro h;
    constructor;
    · apply h₁.defines F |>.mpr;
      simp_all
    · apply h₂.defines F |>.mpr;
      simp_all
⟩

/-- Imported declaration from the Incompleteness formalization. -/
class IsNonempty (C : Kripke.FiniteFrameClass) where
  nonempty : Nonempty C

end FiniteFrameClass

/-- Imported declaration from the Incompleteness formalization. -/
abbrev AllFiniteFrameClass : FiniteFrameClass := Set.univ

instance _root_.LO.Modal.Kripke.AllFiniteFrameClass.DefinedBy :
    AllFiniteFrameClass.DefinedByFormula (Axioms.K (.atom 0) (.atom 1)) :=
  FiniteFrameClass.definedByFormula_of_iff_mem_validate <| by
    simp only [Set.mem_univ, true_iff];
    intro F;
    exact Formula.Kripke.ValidOnFrame.axiomK;

namespace FiniteFrameClass

variable {C : Kripke.FiniteFrameClass}

/--
@isnad1 id=definedb.1h2v.s5.3af63eb28a62 from=translated src=- shape=86cd7cc9 vocab=f0806206
-/
lemma definedBy_with_axiomK (defines : C.DefinedBy Γ) :
    DefinedBy C (insert (Axioms.K (.atom 0) (.atom 1)) Γ) := by
  convert FiniteFrameClass.definedBy_inter AllFiniteFrameClass
      {Axioms.K (.atom 0) (.atom 1)} C Γ <;>
    simp [AllFiniteFrameClass, Set.singleton_union];

end FiniteFrameClass

end Kripke

end Modal
end LO
