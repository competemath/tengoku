/-
Copyright (c) 2026 Palalansoukî. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Palalansoukî
-/
module

public import Tengoku.LeanPool.LeanPool.Incompleteness.Foundation.Modal.Entailment.Basic
public import Tengoku.LeanPool.LeanPool.Incompleteness.Foundation.Logic.HilbertStyle.Supplemental

/-! # K -/

@[expose] public section

namespace LO
namespace Entailment

open FiniteContext

variable {S F : Type*} [BasicModalLogicalConnective F] [DecidableEq F] [Entailment F S]
variable {𝓢 : S} [Entailment.K 𝓢]

/-- Imported declaration from the Incompleteness formalization. -/
def multiboxAxiomK : 𝓢 ⊢ □^[n](φ ==> ψ) ==> □^[n]φ ==> □^[n]ψ := by
  induction n with
  | zero => simp only [Function.iterate_zero, id_eq]; apply impId;
  | succ n ih => simpa using impTrans'' (axiomK' <| nec ih) (by apply axiomK);
omit [DecidableEq F] in @[simp] lemma multiboxAxiomK! :
    𝓢 ⊢! □^[n](φ ==> ψ) ==> □^[n]φ ==> □^[n]ψ :=
  ⟨multiboxAxiomK⟩

/-- Imported declaration from the Incompleteness formalization. -/
def multiboxAxiomK' (h : 𝓢 ⊢ □^[n](φ ==> ψ)) : 𝓢 ⊢ □^[n]φ ==> □^[n]ψ := multiboxAxiomK ⨀ h
omit [DecidableEq F] in @[simp] lemma multiboxAxiomK'! (h :
    𝓢 ⊢! □^[n](φ ==> ψ)) : 𝓢 ⊢! □^[n]φ ==> □^[n]ψ :=
  ⟨multiboxAxiomK' h.some⟩

alias multiboxedImplyDistribute := multiboxAxiomK'
alias multiboxed_imply_distribute! := multiboxAxiomK'!

/-- Imported declaration from the Incompleteness formalization. -/
def boxIff' (h : 𝓢 ⊢ φ <=> ψ) : 𝓢 ⊢ (□φ <=> □ψ) :=
  iffIntro (axiomK' <| nec <| and₁' h) (axiomK' <| nec <| and₂' h)
omit [DecidableEq F] in @[simp] lemma box_iff! (h : 𝓢 ⊢! φ <=> ψ) : 𝓢 ⊢! □φ <=> □ψ :=
  ⟨boxIff' h.some⟩

/-- Imported declaration from the Incompleteness formalization. -/
def multiboxIff' (h : 𝓢 ⊢ φ <=> ψ) : 𝓢 ⊢ □^[n]φ <=> □^[n]ψ := by
  induction n with
  | zero => simpa;
  | succ n ih => simpa using boxIff' ih;
omit [DecidableEq F] in @[simp] lemma multibox_iff! (h : 𝓢 ⊢! φ <=> ψ) : 𝓢 ⊢! □^[n]φ <=> □^[n]ψ :=
  ⟨multiboxIff' h.some⟩

/-- Imported declaration from the Incompleteness formalization. -/
def diaDualityMp : 𝓢 ⊢ ◇φ ==> ∼(□(∼φ)) := and₁' diaDuality
omit [DecidableEq F] in @[simp] lemma diaDualityMp! : 𝓢 ⊢! ◇φ ==> ∼(□(∼φ)) := by
  classical
  exact ⟨diaDualityMp⟩

/-- Imported declaration from the Incompleteness formalization. -/
def diaDualityMpr : 𝓢 ⊢ ∼(□(∼φ)) ==> ◇φ := and₂' diaDuality
omit [DecidableEq F] in @[simp] lemma diaDualityMpr! : 𝓢 ⊢! ∼(□(∼φ)) ==> ◇φ := by
  classical
  exact ⟨diaDualityMpr⟩

/-- Imported declaration from the Incompleteness formalization. -/
def _root_.LO.Entailment.diaDuality'.mp (h : 𝓢 ⊢ ◇φ) : 𝓢 ⊢ ∼(□(∼φ)) := (and₁' diaDuality) ⨀ h
/-- Imported declaration from the Incompleteness formalization. -/
def _root_.LO.Entailment.diaDuality'.mpr (h : 𝓢 ⊢ ∼(□(∼φ))) : 𝓢 ⊢ ◇φ := (and₂' diaDuality) ⨀ h

/-- Imported declaration from the Incompleteness formalization. -/
def boxDne : 𝓢 ⊢ □(∼∼φ) ==> □φ := axiomK' <| nec dne
omit [DecidableEq F] in @[simp] lemma boxDne! : 𝓢 ⊢! □(∼∼φ) ==> □φ := by
  classical
  exact ⟨boxDne⟩

/-- Imported declaration from the Incompleteness formalization. -/
def boxDne' (h : 𝓢 ⊢ □(∼∼φ)) : 𝓢 ⊢ □φ := boxDne ⨀ h
omit [DecidableEq F] in lemma boxDne'! (h : 𝓢 ⊢! □(∼∼φ)) : 𝓢 ⊢! □φ := by
  classical
  exact ⟨boxDne' h.some⟩

/-- Imported declaration from the Incompleteness formalization. -/
def multiboxverum : 𝓢 ⊢ (□^[n]⊤ : F) := multinec verum
omit [DecidableEq F] in @[simp] lemma multiboxverum! : 𝓢 ⊢! (□^[n]⊤ : F) := by
  classical
  exact ⟨multiboxverum⟩

/-- Imported declaration from the Incompleteness formalization. -/
def boxverum : 𝓢 ⊢ (□⊤ : F) := multiboxverum (n := 1)
omit [DecidableEq F] in @[simp] lemma boxverum! : 𝓢 ⊢! (□⊤ : F) := by
  classical
  exact ⟨boxverum⟩

/-- Imported declaration from the Incompleteness formalization. -/
def boxdotverum : 𝓢 ⊢ (⊡⊤ : F) := andIntro verum boxverum
omit [DecidableEq F] in @[simp] lemma boxdotverum! : 𝓢 ⊢! (⊡⊤ : F) := by
  classical
  exact ⟨boxdotverum⟩

/-- Imported declaration from the Incompleteness formalization. -/
def implyMultiboxDistribute' (h : 𝓢 ⊢ φ ==> ψ) :
    𝓢 ⊢ □^[n]φ ==> □^[n]ψ :=
  multiboxAxiomK' <| multinec h
omit [DecidableEq F] in lemma imply_multibox_distribute'! (h :
    𝓢 ⊢! φ ==> ψ) : 𝓢 ⊢! □^[n]φ ==> □^[n]ψ :=
  ⟨implyMultiboxDistribute' h.some⟩

/-- Imported declaration from the Incompleteness formalization. -/
def implyBoxDistribute' (h : 𝓢 ⊢ φ ==> ψ) : 𝓢 ⊢ □φ ==> □ψ := implyMultiboxDistribute' (n := 1) h
omit [DecidableEq F] in lemma imply_box_distribute'! (h : 𝓢 ⊢! φ ==> ψ) : 𝓢 ⊢! □φ ==> □ψ :=
  ⟨implyBoxDistribute' h.some⟩

/-- Imported declaration from the Incompleteness formalization. -/
def collectMultiboxAnd : 𝓢 ⊢ □^[n]φ ⋏ □^[n]ψ ==> □^[n](φ ⋏ ψ) := by
  have d₁ : 𝓢 ⊢ □^[n]φ ==> □^[n](ψ ==> φ ⋏ ψ) := implyMultiboxDistribute' and₃;
  have d₂ : 𝓢 ⊢ □^[n](ψ ==> φ ⋏ ψ) ==> (□^[n]ψ ==> □^[n](φ ⋏ ψ)) := multiboxAxiomK;
  exact (and₂' (andImplyIffImplyImply _ _ _)) ⨀ (impTrans'' d₁ d₂);
omit [DecidableEq F] in @[simp] lemma collectMultiboxAnd! :
    𝓢 ⊢! □^[n]φ ⋏ □^[n]ψ ==> □^[n](φ ⋏ ψ) :=
  ⟨collectMultiboxAnd⟩

/-- Imported declaration from the Incompleteness formalization. -/
def collectBoxAnd : 𝓢 ⊢ □φ ⋏ □ψ ==> □(φ ⋏ ψ) := collectMultiboxAnd (n := 1)
omit [DecidableEq F] in @[simp] lemma collectBoxAnd! : 𝓢 ⊢! □φ ⋏ □ψ ==> □(φ ⋏ ψ) := ⟨collectBoxAnd⟩

/-- Imported declaration from the Incompleteness formalization. -/
def collectMultiboxAnd' (h : 𝓢 ⊢ □^[n]φ ⋏ □^[n]ψ) : 𝓢 ⊢ □^[n](φ ⋏ ψ) := collectMultiboxAnd ⨀ h
omit [DecidableEq F] in lemma collectMultiboxAnd'! (h :
    𝓢 ⊢! □^[n]φ ⋏ □^[n]ψ) : 𝓢 ⊢! □^[n](φ ⋏ ψ) :=
  ⟨collectMultiboxAnd' h.some⟩

/-- Imported declaration from the Incompleteness formalization. -/
def collectBoxAnd' (h : 𝓢 ⊢ □φ ⋏ □ψ) : 𝓢 ⊢ □(φ ⋏ ψ) := collectMultiboxAnd' (n := 1) h
omit [DecidableEq F] in lemma collectBoxAnd'! (h : 𝓢 ⊢! □φ ⋏ □ψ) : 𝓢 ⊢! □(φ ⋏ ψ) :=
  ⟨collectBoxAnd' h.some⟩

/-- Imported declaration from the Incompleteness formalization. -/
def collectMultiboxOr :
    𝓢 ⊢ □^[n]φ ⋎ □^[n]ψ ==> □^[n](φ ⋎ ψ) :=
  or₃'' (multiboxAxiomK' <| multinec or₁) (multiboxAxiomK' <| multinec or₂)
omit [DecidableEq F] in @[simp] lemma collectMultiboxOr! :
    𝓢 ⊢! □^[n]φ ⋎ □^[n]ψ ==> □^[n](φ ⋎ ψ) :=
  ⟨collectMultiboxOr⟩

/-- Imported declaration from the Incompleteness formalization. -/
def collectBoxOr : 𝓢 ⊢ □φ ⋎ □ψ ==> □(φ ⋎ ψ) := collectMultiboxOr (n := 1)
omit [DecidableEq F] in @[simp] lemma collectBoxOr! : 𝓢 ⊢! □φ ⋎ □ψ ==> □(φ ⋎ ψ) := ⟨collectBoxOr⟩

/-- Imported declaration from the Incompleteness formalization. -/
def collectMultiboxOr' (h : 𝓢 ⊢ □^[n]φ ⋎ □^[n]ψ) : 𝓢 ⊢ □^[n](φ ⋎ ψ) := collectMultiboxOr ⨀ h
omit [DecidableEq F] in lemma collectMultiboxOr'! (h :
    𝓢 ⊢! □^[n]φ ⋎ □^[n]ψ) : 𝓢 ⊢! □^[n](φ ⋎ ψ) :=
  ⟨collectMultiboxOr' h.some⟩

/-- Imported declaration from the Incompleteness formalization. -/
def collectBoxOr' (h : 𝓢 ⊢ □φ ⋎ □ψ) : 𝓢 ⊢ □(φ ⋎ ψ) := collectMultiboxOr' (n := 1) h
omit [DecidableEq F] in lemma collectBoxOr'! (h : 𝓢 ⊢! □φ ⋎ □ψ) : 𝓢 ⊢! □(φ ⋎ ψ) :=
  ⟨collectBoxOr' h.some⟩

/-- Imported declaration from the Incompleteness formalization. -/
def boxdotAxiomT : 𝓢 ⊢ ⊡φ ==> φ := and₁
omit [DecidableEq F] in @[simp 1100] lemma boxdot_axiomT! : 𝓢 ⊢! ⊡φ ==> φ := by
  simp_all

/-- Imported declaration from the Incompleteness formalization. -/
def boxdotNec (d : 𝓢 ⊢ φ) : 𝓢 ⊢ ⊡φ := and₃' d (nec d)
omit [DecidableEq F] in lemma boxdot_nec! (d : 𝓢 ⊢! φ) : 𝓢 ⊢! ⊡φ := by
  classical
  exact ⟨boxdotNec d.some⟩

/-- Imported declaration from the Incompleteness formalization. -/
def boxdotBox : 𝓢 ⊢ ⊡φ ==> □φ := and₂
omit [DecidableEq F] in lemma boxdot_box! : 𝓢 ⊢! ⊡φ ==> □φ := by
  simp_all

namespace Context

variable {X : Set F}

end Context

end Entailment
end LO
