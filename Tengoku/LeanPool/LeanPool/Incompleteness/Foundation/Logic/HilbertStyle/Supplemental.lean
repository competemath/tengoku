/-
Copyright (c) 2026 Palalansoukî. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Palalansoukî
-/
module

public import Tengoku.LeanPool.LeanPool.Incompleteness.Foundation.Logic.HilbertStyle.Context

/-! # Supplemental -/

@[expose] public section

namespace LO
namespace Entailment

variable {F : Type*} [LogicalConnective F] [DecidableEq F]
         {S : Type*} [Entailment F S]
         {𝓢 : S} [Entailment.Minimal 𝓢]
         {φ ψ χ : F}
         {Γ Δ : List F}

open NegationEquiv
open FiniteContext
open List

/-- Imported declaration from the Incompleteness formalization. -/
def negMdp (hnp : 𝓢 ⊢ ∼φ) (hn : 𝓢 ⊢ φ) : 𝓢 ⊢ ⊥ := (negEquiv'.mp hnp) ⨀ hn
-- infixl:90 "⨀" => negMdp

omit [DecidableEq F] in
lemma negMdp! (hnp : 𝓢 ⊢! ∼φ) (hn : 𝓢 ⊢! φ) : 𝓢 ⊢! ⊥ := by
  classical
  exact ⟨negMdp hnp.some hn.some⟩
-- infixl:90 "⨀" => negMdp!

/-- Imported declaration from the Incompleteness formalization. -/
def dneOr [HasAxiomDNE 𝓢] (d : 𝓢 ⊢ ∼∼φ ⋎ ∼∼ψ) :
    𝓢 ⊢ φ ⋎ ψ :=
  or₃''' (impTrans'' dne or₁) (impTrans'' dne or₂) d

/-- Imported declaration from the Incompleteness formalization. -/
def implyLeftOr' (h : 𝓢 ⊢ φ ==> χ) : 𝓢 ⊢ φ ==> (χ ⋎ ψ) :=
  deduct' <| or₁' <| deductInv <| of h

/-- Imported declaration from the Incompleteness formalization. -/
def implyRightOr' (h : 𝓢 ⊢ ψ ==> χ) : 𝓢 ⊢ ψ ==> (φ ⋎ χ) :=
  deduct' <| or₂' <| deductInv <| of h

/-- Imported declaration from the Incompleteness formalization. -/
def orComm : 𝓢 ⊢ φ ⋎ ψ ==> ψ ⋎ φ :=
  deduct' <| or₃''' or₂ or₁ FiniteContext.id

/-- Imported declaration from the Incompleteness formalization. -/
def orComm' (h : 𝓢 ⊢ φ ⋎ ψ) : 𝓢 ⊢ ψ ⋎ φ := orComm ⨀ h

/-- Imported declaration from the Incompleteness formalization. -/
def andReplaceLeft' (hc : 𝓢 ⊢ φ ⋏ ψ) (h : 𝓢 ⊢ φ ==> χ) :
    𝓢 ⊢ χ ⋏ ψ :=
  and₃' (h ⨀ and₁' hc) (and₂' hc)

/-- Imported declaration from the Incompleteness formalization. -/
def andReplaceLeft (h : 𝓢 ⊢ φ ==> χ) : 𝓢 ⊢ φ ⋏ ψ ==> χ ⋏ ψ :=
  deduct' <| andReplaceLeft' FiniteContext.id (of h)

/-- Imported declaration from the Incompleteness formalization. -/
def andReplaceRight' (hc : 𝓢 ⊢ φ ⋏ ψ) (h : 𝓢 ⊢ ψ ==> χ) :
    𝓢 ⊢ φ ⋏ χ :=
  and₃' (and₁' hc) (h ⨀ and₂' hc)
omit [DecidableEq F] in
lemma andReplaceRight'! (hc : 𝓢 ⊢! φ ⋏ ψ) (h : 𝓢 ⊢! ψ ==> χ) : 𝓢 ⊢! φ ⋏ χ := by
  classical
  exact ⟨andReplaceRight' hc.some h.some⟩

/-- Imported declaration from the Incompleteness formalization. -/
def andReplaceRight (h : 𝓢 ⊢ ψ ==> χ) : 𝓢 ⊢ φ ⋏ ψ ==> φ ⋏ χ :=
  deduct' <| andReplaceRight' FiniteContext.id (of h)

/-- Imported declaration from the Incompleteness formalization. -/
def andReplace' (hc : 𝓢 ⊢ φ ⋏ ψ) (h₁ : 𝓢 ⊢ φ ==> χ) (h₂ : 𝓢 ⊢ ψ ==> s) :
    𝓢 ⊢ χ ⋏ s :=
  andReplaceRight' (andReplaceLeft' hc h₁) h₂

/-- Imported declaration from the Incompleteness formalization. -/
def andReplace (h₁ : 𝓢 ⊢ φ ==> χ) (h₂ : 𝓢 ⊢ ψ ==> s) : 𝓢 ⊢ φ ⋏ ψ ==> χ ⋏ s :=
  deduct' <| andReplace' FiniteContext.id (of h₁) (of h₂)

/-- Imported declaration from the Incompleteness formalization. -/
def orReplaceLeft' (hc : 𝓢 ⊢ φ ⋎ ψ) (hp : 𝓢 ⊢ φ ==> χ) :
    𝓢 ⊢ χ ⋎ ψ :=
  or₃''' (impTrans'' hp or₁) (or₂) hc

/-- Imported declaration from the Incompleteness formalization. -/
def orReplaceLeft (hp : 𝓢 ⊢ φ ==> χ) : 𝓢 ⊢ φ ⋎ ψ ==> χ ⋎ ψ :=
  deduct' <| orReplaceLeft' FiniteContext.id (of hp)

/-- Imported declaration from the Incompleteness formalization. -/
def orReplaceRight' (hc : 𝓢 ⊢ φ ⋎ ψ) (hq : 𝓢 ⊢ ψ ==> χ) :
    𝓢 ⊢ φ ⋎ χ :=
  or₃''' (or₁) (impTrans'' hq or₂) hc

/-- Imported declaration from the Incompleteness formalization. -/
def orReplaceRight (hq : 𝓢 ⊢ ψ ==> χ) : 𝓢 ⊢ φ ⋎ ψ ==> φ ⋎ χ :=
  deduct' <| orReplaceRight' FiniteContext.id (of hq)
omit [DecidableEq F] in
lemma «or_replace_right!» (hq : 𝓢 ⊢! ψ ==> χ) : 𝓢 ⊢! φ ⋎ ψ ==> φ ⋎ χ := by
  classical
  exact ⟨orReplaceRight hq.some⟩

/-- Imported declaration from the Incompleteness formalization. -/
def orReplace' (h : 𝓢 ⊢ φ₁ ⋎ ψ₁) (hp : 𝓢 ⊢ φ₁ ==> φ₂) (hq : 𝓢 ⊢ ψ₁ ==> ψ₂) :
    𝓢 ⊢ φ₂ ⋎ ψ₂ :=
  orReplaceRight' (orReplaceLeft' h hp) hq

/-- Imported declaration from the Incompleteness formalization. -/
def orReplace (hp : 𝓢 ⊢ φ₁ ==> φ₂) (hq : 𝓢 ⊢ ψ₁ ==> ψ₂) : 𝓢 ⊢ φ₁ ⋎ ψ₁ ==> φ₂ ⋎ ψ₂ :=
  deduct' <| orReplace' FiniteContext.id (of hp) (of hq)

/-- Imported declaration from the Incompleteness formalization. -/
def orReplaceIff (hp : 𝓢 ⊢ φ₁ <=> φ₂) (hq : 𝓢 ⊢ ψ₁ <=> ψ₂) : 𝓢 ⊢ φ₁ ⋎ ψ₁ <=> φ₂ ⋎ ψ₂ :=
  iffIntro (orReplace (and₁' hp) (and₁' hq)) (orReplace (and₂' hp) (and₂' hq))

/-- Imported declaration from the Incompleteness formalization. -/
def andReplaceIff (hp : 𝓢 ⊢ φ₁ <=> φ₂) (hq : 𝓢 ⊢ ψ₁ <=> ψ₂) : 𝓢 ⊢ φ₁ ⋏ ψ₁ <=> φ₂ ⋏ ψ₂ :=
  iffIntro (andReplace (and₁' hp) (and₁' hq)) (andReplace (and₂' hp) (and₂' hq))

/-- Imported declaration from the Incompleteness formalization. -/
def impReplaceIff (hp : 𝓢 ⊢ φ₁ <=> φ₂) (hq : 𝓢 ⊢ ψ₁ <=> ψ₂) : 𝓢 ⊢ (φ₁ ==> ψ₁) <=> (φ₂ ==> ψ₂) := by
  apply iffIntro;
  · apply deduct'; exact impTrans'' (of <| and₂' hp) <| impTrans'' (FiniteContext.id) (of <|
      and₁' hq);
  · apply deduct'; exact impTrans'' (of <| and₁' hp) <| impTrans'' (FiniteContext.id) (of <|
      and₂' hq);
omit [DecidableEq F] in
lemma «imp_replace_iff!» (hp : 𝓢 ⊢! φ₁ <=> φ₂) (hq : 𝓢 ⊢! ψ₁ <=> ψ₂) :
    𝓢 ⊢! (φ₁ ==> ψ₁) <=> (φ₂ ==> ψ₂) := by
  classical
  exact ⟨impReplaceIff hp.some hq.some⟩

/-- Imported declaration from the Incompleteness formalization. -/
def falsumDNE : 𝓢 ⊢ ∼∼⊥ ==> ⊥ := by
  apply deduct'
  have d₁ : [∼∼⊥] ⊢[𝓢] ∼⊥ ==> ⊥ := negEquiv'.mp byAxm₀
  have d₂ : [∼∼⊥] ⊢[𝓢] ∼⊥ := negEquiv'.mpr (impId ⊥)
  exact d₁ ⨀ d₂

section «lp_section_1»

end «lp_section_1»

/-- Imported declaration from the Incompleteness formalization. -/
def implyLeftReplace (h : 𝓢 ⊢ ψ ==> φ) : 𝓢 ⊢ (φ ==> χ) ==> (ψ ==> χ) :=
  deduct' <| impTrans'' (of h) id
omit [DecidableEq F] in
lemma «replace_imply_left!» (h : 𝓢 ⊢! ψ ==> φ) :
    𝓢 ⊢! (φ ==> χ) ==> (ψ ==> χ) := by
  classical
  exact ⟨implyLeftReplace h.some⟩

/-- Imported declaration from the Incompleteness formalization. -/
def dhypImp' (h : 𝓢 ⊢ φ ==> ψ) : 𝓢 ⊢ (χ ==> φ) ==> (χ ==> ψ) := imply₂ ⨀ (imply₁' h)
omit [DecidableEq F] in
lemma dhypImp'! (h : 𝓢 ⊢! φ ==> ψ) : 𝓢 ⊢! (χ ==> φ) ==> (χ ==> ψ) := by
  classical
  exact ⟨dhypImp' h.some⟩

/-- Imported declaration from the Incompleteness formalization. -/
def introFalsumOfAnd' (h : 𝓢 ⊢ φ ⋏ ∼φ) : 𝓢 ⊢ ⊥ := (negEquiv'.mp <| and₂' h) ⨀ (and₁' h)
omit [DecidableEq F] in
lemma «intro_falsum_of_and'!» (h : 𝓢 ⊢! φ ⋏ ∼φ) : 𝓢 ⊢! ⊥ := by
  classical
  exact ⟨introFalsumOfAnd' h.some⟩
/-- Law of contradiction -/
alias lac'! := intro_falsum_of_and'!

/-- Imported declaration from the Incompleteness formalization. -/
def introFalsumOfAnd : 𝓢 ⊢ φ ⋏ ∼φ ==> ⊥ :=
  deduct' <| introFalsumOfAnd' (φ := φ) FiniteContext.id
omit [DecidableEq F] in
@[simp] lemma «intro_bot_of_and!» : 𝓢 ⊢! φ ⋏ ∼φ ==> ⊥ := by
  classical
  exact ⟨introFalsumOfAnd⟩
/-- Law of contradiction -/
alias lac! := intro_bot_of_and!

/-- Imported declaration from the Incompleteness formalization. -/
def andImplyAndOfImply {φ ψ φ' ψ' : F} (bp : 𝓢 ⊢ φ ==> φ') (bq : 𝓢 ⊢ ψ ==> ψ') :
    𝓢 ⊢ φ ⋏ ψ ==> φ' ⋏ ψ' :=
  deduct' <| andIntro
    (deductInv' <| impTrans'' and₁ bp)
    (deductInv' <| impTrans'' and₂ bq)

/-- Imported declaration from the Incompleteness formalization. -/
def andIffAndOfIff {φ ψ φ' ψ' : F} (bp : 𝓢 ⊢ φ <=> φ') (bq : 𝓢 ⊢ ψ <=> ψ') :
    𝓢 ⊢ φ ⋏ ψ <=> φ' ⋏ ψ' :=
  iffIntro (andImplyAndOfImply (andLeft bp) (andLeft bq)) (andImplyAndOfImply (andRight bp)
    (andRight bq))

section «lp_section_2»

omit [DecidableEq F] in
instance [HasAxiomLEM 𝓢] : HasAxiomWeakLEM 𝓢 where
  wlem φ := by
    classical
    exact lem (φ := ∼φ);

end «lp_section_2»

/-- Imported declaration from the Incompleteness formalization. -/
def conjIffConj : (Γ : List F) → 𝓢 ⊢ ⋀Γ <=> Γ.conj
  | []          => iffId ⊤
  | [_]         => iffIntro (deduct' <| andIntro FiniteContext.id verum) and₁
  | φ :: ψ :: Γ => andIffAndOfIff (iffId φ) (conjIffConj (ψ :: Γ))
omit [DecidableEq F] in
@[simp] lemma «conjIffConj!» : 𝓢 ⊢! ⋀Γ <=> Γ.conj := by
  classical
  exact ⟨conjIffConj Γ⟩

section «lp_section_3»

end «lp_section_3»

section «lp_section_4»

@[simp]
lemma forthback_disj_remove [HasAxiomEFQ 𝓢] : 𝓢 ⊢! ⋁Γ ==> φ ⋎ ⋁(Γ.remove φ) := by
  induction Γ using List.induction_with_singleton with
  | hnil => simp;
  | hsingle ψ =>
    simp only [disj₂_singleton];
    by_cases h: ψ = φ;
    · subst_vars; simp;
    · simp [(List.remove_singleton_of_ne h)];
  | hcons ψ Γ h ih =>
    simp_all only [ne_eq, not_false_eq_true, disj₂_cons_nonempty]
    by_cases hpq : ψ = φ;
    · simp_all only [List.remove_cons_self]; exact or₃''! or₁! ih;
    · rw [List.remove_cons_of_ne Γ hpq];
      by_cases hqΓ : Γ.remove φ = [];
      · simp_all only [disj₂_nil, disj₂_singleton]
        exact or₃''! or₂! (imp_trans''! ih <| or_replace_right! efq!);
      · simp_all only [ne_eq, not_false_eq_true, disj₂_cons_nonempty]
        exact or₃''! (imp_trans''! or₁! or₂!) (imp_trans''! ih (or_replace_right! or₂!));

end «lp_section_4»

section «lp_section_5»

variable [HasAxiomEFQ 𝓢]

omit [DecidableEq F] in
lemma inconsistent_of_provable_of_unprovable {φ : F}
    (hp : 𝓢 ⊢! φ) (hn : 𝓢 ⊢! ∼φ) : Inconsistent 𝓢 := by
  classical
  have : 𝓢 ⊢! φ ==> ⊥ := negEquiv'!.mp hn
  intro ψ; exact efq! ⨀ (this ⨀ hp)

end «lp_section_5»

end Entailment
end LO
