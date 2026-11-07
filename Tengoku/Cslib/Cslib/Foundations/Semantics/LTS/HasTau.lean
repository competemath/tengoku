/-
Copyright (c) 2026 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi
-/

module

public import Tengoku.Cslib.Cslib.Foundations.Semantics.LTS.Relation

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# LTS with a special "internal" transition `τ`.
-/

@[expose] public section

namespace Cslib

universe u v

/-- A type of transition labels that includes a special 'internal' transition `τ`.-/
class HasTau (Label : Type v) where
  /-- The internal transition label, also known as τ.-/
  τ : Label

/-- Checking whether an element is `τ` is decidable.-/
abbrev DecidableEqTau (α : Type*) [HasTau α] := ∀ a : α, Decidable (a = HasTau.τ)

namespace LTS

/-- Saturated τ-transition relation.-/
def τSTr [HasTau Label] (lts : LTS State Label) : State → State → Prop :=
  Relation.ReflTransGen (Tr.toRelation lts HasTau.τ)

/--
@isnad1 id=str.0h4v.s4.da9883178df5 from=translated src=- shape=3811a180 vocab=475f5cd9
-/
@[scoped grind .]
theorem τSTr.refl [HasTau Label] {lts : LTS State Label} : lts.τSTr s s :=
  Relation.ReflTransGen.refl

/-- Saturated transition relation.-/
inductive STr [HasTau Label] (lts : LTS State Label) : State → Label → State → Prop where
  | refl : lts.STr s HasTau.τ s
  | tr : lts.τSTr s1 s2 → lts.Tr s2 μ s3 → lts.τSTr s3 s4 → lts.STr s1 μ s4

/-- The `LTS` obtained by saturating the transition relation in `lts`.-/
@[scoped grind =]
def saturate [HasTau Label] (lts : LTS State Label) : LTS State Label where
  Tr := lts.STr

/--
@isnad1 id=eq.0h3v.s5.ec9fb7ac058c from=translated src=- shape=b74ec72c vocab=b11aef7a
-/
@[scoped grind _=_]
theorem saturate_tr_sTr [HasTau Label] {lts : LTS State Label} :
  lts.saturate.Tr = lts.STr := by rfl

/-- Any transition is also a saturated transition.
@isnad1 id=str.1h6v.s5.8139ee8de408 from=translated src=- shape=137ed1e7 vocab=97c99535
-/
theorem STr.single [HasTau Label] {lts : LTS State Label} :
    lts.Tr s μ s' → lts.STr s μ s' := by
  intro h
  apply STr.tr .refl h .refl

/--
@isnad1 id=le.0h3v.s5.eeaf12a89947 from=translated src=- shape=dec27a5b vocab=33f2d7be
-/
lemma tr_le_tr_saturate [HasTau Label] (lts : LTS State Label) : lts.Tr ≤ lts.saturate.Tr :=
  fun _ _ _ => STr.single

/-- STr transitions labeled by HasTau.τ are exactly the τSTr transitions.
@isnad1 id=iff.0h5v.s5.4f38e1457055 from=translated src=- shape=5a4e5c5a vocab=f10280f0
-/
theorem sTr_τSTr_iff [HasTau Label] (lts : LTS State Label) :
    lts.STr s HasTau.τ s' ↔ lts.τSTr s s' := by
  apply Iff.intro <;> intro h
  case mp =>
    cases h
    case refl => exact .refl
    case tr _ _ h1 h2 h3 =>
      exact (.trans h1 (.head h2 h3))
  case mpr =>
    cases h
    case refl => exact STr.refl
    case tail _ h1 h2 => exact STr.tr h1 h2 .refl

/-- Saturating an LTS does not change its saturated τ-transition relation.
@isnad1 id=eq.0h3v.s4.a3de0c0ac9d7 from=translated src=- shape=eb5947d9 vocab=01a203e2
-/
theorem saturate_τsTr_τSTr_iff [hHasTau : HasTau Label] (lts : LTS State Label) :
    lts.saturate.τSTr = lts.τSTr := by
  change Relation.ReflTransGen (fun s s' => lts.STr s HasTau.τ s') = _
  simp only [sTr_τSTr_iff]
  exact Relation.reflTransGen_eq_self (r := Relation.ReflTransGen _)

/-- Saturated transitions labelled by τ can be composed.
@isnad1 id=str.2h6v.s5.14f8f7c81b3c from=translated src=- shape=1df122e3 vocab=428e0cb9
-/
@[scoped grind .]
theorem STr.trans_τ
    [HasTau Label] {lts : LTS State Label}
    (h1 : lts.STr s1 HasTau.τ s2) (h2 : lts.STr s2 HasTau.τ s3) :
    lts.STr s1 HasTau.τ s3 := by
  rw [sTr_τSTr_iff _] at h1 h2
  rw [sTr_τSTr_iff _]
  apply Relation.ReflTransGen.trans h1 h2

/-- Saturated transitions can be composed.
@isnad1 id=str.3h8v.s5.72d07598876d from=translated src=- shape=3a856369 vocab=428e0cb9
-/
theorem STr.comp
    [HasTau Label] {lts : LTS State Label}
    (h1 : lts.STr s1 HasTau.τ s2)
    (h2 : lts.STr s2 μ s3)
    (h3 : lts.STr s3 HasTau.τ s4) :
  lts.STr s1 μ s4 := by
  rw [sTr_τSTr_iff _] at h1 h3
  cases h2
  case refl =>
    rw [sTr_τSTr_iff _]
    apply Relation.ReflTransGen.trans h1 h3
  case tr _ _ hτ1 htr hτ2 =>
    exact STr.tr (Relation.ReflTransGen.trans h1 hτ1) htr (Relation.ReflTransGen.trans hτ2 h3)

/-- In a saturated LTS, transitions and saturated transitions agree for every label.
@isnad1 id=eq.0h5v.s5.4ca12af06289 from=translated src=- shape=e2739cf7 vocab=b11aef7a
-/
theorem saturate_tr_saturate_sTr [hHasTau : HasTau Label] (lts : LTS State Label) :
    lts.saturate.Tr s μ = lts.saturate.STr s μ := by
  ext s'
  constructor
  · exact STr.single
  · intro h
    cases h with
    | refl => exact STr.refl
    | tr h₁ h₂ h₃ =>
      rw [saturate_τsTr_τSTr_iff] at h₁ h₃
      exact STr.comp ((sTr_τSTr_iff _).mpr h₁) h₂ ((sTr_τSTr_iff _).mpr h₃)

/-- In a saturated LTS, every state is in its τ-image.
@isnad1 id=mem.0h4v.s5.aedfcb116e24 from=translated src=- shape=a6e2b52b vocab=599e38f7
-/
@[scoped grind .]
lemma mem_saturate_image_τ [HasTau Label] (lts : LTS State Label) :
  s ∈ lts.saturate.image s HasTau.τ := STr.refl

/-- Monotonicity of `setImage` on `HasTau.τ`.
@isnad1 id=le.0h4v.s5.8384ee63ae29 from=translated src=- shape=10ef941f vocab=cc844613
-/
@[scoped grind .]
lemma subset_saturate_setImage_τ [HasTau Label] (lts : LTS State Label) :
    S ⊆ lts.saturate.setImage S HasTau.τ := by
  grind [setImage, Set.mem_iUnion]

/-- `setImage` preserves (non-)emptyness.
@isnad1 id=iff.0h4v.s5.d2d35c7de2ee from=translated src=- shape=59966189 vocab=4159854b
-/
@[scoped grind =]
lemma empty_saturate_setImage_τ [HasTau Label] (lts : LTS State Label) :
    lts.saturate.setImage S HasTau.τ = ∅ ↔ S = ∅:= by grind [Set.mem_of_mem_of_subset]

/-- The `τ`-closure of a set of states `S` is the set of states reachable by any state in `S`
by performing only `τ`-transitions.-/
def τClosure [HasTau Label] (lts : LTS State Label) (S : Set State) : Set State :=
  lts.saturate.setImage S HasTau.τ

/-- Monotonicity of `setImage` on `HasTau.τ`.
@isnad1 id=le.0h4v.s4.b6737a065733 from=translated src=- shape=4d201c69 vocab=7eb81c68
-/
@[scoped grind .]
lemma τClosure_subset [HasTau Label] (lts : LTS State Label) :
    S ⊆ lts.τClosure S := by grind [Set.mem_of_mem_of_subset, = τClosure]

/-- Saturated multistep transition relation.-/
inductive SMTr [HasTau Label] (lts : LTS State Label) : State → List Label → State → Prop where
  | τ : lts.STr s HasTau.τ s' → lts.SMTr s [] s'
  | stepL : lts.STr s1 μ s2 → lts.SMTr s2 μs s3 → lts.SMTr s1 (μ :: μs) s3

/-- The saturated multistep transition relation is reflexive.
@isnad1 id=smtr.0h4v.s4.2e81d2f2e8d1 from=translated src=- shape=e50fef91 vocab=55e8ca70
-/
@[scoped grind .]
theorem SMTr.refl [HasTau Label] (lts : LTS State Label) (s : State) :
    lts.SMTr s [] s := by grind [LTS.STr, LTS.SMTr]

open scoped LTS.STr

/-- The saturated multistep transition relation is transitive.
@isnad1 id=smtr.2h8v.s5.4d45b6b9f338 from=translated src=- shape=9e122e0e vocab=81089a48
-/
@[scoped grind .]
theorem SMTr.comp [HasTau Label] {lts : LTS State Label}
    (h₁ : lts.SMTr s₁ μs₁ s₂) (h₂ : lts.SMTr s₂ μs₂ s₃) : lts.SMTr s₁ (μs₁ ++ μs₂) s₃ := by
  induction h₁
  case τ s₁ s₂ htr =>
    cases h₂
    case τ htr' => grind [SMTr]
    case stepL _ _ _ μ s₂' μs hstr hmstr => exact stepL (htr.comp hstr STr.refl) hmstr
  case stepL s₁ μ s₁' μs s₂ hstr hmstr ih =>
    apply stepL hstr (ih h₂)

/-- A multistep transition implies a saturated multistep transition.
@isnad1 id=smtr.1h6v.s5.2263808ce0f2 from=translated src=- shape=698143a9 vocab=77bc02a2
-/
@[scoped grind .]
theorem SMTr.fromMTr [HasTau Label] {lts : LTS State Label}
    (h : lts.MTr s μs s') : lts.SMTr s μs s' := by
  induction μs generalizing s s'
  case nil => grind [LTS.STr, LTS.SMTr]
  case cons x xs ih =>
    cases h
    case stepL sb htr hmtr => exact SMTr.stepL (STr.single htr) (ih hmtr)

/--
@isnad1 id=iff.0h5v.s5.3e62a01bbd90 from=translated src=- shape=e91bfd37 vocab=93b9a10f
-/
@[scoped grind =]
theorem sMTr_τSTr_iff [HasTau Label] {lts : LTS State Label} :
    lts.τSTr s s' ↔ lts.SMTr s [] s' := by grind only [=_ sTr_τSTr_iff, SMTr]

/-- A saturated multistep transition with a nonempty label list implies a multistep transition.
@isnad1 id=iff.1h6v.s5.56aa0f9e0c45 from=translated src=- shape=615e8739 vocab=1fdd543e
-/
@[scoped grind =]
theorem saturate_mTr_sMTr_not_nil_iff [HasTau Label] {lts : LTS State Label}
    (hμs : μs ≠ []) : lts.saturate.MTr s μs s' ↔ lts.SMTr s μs s' := by
  induction μs generalizing s
  case nil => contradiction
  case cons x xs ih =>
    apply Iff.intro <;> intro h
    case mp =>
      cases h
      case stepL sb htr hmtr =>
        cases xs with
        | nil =>
          cases hmtr
          apply LTS.SMTr.stepL htr (by grind only [SMTr.fromMTr, MTr.refl])
        | cons x' xs' =>
          exact LTS.SMTr.stepL htr ((ih (by simp)).mp hmtr)
    case mpr =>
      cases h
      case stepL sb htr hmtr =>
        cases xs with
        | nil =>
          cases hmtr
          case τ h_τ =>
            exact LTS.MTr.stepL
              (LTS.STr.comp LTS.STr.refl htr h_τ)
              LTS.MTr.refl
        | cons x' xs' =>
          exact LTS.MTr.stepL htr ((ih (by simp)).mpr hmtr)

end LTS

end Cslib
