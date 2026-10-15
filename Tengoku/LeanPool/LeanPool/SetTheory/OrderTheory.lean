/-
Copyright (c) 2026 Shuhao Song. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shuhao Song
-/
module

public import Tengoku

/-!
# Order-theoretic preliminaries

This module collects order-theoretic lemmas about infima and suprema in conditionally
complete lattices, in particular closure under bounded infima and suprema.
-/

@[expose] public section

open Function OrderDual Set

variable {α β : Type*} [ConditionallyCompleteLattice α] [ConditionallyCompleteLattice β]

/-- The `sInfClosed` declaration. -/
def sInfClosed (S : Set α) := ∀ s ⊆ S, s.Nonempty → BddBelow s → sInf s ∈ S
/-- The `sSupClosed` declaration. -/
def sSupClosed (S : Set α) := ∀ s ⊆ S, s.Nonempty → BddAbove s → sSup s ∈ S

/--
@isnad1 id=sinfclos.0h1v.s4.293a2e971e39 from=translated src=- shape=b8471119 vocab=4d704ca2
-/
lemma sInfClosed_top : sInfClosed (⊤ : Set α) := by simp [sInfClosed]
/--
@isnad1 id=sinfclos.0h2v.s4.25e6d5eb297c from=translated src=- shape=101348a6 vocab=23add86d
-/
lemma sInfClosed_Ici (x : α) : sInfClosed (Ici x) := fun _ hsub hne _ => le_csInf hne hsub
/--
@isnad1 id=sinfclos.0h1v.s4.416a7824fd52 from=translated src=- shape=b8471119 vocab=e3b5e16d
-/
lemma sInfClosed_bot : sInfClosed (⊥ : Set α) := by simp [sInfClosed]
/--
@isnad1 id=ssupclos.0h1v.s4.423a911e932a from=translated src=- shape=b8471119 vocab=7fa25db2
-/
lemma sSupClosed_top : sSupClosed (⊤ : Set α) := by simp [sSupClosed]
/--
@isnad1 id=ssupclos.0h2v.s4.72f039487ee2 from=translated src=- shape=101348a6 vocab=d526e880
-/
lemma sSupClosed_Iic (x : α) : sSupClosed (Iic x) := fun _ hsub hne _ => csSup_le hne hsub
/--
@isnad1 id=ssupclos.0h1v.s4.d7d6be7728a8 from=translated src=- shape=b8471119 vocab=d7508137
-/
lemma sSupClosed_bot : sSupClosed (⊥ : Set α) := by simp [sSupClosed]

/-- The `ContinuousOrderMap` type. -/
class ContinuousOrderMap (f : α → β) where
  monotone : Monotone f
  preimage_Ici_closed : ∀ x, sInfClosed (f ⁻¹' (Ici x))
  preimage_Iic_closed : ∀ x, sSupClosed (f ⁻¹' (Iic x))

/-- The `ContinuousOrderMapBounded` type. -/
class ContinuousOrderMapBounded (f : α → β) extends ContinuousOrderMap f where
  bounded_preimage_Ici : ∀ y, BddBelow (f ⁻¹' (Ici y))
  bounded_preimage_Iic : ∀ y, BddAbove (f ⁻¹' (Iic y))

namespace ContinuousOrderMap

variable (f : α → β) [ContinuousOrderMap f]
open ContinuousOrderMap

instance : ContinuousOrderMap (toDual ∘ f ∘ ofDual) where
  monotone := monotone.dual
  preimage_Ici_closed := preimage_Iic_closed (f := f)
  preimage_Iic_closed := preimage_Ici_closed (f := f)

variable {ι} [Nonempty ι] {s : Set α} {g : ι → α}

/--
@isnad1 id=eq.2h4v.s6.d15a58cc1314 from=translated src=- shape=344562aa vocab=b838ba83
-/
lemma map_sInf' (hne : s.Nonempty) (hbdd : BddBelow s) : f (sInf s) = sInf (f '' s) := by
  refine (IsGLB.csInf_eq ?_ (by simpa)).symm
  simpa only [
    IsGLB, IsGreatest, lowerBounds, mem_image, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂, mem_ofPred_eq, upperBounds
  ] using ⟨
    fun _ hs => monotone (csInf_le hbdd hs),
    fun y hy => preimage_Ici_closed _ _ hy hne hbdd
  ⟩

/--
@isnad1 id=eq.2h4v.s6.8bbd6b42f4ea from=translated src=- shape=3190ab55 vocab=e90ef3b2
-/
lemma map_sInf (hne : s.Nonempty) (hbdd : BddBelow s) : f (sInf s) = ⨅ x : s, f x := by
  rw [← sInf_image', ← map_sInf' f hne hbdd]

/--
@isnad1 id=eq.2h4v.s6.b5facc188537 from=translated src=- shape=344562aa vocab=cd7e71a7
-/
lemma map_sSup' (hne : s.Nonempty) (hbdd : BddAbove s) : f (sSup s) = sSup (f '' s) :=
  map_sInf' (toDual ∘ f ∘ ofDual) hne hbdd

/--
@isnad1 id=eq.2h4v.s6.ba770121a32c from=translated src=- shape=3190ab55 vocab=f5ab31e7
-/
lemma map_sSup (hne : s.Nonempty) (hbdd : BddAbove s) : f (sSup s) = ⨆ x : s, f x :=
  map_sInf (toDual ∘ f ∘ ofDual) hne hbdd

/--
@isnad1 id=eq.1h5v.s6.d20110a2e1f6 from=translated src=- shape=671554ad vocab=367c0d52
-/
lemma map_iInf (hbdd : BddBelow (range g)) : f (⨅ i, g i) = ⨅ i, f (g i) := by
  erw [← sInf_range, ← sInf_range,
    map_sInf' f (Set.range_nonempty_iff_nonempty.mpr (by infer_instance)) hbdd, range_comp]

/--
@isnad1 id=eq.1h5v.s6.2513fbdb6de7 from=translated src=- shape=671554ad vocab=c23212c3
-/
lemma map_iSup (hbdd : BddAbove (range g)) : f (⨆ i, g i) = ⨆ i, f (g i) :=
  map_iInf (toDual ∘ f ∘ ofDual) hbdd

end ContinuousOrderMap

namespace ContinuousOrderMapBounded

variable (f : α → β) {s : Set α}
open ContinuousOrderMapBounded ContinuousOrderMap

variable [ContinuousOrderMapBounded f]

instance : ContinuousOrderMapBounded (toDual ∘ f ∘ ofDual) where
  monotone := monotone
  bounded_preimage_Iic := bounded_preimage_Ici (f := f)
  bounded_preimage_Ici := bounded_preimage_Iic (f := f)
  preimage_Ici_closed := preimage_Iic_closed (f := f)
  preimage_Iic_closed := preimage_Ici_closed (f := f)

/--
@isnad1 id=iff.0h4v.s5.ab879b95a5b3 from=translated src=- shape=6d3543d6 vocab=4c374b0b
-/
lemma bddBelow_iff : BddBelow (f '' s) ↔ BddBelow s := by
  refine ⟨fun | ⟨y, hy⟩ => ?_, fun | ⟨x, hx⟩ => ?_⟩
  · contrapose! hy
    simp only [BddBelow, Set.Nonempty, lowerBounds, mem_ofPred_eq, not_exists, not_forall,
      exists_prop, mem_image, forall_exists_index, and_imp,
      forall_apply_eq_imp_iff₂] at hy ⊢
    obtain ⟨b, hb⟩ := bounded_preimage_Ici (f := f) y
    obtain ⟨x, hx⟩ := hy b
    exact ⟨x, hx.1, fun le => hx.2 (hb le)⟩
  · exact ⟨f x, by simpa [lowerBounds] using fun _ hs => monotone (hx hs)⟩

/--
@isnad1 id=iff.0h4v.s5.e014a4818e78 from=translated src=- shape=6d3543d6 vocab=7ed9de40
-/
lemma bddAbove_iff : BddAbove (f '' s) ↔ BddAbove s := bddBelow_iff (toDual ∘ f ∘ ofDual)

end ContinuousOrderMapBounded
