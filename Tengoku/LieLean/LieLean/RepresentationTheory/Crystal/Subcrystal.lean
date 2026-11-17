/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import Tengoku.LieLean.LieLean.RepresentationTheory.Crystal.Character

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Subcrystals and disjoint unions of crystals

## Main definitions

* `Crystal.restrict`: the crystal structure on a subset `S ⊆ B` stable under all `ẽᵢ` and `f̃ᵢ`
  (e.g. a union of connected components).
* `Crystal.restrictHom`: the inclusion `S → B`, a strict morphism.
* `Crystal.closure`: the smallest stable subset containing a given set (for a singleton `{b}`,
  the connected component of `b`).
* `Crystal.sum`: the disjoint union `B₁ ⊔ B₂` of two crystals.

## Main results

* `Crystal.IsSeminormal.restrict`, `Crystal.IsSeminormal.sum`: seminormality is inherited.
* `Crystal.character_sum`: `ch (B₁ ⊔ B₂) = ch B₁ + ch B₂`.

## References

* [Kas] M. Kashiwara, *On crystal bases*, CMS Conf. Proc. 16 (1995).
-/
namespace Tengoku.LieLean end Tengoku.LieLean open Tengoku.LieLean
namespace Tengoku.LieLean.Crystal

variable {ι X : Type*} [AddCommGroup X] {D : CartanDatum ι X} {B B₁ B₂ : Type*}
  (C : Crystal D B)

/-! ### Subcrystals -/

/-- A subset of a crystal stable under all the Kashiwara operators `ẽᵢ` and `f̃ᵢ`.-/
structure IsStable (S : Set B) : Prop where
  e_mem : ∀ i b b', b ∈ S → C.e i b = some b' → b' ∈ S
  f_mem : ∀ i b b', b ∈ S → C.f i b = some b' → b' ∈ S

variable {C} {S : Set B}

/--
@isnad1 id=isstable.1h6v.s5.35a2ec365b26 from=translated src=- shape=bb49c964 vocab=cb61cbd4
-/
lemma isStable_sInter {𝒮 : Set (Set B)} (h𝒮 : ∀ S ∈ 𝒮, C.IsStable S) : C.IsStable (⋂₀ 𝒮) where
  e_mem i b b' hb h := Set.mem_sInter.mpr fun S hS ↦
    (h𝒮 S hS).e_mem i b b' (Set.mem_sInter.mp hb S hS) h
  f_mem i b b' hb h := Set.mem_sInter.mpr fun S hS ↦
    (h𝒮 S hS).f_mem i b b' (Set.mem_sInter.mp hb S hS) h

variable (C) in
/-- The smallest subset of `B` containing `s` and stable under all `ẽᵢ` and `f̃ᵢ` (for `s = {b}`,
the connected component of `b`).-/
def closure (s : Set B) : Set B := ⋂₀ {S | C.IsStable S ∧ s ⊆ S}

/--
@isnad1 id=isstable.0h6v.s5.6aed47d0904c from=translated src=- shape=58a202e6 vocab=959dde75
-/
lemma isStable_closure (s : Set B) : C.IsStable (C.closure s) :=
  isStable_sInter fun _ hS ↦ hS.1

/--
@isnad1 id=le.0h6v.s5.f67a4956930c from=translated src=- shape=88fc5a0e vocab=002cddd6
-/
lemma subset_closure (s : Set B) : s ⊆ C.closure s :=
  Set.subset_sInter fun _ hS ↦ hS.2

/--
@isnad1 id=le.2h7v.s5.cdb73084c2c4 from=translated src=- shape=c122febd vocab=91a111b3
-/
lemma closure_subset {s : Set B} (hS : C.IsStable S) (hsS : s ⊆ S) : C.closure s ⊆ S :=
  Set.sInter_subset_of_mem ⟨hS, hsS⟩

/-- The crystal structure on a subset `S` of a crystal which is stable under all `ẽᵢ` and
`f̃ᵢ`.-/
def restrict (hS : C.IsStable S) : Crystal D S where
  wt b := C.wt b
  ε i b := C.ε i b
  φ i b := C.φ i b
  e i b := (C.e i b).pmap (fun b' h ↦ ⟨b', h⟩) fun b' h ↦ hS.e_mem i b b' b.2 h
  f i b := (C.f i b).pmap (fun b' h ↦ ⟨b', h⟩) fun b' h ↦ hS.f_mem i b b' b.2 h
  φ_eq i b := C.φ_eq i b
  f_eq_some_iff i b b' := by
    simp only [Option.pmap_eq_some_iff]
    constructor
    · rintro ⟨c, hc, hfc, rfl⟩
      exact ⟨b, b.2, (C.f_eq_some_iff i b c).mp hfc, rfl⟩
    · rintro ⟨c, hc, hec, rfl⟩
      exact ⟨b', b'.2, (C.f_eq_some_iff i c b').mpr hec, rfl⟩
  wt_e i b b' h := by
    obtain ⟨c, -, hc, rfl⟩ := Option.pmap_eq_some_iff.mp h
    exact C.wt_e i b c hc
  ε_e i b b' h := by
    obtain ⟨c, -, hc, rfl⟩ := Option.pmap_eq_some_iff.mp h
    exact C.ε_e i b c hc
  e_eq_none_of_φ_eq_bot i b h := by
    simp [C.e_eq_none_of_φ_eq_bot i b h]

/--
@isnad1 id=eq.1h7v.s6.522f710ed47b from=translated src=- shape=4cb00223 vocab=ddcf4075
-/
@[simp] lemma restrict_wt (hS : C.IsStable S) (b : S) : (restrict hS).wt b = C.wt b := rfl

/--
@isnad1 id=eq.1h8v.s6.dbb947461bff from=translated src=- shape=795bb542 vocab=16811684
-/
@[simp] lemma restrict_ε (hS : C.IsStable S) (i : ι) (b : S) : (restrict hS).ε i b = C.ε i b :=
  rfl

/--
@isnad1 id=eq.1h8v.s6.683976cd5bd7 from=translated src=- shape=795bb542 vocab=a1a735eb
-/
@[simp] lemma restrict_φ (hS : C.IsStable S) (i : ι) (b : S) : (restrict hS).φ i b = C.φ i b :=
  rfl

/--
@isnad1 id=eq.1h8v.s6.59d95afebaeb from=translated src=- shape=caaa1e68 vocab=53a39ca0
-/
lemma restrict_e (hS : C.IsStable S) (i : ι) (b : S) :
    ((restrict hS).e i b).map Subtype.val = C.e i b := by
  simp [restrict, Option.map_pmap]

/--
@isnad1 id=eq.1h8v.s6.f48740a68a6b from=translated src=- shape=caaa1e68 vocab=5146ac89
-/
lemma restrict_f (hS : C.IsStable S) (i : ι) (b : S) :
    ((restrict hS).f i b).map Subtype.val = C.f i b := by
  simp [restrict, Option.map_pmap]

/-- The inclusion of a stable subset, as a strict morphism of crystals.-/
def restrictHom (hS : C.IsStable S) : StrictHom (restrict hS) C where
  toFun := Subtype.val
  wt_map _ := rfl
  ε_map _ _ := rfl
  e_map i b := (restrict_e hS i b).symm
  f_map i b := (restrict_f hS i b).symm

/--
@isnad1 id=eq.1h7v.s6.f9ccea80b247 from=translated src=- shape=9ba5069b vocab=62e69f77
-/
@[simp] lemma restrictHom_apply (hS : C.IsStable S) (b : S) : restrictHom hS b = b.1 := rfl

/--
@isnad1 id=issemino.2h6v.s5.5bcf3e9d4b4e from=translated src=- shape=6e047ef3 vocab=121367d1
-/
lemma IsSeminormal.restrict (hC : C.IsSeminormal) (hS : C.IsStable S) :
    (Crystal.restrict hS).IsSeminormal := by
  rw [isSeminormal_iff]
  intro i b
  refine ⟨hC.ε_nonneg i b, hC.φ_nonneg i b, fun h ↦ hC.ε_eq_zero ?_, fun h ↦ hC.φ_eq_zero ?_⟩
  · rw [← restrict_e hS, h, Option.map_none]
  · rw [← restrict_f hS, h, Option.map_none]

/-! ### Disjoint unions -/

variable (C₁ : Crystal D B₁) (C₂ : Crystal D B₂)

/-- The disjoint union `B₁ ⊔ B₂` of two crystals (cf. [Kas] §7.6).-/
def sum : Crystal D (B₁ ⊕ B₂) where
  wt := Sum.elim C₁.wt C₂.wt
  ε i := Sum.elim (C₁.ε i) (C₂.ε i)
  φ i := Sum.elim (C₁.φ i) (C₂.φ i)
  e i := Sum.elim (fun b ↦ (C₁.e i b).map Sum.inl) (fun b ↦ (C₂.e i b).map Sum.inr)
  f i := Sum.elim (fun b ↦ (C₁.f i b).map Sum.inl) (fun b ↦ (C₂.f i b).map Sum.inr)
  φ_eq i b := by cases b <;> simp [C₁.φ_eq, C₂.φ_eq]
  f_eq_some_iff i b b' := by
    cases b <;> cases b' <;> simp [C₁.f_eq_some_iff, C₂.f_eq_some_iff]
  wt_e i b b' h := by
    cases b <;> simp only [Sum.elim_inl, Sum.elim_inr, Option.map_eq_some_iff] at h <;>
      obtain ⟨c, hc, rfl⟩ := h
    · exact C₁.wt_e i _ c hc
    · exact C₂.wt_e i _ c hc
  ε_e i b b' h := by
    cases b <;> simp only [Sum.elim_inl, Sum.elim_inr, Option.map_eq_some_iff] at h <;>
      obtain ⟨c, hc, rfl⟩ := h
    · exact C₁.ε_e i _ c hc
    · exact C₂.ε_e i _ c hc
  e_eq_none_of_φ_eq_bot i b h := by
    cases b
    · simp [C₁.e_eq_none_of_φ_eq_bot i _ h]
    · simp [C₂.e_eq_none_of_φ_eq_bot i _ h]

variable {C₁ C₂}

/-- The character of a disjoint union of finite crystals is the sum of the characters.
@isnad1 id=eq.0h7v.s6.36a11e2ce50f from=translated src=- shape=82d7d969 vocab=7c3a23e4
-/
theorem character_sum [Fintype B₁] [Fintype B₂] :
    (C₁.sum C₂).character = C₁.character + C₂.character := by
  simp only [character]
  exact Fintype.sum_sum_type _

end Tengoku.LieLean.Crystal
-- Tengoku: root names of this library moved to Tengoku.LieLean so they do not collide with other libraries (generated)
