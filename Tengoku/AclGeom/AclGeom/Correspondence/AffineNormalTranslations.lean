/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import Tengoku.AclGeom.AclGeom.Correspondence.AffineAction

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Nontrivial normal affine point subgroups contain translations

**Status:** proved over every field. A nontrivial normal subgroup of the ordinary affine
transformation group contains every translation. A nonunit multiplier gives translations
by commutators; a nonzero translation gives all others by scalar conjugation.
Named consumer: the actual closed normal subgroup image in
`NormalTranslation.image_eq_translations` (#21).
-/

namespace AclGeom.AffineTransformation
noncomputable section
variable {k : Type*} [Field k]

/-- Named consumer: the closed image of the genuine normal subgroup contains translations.-/
theorem translations_mem_of_normal_ne_bot (S : Subgroup (AffineTransformation k))
    [S.Normal] (hS : S ≠ ⊥) (b : k) : translation b ∈ S := by
  obtain ⟨⟨g, hg⟩, hg1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hS
  have hg1 : g ≠ 1 := fun h ↦ hg1 (Subtype.ext h)
  by_cases ha : (g.multiplier : k) = 1
  · have hge : g = translation g.shift := by
      apply AffineTransformation.ext
      · exact Units.ext ha
      · rfl
    have hgshift : g.shift ≠ 0 := by
      intro hz
      apply hg1
      rw [hge]
      ext <;> simp [translation, hz]
    by_cases hb : b = 0
    · subst b
      convert S.one_mem using 1
      ext <;> simp [translation]
    · let a : kˣ := Units.mk0 (b / g.shift) (div_ne_zero hb hgshift)
      have hm := (inferInstance : S.Normal).conj_mem g hg (scaling a)
      rw [hge, mul_translation_mul_inv] at hm
      change translation ((b / g.shift) * g.shift) ∈ S at hm
      rwa [div_mul_cancel₀ _ hgshift] at hm
  · let c := b / ((g.multiplier : k) - 1)
    have hm := S.mul_mem hg
      ((inferInstance : S.Normal).conj_mem g⁻¹ (S.inv_mem hg) (translation c))
    have he : g * (translation c * g⁻¹ * (translation c)⁻¹) =
        translation (((g.multiplier : k) - 1) * c) := by
      calc
        _ = (g * translation c * g⁻¹) * (translation c)⁻¹ := by
          rw [← _root_.mul_assoc, ← _root_.mul_assoc]
        _ = translation ((g.multiplier : k) * c) * translation (-c) := by
          rw [mul_translation_mul_inv, translation_inv]
        _ = _ := by rw [translation_mul_translation]; congr 1; ring
    rw [he] at hm
    change translation (((g.multiplier : k) - 1) *
      (b / ((g.multiplier : k) - 1))) ∈ S at hm
    rwa [mul_div_cancel₀ _ (sub_ne_zero.mpr ha)] at hm

end
end AclGeom.AffineTransformation
