/-
Copyright (c) 2023 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.CategoryTheory.Linear.Basic
public import Tengoku.Seed.Algebra.Homology.ComplexShapeSigns
public import Tengoku.Seed.Algebra.Homology.HomologicalBicomplex
public import Tengoku.Seed.Algebra.Module.Basic

/-!
# The total complex of a bicomplex

Given a preadditive category `C`, two complex shapes `c₁ : ComplexShape I₁`,
`c₂ : ComplexShape I₂`, a bicomplex `K : HomologicalComplex₂ C c₁ c₂`,
and a third complex shape `c₁₂ : ComplexShape I₁₂` equipped
with `[TotalComplexShape c₁ c₂ c₁₂]`, we construct the total complex
`K.total c₁₂ : HomologicalComplex C c₁₂`.

In particular, if `c := ComplexShape.up ℤ` and `K : HomologicalComplex₂ c c`, then for any
`n : ℤ`, `(K.total c).X n` identifies to the coproduct of the `(K.X p).X q` such that
`p + q = n`, and the differential on `(K.total c).X n` is induced by the sum of horizontal
differentials `(K.X p).X q ⟶ (K.X (p + 1)).X q` and `(-1) ^ p` times the vertical
differentials `(K.X p).X q ⟶ (K.X p).X (q + 1)`.

-/

@[expose] public section

assert_not_exists TwoSidedIdeal

open CategoryTheory Category Limits Preadditive

namespace HomologicalComplex₂

variable {C : Type*} [Category* C] [Preadditive C]
  {I₁ I₂ I₁₂ : Type*} {c₁ : ComplexShape I₁} {c₂ : ComplexShape I₂}
  (K L M : HomologicalComplex₂ C c₁ c₂) (φ : K ⟶ L) (e : K ≅ L) (ψ : L ⟶ M)
  (c₁₂ : ComplexShape I₁₂) [TotalComplexShape c₁ c₂ c₁₂]

/-- A bicomplex has a total bicomplex if for any `i₁₂ : I₁₂`, the coproduct
of the objects `(K.X i₁).X i₂` such that `ComplexShape.π c₁ c₂ c₁₂ ⟨i₁, i₂⟩ = i₁₂` exists. -/
abbrev HasTotal := K.toGradedObject.HasMap (ComplexShape.π c₁ c₂ c₁₂)

include e in
variable {K L} in
/--
@isnad1 id=hastotal.0h10v.s6.87d4b0051a50 from=seed src=0 shape=aedb5c8f vocab=e0d95a45
-/
lemma hasTotal_of_iso [K.HasTotal c₁₂] : L.HasTotal c₁₂ :=
  GradedObject.hasMap_of_iso (GradedObject.isoMk K.toGradedObject L.toGradedObject
    (fun ⟨i₁, i₂⟩ =>
      (HomologicalComplex.eval _ _ i₁ ⋙ HomologicalComplex.eval _ _ i₂).mapIso e)) _

variable [DecidableEq I₁₂] [K.HasTotal c₁₂]

section

variable (i₁ : I₁) (i₂ : I₂) (i₁₂ : I₁₂)

/-- The horizontal differential in the total complex on a given summand. -/
noncomputable def d₁ :
    (K.X i₁).X i₂ ⟶ (K.toGradedObject.mapObj (ComplexShape.π c₁ c₂ c₁₂)) i₁₂ :=
  ComplexShape.ε₁ c₁ c₂ c₁₂ ⟨i₁, i₂⟩ • ((K.d i₁ (c₁.next i₁)).f i₂ ≫
    K.toGradedObject.ιMapObjOrZero (ComplexShape.π c₁ c₂ c₁₂) ⟨_, i₂⟩ i₁₂)

/-- The vertical differential in the total complex on a given summand. -/
noncomputable def d₂ :
    (K.X i₁).X i₂ ⟶ (K.toGradedObject.mapObj (ComplexShape.π c₁ c₂ c₁₂)) i₁₂ :=
  ComplexShape.ε₂ c₁ c₂ c₁₂ ⟨i₁, i₂⟩ • ((K.X i₁).d i₂ (c₂.next i₂) ≫
    K.toGradedObject.ιMapObjOrZero (ComplexShape.π c₁ c₂ c₁₂) ⟨i₁, _⟩ i₁₂)

set_option backward.isDefEq.respectTransparency.types false in
/--
@isnad1 id=eq.1h11v.s8.519836fa79ab from=seed src=0 shape=98563fc4 vocab=4a6c33ec
-/
lemma d₁_eq_zero (h : ¬ c₁.Rel i₁ (c₁.next i₁)) :
    K.d₁ c₁₂ i₁ i₂ i₁₂ = 0 := by
  dsimp [d₁]
  rw [K.shape_f _ _ h, zero_comp, smul_zero]

set_option backward.isDefEq.respectTransparency.types false in
/--
@isnad1 id=eq.1h11v.s8.88f88ebf304f from=seed src=0 shape=803f6484 vocab=e442aba1
-/
lemma d₂_eq_zero (h : ¬ c₂.Rel i₂ (c₂.next i₂)) :
    K.d₂ c₁₂ i₁ i₂ i₁₂ = 0 := by
  dsimp [d₂]
  rw [HomologicalComplex.shape _ _ _ h, zero_comp, smul_zero]

end

namespace totalAux
/-! Lemmas in the `totalAux` namespace should be used only in the internals of
the construction of the total complex `HomologicalComplex₂.total`. Once that
definition is done, similar lemmas shall be restated, but with
terms like `K.toGradedObject.ιMapObj` replaced by `K.ιTotal`. This is done in order
to prevent API leakage from definitions involving graded objects. -/

/--
@isnad1 id=eq.1h12v.s10.d54c65ca2099 from=seed src=0 shape=0f40f51b vocab=43a765d2
-/
lemma d₁_eq' {i₁ i₁' : I₁} (h : c₁.Rel i₁ i₁') (i₂ : I₂) (i₁₂ : I₁₂) :
    K.d₁ c₁₂ i₁ i₂ i₁₂ = ComplexShape.ε₁ c₁ c₂ c₁₂ ⟨i₁, i₂⟩ • ((K.d i₁ i₁').f i₂ ≫
      K.toGradedObject.ιMapObjOrZero (ComplexShape.π c₁ c₂ c₁₂) ⟨i₁', i₂⟩ i₁₂) := by
  obtain rfl := c₁.next_eq' h
  rfl

/--
@isnad1 id=eq.2h12v.s10.2d0fac1c9f94 from=seed src=0 shape=8747d3eb vocab=38b2d27a
-/
lemma d₁_eq {i₁ i₁' : I₁} (h : c₁.Rel i₁ i₁') (i₂ : I₂) (i₁₂ : I₁₂)
    (h' : ComplexShape.π c₁ c₂ c₁₂ ⟨i₁', i₂⟩ = i₁₂) :
    K.d₁ c₁₂ i₁ i₂ i₁₂ = ComplexShape.ε₁ c₁ c₂ c₁₂ ⟨i₁, i₂⟩ • ((K.d i₁ i₁').f i₂ ≫
      K.toGradedObject.ιMapObj (ComplexShape.π c₁ c₂ c₁₂) ⟨i₁', i₂⟩ i₁₂ h') := by
  rw [d₁_eq' K c₁₂ h i₂ i₁₂, K.toGradedObject.ιMapObjOrZero_eq]

/--
@isnad1 id=eq.1h12v.s10.a62e5c7d536c from=seed src=0 shape=9c266688 vocab=2a5e0dfd
-/
lemma d₂_eq' (i₁ : I₁) {i₂ i₂' : I₂} (h : c₂.Rel i₂ i₂') (i₁₂ : I₁₂) :
    K.d₂ c₁₂ i₁ i₂ i₁₂ = ComplexShape.ε₂ c₁ c₂ c₁₂ ⟨i₁, i₂⟩ • ((K.X i₁).d i₂ i₂' ≫
    K.toGradedObject.ιMapObjOrZero (ComplexShape.π c₁ c₂ c₁₂) ⟨i₁, i₂'⟩ i₁₂) := by
  obtain rfl := c₂.next_eq' h
  rfl

/--
@isnad1 id=eq.2h12v.s10.b23ab1fcc792 from=seed src=0 shape=8703ef92 vocab=a361bd2b
-/
lemma d₂_eq (i₁ : I₁) {i₂ i₂' : I₂} (h : c₂.Rel i₂ i₂') (i₁₂ : I₁₂)
    (h' : ComplexShape.π c₁ c₂ c₁₂ ⟨i₁, i₂'⟩ = i₁₂) :
    K.d₂ c₁₂ i₁ i₂ i₁₂ = ComplexShape.ε₂ c₁ c₂ c₁₂ ⟨i₁, i₂⟩ • ((K.X i₁).d i₂ i₂' ≫
    K.toGradedObject.ιMapObj (ComplexShape.π c₁ c₂ c₁₂) ⟨i₁, i₂'⟩ i₁₂ h') := by
  rw [d₂_eq' K c₁₂ i₁ h i₁₂, K.toGradedObject.ιMapObjOrZero_eq]

end totalAux

set_option backward.isDefEq.respectTransparency false in
/--
@isnad1 id=eq.2h12v.s8.ca5b33062def from=seed src=0 shape=42654a1f vocab=a6a4e5a6
-/
lemma d₁_eq_zero' {i₁ i₁' : I₁} (h : c₁.Rel i₁ i₁') (i₂ : I₂) (i₁₂ : I₁₂)
    (h' : ComplexShape.π c₁ c₂ c₁₂ ⟨i₁', i₂⟩ ≠ i₁₂) :
    K.d₁ c₁₂ i₁ i₂ i₁₂ = 0 := by
  rw [totalAux.d₁_eq' K c₁₂ h i₂ i₁₂, K.toGradedObject.ιMapObjOrZero_eq_zero, comp_zero, smul_zero]
  exact h'

set_option backward.isDefEq.respectTransparency false in
/--
@isnad1 id=eq.2h12v.s8.89e2cf4cb13a from=seed src=0 shape=1206f65b vocab=2f96784a
-/
lemma d₂_eq_zero' (i₁ : I₁) {i₂ i₂' : I₂} (h : c₂.Rel i₂ i₂') (i₁₂ : I₁₂)
    (h' : ComplexShape.π c₁ c₂ c₁₂ ⟨i₁, i₂'⟩ ≠ i₁₂) :
    K.d₂ c₁₂ i₁ i₂ i₁₂ = 0 := by
  rw [totalAux.d₂_eq' K c₁₂ i₁ h i₁₂, K.toGradedObject.ιMapObjOrZero_eq_zero, comp_zero, smul_zero]
  exact h'

/-- The horizontal differential in the total complex. -/
noncomputable def D₁ (i₁₂ i₁₂' : I₁₂) :
    K.toGradedObject.mapObj (ComplexShape.π c₁ c₂ c₁₂) i₁₂ ⟶
      K.toGradedObject.mapObj (ComplexShape.π c₁ c₂ c₁₂) i₁₂' :=
  GradedObject.descMapObj _ (ComplexShape.π c₁ c₂ c₁₂)
    (fun ⟨i₁, i₂⟩ _ => K.d₁ c₁₂ i₁ i₂ i₁₂')

/-- The vertical differential in the total complex. -/
noncomputable def D₂ (i₁₂ i₁₂' : I₁₂) :
    K.toGradedObject.mapObj (ComplexShape.π c₁ c₂ c₁₂) i₁₂ ⟶
      K.toGradedObject.mapObj (ComplexShape.π c₁ c₂ c₁₂) i₁₂' :=
  GradedObject.descMapObj _ (ComplexShape.π c₁ c₂ c₁₂)
    (fun ⟨i₁, i₂⟩ _ => K.d₂ c₁₂ i₁ i₂ i₁₂')

namespace totalAux

set_option backward.isDefEq.respectTransparency.types false in
/--
@isnad1 id=eq.1h11v.s8.f8609d20d40e from=seed src=0 shape=f724dfb5 vocab=9df739d3
-/
@[reassoc (attr := simp)]
lemma ιMapObj_D₁ (i₁₂ i₁₂' : I₁₂) (i : I₁ × I₂) (h : ComplexShape.π c₁ c₂ c₁₂ i = i₁₂) :
    K.toGradedObject.ιMapObj (ComplexShape.π c₁ c₂ c₁₂) i i₁₂ h ≫ K.D₁ c₁₂ i₁₂ i₁₂' =
      K.d₁ c₁₂ i.1 i.2 i₁₂' := by
  simp [D₁]

set_option backward.isDefEq.respectTransparency.types false in
/--
@isnad1 id=eq.1h11v.s8.c4f47a43e394 from=seed src=0 shape=f724dfb5 vocab=6f78a67e
-/
@[reassoc (attr := simp)]
lemma ιMapObj_D₂ (i₁₂ i₁₂' : I₁₂) (i : I₁ × I₂) (h : ComplexShape.π c₁ c₂ c₁₂ i = i₁₂) :
    K.toGradedObject.ιMapObj (ComplexShape.π c₁ c₂ c₁₂) i i₁₂ h ≫ K.D₂ c₁₂ i₁₂ i₁₂' =
      K.d₂ c₁₂ i.1 i.2 i₁₂' := by
  simp [D₂]

end totalAux

set_option backward.isDefEq.respectTransparency false in
/--
@isnad1 id=eq.1h10v.s8.eb3121e6ce8e from=seed src=0 shape=118fcafd vocab=5851ca79
-/
lemma D₁_shape (i₁₂ i₁₂' : I₁₂) (h₁₂ : ¬ c₁₂.Rel i₁₂ i₁₂') : K.D₁ c₁₂ i₁₂ i₁₂' = 0 := by
  ext ⟨i₁, i₂⟩ h
  simp only [totalAux.ιMapObj_D₁, comp_zero]
  by_cases h₁ : c₁.Rel i₁ (c₁.next i₁)
  · rw [K.d₁_eq_zero' c₁₂ h₁ i₂ i₁₂']
    intro h₂
    exact h₁₂ (by simpa only [← h, ← h₂] using ComplexShape.rel_π₁ c₂ c₁₂ h₁ i₂)
  · exact d₁_eq_zero _ _ _ _ _ h₁

set_option backward.isDefEq.respectTransparency false in
/--
@isnad1 id=eq.1h10v.s8.bc258e748f23 from=seed src=0 shape=118fcafd vocab=bc0d3053
-/
lemma D₂_shape (i₁₂ i₁₂' : I₁₂) (h₁₂ : ¬ c₁₂.Rel i₁₂ i₁₂') : K.D₂ c₁₂ i₁₂ i₁₂' = 0 := by
  ext ⟨i₁, i₂⟩ h
  simp only [totalAux.ιMapObj_D₂, comp_zero]
  by_cases h₂ : c₂.Rel i₂ (c₂.next i₂)
  · rw [K.d₂_eq_zero' c₁₂ i₁ h₂ i₁₂']
    intro h₁
    exact h₁₂ (by simpa only [← h, ← h₁] using ComplexShape.rel_π₂ c₁ c₁₂ i₁ h₂)
  · exact d₂_eq_zero _ _ _ _ _ h₂

set_option backward.isDefEq.respectTransparency false in
/--
@isnad1 id=eq.0h11v.s8.c9ec4815baec from=seed src=0 shape=0a6d724b vocab=297c4459
-/
@[reassoc (attr := simp)]
lemma D₁_D₁ (i₁₂ i₁₂' i₁₂'' : I₁₂) : K.D₁ c₁₂ i₁₂ i₁₂' ≫ K.D₁ c₁₂ i₁₂' i₁₂'' = 0 := by
  by_cases h₁ : c₁₂.Rel i₁₂ i₁₂'
  · by_cases h₂ : c₁₂.Rel i₁₂' i₁₂''
    · ext ⟨i₁, i₂⟩ h
      simp only [totalAux.ιMapObj_D₁_assoc, comp_zero]
      by_cases h₃ : c₁.Rel i₁ (c₁.next i₁)
      · rw [totalAux.d₁_eq K c₁₂ h₃ i₂ i₁₂']; swap
        · rw [← ComplexShape.next_π₁ c₂ c₁₂ h₃ i₂, ← c₁₂.next_eq' h₁, h]
        simp only [Linear.units_smul_comp, assoc, totalAux.ιMapObj_D₁]
        by_cases h₄ : c₁.Rel (c₁.next i₁) (c₁.next (c₁.next i₁))
        · rw [totalAux.d₁_eq K c₁₂ h₄ i₂ i₁₂'', Linear.comp_units_smul,
            d_f_comp_d_f_assoc, zero_comp, smul_zero, smul_zero]
          rw [← ComplexShape.next_π₁ c₂ c₁₂ h₄, ← ComplexShape.next_π₁ c₂ c₁₂ h₃,
            h, c₁₂.next_eq' h₁, c₁₂.next_eq' h₂]
        · rw [K.d₁_eq_zero _ _ _ _ h₄, comp_zero, smul_zero]
      · rw [K.d₁_eq_zero c₁₂ _ _ _ h₃, zero_comp]
    · rw [K.D₁_shape c₁₂ _ _ h₂, comp_zero]
  · rw [K.D₁_shape c₁₂ _ _ h₁, zero_comp]

set_option backward.isDefEq.respectTransparency false in
/--
@isnad1 id=eq.0h11v.s8.06c2b1b936bd from=seed src=0 shape=0a6d724b vocab=ecc1829d
-/
@[reassoc (attr := simp)]
lemma D₂_D₂ (i₁₂ i₁₂' i₁₂'' : I₁₂) : K.D₂ c₁₂ i₁₂ i₁₂' ≫ K.D₂ c₁₂ i₁₂' i₁₂'' = 0 := by
  by_cases h₁ : c₁₂.Rel i₁₂ i₁₂'
  · by_cases h₂ : c₁₂.Rel i₁₂' i₁₂''
    · ext ⟨i₁, i₂⟩ h
      simp only [totalAux.ιMapObj_D₂_assoc, comp_zero]
      by_cases h₃ : c₂.Rel i₂ (c₂.next i₂)
      · rw [totalAux.d₂_eq K c₁₂ i₁ h₃ i₁₂']; swap
        · rw [← ComplexShape.next_π₂ c₁ c₁₂ i₁ h₃, ← c₁₂.next_eq' h₁, h]
        simp only [Linear.units_smul_comp, assoc, totalAux.ιMapObj_D₂]
        by_cases h₄ : c₂.Rel (c₂.next i₂) (c₂.next (c₂.next i₂))
        · rw [totalAux.d₂_eq K c₁₂ i₁ h₄ i₁₂'', Linear.comp_units_smul,
            HomologicalComplex.d_comp_d_assoc, zero_comp, smul_zero, smul_zero]
          rw [← ComplexShape.next_π₂ c₁ c₁₂ i₁ h₄, ← ComplexShape.next_π₂ c₁ c₁₂ i₁ h₃,
            h, c₁₂.next_eq' h₁, c₁₂.next_eq' h₂]
        · rw [K.d₂_eq_zero c₁₂ _ _ _ h₄, comp_zero, smul_zero]
      · rw [K.d₂_eq_zero c₁₂ _ _ _ h₃, zero_comp]
    · rw [K.D₂_shape c₁₂ _ _ h₂, comp_zero]
  · rw [K.D₂_shape c₁₂ _ _ h₁, zero_comp]

set_option backward.isDefEq.respectTransparency false in
/--
@isnad1 id=eq.0h11v.s9.1663deb55d72 from=seed src=0 shape=e579d72c vocab=698cff6c
-/
@[reassoc (attr := simp)]
lemma D₂_D₁ (i₁₂ i₁₂' i₁₂'' : I₁₂) :
    K.D₂ c₁₂ i₁₂ i₁₂' ≫ K.D₁ c₁₂ i₁₂' i₁₂'' = - K.D₁ c₁₂ i₁₂ i₁₂' ≫ K.D₂ c₁₂ i₁₂' i₁₂'' := by
  by_cases h₁ : c₁₂.Rel i₁₂ i₁₂'
  · by_cases h₂ : c₁₂.Rel i₁₂' i₁₂''
    · ext ⟨i₁, i₂⟩ h
      simp only [totalAux.ιMapObj_D₂_assoc, comp_neg, totalAux.ιMapObj_D₁_assoc]
      by_cases h₃ : c₁.Rel i₁ (c₁.next i₁)
      · rw [totalAux.d₁_eq K c₁₂ h₃ i₂ i₁₂']; swap
        · rw [← ComplexShape.next_π₁ c₂ c₁₂ h₃ i₂, ← c₁₂.next_eq' h₁, h]
        simp only [Linear.units_smul_comp, assoc, totalAux.ιMapObj_D₂]
        by_cases h₄ : c₂.Rel i₂ (c₂.next i₂)
        · have h₅ : ComplexShape.π c₁ c₂ c₁₂ (i₁, c₂.next i₂) = i₁₂' := by
            rw [← c₁₂.next_eq' h₁, ← h, ComplexShape.next_π₂ c₁ c₁₂ i₁ h₄]
          have h₆ : ComplexShape.π c₁ c₂ c₁₂ (c₁.next i₁, c₂.next i₂) = i₁₂'' := by
            rw [← c₁₂.next_eq' h₂, ← ComplexShape.next_π₁ c₂ c₁₂ h₃, h₅]
          simp only [totalAux.d₂_eq K c₁₂ _ h₄ _ h₅, totalAux.d₂_eq K c₁₂ _ h₄ _ h₆,
            Linear.units_smul_comp, assoc, totalAux.ιMapObj_D₁, Linear.comp_units_smul,
            totalAux.d₁_eq K c₁₂ h₃ _ _ h₆, HomologicalComplex.Hom.comm_assoc, smul_smul,
            ComplexShape.ε₂_ε₁ c₁₂ h₃ h₄, neg_mul, Units.neg_smul]
        · simp only [K.d₂_eq_zero c₁₂ _ _ _ h₄, zero_comp, comp_zero, smul_zero, neg_zero]
      · rw [K.d₁_eq_zero c₁₂ _ _ _ h₃, zero_comp, neg_zero]
        by_cases h₄ : c₂.Rel i₂ (c₂.next i₂)
        · rw [totalAux.d₂_eq K c₁₂ i₁ h₄ i₁₂']; swap
          · rw [← ComplexShape.next_π₂ c₁ c₁₂ i₁ h₄, ← c₁₂.next_eq' h₁, h]
          simp only [Linear.units_smul_comp, assoc, totalAux.ιMapObj_D₁]
          rw [K.d₁_eq_zero c₁₂ _ _ _ h₃, comp_zero, smul_zero]
        · rw [K.d₂_eq_zero c₁₂ _ _ _ h₄, zero_comp]
    · rw [K.D₁_shape c₁₂ _ _ h₂, K.D₂_shape c₁₂ _ _ h₂, comp_zero, comp_zero, neg_zero]
  · rw [K.D₁_shape c₁₂ _ _ h₁, K.D₂_shape c₁₂ _ _ h₁, zero_comp, zero_comp, neg_zero]

/--
@isnad1 id=eq.0h11v.s9.ca143e802119 from=seed src=0 shape=e579d72c vocab=698cff6c
-/
@[reassoc]
lemma D₁_D₂ (i₁₂ i₁₂' i₁₂'' : I₁₂) :
    K.D₁ c₁₂ i₁₂ i₁₂' ≫ K.D₂ c₁₂ i₁₂' i₁₂'' = - K.D₂ c₁₂ i₁₂ i₁₂' ≫ K.D₁ c₁₂ i₁₂' i₁₂'' := by simp

/-- The total complex of a bicomplex. -/
@[simps -isSimp d, implicit_reducible]
noncomputable def total : HomologicalComplex C c₁₂ where
  X := K.toGradedObject.mapObj (ComplexShape.π c₁ c₂ c₁₂)
  d i₁₂ i₁₂' := K.D₁ c₁₂ i₁₂ i₁₂' + K.D₂ c₁₂ i₁₂ i₁₂'
  shape i₁₂ i₁₂' h₁₂ := by
    rw [K.D₁_shape c₁₂ _ _ h₁₂, K.D₂_shape c₁₂ _ _ h₁₂, zero_add]

/-- The inclusion of a summand in the total complex. -/
noncomputable def ιTotal (i₁ : I₁) (i₂ : I₂) (i₁₂ : I₁₂)
    (h : ComplexShape.π c₁ c₂ c₁₂ (i₁, i₂) = i₁₂) :
    (K.X i₁).X i₂ ⟶ (K.total c₁₂).X i₁₂ :=
  K.toGradedObject.ιMapObj (ComplexShape.π c₁ c₂ c₁₂) ⟨i₁, i₂⟩ i₁₂ h

/--
@isnad1 id=eq.3h13v.s8.8b7d557291a8 from=seed src=0 shape=36becfa8 vocab=89fe9693
-/
@[reassoc (attr := simp)]
lemma XXIsoOfEq_hom_ιTotal {x₁ y₁ : I₁} (h₁ : x₁ = y₁) {x₂ y₂ : I₂} (h₂ : x₂ = y₂)
    (i₁₂ : I₁₂) (h : ComplexShape.π c₁ c₂ c₁₂ (y₁, y₂) = i₁₂) :
    (K.XXIsoOfEq _ _ _ h₁ h₂).hom ≫ K.ιTotal c₁₂ y₁ y₂ i₁₂ h =
      K.ιTotal c₁₂ x₁ x₂ i₁₂ (by rw [h₁, h₂, h]) := by
  subst h₁ h₂
  simp

/--
@isnad1 id=eq.3h13v.s8.d008af4f1e31 from=seed src=0 shape=c2decaf1 vocab=fa142214
-/
@[reassoc (attr := simp)]
lemma XXIsoOfEq_inv_ιTotal {x₁ y₁ : I₁} (h₁ : x₁ = y₁) {x₂ y₂ : I₂} (h₂ : x₂ = y₂)
    (i₁₂ : I₁₂) (h : ComplexShape.π c₁ c₂ c₁₂ (x₁, x₂) = i₁₂) :
    (K.XXIsoOfEq _ _ _ h₁ h₂).inv ≫ K.ιTotal c₁₂ x₁ x₂ i₁₂ h =
      K.ιTotal c₁₂ y₁ y₂ i₁₂ (by rw [← h, h₁, h₂]) := by
  subst h₁ h₂
  simp

/-- The inclusion of a summand in the total complex, or zero if the degrees do not match. -/
noncomputable def ιTotalOrZero (i₁ : I₁) (i₂ : I₂) (i₁₂ : I₁₂) :
    (K.X i₁).X i₂ ⟶ (K.total c₁₂).X i₁₂ :=
  K.toGradedObject.ιMapObjOrZero (ComplexShape.π c₁ c₂ c₁₂) ⟨i₁, i₂⟩ i₁₂

/--
@isnad1 id=eq.1h11v.s7.5a33b0847a8e from=seed src=0 shape=33de26d9 vocab=711a79c9
-/
lemma ιTotalOrZero_eq (i₁ : I₁) (i₂ : I₂) (i₁₂ : I₁₂)
    (h : ComplexShape.π c₁ c₂ c₁₂ (i₁, i₂) = i₁₂) :
    K.ιTotalOrZero c₁₂ i₁ i₂ i₁₂ = K.ιTotal c₁₂ i₁ i₂ i₁₂ h := dite_eq_left h

/--
@isnad1 id=eq.1h11v.s8.5fe0898d461c from=seed src=0 shape=17b500b7 vocab=d8108b4e
-/
lemma ιTotalOrZero_eq_zero (i₁ : I₁) (i₂ : I₂) (i₁₂ : I₁₂)
    (h : ComplexShape.π c₁ c₂ c₁₂ (i₁, i₂) ≠ i₁₂) :
    K.ιTotalOrZero c₁₂ i₁ i₂ i₁₂ = 0 := dite_eq_right h

/--
@isnad1 id=eq.1h12v.s8.1fd786fc7ebe from=seed src=0 shape=92ba99cd vocab=f3b3a6fc
-/
@[reassoc (attr := simp)]
lemma ι_D₁ (i₁₂ i₁₂' : I₁₂) (i₁ : I₁) (i₂ : I₂) (h : ComplexShape.π c₁ c₂ c₁₂ ⟨i₁, i₂⟩ = i₁₂) :
    K.ιTotal c₁₂ i₁ i₂ i₁₂ h ≫ K.D₁ c₁₂ i₁₂ i₁₂' =
      K.d₁ c₁₂ i₁ i₂ i₁₂' := by
  apply totalAux.ιMapObj_D₁

/--
@isnad1 id=eq.1h12v.s8.c0ccc6fd4a61 from=seed src=0 shape=92ba99cd vocab=5c36176b
-/
@[reassoc (attr := simp)]
lemma ι_D₂ (i₁₂ i₁₂' : I₁₂) (i₁ : I₁) (i₂ : I₂)
    (h : ComplexShape.π c₁ c₂ c₁₂ ⟨i₁, i₂⟩ = i₁₂) :
    K.ιTotal c₁₂ i₁ i₂ i₁₂ h ≫ K.D₂ c₁₂ i₁₂ i₁₂' =
      K.d₂ c₁₂ i₁ i₂ i₁₂' := by
  apply totalAux.ιMapObj_D₂

/--
@isnad1 id=eq.1h12v.s10.0657c89a8d78 from=seed src=0 shape=2ad9b5e2 vocab=b721f83e
-/
lemma d₁_eq' {i₁ i₁' : I₁} (h : c₁.Rel i₁ i₁') (i₂ : I₂) (i₁₂ : I₁₂) :
    K.d₁ c₁₂ i₁ i₂ i₁₂ = ComplexShape.ε₁ c₁ c₂ c₁₂ ⟨i₁, i₂⟩ • ((K.d i₁ i₁').f i₂ ≫
      K.ιTotalOrZero c₁₂ i₁' i₂ i₁₂) :=
  totalAux.d₁_eq' _ _ h _ _

/--
@isnad1 id=eq.2h12v.s10.ecc11fea9c71 from=seed src=0 shape=29481be9 vocab=fba99ed3
-/
lemma d₁_eq {i₁ i₁' : I₁} (h : c₁.Rel i₁ i₁') (i₂ : I₂) (i₁₂ : I₁₂)
    (h' : ComplexShape.π c₁ c₂ c₁₂ ⟨i₁', i₂⟩ = i₁₂) :
    K.d₁ c₁₂ i₁ i₂ i₁₂ = ComplexShape.ε₁ c₁ c₂ c₁₂ ⟨i₁, i₂⟩ • ((K.d i₁ i₁').f i₂ ≫
      K.ιTotal c₁₂ i₁' i₂ i₁₂ h') :=
  totalAux.d₁_eq _ _ h _ _ _

/--
@isnad1 id=eq.1h12v.s10.9a02ce967bb8 from=seed src=0 shape=533a5cff vocab=d6a42806
-/
lemma d₂_eq' (i₁ : I₁) {i₂ i₂' : I₂} (h : c₂.Rel i₂ i₂') (i₁₂ : I₁₂) :
    K.d₂ c₁₂ i₁ i₂ i₁₂ = ComplexShape.ε₂ c₁ c₂ c₁₂ ⟨i₁, i₂⟩ • ((K.X i₁).d i₂ i₂' ≫
    K.ιTotalOrZero c₁₂ i₁ i₂' i₁₂) :=
  totalAux.d₂_eq' _ _ _ h _

/--
@isnad1 id=eq.2h12v.s10.fca24436fcc1 from=seed src=0 shape=29a51878 vocab=b92f4d3f
-/
lemma d₂_eq (i₁ : I₁) {i₂ i₂' : I₂} (h : c₂.Rel i₂ i₂') (i₁₂ : I₁₂)
    (h' : ComplexShape.π c₁ c₂ c₁₂ ⟨i₁, i₂'⟩ = i₁₂) :
    K.d₂ c₁₂ i₁ i₂ i₁₂ = ComplexShape.ε₂ c₁ c₂ c₁₂ ⟨i₁, i₂⟩ • ((K.X i₁).d i₂ i₂' ≫
    K.ιTotal c₁₂ i₁ i₂' i₁₂ h') :=
  totalAux.d₂_eq _ _ _ h _ _

section

variable {c₁₂}
variable {A : C} {i₁₂ : I₁₂}
  (f : ∀ (i₁ : I₁) (i₂ : I₂) (_ : ComplexShape.π c₁ c₂ c₁₂ (i₁, i₂) = i₁₂), (K.X i₁).X i₂ ⟶ A)

/-- Given a bicomplex `K`, this is a constructor for morphisms from `(K.total c₁₂).X i₁₂`. -/
noncomputable def totalDesc : (K.total c₁₂).X i₁₂ ⟶ A :=
  K.toGradedObject.descMapObj _ (fun ⟨i₁, i₂⟩ hi => f i₁ i₂ hi)

set_option backward.isDefEq.respectTransparency false in
/--
@isnad1 id=eq.1h13v.s8.74b200044c6c from=seed src=0 shape=dc41411f vocab=641a0601
-/
@[reassoc (attr := simp)]
lemma ι_totalDesc (i₁ : I₁) (i₂ : I₂) (hi : ComplexShape.π c₁ c₂ c₁₂ (i₁, i₂) = i₁₂) :
    K.ιTotal c₁₂ i₁ i₂ i₁₂ hi ≫ K.totalDesc f = f i₁ i₂ hi := by
  simp [totalDesc, ιTotal]

end

namespace total

variable {K L M}

/--
@isnad1 id=eq.1h12v.s8.e30b7dfaff11 from=seed src=0 shape=9231cbbd vocab=810e5ccc
-/
@[ext]
lemma hom_ext {A : C} {i₁₂ : I₁₂} {f g : (K.total c₁₂).X i₁₂ ⟶ A}
    (h : ∀ (i₁ : I₁) (i₂ : I₂) (hi : ComplexShape.π c₁ c₂ c₁₂ (i₁, i₂) = i₁₂),
      K.ιTotal c₁₂ i₁ i₂ i₁₂ hi ≫ f = K.ιTotal c₁₂ i₁ i₂ i₁₂ hi ≫ g) : f = g := by
  apply GradedObject.mapObj_ext
  rintro ⟨i₁, i₂⟩ hi
  exact h i₁ i₂ hi

variable [L.HasTotal c₁₂]

namespace mapAux

set_option backward.isDefEq.respectTransparency false in
/--
@isnad1 id=eq.0h13v.s9.a13cdefa26e4 from=seed src=0 shape=9524abea vocab=6614c5f1
-/
@[reassoc (attr := simp)]
lemma d₁_mapMap (i₁ : I₁) (i₂ : I₂) (i₁₂ : I₁₂) :
    K.d₁ c₁₂ i₁ i₂ i₁₂ ≫ GradedObject.mapMap (toGradedObjectMap φ) _ i₁₂ =
    (φ.f i₁).f i₂ ≫ L.d₁ c₁₂ i₁ i₂ i₁₂ := by
  by_cases h : c₁.Rel i₁ (c₁.next i₁)
  · simp [totalAux.d₁_eq' _ c₁₂ h]
  · simp [d₁_eq_zero _ c₁₂ i₁ i₂ i₁₂ h]

set_option backward.isDefEq.respectTransparency false in
/--
@isnad1 id=eq.0h13v.s9.ef5b45ca8b82 from=seed src=0 shape=9524abea vocab=10b198e0
-/
@[reassoc (attr := simp)]
lemma d₂_mapMap (i₁ : I₁) (i₂ : I₂) (i₁₂ : I₁₂) :
    K.d₂ c₁₂ i₁ i₂ i₁₂ ≫ GradedObject.mapMap (toGradedObjectMap φ) _ i₁₂ =
    (φ.f i₁).f i₂ ≫ L.d₂ c₁₂ i₁ i₂ i₁₂ := by
  by_cases h : c₂.Rel i₂ (c₂.next i₂)
  · simp [totalAux.d₂_eq' _ c₁₂ i₁ h]
  · simp [d₂_eq_zero _ c₁₂ i₁ i₂ i₁₂ h]

set_option backward.isDefEq.respectTransparency false in
/--
@isnad1 id=eq.0h12v.s9.6ede27f53e92 from=seed src=0 shape=2c0059f6 vocab=b42ab0ed
-/
@[reassoc]
lemma mapMap_D₁ (i₁₂ i₁₂' : I₁₂) :
    GradedObject.mapMap (toGradedObjectMap φ) _ i₁₂ ≫ L.D₁ c₁₂ i₁₂ i₁₂' =
      K.D₁ c₁₂ i₁₂ i₁₂' ≫ GradedObject.mapMap (toGradedObjectMap φ) _ i₁₂' := by
  cat_disch

set_option backward.isDefEq.respectTransparency false in
/--
@isnad1 id=eq.0h12v.s9.974f66955a84 from=seed src=0 shape=2c0059f6 vocab=39c7e460
-/
@[reassoc]
lemma mapMap_D₂ (i₁₂ i₁₂' : I₁₂) :
    GradedObject.mapMap (toGradedObjectMap φ) _ i₁₂ ≫ L.D₂ c₁₂ i₁₂ i₁₂' =
      K.D₂ c₁₂ i₁₂ i₁₂' ≫ GradedObject.mapMap (toGradedObjectMap φ) _ i₁₂' := by
  cat_disch

end mapAux

/-- The morphism `K.total c₁₂ ⟶ L.total c₁₂` of homological complexes induced
by a morphism of bicomplexes `K ⟶ L`. -/
noncomputable def map : K.total c₁₂ ⟶ L.total c₁₂ where
  f := GradedObject.mapMap (toGradedObjectMap φ) _
  comm' i₁₂ i₁₂' _ := by
    dsimp [total]
    rw [comp_add, add_comp, mapAux.mapMap_D₁, mapAux.mapMap_D₂]

/--
@isnad1 id=eq.0h10v.s8.48ebc3b44dd0 from=seed src=0 shape=74dd5aff vocab=6f077897
-/
@[simp]
lemma forget_map :
    (HomologicalComplex.forget C c₁₂).map (map φ c₁₂) =
      GradedObject.mapMap (toGradedObjectMap φ) _ := rfl

variable (K) in
/--
@isnad1 id=eq.0h8v.s7.bcf84c55b938 from=seed src=0 shape=ac3f55ee vocab=d9e1c8f2
-/
@[simp]
lemma map_id : map (𝟙 K) c₁₂ = 𝟙 _ := by
  apply (HomologicalComplex.forget _ _).map_injective
  apply GradedObject.mapMap_id

variable [M.HasTotal c₁₂]

/--
@isnad1 id=eq.0h12v.s8.9a6e88132db5 from=seed src=0 shape=91ba91db vocab=05cbc08c
-/
@[simp, reassoc]
lemma map_comp : map (φ ≫ ψ) c₁₂ = map φ c₁₂ ≫ map ψ c₁₂ := by
  apply (HomologicalComplex.forget _ _).map_injective
  exact GradedObject.mapMap_comp (toGradedObjectMap φ) (toGradedObjectMap ψ) _

/-- The isomorphism `K.total c₁₂ ≅ L.total c₁₂` of homological complexes induced
by an isomorphism of bicomplexes `K ≅ L`. -/
@[simps]
noncomputable def mapIso : K.total c₁₂ ≅ L.total c₁₂ where
  hom := map e.hom _
  inv := map e.inv _
  hom_inv_id := by rw [← map_comp, e.hom_inv_id, map_id]
  inv_hom_id := by rw [← map_comp, e.inv_hom_id, map_id]

end total

section

variable [L.HasTotal c₁₂]

set_option backward.isDefEq.respectTransparency false in
/--
@isnad1 id=eq.1h13v.s9.0cafb991e5db from=seed src=0 shape=1aa38260 vocab=992d9879
-/
@[reassoc (attr := simp)]
lemma ιTotal_map (i₁ : I₁) (i₂ : I₂) (i₁₂ : I₁₂) (h : ComplexShape.π c₁ c₂ c₁₂ (i₁, i₂) = i₁₂) :
    K.ιTotal c₁₂ i₁ i₂ i₁₂ h ≫ (total.map φ c₁₂).f i₁₂ =
      (φ.f i₁).f i₂ ≫ L.ιTotal c₁₂ i₁ i₂ i₁₂ h := by
  simp [total.map, ιTotal]

set_option backward.isDefEq.respectTransparency false in
/--
@isnad1 id=eq.0h13v.s9.145432d97f3f from=seed src=0 shape=7b99ffed vocab=1a963f92
-/
@[reassoc (attr := simp)]
lemma ιTotalOrZero_map (i₁ : I₁) (i₂ : I₂) (i₁₂ : I₁₂) :
    K.ιTotalOrZero c₁₂ i₁ i₂ i₁₂ ≫ (total.map φ c₁₂).f i₁₂ =
      (φ.f i₁).f i₂ ≫ L.ιTotalOrZero c₁₂ i₁ i₂ i₁₂ := by
  simp [total.map, ιTotalOrZero]

end

variable (C c₁ c₂)
variable [∀ (K : HomologicalComplex₂ C c₁ c₂), K.HasTotal c₁₂]

/-- The functor which sends a bicomplex to its total complex. -/
@[simps]
noncomputable def totalFunctor :
    HomologicalComplex₂ C c₁ c₂ ⥤ HomologicalComplex C c₁₂ where
  obj K := K.total c₁₂
  map φ := total.map φ c₁₂

end HomologicalComplex₂
