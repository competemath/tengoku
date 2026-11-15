import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_ModularCurve_KatzLevelP

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

universe u

namespace ModularCurve

def IsNormalForm {T : Type u} [CommRing T] (ℓ : ℕ) (W : WeierstrassCurve T) (D : LevelPData T) : Prop :=
  if ℓ = 3 then
    W.a₂ = 0 ∧ W.a₄ = 0 ∧ W.a₆ = 0 ∧ D.xP = 0 ∧ D.yP = 0 ∧ D.xQ = D.yQ
  else
    W.a₄ = 0 ∧ W.a₆ = 0 ∧ W.a₂ = W.a₃ ∧ D.xP = 0 ∧ D.yP = 0

/--
@isnad1 id=iff.1h4v.s6.b1debc5ef32d from=translated src=- shape=521bd063 vocab=7b98f118
-/
theorem isNormalForm_of_ne_three {T : Type u} [CommRing T] {ℓ : ℕ} (hℓ : ℓ ≠ 3) (W : WeierstrassCurve T)
    (D : LevelPData T) :
    IsNormalForm ℓ W D ↔ W.a₄ = 0 ∧ W.a₆ = 0 ∧ W.a₂ = W.a₃ ∧ D.xP = 0 ∧ D.yP = 0 := by
  simp [IsNormalForm, hℓ]

/--
@isnad1 id=iff.0h3v.s7.9d97a95b2732 from=translated src=- shape=66b5b02c vocab=b9d8043d
-/
theorem isNormalForm_three {T : Type u} [CommRing T] (W : WeierstrassCurve T) (D : LevelPData T) :
    IsNormalForm 3 W D ↔ W.a₂ = 0 ∧ W.a₄ = 0 ∧ W.a₆ = 0 ∧ D.xP = 0 ∧ D.yP = 0 ∧ D.xQ = D.yQ := by
  simp [IsNormalForm]

/--
@isnad1 id=isnormal.1h6v.s5.8fcf82bdd865 from=translated src=- shape=0c9f8160 vocab=265dfe97
-/
theorem IsNormalForm.map {T T' : Type u} [CommRing T] [CommRing T'] {ℓ : ℕ} {W : WeierstrassCurve T}
    {D : LevelPData T} (h : IsNormalForm ℓ W D) (f : T →+* T') : IsNormalForm ℓ (W.map f) (D.map f) := by
  unfold IsNormalForm at h ⊢
  split_ifs at h ⊢ with h3
  · obtain ⟨h1, h2, h3', h4, h5, h6⟩ := h
    simp [WeierstrassCurve.map, LevelPData.map, h1, h2, h3', h4, h5, h6]
  · obtain ⟨h1, h2, h3', h4, h5⟩ := h
    simp [WeierstrassCurve.map, LevelPData.map, h1, h2, h3', h4, h5]

end ModularCurve
