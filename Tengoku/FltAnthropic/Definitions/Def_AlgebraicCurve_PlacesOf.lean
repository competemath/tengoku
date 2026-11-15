import Tengoku.Seed.AlgebraicGeometry.FunctionField
import Tengoku.FltAnthropic.Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Tengoku.FltAnthropic.Definitions.Def_AlgebraicCurve_CurveModel

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicCurve

variable {K : Type u} [Field K] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of K)) [IsIntegral C]

def placesOf (U : C.Opens) :
    letI := (baseToFunctionField c).toAlgebra
    Set (Place K C.functionField) :=
  letI := (baseToFunctionField c).toAlgebra
  {v | ∃ x : C, x ∈ U ∧ IsClosed ({x} : Set C) ∧
    (algebraMap (C.presheaf.stalk x) C.functionField).range = v.toValuationSubring.toSubring}

/--
@isnad1 id=iff.0h5v.s9.2d69539d8aab from=translated src=- shape=19adf236 vocab=f2e2b576
-/
theorem mem_placesOf_iff (U : C.Opens) :
    letI := (baseToFunctionField c).toAlgebra
    ∀ v : Place K C.functionField, v ∈ placesOf c U ↔ ∃ x : C, x ∈ U ∧ IsClosed ({x} : Set C) ∧
      (algebraMap (C.presheaf.stalk x) C.functionField).range = v.toValuationSubring.toSubring :=
  fun _ => Iff.rfl

/--
@isnad1 id=le.1h5v.s7.c947e0516ff7 from=translated src=- shape=4222f9f4 vocab=532b4e22
-/
theorem placesOf_mono {U V : C.Opens} (h : U ≤ V) :
    letI := (baseToFunctionField c).toAlgebra
    placesOf c U ⊆ placesOf c V := by
  rintro v ⟨x, hxU, hx, hv⟩
  exact ⟨x, h hxU, hx, hv⟩

/--
@isnad1 id=eq.0h5v.s7.a656e4dec7da from=translated src=- shape=d1ad6a80 vocab=0ee142d9
-/
theorem placesOf_sup (U V : C.Opens) :
    letI := (baseToFunctionField c).toAlgebra
    placesOf c (U ⊔ V) = placesOf c U ∪ placesOf c V := by
  letI := (baseToFunctionField c).toAlgebra
  apply Set.Subset.antisymm
  · rintro v ⟨x, hxUV, hx, hv⟩
    rcases (show x ∈ (U : Set C) ∪ (V : Set C) from hxUV) with h | h
    · exact Or.inl ⟨x, h, hx, hv⟩
    · exact Or.inr ⟨x, h, hx, hv⟩
  · rintro v (h | h)
    · exact placesOf_mono c le_sup_left h
    · exact placesOf_mono c le_sup_right h

/--
@isnad1 id=eq.0h3v.s7.0b5d9833dc36 from=translated src=- shape=79dc8cd5 vocab=2c3d7fc9
-/
theorem placesOf_bot :
    letI := (baseToFunctionField c).toAlgebra
    placesOf c (⊥ : C.Opens) = ∅ := by
  letI := (baseToFunctionField c).toAlgebra
  ext v
  simp only [Set.mem_empty_iff_false, iff_false]
  rintro ⟨x, hx, -, -⟩
  exact hx

end AlgebraicCurve

end
