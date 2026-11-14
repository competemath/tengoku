import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/
namespace Tengoku.FltAnthropic end Tengoku.FltAnthropic open Tengoku.FltAnthropic
set_option autoImplicit false

/--
@isnad1 id=isalgebr.0h0v.s4.92f995461263 from=translated src=- shape=3905abf2 vocab=c7f7e443
-/
local instance _root_.Tengoku.FltAnthropic.isAlgebraicQbar_cc : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) :=
  AlgebraicClosure.isAlgebraic ℚ
/--
@isnad1 id=isalgclo.0h0v.s4.728a7497b292 from=translated src=- shape=3905abf2 vocab=f41c73d6
-/
local instance _root_.Tengoku.FltAnthropic.isAlgClosureQbar_cc : IsAlgClosure ℚ (AlgebraicClosure ℚ) :=
  ⟨inferInstance, inferInstance⟩
/--
@isnad1 id=normal.0h0v.s4.8393bcded6c9 from=translated src=- shape=3905abf2 vocab=399da0a7
-/
local instance _root_.Tengoku.FltAnthropic.normalQbar_cc : Normal ℚ (AlgebraicClosure ℚ) :=
  IsAlgClosure.normal ℚ (AlgebraicClosure ℚ)
noncomputable local instance _root_.Tengoku.FltAnthropic.instDecEqQbar_cc : DecidableEq (AlgebraicClosure ℚ) :=
  Classical.decEq _

noncomputable def _root_.Tengoku.FltAnthropic.complexEmbedding : AlgebraicClosure ℚ →ₐ[ℚ] ℂ :=
  IsAlgClosed.lift

noncomputable local instance _root_.Tengoku.FltAnthropic.instAlgebraQbarComplex : Algebra (AlgebraicClosure ℚ) ℂ :=
  complexEmbedding.toRingHom.toAlgebra
/--
@isnad1 id=isscalar.0h0v.s5.4c801ce3dcde from=translated src=- shape=1bdc2383 vocab=cf340cf2
-/
local instance _root_.Tengoku.FltAnthropic.instTowerQbarComplex : IsScalarTower ℚ (AlgebraicClosure ℚ) ℂ :=
  IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)

noncomputable def _root_.Tengoku.FltAnthropic.complexConjAlgEquiv : ℂ ≃ₐ[ℚ] ℂ :=
  AlgEquiv.ofRingEquiv (f := starRingAut) fun x => map_ratCast (starRingEnd ℂ) x

/--
@isnad1 id=eq.0h1v.s6.c8a42517a8ca from=translated src=- shape=e23240ae vocab=f32f4191
-/
@[simp] lemma _root_.Tengoku.FltAnthropic.complexConjAlgEquiv_apply (z : ℂ) : complexConjAlgEquiv z = starRingEnd ℂ z := rfl

/--
@isnad1 id=eq.0h0v.s8.30bdc4e50764 from=translated src=- shape=4d8ef88e vocab=aac4edb1
-/
lemma _root_.Tengoku.FltAnthropic.complexConjAlgEquiv_mul_self : complexConjAlgEquiv * complexConjAlgEquiv = 1 :=
  AlgEquiv.ext fun z => Complex.conj_conj z

noncomputable def _root_.Tengoku.FltAnthropic.complexConjugation : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ :=
  AlgEquiv.restrictNormalHom (F := ℚ) (K₁ := ℂ) (AlgebraicClosure ℚ) complexConjAlgEquiv

/--
@isnad1 id=eq.0h1v.s8.99031ebac9ec from=translated src=- shape=18bf196c vocab=93dae930
-/
theorem _root_.Tengoku.FltAnthropic.complexEmbedding_complexConjugation (x : AlgebraicClosure ℚ) :
    complexEmbedding (complexConjugation x) = starRingEnd ℂ (complexEmbedding x) :=
  AlgEquiv.restrictNormal_commutes complexConjAlgEquiv (AlgebraicClosure ℚ) x

/--
@isnad1 id=eq.0h0v.s10.8e5776bb277f from=translated src=- shape=28d506fc vocab=0b82e45a
-/
theorem _root_.Tengoku.FltAnthropic.complexConjugation_mul_self : complexConjugation * complexConjugation = 1 := by
  rw [complexConjugation, ← map_mul, complexConjAlgEquiv_mul_self, map_one]

/--
@isnad1 id=eq.0h0v.s9.cbd3c8c1796d from=translated src=- shape=84d5b544 vocab=15b8a67b
-/
theorem _root_.Tengoku.FltAnthropic.complexConjugation_sq : complexConjugation ^ 2 = 1 := by
  rw [sq]; exact complexConjugation_mul_self

/--
@isnad1 id=eq.0h0v.s8.0375c7e4e521 from=translated src=- shape=43ca4396 vocab=7df3d9e0
-/
theorem _root_.Tengoku.FltAnthropic.complexConjugation_inv : complexConjugation⁻¹ = complexConjugation :=
  inv_eq_of_mul_eq_one_right complexConjugation_mul_self

namespace ExtCitation

noncomputable def archimedeanDecomposition :
    Subgroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :=
  Subgroup.zpowers complexConjugation

noncomputable def archimedeanGen : archimedeanDecomposition :=
  ⟨complexConjugation, Subgroup.mem_zpowers complexConjugation⟩

noncomputable def archimedeanLoc :
    archimedeanDecomposition →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :=
  archimedeanDecomposition.subtype

/--
@isnad1 id=eq.0h0v.s12.942abcec6a94 from=translated src=- shape=0eacc5c8 vocab=a6c276f4
-/
@[simp] lemma archimedeanLoc_archimedeanGen :
    archimedeanLoc archimedeanGen = complexConjugation := rfl

end ExtCitation
-- Tengoku: root names of this library moved to Tengoku.FltAnthropic so they do not collide with other libraries (generated)
