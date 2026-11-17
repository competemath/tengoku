import Tengoku.FltAnthropic.Definitions.Def_AlgebraicGeometry_ThetaLevelGroup

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_AlgebraicGeometry_ThetaLevel_schrodMat_one_and_schrodMat_mul.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_AlgebraicGeometry_ThetaLevel_schrodMat_one_and_schrodMat_mul

set_option autoImplicit false

open scoped BigOperators
open AlgebraicGeometry AlgebraicGeometry.ThetaLevel

namespace K77TH3
namespace HeisHom

variable {g : ℕ} (δ : Fin g → ℕ) [∀ i, NeZero (δ i)] (d : ℕ) [NeZero d] (B : Type) [CommRing B] (ω : B)

/--
@isnad1 id=eq.0h8v.s9.a3cc28176846 from=translated src=- shape=b3d8218a vocab=2c6b35f0
-/
theorem schrod_single (z : Heis δ d) (y x : HH δ) :
    schrod δ d B ω z (Pi.single y 1) x =
      if x = y + z.h then omegaPow d B ω z.a * omegaPow d B ω (pair δ d z.k y) else 0 := by
  rw [schrod_apply]
  by_cases hx : x = y + z.h
  · subst hx
    rw [ite_eq_left rfl, thetaChar, add_sub_cancel_right, Pi.single_eq_same, mul_one]
  · have : x - z.h ≠ y := fun h' => hx (by rw [← h']; abel)
    simp [this, hx]

/--
@isnad1 id=eq.1h8v.s11.ef9b71dc7732 from=translated src=- shape=60f3c951 vocab=e77e1eac
-/
theorem schrodMat_eq_submatrix (hω : ω ^ (2 * d) = 1) {n : ℕ} (e : Fin n ≃ HH δ) (z : Heis δ d) :
    schrodMat δ d B ω e z =
      (LinearMap.toMatrix (Pi.basisFun B (HH δ)) (Pi.basisFun B (HH δ)) (schrod δ d B ω z)).submatrix e e := by
  ext i j
  rw [Matrix.submatrix_apply, LinearMap.toMatrix_apply, Pi.basisFun_repr, Pi.basisFun_apply, schrod_single,
    schrodMat_apply]
  by_cases hij : e i = e j + z.h
  · rw [ite_eq_left hij, ite_eq_left hij, omegaPow_add d B ω hω]
  · rw [ite_eq_right hij, ite_eq_right hij]

end K77TH3.HeisHom

open K77TH3.HeisHom in
/--
@isnad1 id=and.1h7v.s8.d239377a20c7 from=translated src=- shape=5fff70de vocab=ebd282e7
-/
theorem solution
    {g : ℕ} (δ : Fin g → ℕ) [∀ i, NeZero (δ i)] (d : ℕ) [NeZero d] (B : Type) [CommRing B] (ω : B) (hω : ω ^ (2 * d) = 1)
    {n : ℕ} (e : Fin n ≃ HH δ) :
    schrodMat δ d B ω e 1 = 1 ∧
      ∀ z z' : Heis δ d, schrodMat δ d B ω e (z * z') = schrodMat δ d B ω e z * schrodMat δ d B ω e z' := by
  refine ⟨?_, fun z z' => ?_⟩
  · rw [schrodMat_eq_submatrix δ d B ω hω e, schrod_one, LinearMap.toMatrix_id, Matrix.submatrix_one_equiv]
  · rw [schrodMat_eq_submatrix δ d B ω hω e, schrodMat_eq_submatrix δ d B ω hω e, schrodMat_eq_submatrix δ d B ω hω e,
      schrod_mul δ d B ω hω, LinearMap.toMatrix_comp (Pi.basisFun B (HH δ)) (Pi.basisFun B (HH δ)) (Pi.basisFun B (HH δ)),
      Matrix.submatrix_mul_equiv]
