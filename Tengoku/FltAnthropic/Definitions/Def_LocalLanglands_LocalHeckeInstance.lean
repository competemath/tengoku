import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_LocalLanglands_HeckePair
import Tengoku.FltAnthropic.Definitions.Def_LocalLanglands_CartanDecomposition

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

open Matrix

noncomputable section

namespace LocalGL2

def integralSubgroup (R K : Type*) [CommRing R] [Field K] [Algebra R K] :
    Subgroup (GL (Fin 2) K) :=
  (Matrix.GeneralLinearGroup.map (n := Fin 2) (algebraMap R K)).range

/--
@isnad1 id=iff.0h3v.s9.ab94fa7091e1 from=translated src=- shape=72a2c5d4 vocab=66e8ab78
-/
theorem mem_integralSubgroup_iff {R K : Type*} [CommRing R] [Field K] [Algebra R K]
    {x : GL (Fin 2) K} :
    x ∈ integralSubgroup R K ↔
      ∃ y : GL (Fin 2) R, Matrix.GeneralLinearGroup.map (algebraMap R K) y = x :=
  Iff.rfl

section Transpose

variable {A : Type*} [CommRing A]

def transposeGL (x : GL (Fin 2) A) : GL (Fin 2) A where
  val := x.valᵀ
  inv := x.invᵀ
  val_inv := by rw [← Matrix.transpose_mul, x.inv_val, Matrix.transpose_one]
  inv_val := by rw [← Matrix.transpose_mul, x.val_inv, Matrix.transpose_one]

/--
@isnad1 id=eq.0h2v.s7.b488aca427cf from=translated src=- shape=55adc562 vocab=2bc84513
-/
@[simp] theorem transposeGL_val (x : GL (Fin 2) A) :
    (transposeGL x : Matrix (Fin 2) (Fin 2) A) = (x : Matrix (Fin 2) (Fin 2) A)ᵀ := rfl

/--
@isnad1 id=eq.0h3v.s8.0aff65809a9f from=translated src=- shape=a87c6ae4 vocab=89c20cc1
-/
theorem transposeGL_mul (x y : GL (Fin 2) A) :
    transposeGL (x * y) = transposeGL y * transposeGL x := by
  refine Units.ext ?_
  rw [Units.val_mul, transposeGL_val, transposeGL_val, transposeGL_val, Units.val_mul,
    Matrix.transpose_mul]

/--
@isnad1 id=eq.0h2v.s6.e08340a7419d from=translated src=- shape=75e5737b vocab=f26b0203
-/
theorem transposeGL_involutive (x : GL (Fin 2) A) : transposeGL (transposeGL x) = x := by
  refine Units.ext ?_
  rw [transposeGL_val, transposeGL_val, Matrix.transpose_transpose]

/--
@isnad1 id=eq.0h1v.s7.26148ae506d9 from=translated src=- shape=1eda0a34 vocab=2692cf07
-/
@[simp] theorem transposeGL_one : transposeGL (1 : GL (Fin 2) A) = 1 := by
  refine Units.ext ?_
  rw [transposeGL_val, Units.val_one, Matrix.transpose_one]

end Transpose

section IntegralPreservation

variable {R : Type*} [CommRing R] {K : Type*} [Field K] [Algebra R K]

/--
@isnad1 id=eq.0h3v.s10.b7aacbee2eda from=translated src=- shape=8b91c06c vocab=f3421550
-/
theorem transposeGL_map_algebraMap (y : GL (Fin 2) R) :
    transposeGL (Matrix.GeneralLinearGroup.map (n := Fin 2) (algebraMap R K) y)
      = Matrix.GeneralLinearGroup.map (algebraMap R K) (transposeGL y) := by
  refine Units.ext ?_
  show ((Matrix.GeneralLinearGroup.map (algebraMap R K) y :
      Matrix (Fin 2) (Fin 2) K))ᵀ = _
  ext i j
  simp [Matrix.transpose_apply]

/--
@isnad1 id=mem.1h3v.s9.293f72c41448 from=translated src=- shape=8a4dcd3f vocab=67efc7a8
-/
theorem transposeGL_mem_integralSubgroup {x : GL (Fin 2) K} (hx : x ∈ integralSubgroup R K) :
    transposeGL x ∈ integralSubgroup R K := by
  obtain ⟨y, rfl⟩ := hx
  exact ⟨transposeGL y, (transposeGL_map_algebraMap y).symm⟩

/--
@isnad1 id=eq.0h3v.s7.4f9cffe43a37 from=translated src=- shape=48a32f25 vocab=49599540
-/
theorem det_map_algebraMap (M : Matrix (Fin 2) (Fin 2) R) :
    (M.map (algebraMap R K)).det = algebraMap R K M.det := by
  simp [Matrix.det_fin_two]

end IntegralPreservation

end LocalGL2

end
