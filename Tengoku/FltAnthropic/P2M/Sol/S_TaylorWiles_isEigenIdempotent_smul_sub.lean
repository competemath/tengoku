import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_Deformations_LocalSplitting
import Tengoku.FltAnthropic.Theorems.Thm_Matrix_sub_smul_one_mul_sub_smul_one_eq_zero

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_TaylorWiles_isEigenIdempotent_smul_sub.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_TaylorWiles_isEigenIdempotent_smul_sub

set_option autoImplicit false

universe u v

open Matrix

namespace Ws14Port
open TaylorWiles

variable {A : Type u} [CommRing A]

/--
@isnad1 id=eq.0h1v.s6.e38d83a7a913 from=translated src=- shape=28c9e97e vocab=2259428a
-/
theorem trace_one_fin_two : (1 : Matrix (Fin 2) (Fin 2) A).trace = 2 := by
  rw [Matrix.trace_one, Fintype.card_fin, Nat.cast_ofNat]

end Ws14Port

open TaylorWiles in
/--
@isnad1 id=iseigeni.3h5v.s8.b0136a357955 from=translated src=- shape=2013e5d7 vocab=1e7b731d
-/
theorem solution {A : Type u} [CommRing A] {M : Matrix (Fin 2) (Fin 2) A} {a b v : A}
    (htr : M.trace = a + b) (hdet : M.det = a * b) (hv : v * (a - b) = 1) :
    TaylorWiles.IsEigenIdempotent M a b (v • (M - b • (1 : Matrix (Fin 2) (Fin 2) A))) := by
  have hfact := Matrix.sub_smul_one_mul_sub_smul_one_eq_zero htr hdet
  have hfact' : (M - b • (1 : Matrix (Fin 2) (Fin 2) A)) * (M - a • (1 : Matrix (Fin 2) (Fin 2) A)) = 0 :=
    Matrix.sub_smul_one_mul_sub_smul_one_eq_zero (by rw [htr]; ring) (by rw [hdet]; ring)
  have hexp : M - a • (1 : Matrix (Fin 2) (Fin 2) A) + (a - b) • (1 : Matrix (Fin 2) (Fin 2) A) = M - b • (1 : Matrix (Fin 2) (Fin 2) A) := by
    rw [sub_smul]; abel
  have hsq : (M - b • (1 : Matrix (Fin 2) (Fin 2) A)) * (M - b • (1 : Matrix (Fin 2) (Fin 2) A)) =
      (a - b) • (M - b • (1 : Matrix (Fin 2) (Fin 2) A)) := by
    nth_rewrite 2 [← hexp]
    rw [mul_add, hfact', mul_smul_comm, mul_one, zero_add]
  have hMe : M * (M - b • (1 : Matrix (Fin 2) (Fin 2) A)) = a • (M - b • (1 : Matrix (Fin 2) (Fin 2) A)) := by
    have hexp2 : M - a • (1 : Matrix (Fin 2) (Fin 2) A) + a • (1 : Matrix (Fin 2) (Fin 2) A) = M := by abel
    nth_rewrite 1 [← hexp2]
    rw [add_mul, hfact, smul_mul_assoc, one_mul, zero_add]
  have hMe' : M * (M - a • (1 : Matrix (Fin 2) (Fin 2) A)) = b • (M - a • (1 : Matrix (Fin 2) (Fin 2) A)) := by
    have hexp2 : M - b • (1 : Matrix (Fin 2) (Fin 2) A) + b • (1 : Matrix (Fin 2) (Fin 2) A) = M := by abel
    nth_rewrite 1 [← hexp2]
    rw [add_mul, hfact', smul_mul_assoc, one_mul, zero_add]
  have hsub : (M - b • (1 : Matrix (Fin 2) (Fin 2) A)) - (M - a • (1 : Matrix (Fin 2) (Fin 2) A)) = (a - b) • (1 : Matrix (Fin 2) (Fin 2) A) := by
    rw [sub_smul]; abel
  have hsum : v • (M - b • (1 : Matrix (Fin 2) (Fin 2) A)) + (-v) • (M - a • (1 : Matrix (Fin 2) (Fin 2) A)) = 1 := by
    rw [neg_smul, ← sub_eq_add_neg, ← smul_sub, hsub, smul_smul, hv, one_smul]
  have hcompl : (1 : Matrix (Fin 2) (Fin 2) A) - v • (M - b • (1 : Matrix (Fin 2) (Fin 2) A)) = (-v) • (M - a • (1 : Matrix (Fin 2) (Fin 2) A)) := by
    nth_rewrite 1 [← hsum]
    abel
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [smul_mul_assoc, mul_smul_comm, hsq, smul_smul, smul_smul, mul_assoc, hv, mul_one]
  · rw [Matrix.trace_smul, Matrix.trace_sub, Matrix.trace_smul, htr, Ws14Port.trace_one_fin_two,
      smul_eq_mul, smul_eq_mul, show a + b - b * 2 = a - b by ring, hv]
  · rw [mul_smul_comm, hMe, smul_smul, smul_smul, mul_comm v a]
  · rw [hcompl, mul_smul_comm, hMe', smul_smul, smul_smul, mul_comm b (-v)]
