import Tengoku.Seed.Data.Matrix.Basic
import Tengoku.Seed.Data.Fin.VecNotation
import Tengoku.Seed.LinearAlgebra.Matrix.Determinant.Basic
import Tengoku.Seed.LinearAlgebra.Matrix.NonsingularInverse

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_Matrix_exists_adapted_frob_shape.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_Matrix_exists_adapted_frob_shape

set_option autoImplicit false

private def sl2M {R : Type} [CommRing R] (s t u : R) : Matrix (Fin 2) (Fin 2) R :=
  Matrix.of ![![s, t], ![u, -s]]

private theorem frob_shape_of_line {R : Type} [CommRing R] (F : Matrix (Fin 2) (Fin 2) R)
    (t q : R) (ht : ∀ r : R, t * r = 0 → r = 0)
    (hFN : F * sl2M 0 t 0 = q • (sl2M 0 t 0 * F)) : F 1 0 = 0 ∧ F 0 0 = q * F 1 1 := by
  have hL : F * sl2M 0 t 0 = Matrix.of ![![0, F 0 0 * t], ![0, F 1 0 * t]] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [sl2M, Matrix.mul_apply, Fin.sum_univ_two]
  have hR : q • (sl2M 0 t 0 * F) = Matrix.of ![![q * (t * F 1 0), q * (t * F 1 1)], ![0, 0]] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp only [Matrix.smul_apply, Matrix.mul_apply, Fin.sum_univ_two, smul_eq_mul] <;> simp [sl2M]
  rw [hL, hR] at hFN
  have h11 : F 1 0 * t = 0 := congrFun (congrFun hFN 1) 1
  have h01 : F 0 0 * t = q * (t * F 1 1) := congrFun (congrFun hFN 0) 1
  have h10 : F 1 0 = 0 := ht _ (by rw [mul_comm]; exact h11)
  refine ⟨h10, ?_⟩
  have : t * (F 0 0 - q * F 1 1) = 0 := by
    calc t * (F 0 0 - q * F 1 1) = F 0 0 * t - q * (t * F 1 1) := by ring
      _ = 0 := by rw [h01, sub_self]
  exact sub_eq_zero.mp (ht _ this)

/--
@isnad1 id=ex.4h6v.s10.419f1b2b0ab5 from=translated src=- shape=a9bc3d75 vocab=daf43213
-/
theorem solution {R : Type} [CommRing R] [IsDomain R]
    (N₀ P F : Matrix (Fin 2) (Fin 2) R) (hP : IsUnit P.det)
    (t : R) (ht : t ≠ 0) (hN₀P : N₀ * P = P * Matrix.of ![![0, t], ![0, 0]])
    (q : R) (hFN : F * N₀ = q • (N₀ * F)) :
    ∃ F' : Matrix (Fin 2) (Fin 2) R,
      F * P = P * F' ∧ F' 1 0 = 0 ∧ F' 0 0 = q * F' 1 1 := by
  haveI := P.invertibleOfIsUnitDet hP
  have hline : Matrix.of ![![0, t], ![0, 0]] = sl2M 0 t 0 := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [sl2M]
  rw [hline] at hN₀P
  have ht' : ∀ r : R, t * r = 0 → r = 0 := fun r hr => (mul_eq_zero.mp hr).resolve_left ht
  have htE : sl2M 0 t 0 = ⅟P * N₀ * P := by
    rw [Matrix.mul_assoc, hN₀P, ← Matrix.mul_assoc, invOf_mul_self, Matrix.one_mul]
  have hFP : F * P = P * (⅟P * F * P) := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, mul_invOf_self, Matrix.one_mul]
  have hshuffle : ∀ X Y : Matrix (Fin 2) (Fin 2) R,
      (⅟P * X * P) * (⅟P * Y * P) = ⅟P * (X * Y) * P := by
    intro X Y
    calc (⅟P * X * P) * (⅟P * Y * P)
        = ⅟P * X * (P * (⅟P * (Y * P))) := by simp only [Matrix.mul_assoc]
      _ = ⅟P * X * ((P * ⅟P) * (Y * P)) := by rw [← Matrix.mul_assoc P]
      _ = ⅟P * (X * Y) * P := by
          rw [mul_invOf_self, Matrix.one_mul]; simp only [Matrix.mul_assoc]
  have hF'tE : (⅟P * F * P) * sl2M 0 t 0 = q • (sl2M 0 t 0 * (⅟P * F * P)) := by
    rw [htE, hshuffle, hshuffle, hFN]
    rw [Matrix.mul_smul, Matrix.smul_mul]
  obtain ⟨h10, h00⟩ := frob_shape_of_line (⅟P * F * P) t q ht' hF'tE
  exact ⟨⅟P * F * P, hFP, h10, h00⟩
