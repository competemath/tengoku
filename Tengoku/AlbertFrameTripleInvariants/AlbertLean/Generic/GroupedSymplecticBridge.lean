import Tengoku.Seed.LinearAlgebra.Matrix.NonsingularInverse
import Tengoku.Seed.Tactic.FinCases
import Tengoku.Seed.Tactic.Ring
import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generic.QuaternionHatAdjugate

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms grouped_symplectic_selfadjoint` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms scalarSimilitude_form` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms scalarSimilitude_conjugates_grouped` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms scalarSimilitude_map_jordan` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms scalarSimilitude_map_one` (it only prints; the queue checks the axioms of every declaration). -/

/-! The literal grouped `W ⊕ W*` six-dimensional realization.  The existing
interleaved `Fin 3 × Fin 2` split-quaternion basis is related by a permutation;
no definitional equality between those carriers is asserted here. -/

noncomputable section
namespace AlbertLean.Generic.QuaternionRow.GroupedBridge

open AlbertLean.Generic.QuaternionRow.ScalarFibre

universe u
variable {K : Type u} [Field K] [CharZero K]

abbrev Ix6 := Sum (Fin 3) (Fin 3)
abbrev Mat6 (K : Type u) := Matrix Ix6 Ix6 K

/-- `J = [[0,I],[-I,0]]` in the grouped basis.-/
def symplecticJ : Mat6 K :=
  Matrix.fromBlocks 0 1 (-1) 0

/-- `[[a,hat u],[hat v,aᵀ]]` in exactly the workshop convention.-/
def grouped (a : Mat3 K) (u v : Vec3 K) : Mat6 K :=
  Matrix.fromBlocks a (hat u) (hat v) a.transpose

/--
@isnad1 id=eq.0h2v.s6.74f1d63b2bf7 from=translated src=- shape=4475fbad vocab=19a03f87
-/
@[simp] theorem hat_transpose (u : Vec3 K) : (hat u).transpose = -hat u := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hat, Matrix.transpose_apply]

/--
@isnad1 id=eq.0h3v.s6.dc7bcaddf98b from=translated src=- shape=67b8137e vocab=97f31c76
-/
@[simp] theorem hat_smul (t : K) (u : Vec3 K) : hat (t • u) = t • hat u := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hat]

/-- The grouped matrices are precisely presented with the required
symplectic-selfadjoint sign: `PᵀJ=JP`.
@isnad1 id=eq.0h4v.s7.2502a1bea59d from=translated src=- shape=04713b1f vocab=451dbf3b
-/
theorem grouped_symplectic_selfadjoint (a : Mat3 K) (u v : Vec3 K) :
    (grouped a u v).transpose * symplecticJ =
      symplecticJ * grouped a u v := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    fin_cases i <;> fin_cases j <;>
    simp [grouped, symplecticJ, Matrix.mul_apply, Fintype.sum_sum_type,
      Matrix.transpose_apply, Matrix.one_apply, Fin.sum_univ_succ, hat] <;> ring

/-- The rational similitude `diag(tI,I)`.-/
def scalarSimilitude (t : K) : Mat6 K :=
  Matrix.fromBlocks (t • (1 : Mat3 K)) 0 0 1

def scalarSimilitudeInv (t : K) : Mat6 K :=
  Matrix.fromBlocks (t⁻¹ • (1 : Mat3 K)) 0 0 1

/--
@isnad1 id=eq.1h2v.s7.1138c4e20003 from=translated src=- shape=39ced7a1 vocab=4d2fdd6d
-/
theorem scalarSimilitude_mul_inv (t : K) (ht : t ≠ 0) :
    scalarSimilitude t * scalarSimilitudeInv t = 1 := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    fin_cases i <;> fin_cases j <;>
    simp [scalarSimilitude, scalarSimilitudeInv, Matrix.mul_apply,
      Fintype.sum_sum_type, Matrix.one_apply, Fin.sum_univ_succ, ht]

/--
@isnad1 id=eq.1h2v.s7.e6db49f0ac15 from=translated src=- shape=39ced7a1 vocab=4d2fdd6d
-/
theorem scalarSimilitude_inv_mul (t : K) (ht : t ≠ 0) :
    scalarSimilitudeInv t * scalarSimilitude t = 1 := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    fin_cases i <;> fin_cases j <;>
    simp [scalarSimilitude, scalarSimilitudeInv, Matrix.mul_apply,
      Fintype.sum_sum_type, Matrix.one_apply, Fin.sum_univ_succ, ht]

/-- Direct calculation of `h_tᵀ J h_t=tJ`; this is a similitude, and no
square root of `t` is chosen.
@isnad1 id=eq.0h2v.s7.492dbf304c25 from=translated src=- shape=5c07be5b vocab=db9e0c12
-/
theorem scalarSimilitude_form (t : K) :
    (scalarSimilitude t).transpose * symplecticJ * scalarSimilitude t =
      t • symplecticJ := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    fin_cases i <;> fin_cases j <;>
    simp [scalarSimilitude, symplecticJ, Matrix.mul_apply,
      Fintype.sum_sum_type, Matrix.transpose_apply, Matrix.one_apply,
      Fin.sum_univ_succ] <;> ring

/-- Conjugation gives exactly `(a,u,v) ↦ (a,tu,t⁻¹v)` in grouped
coordinates.
@isnad1 id=eq.1h5v.s8.5de2096eb81b from=translated src=- shape=8af33984 vocab=54effb4e
-/
theorem scalarSimilitude_conjugates_grouped
    (t : K) (ht : t ≠ 0) (a : Mat3 K) (u v : Vec3 K) :
    scalarSimilitude t * grouped a u v * scalarSimilitudeInv t =
      grouped a (t • u) (t⁻¹ • v) := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    fin_cases i <;> fin_cases j <;>
    simp [scalarSimilitude, scalarSimilitudeInv, grouped, hat,
      Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply,
      Fin.sum_univ_succ, ht] <;> field_simp [ht] <;> ring

def matrixJordan (A B : Mat6 K) : Mat6 K :=
  (2 : K)⁻¹ • (A * B + B * A)

/-- Associativity alone proves that conjugation by the displayed inverse is
an actual unital linear Jordan automorphism of the ambient matrix algebra.
@isnad1 id=eq.1h4v.s8.5ba33b410740 from=translated src=- shape=8fbec12b vocab=5e476dd5
-/
theorem scalarSimilitude_map_jordan
    (t : K) (ht : t ≠ 0) (A B : Mat6 K) :
    scalarSimilitude t * matrixJordan A B * scalarSimilitudeInv t =
      matrixJordan
        (scalarSimilitude t * A * scalarSimilitudeInv t)
        (scalarSimilitude t * B * scalarSimilitudeInv t) := by
  have hmul (X Y : Mat6 K) :
      scalarSimilitude t * (X * Y) * scalarSimilitudeInv t =
        (scalarSimilitude t * X * scalarSimilitudeInv t) *
          (scalarSimilitude t * Y * scalarSimilitudeInv t) := by
    symm
    calc
      (scalarSimilitude t * X * scalarSimilitudeInv t) *
          (scalarSimilitude t * Y * scalarSimilitudeInv t) =
        scalarSimilitude t * X *
          (scalarSimilitudeInv t * scalarSimilitude t) * Y *
            scalarSimilitudeInv t := by simp only [Matrix.mul_assoc]
      _ = scalarSimilitude t * X * 1 * Y * scalarSimilitudeInv t := by
        rw [scalarSimilitude_inv_mul t ht]
      _ = scalarSimilitude t * (X * Y) * scalarSimilitudeInv t := by
        simp [Matrix.mul_assoc]
  simp only [matrixJordan, Matrix.mul_smul, Matrix.smul_mul]
  rw [Matrix.mul_add, Matrix.add_mul]
  rw [hmul A B, hmul B A]

/--
@isnad1 id=eq.1h2v.s8.567ff63e5f65 from=translated src=- shape=a2f99aa1 vocab=4d2fdd6d
-/
theorem scalarSimilitude_map_one (t : K) (ht : t ≠ 0) :
    scalarSimilitude t * (1 : Mat6 K) * scalarSimilitudeInv t = 1 := by
  simpa using scalarSimilitude_mul_inv t ht

end AlbertLean.Generic.QuaternionRow.GroupedBridge
