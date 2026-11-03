import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generic.ComplexPairPolynomial
import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generic.C1Coordinates
import Tengoku.Seed.LinearAlgebra.Matrix.NonsingularInverse
import Tengoku.Seed.Tactic.FinCases
import Tengoku.Seed.Tactic.FieldSimp
import Tengoku.Seed.Tactic.Ring

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms dephased_inv_eq` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms overlap_table` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms pairQuadratic_root` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms reconstruct_entries` (it only prints; the queue checks the axioms of every declaration). -/

noncomputable section
namespace AlbertLean.Generic.ComplexDephasedPair

open C1Coordinates ComplexPairPolynomial

universe u
variable {K : Type u} [Field K]

def dephased (a b c d : K) : Mat3 K :=
  !![1, 1, 1; 1, a, b; 1, c, d]

def delta (a b c d : K) : K := a * d - b * c - d + b + c - a

def cofactorInverseNumerator (a b c d : K) : Mat3 K :=
  !![a*d-b*c, c-d, b-a;
     b-d, d-1, 1-b;
     c-a, 1-c, a-1]

/--
@isnad1 id=eq.0h5v.s5.7a4692db5482 from=translated src=- shape=5b285464 vocab=84b1c319
-/
theorem det_dephased (a b c d : K) :
    Matrix.det (dephased a b c d) = delta a b c d := by
  simp [dephased, delta, Matrix.det_fin_three]

/--
@isnad1 id=eq.0h5v.s7.d8702b7a996f from=translated src=- shape=a33159d8 vocab=69e46885
-/
theorem cofactor_mul (a b c d : K) :
    cofactorInverseNumerator a b c d * dephased a b c d =
      delta a b c d • (1 : Mat3 K) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [cofactorInverseNumerator, dephased, delta, Matrix.mul_apply,
      Fin.sum_univ_succ] <;> ring

/--
@isnad1 id=eq.0h5v.s7.fea86a6d13f8 from=translated src=- shape=a33159d8 vocab=69e46885
-/
theorem dephased_mul_cofactor (a b c d : K) :
    dephased a b c d * cofactorInverseNumerator a b c d =
      delta a b c d • (1 : Mat3 K) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [cofactorInverseNumerator, dephased, delta, Matrix.mul_apply,
      Fin.sum_univ_succ] <;> ring

/--
@isnad1 id=eq.1h5v.s7.e75d1e348cc4 from=translated src=- shape=517900e8 vocab=5fb04567
-/
theorem dephased_inv_eq (a b c d : K) (hΔ : delta a b c d ≠ 0) :
    (dephased a b c d)⁻¹ =
      (delta a b c d)⁻¹ • cofactorInverseNumerator a b c d := by
  apply Matrix.inv_eq_left_inv
  rw [Matrix.smul_mul, cofactor_mul, smul_smul]
  simp [hΔ]

/-- Literal overlap table `Pᵢⱼ=Xᵢⱼ(X⁻¹)ⱼᵢ`.-/
def overlap (a b c d : K) (i j : Fin 3) : K :=
  dephased a b c d i j * (dephased a b c d)⁻¹ j i

/--
@isnad1 id=eq.1h5v.s9.bb5967c916bc from=translated src=- shape=a6d8f538 vocab=d23959e1
-/
theorem overlap_table (a b c d : K) (hΔ : delta a b c d ≠ 0) :
    (fun i j => overlap a b c d i j) =
      !![(a*d-b*c)/delta a b c d,
          (b-d)/delta a b c d, (c-a)/delta a b c d;
         (c-d)/delta a b c d,
          a*(d-1)/delta a b c d, b*(1-c)/delta a b c d;
         (b-a)/delta a b c d,
          c*(1-b)/delta a b c d, d*(a-1)/delta a b c d] := by
  funext i j
  unfold overlap
  rw [dephased_inv_eq a b c d hΔ]
  fin_cases i <;> fin_cases j <;>
    simp [dephased, cofactorInverseNumerator, div_eq_mul_inv] <;> ring

/--
@isnad1 id=other.1h5v.s8.1aaaed926499 from=translated src=- shape=9b544c9d vocab=ac6d5acd
-/
theorem nu_mul_delta (a b c d : K) (hΔ : delta a b c d ≠ 0) :
    let p := overlap a b c d 0 0
    let q := overlap a b c d 0 1
    let r := overlap a b c d 1 0
    let s := overlap a b c d 1 1
    nu p q r s d * delta a b c d = d * (d - 1) := by
  rw [show overlap a b c d 0 0 = (a*d-b*c)/delta a b c d by
        simpa using congrFun (congrFun (overlap_table a b c d hΔ) 0) 0,
      show overlap a b c d 0 1 = (b-d)/delta a b c d by
        simpa using congrFun (congrFun (overlap_table a b c d hΔ) 0) 1,
      show overlap a b c d 1 0 = (c-d)/delta a b c d by
        simpa using congrFun (congrFun (overlap_table a b c d hΔ) 1) 0,
      show overlap a b c d 1 1 = a*(d-1)/delta a b c d by
        simpa using congrFun (congrFun (overlap_table a b c d hΔ) 1) 1]
  unfold nu
  field_simp
  unfold delta
  ring

/--
@isnad1 id=eq.1h5v.s7.921bfc2698be from=translated src=- shape=d220c17e vocab=c0902bfa
-/
theorem pairQuadratic_root (a b c d : K) (hΔ : delta a b c d ≠ 0) :
    pairQuadratic (overlap a b c d 0 0) (overlap a b c d 0 1)
      (overlap a b c d 1 0) (overlap a b c d 1 1) d = 0 := by
  rw [show overlap a b c d 0 0 = (a*d-b*c)/delta a b c d by
        simpa using congrFun (congrFun (overlap_table a b c d hΔ) 0) 0,
      show overlap a b c d 0 1 = (b-d)/delta a b c d by
        simpa using congrFun (congrFun (overlap_table a b c d hΔ) 0) 1,
      show overlap a b c d 1 0 = (c-d)/delta a b c d by
        simpa using congrFun (congrFun (overlap_table a b c d hΔ) 1) 0,
      show overlap a b c d 1 1 = a*(d-1)/delta a b c d by
        simpa using congrFun (congrFun (overlap_table a b c d hΔ) 1) 1]
  unfold pairQuadratic
  field_simp
  unfold delta
  ring

/-- Reconstruction of the other dephased entries from the four northwest
overlaps and a legal chosen root `d`.
@isnad1 id=other.2h5v.s9.b6c0c5ea10f6 from=translated src=- shape=9d13987c vocab=b1316aed
-/
theorem reconstruct_entries (a b c d : K) (hΔ : delta a b c d ≠ 0)
    (hnu : nu (overlap a b c d 0 0) (overlap a b c d 0 1)
      (overlap a b c d 1 0) (overlap a b c d 1 1) d ≠ 0) :
    let p := overlap a b c d 0 0
    let q := overlap a b c d 0 1
    let r := overlap a b c d 1 0
    let s := overlap a b c d 1 1
    let χ := d * (d - 1) / nu p q r s d
    a = s * d / nu p q r s d ∧ b = d + q * χ ∧ c = d + r * χ := by
  have hnΔ := nu_mul_delta a b c d hΔ
  have hχ : d * (d - 1) /
      nu (overlap a b c d 0 0) (overlap a b c d 0 1)
        (overlap a b c d 1 0) (overlap a b c d 1 1) d =
      delta a b c d := by
    apply (div_eq_iff hnu).2
    simpa [mul_comm] using hnΔ.symm
  dsimp only
  rw [hχ]
  have ht := overlap_table a b c d hΔ
  have hs : overlap a b c d 1 1 = a * (d - 1) / delta a b c d := by
    simpa using congrFun (congrFun ht 1) 1
  have hq : overlap a b c d 0 1 = (b - d) / delta a b c d := by
    simpa using congrFun (congrFun ht 0) 1
  have hr : overlap a b c d 1 0 = (c - d) / delta a b c d := by
    simpa using congrFun (congrFun ht 1) 0
  constructor
  · apply (eq_div_iff hnu).2
    apply mul_right_cancel₀ hΔ
    rw [mul_assoc a, hnΔ, hs]
    field_simp
  · constructor
    · rw [hq, div_mul_cancel₀ _ hΔ]
      ring
    · rw [hr, div_mul_cancel₀ _ hΔ]
      ring

end AlbertLean.Generic.ComplexDephasedPair
