import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_Matrix_SpecialLinearGroup_trace_sq_le_four_of_isOfFinOrder.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_Matrix_SpecialLinearGroup_trace_sq_le_four_of_isOfFinOrder

set_option autoImplicit false

open scoped MatrixGroups

namespace FinordTrace

def a (t : ℤ) : ℕ → ℤ
  | 0 => 2
  | 1 => t
  | (k + 2) => t * a t (k + 1) - a t k

/--
@isnad1 id=eq.0h1v.s4.67b591080f2a from=translated src=- shape=0e0c2bda vocab=9c42a81e
-/
theorem a_zero (t : ℤ) : a t 0 = 2 := rfl
/--
@isnad1 id=eq.0h1v.s3.ec44e0c7ca14 from=translated src=- shape=bb0110a5 vocab=9c42a81e
-/
theorem a_one (t : ℤ) : a t 1 = t := rfl
/--
@isnad1 id=eq.0h2v.s5.beab2f38a8f4 from=translated src=- shape=5d40bff2 vocab=0977660b
-/
theorem a_add_two (t : ℤ) (k : ℕ) : a t (k + 2) = t * a t (k + 1) - a t k := rfl

/--
@isnad1 id=lt.1h2v.s5.af02d5cd15fe from=translated src=- shape=6ec7f032 vocab=b7921134
-/
theorem abs_a_lt_abs_a_succ {t : ℤ} (ht : 3 ≤ |t|) : ∀ k : ℕ, |a t k| < |a t (k + 1)| := by
  intro k
  induction k with
  | zero =>
    rw [a_zero, a_one]
    have : |(2 : ℤ)| = 2 := by norm_num
    omega
  | succ k ih =>
    rw [show k + 1 + 1 = k + 2 from rfl, a_add_two]
    have h1 : |t * a t (k + 1)| - |a t k| ≤ |t * a t (k + 1) - a t k| := abs_sub_abs_le_abs_sub _ _
    rw [abs_mul] at h1
    have h2 : 3 * |a t (k + 1)| ≤ |t| * |a t (k + 1)| :=
      mul_le_mul_of_nonneg_right ht (abs_nonneg _)
    have h3 : 0 ≤ |a t k| := abs_nonneg _
    omega

/--
@isnad1 id=lt.2h2v.s5.7b77f0ba0bed from=translated src=- shape=d46249da vocab=e7024ec4
-/
theorem two_lt_abs_a {t : ℤ} (ht : 3 ≤ |t|) : ∀ n : ℕ, 1 ≤ n → 2 < |a t n| := by
  intro n hn
  induction n with
  | zero => omega
  | succ n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hpos
    · rw [zero_add, a_one]; omega
    · have := abs_a_lt_abs_a_succ ht n
      have := ih hpos
      omega

/--
@isnad1 id=eq.1h1v.s8.e5917aab26e0 from=translated src=- shape=4badc1c8 vocab=1107d654
-/
theorem mul_self_eq (A : Matrix (Fin 2) (Fin 2) ℤ) (hdet : A.det = 1) :
    A * A = A.trace • A - 1 := by
  rw [Matrix.det_fin_two] at hdet
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
      Matrix.trace_fin_two, Matrix.one_apply, Fin.zero_eta, Fin.mk_one, Fin.isValue] <;>
    simp <;> nlinarith [hdet]

/--
@isnad1 id=eq.1h2v.s7.b5f5e0141ab6 from=translated src=- shape=f5145a3a vocab=29fdc597
-/
theorem trace_pow_eq_a (A : Matrix (Fin 2) (Fin 2) ℤ) (hdet : A.det = 1) :
    ∀ k : ℕ, (A ^ k).trace = a A.trace k := by
  have key : ∀ k : ℕ, (A ^ k).trace = a A.trace k ∧ (A ^ (k + 1)).trace = a A.trace (k + 1) := by
    intro k
    induction k with
    | zero =>
      refine ⟨?_, ?_⟩
      · rw [pow_zero, a_zero, Matrix.trace_one, Fintype.card_fin]; rfl
      · rw [zero_add, pow_one, a_one]
    | succ k ih =>
      refine ⟨ih.2, ?_⟩
      rw [show k + 1 + 1 = k + 2 from rfl, a_add_two, ← ih.1, ← ih.2, pow_succ, pow_succ, mul_assoc,
        mul_self_eq A hdet, mul_sub, mul_one, Matrix.mul_smul, Matrix.trace_sub, Matrix.trace_smul,
        smul_eq_mul, ← pow_succ]
  exact fun k => (key k).1

end FinordTrace

/--
@isnad1 id=le.1h1v.s7.bc44c41b3c2c from=translated src=- shape=d17094ae vocab=780e4f56
-/
theorem solution (γ : SL(2, ℤ)) (h : IsOfFinOrder γ) :
    (γ : Matrix (Fin 2) (Fin 2) ℤ).trace ^ 2 ≤ 4 := by
  obtain ⟨n, hn, hγn⟩ := h.exists_pow_eq_one
  set A : Matrix (Fin 2) (Fin 2) ℤ := (γ : Matrix (Fin 2) (Fin 2) ℤ) with hA
  have hdet : A.det = 1 := γ.det_coe
  have htr : (A ^ n).trace = 2 := by
    have : A ^ n = 1 := by
      rw [hA, ← Matrix.SpecialLinearGroup.coe_pow, hγn, Matrix.SpecialLinearGroup.coe_one]
    rw [this, Matrix.trace_one, Fintype.card_fin]; rfl
  rw [FinordTrace.trace_pow_eq_a A hdet n] at htr
  by_contra hbig
  have ht : 3 ≤ |A.trace| := by
    by_contra h3
    push Not at h3
    have : A.trace ^ 2 ≤ 4 := by
      have hle : |A.trace| ≤ 2 := by omega
      have := abs_le.mp hle
      nlinarith [this.1, this.2]
    exact hbig this
  have := FinordTrace.two_lt_abs_a ht n hn
  rw [htr] at this
  norm_num at this
