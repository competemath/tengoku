import Tengoku.QuadraticCarlesonPalomarSubmission.QuadraticCarleson.KrauseLaceyRademacherMenshov

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Ordered finite energy bookkeeping

An exact finite double-sum decomposition separates diagonal energy from
strictly lower-rank cross rows. The result applies to arbitrary coefficients
of absolute value at most one, without assuming a signed-sum estimate.
-/

namespace QuadraticCarleson.KrauseLaceyOrderedEnergy

set_option autoImplicit false

/--
@isnad1 id=eq.1h5v.s7.e447f6e2d9ed from=translated src=- shape=ba4e5fbe vocab=7056c73d
-/
theorem sum_abs_inner_eq_diagonal_add_crossRows
    {ι E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (S : Finset ι) (v : ι → E) (rank : ι → ℤ)
    (heq : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → rank i = rank j → inner ℝ (v i) (v j) = 0) :
    (∑ i ∈ S, ∑ j ∈ S, |inner ℝ (v i) (v j)|) =
      (∑ i ∈ S, ‖v i‖ ^ 2) +
        2 * ∑ i ∈ S, ∑ j ∈ S.filter (fun j ↦ rank j < rank i),
          |inner ℝ (v i) (v j)| := by
  classical
  have hpair (i : ι) (hi : i ∈ S) (j : ι) (hj : j ∈ S) :
      |inner ℝ (v i) (v j)| =
        (if rank j < rank i then |inner ℝ (v i) (v j)| else 0) +
        (if rank i < rank j then |inner ℝ (v i) (v j)| else 0) +
        (if i = j then ‖v i‖ ^ 2 else 0) := by
    by_cases hij : i = j
    · subst j
      simp [real_inner_self_eq_norm_sq]
    · by_cases hlt : rank j < rank i
      · simp [hij, hlt, not_lt_of_ge hlt.le]
      · by_cases hgt : rank i < rank j
        · simp [hij, hlt, hgt]
        · have hr : rank i = rank j := by omega
          simp [hij, hlt, hgt, heq i hi j hj hij hr]
  have hswap :
      (∑ i ∈ S, ∑ j ∈ S, if rank i < rank j then |inner ℝ (v i) (v j)| else 0) =
      ∑ i ∈ S, ∑ j ∈ S, if rank j < rank i then |inner ℝ (v i) (v j)| else 0 := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    rw [real_inner_comm (v i) (v j)]
  calc
    _ = ∑ i ∈ S, ∑ j ∈ S,
        ((if rank j < rank i then |inner ℝ (v i) (v j)| else 0) +
        (if rank i < rank j then |inner ℝ (v i) (v j)| else 0) +
        (if i = j then ‖v i‖ ^ 2 else 0)) := by
      exact Finset.sum_congr rfl fun i hi ↦ Finset.sum_congr rfl fun j hj ↦ hpair i hi j hj
    _ = _ := by
      simp_rw [Finset.sum_add_distrib]
      rw [hswap]
      simp_rw [Finset.sum_ite_eq, Finset.sum_filter]
      have hdiag : (∑ i ∈ S, if i ∈ S then ‖v i‖ ^ 2 else 0) =
          ∑ i ∈ S, ‖v i‖ ^ 2 := Finset.sum_congr rfl fun i hi ↦ ite_eq_left hi
      rw [hdiag]
      ring

/--
@isnad1 id=le.2h6v.s8.a13360e276f4 from=translated src=- shape=98159029 vocab=abd323b4
-/
theorem signed_sum_sq_le_diagonal_add_crossRows
    {ι E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (S : Finset ι) (v : ι → E) (rank : ι → ℤ)
    (heq : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → rank i = rank j → inner ℝ (v i) (v j) = 0)
    (c : ι → ℝ) (hc : ∀ i ∈ S, |c i| ≤ 1) :
    ‖∑ i ∈ S, c i • v i‖ ^ 2 ≤
      (∑ i ∈ S, ‖v i‖ ^ 2) +
        2 * ∑ i ∈ S, ∑ j ∈ S.filter (fun j ↦ rank j < rank i),
          |inner ℝ (v i) (v j)| := by
  rw [← sum_abs_inner_eq_diagonal_add_crossRows S v rank heq,
    ← real_inner_self_eq_norm_sq]
  simp_rw [sum_inner, inner_sum, real_inner_smul_left, real_inner_smul_right]
  apply Finset.sum_le_sum
  intro i hi
  apply Finset.sum_le_sum
  intro j hj
  calc
    c i * (c j * inner ℝ (v i) (v j)) ≤ |c i * (c j * inner ℝ (v i) (v j))| :=
      le_abs_self _
    _ = (|c i| * |c j|) * |inner ℝ (v i) (v j)| := by rw [abs_mul, abs_mul]; ring
    _ ≤ 1 * |inner ℝ (v i) (v j)| := mul_le_mul_of_nonneg_right
      (mul_le_one₀ (hc i hi) (abs_nonneg _) (hc j hj)) (abs_nonneg _)
    _ = _ := one_mul _

end QuadraticCarleson.KrauseLaceyOrderedEnergy
