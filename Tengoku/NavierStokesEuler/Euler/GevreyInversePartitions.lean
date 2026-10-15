import Tengoku.NavierStokesEuler.Euler.GevreyCompositionPartitions

/-!
# A shifted partition estimate for a differential equation

For the relation `DY = A ∘ Y`, the useful induction controls the order-`j`
derivative of `Y` by `(j-1)!²`.  With those inner weights the normalized
Faà di Bruno partition sum stays bounded at every positive order, provided
its scalar argument is at most one half.
-/

noncomputable section

open scoped BigOperators

namespace EulerGevreyComposition

variable {n : ℕ}

/--
@isnad1 id=le.0h3v.s5.c9a8da00cdfd from=translated src=- shape=6959cee7 vocab=9e801b1b
-/
lemma partSize_add_length_le (c : OrderedFinpartition n) (i : Fin c.length) :
    c.partSize i + c.length ≤ n + 1 := by
  have hs : (∑ j : Fin c.length, (c.partSize j - 1)) + c.length = n := by
    have h : ∑ j : Fin c.length, (c.partSize j - 1 + 1) = n := by
      simpa only [Nat.sub_add_cancel (c.partSize_pos _)] using sum_partSize c
    simpa only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, smul_eq_mul, mul_one] using h
  have hi : c.partSize i - 1 ≤ ∑ j : Fin c.length, (c.partSize j - 1) :=
    Finset.single_le_sum (fun j _ => Nat.zero_le (c.partSize j - 1)) (Finset.mem_univ i)
  have hp := c.partSize_pos i
  omega

/--
@isnad1 id=le.0h2v.s6.eb42f80403e3 from=translated src=- shape=e27266f5 vocab=343a8a55
-/
lemma sum_partSize_sq_le (c : OrderedFinpartition n) :
    ∑ i, (c.partSize i : ℝ)^2 ≤ ((n : ℝ) - c.length + 1) * n := by
  calc
    _ ≤ ∑ i, ((n : ℝ) - c.length + 1) * (c.partSize i : ℝ) := by
      apply Finset.sum_le_sum
      intro i _
      have h : (c.partSize i : ℝ) + c.length ≤ (n : ℝ) + 1 := by
        exact_mod_cast partSize_add_length_le c i
      have hmul := mul_le_mul_of_nonneg_right
        (show (c.partSize i : ℝ) ≤ (n : ℝ) - c.length + 1 by linarith)
        (show 0 ≤ (c.partSize i : ℝ) by positivity)
      nlinarith
    _ = _ := by rw [← Finset.mul_sum, sum_partSize_real]

def predecessorFactorialProduct (c : OrderedFinpartition n) : ℝ :=
  ∏ i, ((c.partSize i - 1).factorial : ℝ)

def predecessorPartitionWeight (x : ℝ) (c : OrderedFinpartition n) : ℝ :=
  x^c.length * ((c.length.factorial : ℝ) * predecessorFactorialProduct c)^2

def predecessorPartitionSum (n : ℕ) (x : ℝ) : ℝ :=
  ∑ c : OrderedFinpartition n, predecessorPartitionWeight x c

/--
@isnad1 id=le.1h3v.s4.b16bbbeffae9 from=translated src=- shape=07de1eae vocab=a6b705f6
-/
lemma predecessorPartitionWeight_nonneg (x : ℝ) (hx : 0 ≤ x)
    (c : OrderedFinpartition n) : 0 ≤ predecessorPartitionWeight x c := by
  unfold predecessorPartitionWeight
  positivity

/--
@isnad1 id=eq.0h2v.s4.7c3686c730f9 from=translated src=- shape=39cc4c45 vocab=fb405c4e
-/
lemma predecessorFactorialProduct_extendLeft (c : OrderedFinpartition n) :
    predecessorFactorialProduct c.extendLeft = predecessorFactorialProduct c := by
  change (∏ i : Fin (c.length+1),
    (Nat.factorial (Fin.cons (α := fun _ => ℕ) 1 c.partSize i - 1) : ℝ)) =
      ∏ i : Fin c.length, ((c.partSize i - 1).factorial : ℝ)
  rw [Fin.prod_univ_succ]
  simp

/--
@isnad1 id=eq.0h3v.s5.15d91693e5d5 from=translated src=- shape=b054b0c1 vocab=8f01b6bf
-/
lemma predecessorFactorialProduct_extendMiddle (c : OrderedFinpartition n)
    (i : Fin c.length) :
    predecessorFactorialProduct (c.extendMiddle i) =
      (c.partSize i : ℝ) * predecessorFactorialProduct c := by
  change (∏ j : Fin c.length,
    ((Function.update c.partSize i (c.partSize i+1) j - 1).factorial : ℝ)) =
      (c.partSize i : ℝ) * ∏ j : Fin c.length, ((c.partSize j - 1).factorial : ℝ)
  have he : (fun j : Fin c.length =>
      ((Function.update c.partSize i (c.partSize i+1) j - 1).factorial : ℝ)) =
      fun j => (if j = i then (c.partSize i : ℝ) else 1) *
        ((c.partSize j - 1).factorial : ℝ) := by
    funext j
    by_cases h : j = i
    · subst j
      simp only [Function.update_self, Nat.add_sub_cancel, ite_true]
      exact_mod_cast (Nat.mul_factorial_pred (c.partSize_pos i).ne').symm
    · simp [h]
  rw [he, Finset.prod_mul_distrib]
  simp

/--
@isnad1 id=eq.0h3v.s6.0cc6e41741b0 from=translated src=- shape=1b72953b vocab=0c00a1e4
-/
lemma predecessorPartitionWeight_extendLeft (x : ℝ) (c : OrderedFinpartition n) :
    predecessorPartitionWeight x c.extendLeft =
      (x * ((c.length : ℝ) + 1)^2) * predecessorPartitionWeight x c := by
  simp only [predecessorPartitionWeight, OrderedFinpartition.extendLeft_length,
    predecessorFactorialProduct_extendLeft, Nat.factorial_succ, Nat.cast_mul,
    Nat.cast_add, Nat.cast_one, pow_succ]
  ring

/--
@isnad1 id=eq.0h4v.s6.62162ff0e0e6 from=translated src=- shape=b22800a6 vocab=628d7d50
-/
lemma predecessorPartitionWeight_extendMiddle (x : ℝ) (c : OrderedFinpartition n)
    (i : Fin c.length) :
    predecessorPartitionWeight x (c.extendMiddle i) =
      (c.partSize i : ℝ)^2 * predecessorPartitionWeight x c := by
  simp only [predecessorPartitionWeight, OrderedFinpartition.extendMiddle_length,
    predecessorFactorialProduct_extendMiddle]
  ring

/--
@isnad1 id=eq.0h2v.s7.496da7493da1 from=translated src=- shape=adeb03d6 vocab=c1f2711a
-/
lemma predecessorPartitionSum_succ (n : ℕ) (x : ℝ) :
    predecessorPartitionSum (n+1) x =
      ∑ c : OrderedFinpartition n,
        (x * ((c.length : ℝ) + 1)^2 + ∑ i, (c.partSize i : ℝ)^2) *
          predecessorPartitionWeight x c := by
  unfold predecessorPartitionSum
  rw [← (OrderedFinpartition.extendEquiv n).sum_comp]
  simp only [Fintype.sum_sigma, Fintype.sum_option, OrderedFinpartition.extendEquiv_apply,
    OrderedFinpartition.extend_none, OrderedFinpartition.extend_some,
    predecessorPartitionWeight_extendLeft, predecessorPartitionWeight_extendMiddle,
    ← Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro c _
  ring

/--
@isnad1 id=le.3h2v.s6.fb6bf1e4617f from=translated src=- shape=83a245a6 vocab=43b8a4ee
-/
lemma predecessorPartitionSum_succ_le (n : ℕ) (hn : 0 < n)
    (x : ℝ) (hx : 0 ≤ x) (hxhalf : x ≤ 1/2) :
    predecessorPartitionSum (n+1) x ≤
      ((n : ℝ) + 1)^2 * predecessorPartitionSum n x := by
  rw [predecessorPartitionSum_succ, predecessorPartitionSum, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro c _
  apply mul_le_mul_of_nonneg_right _ (predecessorPartitionWeight_nonneg x hx c)
  have hl : (c.length : ℝ) ≤ n := by exact_mod_cast c.length_le
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hprod := mul_le_mul_of_nonneg_right
    (show (c.length : ℝ)+1 ≤ 2*n by linarith)
    (show 0 ≤ (c.length : ℝ)+1 by positivity)
  have hscalar := mul_le_mul_of_nonneg_right hxhalf (sq_nonneg ((c.length : ℝ)+1))
  have hs := sum_partSize_sq_le c
  nlinarith

/-- Unlike the unshifted weights, these weights have a uniformly bounded
normalized sum on the scalar interval `[0, 1/2]`.
@isnad1 id=le.3h2v.s6.ef71f21539bc from=translated src=- shape=2d242fac vocab=5a66a294
-/
theorem predecessorPartitionSum_le (n : ℕ) (hn : 0 < n)
    (x : ℝ) (hx : 0 ≤ x) (hxhalf : x ≤ 1/2) :
    predecessorPartitionSum n x ≤ x * (n.factorial : ℝ)^2 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  induction m with
  | zero =>
    simp [predecessorPartitionSum, predecessorPartitionWeight,
      predecessorFactorialProduct, OrderedFinpartition.default_eq]
  | succ m ih =>
    calc
      _ ≤ ((m+1 : ℕ) + 1 : ℝ)^2 * predecessorPartitionSum (m+1) x :=
        predecessorPartitionSum_succ_le (m+1) (by omega) x hx hxhalf
      _ ≤ ((m+1 : ℕ) + 1 : ℝ)^2 * (x * ((m+1).factorial : ℝ)^2) := by
        exact mul_le_mul_of_nonneg_left (ih (by omega)) (sq_nonneg _)
      _ = _ := by
        change ((m+1 : ℕ) + 1 : ℝ)^2 * (x * ((m+1).factorial : ℝ)^2) =
          x * (((m+1)+1).factorial : ℝ)^2
        rw [Nat.factorial_succ (m+1), Nat.cast_mul]
        push_cast
        ring

end EulerGevreyComposition
