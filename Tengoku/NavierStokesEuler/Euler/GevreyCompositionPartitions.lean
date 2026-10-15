import Tengoku

/-!
# A factorial-square bound for the partitions in Faà di Bruno's formula

The estimate is uniform in the order.  Extending a partition either creates a
singleton or increases one old part, so the factorial-square weight grows by
at most `(n + 1)^2 * (x + 2)`.  This avoids replacing every derivative in the
composition formula by the largest derivative bound.
-/

noncomputable section

open scoped BigOperators

namespace EulerGevreyComposition

variable {n : ℕ}

/--
@isnad1 id=eq.0h2v.s5.543860fabe2f from=translated src=- shape=1c0a5056 vocab=baa482a8
-/
lemma sum_partSize (c : OrderedFinpartition n) :
    ∑ i, c.partSize i = n := by
  simpa only [Fintype.card_sigma, Fintype.card_fin] using
    Fintype.card_congr c.equivSigma

/--
@isnad1 id=eq.0h2v.s5.b60148e446c3 from=translated src=- shape=00809faf vocab=d8c1937b
-/
lemma sum_partSize_real (c : OrderedFinpartition n) :
    ∑ i, (c.partSize i : ℝ) = n := by
  exact_mod_cast sum_partSize c

/--
@isnad1 id=le.0h2v.s6.a0f739c68ca1 from=translated src=- shape=b17d09d0 vocab=dff4fa19
-/
lemma sum_partSize_succ_sq_le (c : OrderedFinpartition n) :
    ∑ i, ((c.partSize i : ℝ) + 1)^2 ≤ 2 * ((n : ℝ) + 1)^2 := by
  have hl : (c.length : ℝ) ≤ n := by exact_mod_cast c.length_le
  calc
    _ ≤ ∑ i, ((n : ℝ) + 1) * ((c.partSize i : ℝ) + 1) := by
      apply Finset.sum_le_sum
      intro i _
      have hi : (c.partSize i : ℝ) ≤ n := by exact_mod_cast c.partSize_le i
      nlinarith [mul_nonneg (sub_nonneg.mpr hi) (show 0 ≤ (c.partSize i : ℝ) + 1 by positivity)]
    _ = ((n : ℝ) + 1) * ((n : ℝ) + c.length) := by
      rw [← Finset.mul_sum, Finset.sum_add_distrib, sum_partSize_real]
      simp
    _ ≤ _ := by nlinarith

def factorialProduct (c : OrderedFinpartition n) : ℝ :=
  ∏ i, ((c.partSize i).factorial : ℝ)

def partitionWeight (x : ℝ) (c : OrderedFinpartition n) : ℝ :=
  x^c.length * ((c.length.factorial : ℝ) * factorialProduct c)^2

def partitionSum (n : ℕ) (x : ℝ) : ℝ :=
  ∑ c : OrderedFinpartition n, partitionWeight x c

/--
@isnad1 id=le.1h3v.s4.bbdc93f01d65 from=translated src=- shape=07de1eae vocab=668726af
-/
lemma partitionWeight_nonneg (x : ℝ) (hx : 0 ≤ x) (c : OrderedFinpartition n) :
    0 ≤ partitionWeight x c := by
  unfold partitionWeight
  positivity

/--
@isnad1 id=eq.0h2v.s4.0d1f140b384c from=translated src=- shape=39cc4c45 vocab=10646013
-/
lemma factorialProduct_extendLeft (c : OrderedFinpartition n) :
    factorialProduct c.extendLeft = factorialProduct c := by
  change (∏ i : Fin (c.length+1),
    (Nat.factorial (Fin.cons (α := fun _ => ℕ) 1 c.partSize i) : ℝ)) =
    ∏ i : Fin c.length, ((c.partSize i).factorial : ℝ)
  rw [Fin.prod_univ_succ]
  simp

/--
@isnad1 id=eq.0h3v.s5.6222a07b22db from=translated src=- shape=3815d354 vocab=5b868f1f
-/
lemma factorialProduct_extendMiddle (c : OrderedFinpartition n) (i : Fin c.length) :
    factorialProduct (c.extendMiddle i) =
      ((c.partSize i : ℝ) + 1) * factorialProduct c := by
  change (∏ j : Fin c.length,
    ((Function.update c.partSize i (c.partSize i+1) j).factorial : ℝ)) =
      ((c.partSize i : ℝ) + 1) * ∏ j : Fin c.length, ((c.partSize j).factorial : ℝ)
  have he : (fun j : Fin c.length =>
      ((Function.update c.partSize i (c.partSize i+1) j).factorial : ℝ)) =
      fun j => (if j = i then (c.partSize i : ℝ) + 1 else 1) *
        ((c.partSize j).factorial : ℝ) := by
    funext j
    by_cases h : j = i
    · subst j
      simp [Nat.factorial_succ]
    · simp [h]
  rw [he, Finset.prod_mul_distrib]
  simp

/--
@isnad1 id=eq.0h3v.s6.01b773535fa0 from=translated src=- shape=1b72953b vocab=11f86b65
-/
lemma partitionWeight_extendLeft (x : ℝ) (c : OrderedFinpartition n) :
    partitionWeight x c.extendLeft =
      (x * ((c.length : ℝ) + 1)^2) * partitionWeight x c := by
  simp only [partitionWeight, OrderedFinpartition.extendLeft_length,
    factorialProduct_extendLeft, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add,
    Nat.cast_one, pow_succ]
  ring

/--
@isnad1 id=eq.0h4v.s6.7958a559dc4a from=translated src=- shape=2c83c131 vocab=dcdb9f31
-/
lemma partitionWeight_extendMiddle (x : ℝ) (c : OrderedFinpartition n) (i : Fin c.length) :
    partitionWeight x (c.extendMiddle i) =
      ((c.partSize i : ℝ) + 1)^2 * partitionWeight x c := by
  simp only [partitionWeight, OrderedFinpartition.extendMiddle_length,
    factorialProduct_extendMiddle]
  ring

/--
@isnad1 id=eq.0h2v.s7.b65b8b4bdcc4 from=translated src=- shape=ce07d573 vocab=f742a209
-/
lemma partitionSum_succ (n : ℕ) (x : ℝ) :
    partitionSum (n+1) x =
      ∑ c : OrderedFinpartition n,
        (x * ((c.length : ℝ) + 1)^2 + ∑ i, ((c.partSize i : ℝ) + 1)^2) *
          partitionWeight x c := by
  unfold partitionSum
  rw [← (OrderedFinpartition.extendEquiv n).sum_comp]
  simp only [Fintype.sum_sigma, Fintype.sum_option, OrderedFinpartition.extendEquiv_apply,
    OrderedFinpartition.extend_none, OrderedFinpartition.extend_some,
    partitionWeight_extendLeft, partitionWeight_extendMiddle, ← Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro c _
  ring

/--
@isnad1 id=le.1h2v.s6.56d62dec9eda from=translated src=- shape=1b9ae6f4 vocab=946cffbe
-/
lemma partitionSum_succ_le (n : ℕ) (x : ℝ) (hx : 0 ≤ x) :
    partitionSum (n+1) x ≤ ((n : ℝ) + 1)^2 * (x+2) * partitionSum n x := by
  rw [partitionSum_succ, partitionSum, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro c _
  have hl : (c.length : ℝ) ≤ n := by exact_mod_cast c.length_le
  have hs : ((c.length : ℝ) + 1)^2 ≤ ((n : ℝ) + 1)^2 := by gcongr
  apply mul_le_mul_of_nonneg_right _ (partitionWeight_nonneg x hx c)
  calc
    _ ≤ x * ((n : ℝ) + 1)^2 + 2 * ((n : ℝ) + 1)^2 :=
      add_le_add (mul_le_mul_of_nonneg_left hs hx) (sum_partSize_succ_sq_le c)
    _ = _ := by ring

/-- The entire factorial-square Faà di Bruno partition sum has one fixed
exponential radius, independent of the differentiation order.
@isnad1 id=le.1h2v.s6.49f7c9542f9b from=translated src=- shape=a8cb8378 vocab=e180da18
-/
theorem partitionSum_le (n : ℕ) (x : ℝ) (hx : 0 ≤ x) :
    partitionSum n x ≤ (x+2)^n * (n.factorial : ℝ)^2 := by
  induction n with
  | zero =>
    simp [partitionSum, partitionWeight, factorialProduct,
      OrderedFinpartition.default_eq]
  | succ n ih =>
    calc
      _ ≤ ((n : ℝ) + 1)^2 * (x+2) * partitionSum n x :=
        partitionSum_succ_le n x hx
      _ ≤ ((n : ℝ) + 1)^2 * (x+2) * ((x+2)^n * (n.factorial : ℝ)^2) := by
        gcongr
      _ = _ := by
        rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one, pow_succ]
        ring

end EulerGevreyComposition
