import Tengoku.MagnitudeConjecture.MagnitudeConjecture.Graded.IntervalConvolution
import Tengoku.MagnitudeConjecture.MagnitudeConjecture.Graded.ProjectiveCorners

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # The interval matrix coefficients of a nonnegatively graded algebra -/
set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable
namespace MagnitudeConjecture.Graded
variable {k A : Type*} [Field k] [Ring A] [Algebra k A]
variable (R : VectorGrading k A)
variable {ι : Type*} [Fintype ι] (e : ι → A)

/-- The coefficient sending the (j,t) coordinate to (i,r).-/
def intervalCorner (m : ℕ) (p q : ι × Fin (m + 1)) (a : A) : A :=
  e p.1 * R.projection ((p.2.val : ℤ) - q.2.val) a * e q.1

/--
@isnad1 id=eq.0h10v.s7.ef839def53ff from=translated src=- shape=2658d8d4 vocab=b5664e0b
-/
theorem intervalCorner_add (m : ℕ) (p q : ι × Fin (m + 1)) (a b : A) :
    intervalCorner R e m p q (a + b) = intervalCorner R e m p q a + intervalCorner R e m p q b := by
  simp only [intervalCorner, map_add, mul_add, add_mul]

/--
@isnad1 id=eq.0h10v.s7.b7dd68c9e6f4 from=translated src=- shape=c83047cf vocab=49f48b0e
-/
theorem intervalCorner_smul (m : ℕ) (p q : ι × Fin (m + 1)) (c : k) (a : A) :
    intervalCorner R e m p q (c • a) = c • intervalCorner R e m p q a := by
  simp only [intervalCorner, map_smul, mul_smul_comm, smul_mul_assoc]

variable (hmul : ∀ {i j : ℤ} {a b : A}, a ∈ R.component i → b ∈ R.component j →
  a * b ∈ R.component (i + j))
variable (he0 : ∀ i, e i ∈ R.component 0) (he : ∀ i, e i * e i = e i)
include hmul he0 he

/--
@isnad1 id=mem.3h9v.s9.43a733e9a899 from=translated src=- shape=19b86ce7 vocab=ce6d4c27
-/
theorem intervalCorner_mem (m : ℕ) (p q : ι × Fin (m + 1)) (a : A) :
    intervalCorner R e m p q a ∈ cornerComponent R (e p.1) (e q.1)
      ((p.2.val : ℤ) - q.2.val) := by
  refine ⟨?_, ?_, ?_⟩
  · have h := hmul (hmul (he0 p.1) (R.projection_mem ((p.2.val : ℤ) - q.2.val) a)) (he0 q.1)
    simpa only [intervalCorner, zero_add, add_zero] using h
  · dsimp only [intervalCorner]
    rw [← mul_assoc, ← mul_assoc, he p.1]
  · dsimp only [intervalCorner]
    rw [mul_assoc, he q.1]

omit hmul he0 in
/-- Completeness inserts all middle idempotents into a product.
@isnad1 id=eq.2h5v.s7.fb881f16cb99 from=translated src=- shape=7b34f3da vocab=0d5c8069
-/
theorem sum_idempotent_products (hsum : ∑ i, e i = 1) (x y : A) :
    ∑ i, (x * e i) * (e i * y) = x * y := by
  calc
    _ = ∑ i, x * (e i * y) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [mul_assoc, ← mul_assoc (e i) (e i) y, he i]
    _ = x * ((∑ i, e i) * y) := by rw [Finset.sum_mul, Finset.mul_sum]
    _ = x * y := by rw [hsum, one_mul]

omit he0 in
/-- Matrix multiplication of the finite interval coefficients agrees with algebra multiplication.
@isnad1 id=eq.4h10v.s9.bbaabb464f77 from=translated src=- shape=e4ff8b6a vocab=bd8943f6
-/
theorem intervalCorner_mul (hneg : ∀ d : ℤ, d < 0 → R.component d = ⊥)
    (hsum : ∑ i, e i = 1) (m : ℕ) (p q : ι × Fin (m + 1)) (a b : A) :
    intervalCorner R e m p q (a * b) =
      ∑ z : ι × Fin (m + 1), intervalCorner R e m p z a * intervalCorner R e m z q b := by
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  unfold intervalCorner
  rw [R.interval_convolution hmul hneg m p.2 q.2 a b, Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro s hs
  have h := sum_idempotent_products e he hsum
    (e p.1 * R.projection ((p.2.val : ℤ) - s.val) a)
    (R.projection ((s.val : ℤ) - q.2.val) b * e q.1)
  simpa only [mul_assoc] using h.symm

omit hmul he0 in
/-- The coefficient matrix of 1 is the identity on the idempotent coordinates.
@isnad1 id=eq.3h8v.s8.a77fc377df7a from=translated src=- shape=c28d69b3 vocab=901cd3cf
-/
theorem intervalCorner_one (h1 : (1 : A) ∈ R.component 0)
    (horth : Pairwise fun i j ↦ e i * e j = 0)
    (m : ℕ) (p q : ι × Fin (m + 1)) :
    intervalCorner R e m p q 1 = if p = q then e p.1 else 0 := by
  classical
  by_cases hd : p.2 = q.2
  · have hd' : (p.2.val : ℤ) - q.2.val = 0 := by rw [hd]; omega
    simp only [intervalCorner, hd', R.projection_of_mem h1, mul_one]
    by_cases hi : p.1 = q.1
    · have hpq : p = q := Prod.ext hi hd
      rw [hpq, ite_eq_left rfl, he q.1]
    · have hpq : p ≠ q := fun h ↦ hi (congrArg Prod.fst h)
      rw [ite_eq_right hpq, horth hi]
  · have hd' : (0 : ℤ) ≠ (p.2.val : ℤ) - q.2.val := by
      intro h
      apply hd
      apply Fin.ext
      omega
    have hpq : p ≠ q := fun h ↦ hd (congrArg Prod.snd h)
    simp only [intervalCorner, R.projection_of_mem_ne h1 hd', mul_zero, zero_mul, ite_eq_right hpq]

end MagnitudeConjecture.Graded
