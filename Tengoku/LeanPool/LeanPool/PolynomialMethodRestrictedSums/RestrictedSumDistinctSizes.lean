/-
Copyright (c) 2026 Nick Adfor. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nick Adfor
-/
module

public import Tengoku.LeanPool.LeanPool.PolynomialMethodRestrictedSums.VandermondeCoefficientFormula
public import Tengoku.Seed.Algebra.Field.ZMod
public import Tengoku.Seed.Algebra.MvPolynomial.Degrees
import Tengoku.LeanPool.LeanPool.PolynomialMethodRestrictedSums.ANRPolynomialMethod
import Tengoku.Seed.Algebra.MvPolynomial.NoZeroDivisors
import Tengoku.Seed.Algebra.Order.Field.Basic
import Tengoku.Seed.Data.Nat.Choose.Multinomial
import Tengoku.Seed.Data.Nat.Prime.Factorial
import Tengoku.Seed.RingTheory.Int.Basic
import Tengoku.Seed.Tactic.Positivity.Finset

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Restricted sums of sets with distinct sizes

The Alon-Nathanson-Ruzsa lower bound `restricted_sum_distinct_sizes` on the
set of sums `a 0 + ... + a k` with `a i ∈ A i` pairwise distinct, when the
sets `A i` have distinct sizes.
-/

@[expose] public section

open MvPolynomial
open AddMonoidAlgebra (coeff)

open Finset

open Matrix

open BigOperators

variable {R : Type*} [CommRing R]

variable {p : ℕ} [Fact (Nat.Prime p)] {k : ℕ}

/-- S = {a + ... + a | a ∈ A, a ≠ a for all i ≠ j} -/
def restrictedSumSet (k : ℕ) (A : Fin (k + 1) → Finset (ZMod p)) : Finset (ZMod p) :=
  ((Fintype.piFinset A).filter fun f =>
    ∀ (i j : Fin (k + 1)), i < j → f i ≠ f j)
    |>.image (fun f => ∑ i, f i)

/-- Vandermonde: ∏_{i>j} (X - X) -/
noncomputable def vandermondePolynomial (k : ℕ) : MvPolynomial (Fin (k + 1)) (ZMod p) :=
  ∏ i : Fin (k + 1), ∏ j : Fin (k + 1),
    if j.val < i.val then (X i - X j) else 1

/-- (Used in CompressedSizesRestrictedSum and DiasDaSilvaHamidoune)
The compressed sizes b'_i defined recursively:
    b'_0 = b_0, b'_i = min{b'_{i-1} - 1, b_i} for i ≥ 1 -/
def compressedSizes (b : Fin (k + 1) → ℕ) : Fin (k + 1) → ℕ :=
  fun i =>
    match i with
    | 0 => b 0
    | ⟨i + 1, hi⟩ =>
      let prev : Fin (k + 1) := ⟨i, by omega⟩
      min (compressedSizes b prev - 1) (b ⟨i + 1, hi⟩)

/-
Proposition 1.2:
Let p be a prime, and let A₀, A₁, ..., Aₖ be nonempty subsets of Z_p.
If |A_i| ≠ |A_j| for all 0 ≤ i < j ≤ k and ∑_{i=0}^k |A_i| ≤ p + (k + 2 choose 2) - 1,
then |{a₀ + ... + aₖ : a_i ∈ A_i, a_i ≠ a_j for all i ≠ j}| ≥ ∑_{i=0}^k |A_i| - (k + 2 choose 2) +
1.

Detailed proof:
1. Define the Vandermonde polynomial h(x₀, ..., xₖ) = ∏_{k ≥ i > j ≥ 0} (x_i - x_j).
   This polynomial is nonzero exactly when all x_i are distinct.

2. Let c_i = |A_i| - 1, so that |A_i| = c_i + 1.

3. Compute m = ∑_{i=0}^k c_i - (k + 1 choose 2)
            = (∑_{i=0}^k |A_i| - (k + 1)) - (k + 1 choose 2)
            = ∑_{i=0}^k |A_i| - (k + 2 choose 2)

4. We need m < p. From the hypothesis ∑ |A_i| ≤ p + (k + 2 choose 2) - 1,
   we get m = ∑ |A_i| - (k + 2 choose 2) ≤ p - 1 < p.

5. By Lemma 3.1, the coefficient of the monomial ∏ x_i^{c_i} in h·(∑ x_i)^m is:
      (m! / ∏ c_i!) · ∏_{i>j} (c_i - c_j)
   Since the c_i are all distinct and m < p, this coefficient is nonzero modulo p.

6. Apply Theorem 2.1 with this h, the sets A_i, and parameters c_i, m.
   The theorem gives:
      |⊕_h ∑_{i=0}^k A_i| ≥ m + 1

7. Note that ⊕_h ∑ A_i = {∑ a_i : a_i ∈ A_i, h(a) ≠ 0}
                     = {∑ a_i : a_i ∈ A_i, a_i ≠ a_j for all i ≠ j}
   since h(a) = 0 iff some a_i = a_j for i ≠ j.

8. Therefore:
      |{∑ a_i : a_i ∈ A_i, a_i distinct}| ≥ m + 1
                                        = ∑ |A_i| - (k + 2 choose 2) + 1
   which completes the proof.
-/
noncomputable section AristotleLemmas

/-
The total degree of the Vandermonde polynomial is (k + 1) choose 2.
-/
lemma vandermonde_degree_eq (k : ℕ) (p : ℕ) [Fact (Nat.Prime p)] :
  (vandermondePolynomial k : MvPolynomial (Fin (k + 1)) (ZMod p)).totalDegree = (k + 1).choose 2 :=
      by
    -- The Vandermonde polynomial is a product of linear terms, each contributing a degree of 1.
    have van_deg : ∀ i j : Fin (k + 1),
        j.val < i.val → (X i - X j : MvPolynomial (Fin (k + 1)) (ZMod p)).totalDegree = 1 := by
      intro i j a
      refine le_antisymm ?_ ?_ <;> norm_num [MvPolynomial.totalDegree];
      · intro b hb; rw [MvPolynomial.coeff_X, MvPolynomial.coeff_X] at hb; aesop;
      · refine ⟨Finsupp.single i 1, ?_, ?_⟩ <;> aesop;
    -- The total degree of a product of polynomials is the sum of their total degrees.
    have h_total_deg : ∀ (S : Finset (Fin (k + 1) × Fin (k + 1))),
        (∀ (ij : Fin (k + 1) × Fin (k + 1)), ij ∈ S → ij.1.val > ij.2.val) →
            (Finset.prod S
                (fun ij => (X ij.1 - X ij.2 : MvPolynomial (Fin (k + 1)) (ZMod p)))).totalDegree
              = Finset.card S := by
      intro S hS; induction S using Finset.induction
      · simp_all only [Fin.val_fin_lt, notMem_empty, gt_iff_lt, IsEmpty.forall_iff,
          implies_true, prod_empty, totalDegree_one, card_empty]
      rename_i a s a_1 a_2
      simp_all only [Fin.val_fin_lt, gt_iff_lt, mem_insert, or_true, implies_true,
          forall_const, forall_eq_or_imp, Prod.forall, not_false_eq_true, prod_insert,
          card_insert_of_notMem]
      obtain ⟨fst, snd⟩ := a
      obtain ⟨left, right⟩ := hS
      simp_all only
      rw [totalDegree_mul_of_isDomain, a_2, van_deg] <;> norm_num [left];
      · ring;
      · intro hcontra
        replace hcontra := congr_arg
          (MvPolynomial.eval (fun i => if i = fst then 1 else 0)) hcontra
        aesop;
      · simp? +decide [Finset.prod_eq_zero_iff, sub_eq_zero];
        exact fun x hx => lt_irrefl x (right _ _ hx);
    convert h_total_deg
        (Finset.filter (fun ij => ij.2.val < ij.1.val)
          (Finset.univ : Finset (Fin (k + 1) × Fin (k + 1)))) _ using 1;
    · unfold vandermondePolynomial
      simp? (config := { decide := Bool.true }) [Finset.prod_filter];
      erw [Finset.prod_product];
    · rw [show
            (Finset.filter (fun ij : Fin (k + 1) × Fin (k + 1) => (ij.2 : ℕ) < ij.1) Finset.univ
              : Finset _)
            = Finset.biUnion (Finset.univ : Finset (Fin (k + 1)))
                fun i => Finset.image (fun j => (i, j)) (Finset.Iio i)
          from ?_, Finset.card_biUnion];
      · rw [Finset.sum_congr rfl fun u _ =>
          Finset.card_image_of_injective _ fun _ _ h => congrArg Prod.snd h]
        exact Eq.symm (Nat.recOn k (by norm_num) fun n ih => by
          norm_num [Fin.sum_univ_castSucc, Nat.choose] at *; linarith);
      · exact fun i _ j _ hij => Finset.disjoint_left.mpr fun x hx₁ hx₂ => hij <| by aesop;
      · ext ⟨i, j⟩; aesop;
    · aesop

/-
If the sum of sizes of A_i is bounded by p + (k + 2 choose 2) - 1, then m < p.
-/
lemma restricted_sum_m_bound (A : Fin (k + 1) → Finset (ZMod p))
    (h_nonempty : ∀ i, (A i).Nonempty)
    (h_sum_bound : ∑ i, (A i).card ≤ p + (Nat.choose (k + 2) 2) - 1) :
    let c := fun i => (A i).card - 1
    let m := ∑ i, c i - (k + 1).choose 2
    m < p := by
      -- Therefore, $\sum |A_i| \le p + \binom{k + 1}{2} + (k + 1) - 1$, so $\sum c_i \le p +
      -- \binom{k + 1}{2} - 1$.
      have h_c_sum_bound : ∑ i, (#(A i) - 1) ≤ p + Nat.choose (k + 1) 2 - 1 := by
        -- We know that $\sum |A_i| = \sum (c_i + 1) = \sum c_i + (k + 1)$.
        have h_card_sum : ∑ i, #(A i) = ∑ i, ((#(A i)) - 1) + (k + 1) := by
          zify;
          rw [Finset.sum_congr rfl fun _ _ => Nat.cast_sub <| Finset.card_pos.mpr <| h_nonempty _];
              norm_num;
        simp_all +decide [Nat.choose];
        omega;
      rcases p with (_ | p) <;> (try simp_all (config := { decide := Bool.true }))

/-
The coefficient of the monomial corresponding to c in the product of the power sum and the
Vandermonde polynomial is non-zero in ZMod p, provided c_i and m are small enough.
-/

end AristotleLemmas
