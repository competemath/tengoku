/-
Copyright (c) 2026 Nick Adfor. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nick Adfor
-/
module

public import Tengoku.Seed.Algebra.Field.ZMod
public import Tengoku.Seed.Algebra.MvPolynomial.Degrees
import Tengoku.Seed.Algebra.MvPolynomial.NoZeroDivisors
import Tengoku.Seed.Combinatorics.Nullstellensatz
import Tengoku.Seed.Data.Finsupp.Notation

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The Alon-Nathanson-Ruzsa polynomial method

The core of the polynomial method for restricted sums in `ZMod p`: elimination
polynomials, the vanishing-coefficient lemma on product grids, and the main
theorem `ANR_polynomial_method` giving a non-vanishing-coefficient criterion
for lower-bounding restricted sumsets.
-/

@[expose] public section

open scoped Finset

variable {R : Type*} [CommRing R]
variable {p : ℕ} [Fact (Nat.Prime p)] {k : ℕ}

open MvPolynomial
open AddMonoidAlgebra (coeff)

open Finsupp

/-- Definition of elimination polynomials g_i -/
noncomputable def eliminationPolynomials (A : Fin (k + 1) → Finset (ZMod p)) :
    Fin (k + 1) → MvPolynomial (Fin (k + 1)) (ZMod p) :=
  fun i => ∏ a ∈ A i, (MvPolynomial.X i - C a)

/-- The sum of variables polynomial -/
noncomputable def sumXPolynomial : MvPolynomial (Fin (k + 1)) (ZMod p) :=
  ∑ i, MvPolynomial.X i

/-- The restricted sumset S from the ANR theorem -/
noncomputable def restrictedSumset (h : MvPolynomial (Fin (k + 1)) (ZMod p))
    (A : Fin (k + 1) → Finset (ZMod p)) : Finset (ZMod p) :=
  ((Fintype.piFinset A).filter (fun f => h.eval f ≠ 0)).image (fun f => ∑ i, f i)

/-- The polynomial Q = h * ∏_{e∈E} (∑X_i - e) -/
noncomputable def constructionPolynomial
    (h : MvPolynomial (Fin (k + 1)) (ZMod p))
    (E : Multiset (ZMod p)) :
    MvPolynomial (Fin (k + 1)) (ZMod p) :=
  h * (E.map (fun e => sumXPolynomial - C e)).prod

/-- The construction of E from S when |S| ≤ m -/
def extendToSize (S : Finset (ZMod p)) (m : ℕ) :
    Multiset (ZMod p) :=
  S.val + Multiset.replicate (m - S.card) (0 : ZMod p)

/-- Alternative name for clarity. Here use k explicitly -/
noncomputable def productPolynomial (k : ℕ) (E : Multiset (ZMod p)) :
    MvPolynomial (Fin (k + 1)) (ZMod p) :=
  (E.map (fun e => sumXPolynomial - C e)).prod

/-- Lemma 2.1.1 : Construction_polynomial vanishes on ∏ A_i -/
lemma constructionPolynomial_vanishes
    (h : MvPolynomial (Fin (k + 1)) (ZMod p))
    (A : Fin (k + 1) → Finset (ZMod p))
    (E : Multiset (ZMod p))
    (hE_sub : (restrictedSumset h A).val ⊆ E) :
    ∀ (x : Fin (k + 1) → ZMod p), (∀ i, x i ∈ A i) →
      eval x (h * (E.map (fun e => sumXPolynomial - C e)).prod) = 0 := by
  intro x hx
  rw [eval_mul]
  by_cases hh : eval x h = 0
  · simp [hh]
  · have h_sum_in_S : (∑ i, x i) ∈ restrictedSumset h A := by
      dsimp [restrictedSumset]
      simp_all only [Finset.mem_image, Finset.mem_filter, Fintype.mem_piFinset]
      exact ⟨x, ⟨hx, hh⟩, rfl⟩
    have h_sum_in_E : (∑ i, x i) ∈ E := hE_sub h_sum_in_S
    have h_prod_zero : eval x ((E.map (fun e => sumXPolynomial - C e)).prod) = 0 := by
      rw [map_multiset_prod]
      refine Multiset.prod_eq_zero ?_
      rw [Multiset.mem_map]
      exact ⟨sumXPolynomial - C (∑ i, x i),
        Multiset.mem_map.mpr ⟨∑ i, x i, h_sum_in_E, rfl⟩, by simp [sumXPolynomial]⟩
    simp [h_prod_zero]

/-- Lemma 2.1.2 : The product polynomial ∏_{e∈E} (∑X_i - C e) is always nonzero -/
lemma productPolynomial_ne_zero (k : ℕ) (E : Multiset (ZMod p)) :
    productPolynomial k E ≠ 0 := by
  unfold productPolynomial
  intro hzero
  obtain ⟨e, _, h⟩ := Multiset.mem_map.mp (Multiset.prod_eq_zero_iff.mp hzero)
  have heval := congrArg (MvPolynomial.eval (fun i => if i = 0 then e + 1 else 0)) h
  simp [sumXPolynomial] at heval

open MvPolynomial Finsupp
open scoped BigOperators

noncomputable section AristotleLemmas

end AristotleLemmas
