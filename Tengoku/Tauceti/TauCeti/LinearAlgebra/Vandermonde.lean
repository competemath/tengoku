/-
Copyright (c) 2026 Tau Ceti. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Tengoku
import Tengoku.Tauceti.TauCeti.LinearAlgebra.Determinant
import Tengoku.Tauceti.TauCeti.RingTheory.Polynomial.Pochhammer

/-!
# Vandermonde determinants in the falling-factorial basis

The falling factorials `descPochhammer R j` are monic of degree `j`, so Mathlib's
`Matrix.det_eval_matrixOfPolynomials_eq_det_vandermonde` rewrites `det (vandermonde y)` as the
determinant of the matrix `(descPochhammer R j).eval (yᵢ)`.  Unlike the powers, the falling
factorials have a closed-form discrete antiderivative and a closed-form left shift, and this file
proves the two identities for the Vandermonde determinant that those two facts supply.

## The box-sum identity

Let `x₀ ≤ x₁ ≤ ⋯ ≤ xₙ` be integers and let `y` range over the box of integer vectors with
`xᵢ ≤ yᵢ ≤ xᵢ₊₁ - 1`, one interval for each consecutive pair.  Then

`n ! · ∑ y, det (vandermonde y) = det (vandermonde x)`,

which is `TauCeti.factorial_mul_sum_det_vandermonde`.  Unwinding the determinants, the product
`∏_{i < j} (yⱼ - yᵢ)` of the differences of an `n`-tuple, summed over the box, is `1 / n !` times
the corresponding product for the `(n + 1)`-tuple that bounds it.

The identity drives the branching recursion for the Weyl dimension formula of `GL n`: the
interlacing condition indexing the constituents of an irreducible restricted to `GL (n - 1)` is
exactly such a box, and the two Vandermonde products are the two Weyl dimension numerators.

Three moves prove it; only the last uses the ordering hypothesis.  *The falling-factorial basis*
replaces the powers, because they have the closed-form discrete antiderivative
`TauCeti.sum_Icc_descPochhammer_eval`.  *Multilinearity*: a determinant is multilinear in its rows
and the box constrains the rows independently, so the sum of the determinants over the box is the
determinant of the matrix of row sums (`MultilinearMap.map_sum_finset`); evaluating those row
sums, and clearing the denominators `1, 2, …, n` by a column scaling, produces the matrix of
differences `(descPochhammer ℤ (j+1)).eval (xᵢ₊₁) - (descPochhammer ℤ (j+1)).eval (xᵢ)`, whose
determinant is `n !` times the sum.  *A row reduction*: that matrix of differences is what remains
of the `(n+1) × (n+1)` matrix `(descPochhammer ℤ j).eval (xᵢ)` after subtracting each row from its
predecessor and deleting the column `j = 0`, which is constant equal to `1`.  Multiplying on the
left by the bidiagonal matrix performing the subtraction contributes a factor `(-1)^{n+1}` to the
determinant, and expanding the product along its first column — where only the last entry
survives — contributes the same sign, so the two determinants agree.

## The lowering identity

Over an arbitrary commutative ring, lower a single node `yᵢ` by one and weight the resulting
Vandermonde determinant by `yᵢ`.  Summing over the nodes gives back the original determinant,
scaled by `∑ yᵢ - (0 + 1 + ⋯ + (m - 1))`:

`∑ i, yᵢ · det (vandermonde (update y i (yᵢ - 1))) = (∑ i, yᵢ - ∑ i, i) · det (vandermonde y)`,

which is `TauCeti.sum_mul_det_vandermonde_update_sub_one`, with
`TauCeti.sum_mul_prod_sub_update_sub_one` its unwound form as a product of differences over the
ordered pairs of an initial segment of `ℕ`.  It is the Vandermonde identity behind the Frobenius
determinant formula for the number of standard Young tableaux of a given shape, where the nodes
are the beta-numbers of a Young diagram and lowering one of them is erasing a corner.

Two moves prove it.  *The left shift*: `x · (x - 1)^{underline j} = x^{underline (j+1)}`, so
multiplying the lowered row by `yᵢ` turns the falling-factorial matrix of the lowered node vector
into the same matrix with its `i`-th row shifted up one degree, and
`x^{underline (j+1)} = x^{underline j} · (x - j)` expands that row as `yᵢ` times the original minus
`j` times the original, entry by entry.  *Jacobi's row formula*
`Matrix.sum_det_updateRow_mul_row`: summing over the rows the determinant of a matrix with one row
scaled entry by entry multiplies the determinant by the total of the scaling factors, which turns
the `j`-weighted correction into `(0 + 1 + ⋯ + (m - 1)) · det`.

Mathlib's `monic_descPochhammer` and `descPochhammer_natDegree` assume the coefficient ring is a
nontrivial ring without zero divisors, which the lowering identity does not; it uses
`TauCeti.monic_descPochhammer`, which holds over any ring, and `TauCeti.descPochhammer_natDegree`,
which holds over any nontrivial ring.  The trivial ring is handled separately, where the identity is
vacuous.

## Main results

* `TauCeti.sum_Icc_descPochhammer_eval`: the discrete antiderivative of a falling factorial.
* `TauCeti.factorial_mul_sum_det_vandermonde`: **the box-sum identity for Vandermonde
  determinants.**
* `TauCeti.sum_mul_det_vandermonde_update_sub_one` and `TauCeti.sum_mul_prod_sub_update_sub_one`:
  **the lowering identity for Vandermonde determinants.**
-/

public section

namespace TauCeti

-- `_root_.Matrix`, because importing `TauCeti.LinearAlgebra.Determinant` puts a `TauCeti.Matrix`
-- namespace in scope as well.
open Finset _root_.Matrix Polynomial

/-! ### The discrete antiderivative of a falling factorial -/

/-- Shifting the argument of a falling factorial by one strips off its trailing linear factor:
the degree `m + 1` falling factorial at `x + 1` is `(x + 1)` times the degree `m` one at `x`. -/
private theorem descPochhammer_succ_eval_add_one {R : Type*} [CommRing R] (m : ℕ) (x : R) :
    (descPochhammer R (m + 1)).eval (x + 1) = (x + 1) * (descPochhammer R m).eval x := by
  rw [descPochhammer_succ_left, eval_mul, eval_X, eval_comp, eval_sub, eval_X, eval_one,
    add_sub_cancel_right]

/-! ### The box-sum identity -/

/-- The Vandermonde determinant of a node vector, computed in the falling-factorial basis: the
falling factorials are monic of degree `j`, so they give the same determinant as the powers. -/
private theorem det_vandermonde_eq_det_descPochhammer {R : Type*} [CommRing R] [Nontrivial R]
    (m : ℕ) (y : Fin m → R) :
    (Matrix.vandermonde y).det
      = (Matrix.of fun i j : Fin m => (descPochhammer R (j : ℕ)).eval (y i)).det :=
  Matrix.det_eval_matrixOfPolynomials_eq_det_vandermonde y
    (fun j => descPochhammer R (j : ℕ)) (fun j => descPochhammer_natDegree (j : ℕ))
    (fun j => monic_descPochhammer (j : ℕ))

/-! ### The lowering identity -/

/-- Lowering one node of a Vandermonde matrix by one, read in the falling-factorial basis: only
the corresponding row of the matrix changes. -/
private theorem det_vandermonde_update_sub_one {R : Type*} [CommRing R] [Nontrivial R] {m : ℕ}
    (y : Fin m → R) (i : Fin m) :
    (Matrix.vandermonde (Function.update y i (y i - 1))).det
      = ((Matrix.of fun k j : Fin m => (descPochhammer R (j : ℕ)).eval (y k)).updateRow i
          fun j : Fin m => (descPochhammer R (j : ℕ)).eval (y i - 1)).det := by
  classical
  rw [det_vandermonde_eq_det_descPochhammer]
  congr 1
  ext k j
  rcases eq_or_ne k i with rfl | h
  · simp
  · simp [Matrix.updateRow_ne h, Function.update_of_ne h]

/-- **The lowering identity for Vandermonde determinants.**  Lowering a single node by one and
weighting by that node, then summing over the nodes, multiplies the Vandermonde determinant by the
total of the nodes less `0 + 1 + ⋯ + (m - 1)`. -/
theorem sum_mul_det_vandermonde_update_sub_one {R : Type*} [CommRing R] {m : ℕ} (y : Fin m → R) :
    (∑ i, y i * (Matrix.vandermonde (Function.update y i (y i - 1))).det)
      = ((∑ i, y i) - ∑ i : Fin m, ((i : ℕ) : R)) * (Matrix.vandermonde y).det := by
  classical
  -- over the trivial ring there is nothing to prove, and the falling factorials have no degree
  rcases subsingleton_or_nontrivial R with _ | _
  · exact Subsingleton.elim _ _
  set N : Matrix (Fin m) (Fin m) R :=
    Matrix.of fun k j : Fin m => (descPochhammer R (j : ℕ)).eval (y k) with hNdef
  have hdet : (Matrix.vandermonde y).det = N.det := det_vandermonde_eq_det_descPochhammer m y
  have key : ∀ i : Fin m, y i * (Matrix.vandermonde (Function.update y i (y i - 1))).det
      = y i * N.det - (N.updateRow i fun j : Fin m => ((j : ℕ) : R) * N i j).det := by
    intro i
    have hrow : (y i • fun j : Fin m => (descPochhammer R (j : ℕ)).eval (y i - 1))
        = (y i • N i) - fun j : Fin m => ((j : ℕ) : R) * N i j := by
      funext j
      -- the left shift `x · (x - 1)^{underline j} = x^{underline (j+1)}` …
      have hleft : (descPochhammer R ((j : ℕ) + 1)).eval (y i)
          = y i * (descPochhammer R (j : ℕ)).eval (y i - 1) := by
        simpa using descPochhammer_succ_eval_add_one (j : ℕ) (y i - 1)
      -- … against the trailing factor `x^{underline (j+1)} = x^{underline j} · (x - j)`
      have hright := descPochhammer_succ_eval (S := R) (j : ℕ) (y i)
      simp only [hNdef, Matrix.of_apply, Pi.smul_apply, smul_eq_mul, Pi.sub_apply]
      rw [← hleft, hright]
      ring
    -- the determinant is alternating in the rows, so the difference of rows splits it in two
    have hsplit : (N.updateRow i ((y i • N i) - fun j : Fin m => ((j : ℕ) : R) * N i j)).det
        = (N.updateRow i (y i • N i)).det
          - (N.updateRow i fun j : Fin m => ((j : ℕ) : R) * N i j).det :=
      Matrix.detRowAlternating.map_update_sub N i _ _
    rw [det_vandermonde_update_sub_one, ← Matrix.det_updateRow_smul, hrow, hsplit,
      Matrix.det_updateRow_smul, Matrix.updateRow_eq_self]
  rw [Finset.sum_congr rfl fun i _ => key i, Finset.sum_sub_distrib, ← Finset.sum_mul,
    Matrix.sum_det_updateRow_mul_row, hdet]
  ring

/-- The Vandermonde determinant of the first `m` values of a sequence, as a product of the
differences over the ordered pairs of `Finset.range m`.  The sign is left as an unevaluated power
of `-1`: the lowering identity multiplies it into both of its sides, where it cancels. -/
private theorem det_vandermonde_eq_prod_range {R : Type*} [CommRing R] (m : ℕ) (b : ℕ → R) :
    (Matrix.vandermonde fun i : Fin m => b i).det
      = (-1) ^ (∑ i : Fin m, (Finset.Ioi i).card)
        * ∏ k ∈ Finset.range m, ∏ l ∈ Finset.Ico (k + 1) m, (b k - b l) := by
  classical
  have hIoi : ∀ i : Fin m, ∏ j ∈ Finset.Ioi i, (b j - b i)
      = (-1) ^ (Finset.Ioi i).card * ∏ l ∈ Finset.Ico ((i : ℕ) + 1) m, (b i - b l) := by
    intro i
    have hleft : Finset.Ioi i = Finset.univ.filter fun j : Fin m => (i : ℕ) < (j : ℕ) := by
      ext j
      simp only [Finset.mem_Ioi, Finset.mem_filter, Finset.mem_univ, true_and]
      exact Fin.lt_def
    have hright : Finset.Ico ((i : ℕ) + 1) m
        = (Finset.range m).filter fun l => (i : ℕ) < l := by
      ext l
      simp only [Finset.mem_Ico, Finset.mem_filter, Finset.mem_range]
      omega
    rw [hright, Finset.prod_filter,
      ← Fin.prod_univ_eq_prod_range (fun l : ℕ => if (i : ℕ) < l then b i - b l else 1) m,
      ← Finset.prod_filter, ← hleft, ← Finset.prod_const, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun j _ => by ring
  rw [Matrix.det_vandermonde, Finset.prod_congr rfl fun i _ => hIoi i, Finset.prod_mul_distrib,
    Finset.prod_pow_eq_pow_sum,
    Fin.prod_univ_eq_prod_range (fun k : ℕ => ∏ l ∈ Finset.Ico (k + 1) m, (b k - b l)) m]

/-- Cancelling a common factor of square one carried by every term of a sum and by the value it is
compared to.  A sign is such a factor over any commutative ring, where it need not be cancellable
in the sense of `mul_left_cancel₀`. -/
private theorem mul_self_cancel_sum {ι : Type*} [Fintype ι] {R : Type*} [CommRing R] {c : R}
    (hc : c * c = 1) {f g : ι → R} {a p : R} (h : ∑ i, f i * (c * g i) = a * (c * p)) :
    (∑ i, f i * g i) = a * p := by
  have hsum : ∑ i, f i * (c * g i) = c * ∑ i, f i * g i := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  have key : c * c * ∑ i, f i * g i = c * c * (a * p) := by
    rw [mul_assoc, ← hsum, h]; ring
  rwa [hc, one_mul, one_mul] at key

/-- **The lowering identity, unwound.**  For a sequence in a commutative ring, the product of the
differences over the ordered pairs below a bound, with one term of the sequence lowered by one and
the result weighted by that term, summed over the terms below the bound, is the total of the terms
below the bound less `0 + 1 + ⋯ + (m - 1)`, times the product of the differences of the original
sequence. -/
theorem sum_mul_prod_sub_update_sub_one {R : Type*} [CommRing R] (m : ℕ) (b : ℕ → R) :
    (∑ i ∈ Finset.range m, b i *
        ∏ k ∈ Finset.range m, ∏ l ∈ Finset.Ico (k + 1) m,
          (Function.update b i (b i - 1) k - Function.update b i (b i - 1) l))
      = ((∑ i ∈ Finset.range m, b i) - ∑ i ∈ Finset.range m, (i : R))
        * ∏ k ∈ Finset.range m, ∏ l ∈ Finset.Ico (k + 1) m, (b k - b l) := by
  classical
  have hupd : ∀ i : Fin m, Function.update (fun k : Fin m => b k) i (b (i : ℕ) - 1)
      = fun k : Fin m => Function.update b (i : ℕ) (b (i : ℕ) - 1) (k : ℕ) := by
    intro i
    funext k
    rcases eq_or_ne k i with rfl | h
    · simp
    · rw [Function.update_of_ne h, Function.update_of_ne fun hc => h (Fin.val_injective hc)]
  have hterm : ∀ i : Fin m,
      (Matrix.vandermonde (Function.update (fun k : Fin m => b k) i (b (i : ℕ) - 1))).det
        = (-1) ^ (∑ i : Fin m, (Finset.Ioi i).card)
          * ∏ k ∈ Finset.range m, ∏ l ∈ Finset.Ico (k + 1) m,
              (Function.update b (i : ℕ) (b (i : ℕ) - 1) k
                - Function.update b (i : ℕ) (b (i : ℕ) - 1) l) := by
    intro i
    rw [hupd i, det_vandermonde_eq_prod_range m (Function.update b (i : ℕ) (b (i : ℕ) - 1))]
  have key := sum_mul_det_vandermonde_update_sub_one fun i : Fin m => b i
  rw [Finset.sum_congr rfl fun i _ => by rw [hterm i], det_vandermonde_eq_prod_range m b] at key
  -- both sides now carry the same sign, which cancels
  have hsign : ((-1 : R) ^ (∑ i : Fin m, (Finset.Ioi i).card))
      * ((-1 : R) ^ (∑ i : Fin m, (Finset.Ioi i).card)) = 1 := by
    rw [← mul_pow]; norm_num
  have hcancel := mul_self_cancel_sum hsign key
  rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => b i * ∏ k ∈ Finset.range m,
      ∏ l ∈ Finset.Ico (k + 1) m,
        (Function.update b i (b i - 1) k - Function.update b i (b i - 1) l)) m,
    Fin.sum_univ_eq_sum_range b m,
    Fin.sum_univ_eq_sum_range (fun i : ℕ => (i : R)) m] at hcancel
  exact hcancel

end TauCeti
