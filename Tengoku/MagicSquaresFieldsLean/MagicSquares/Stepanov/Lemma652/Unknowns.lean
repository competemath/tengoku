import Tengoku.Seed.Algebra.Polynomial.OfFn
import Tengoku.Seed.LinearAlgebra.Dimension.Constructions
import Tengoku.Seed.Tactic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace MagicSquares
namespace LN97

open Polynomial

/-!
# The literal coefficient space in LN97 Lemma 6.52

In (6.22), the unknown polynomials are

    e_{ij}(x),  0 ≤ i < m,  0 ≤ j ≤ u,

and every `e_{ij}` has degree at most `D = q/m-k`.

Thus there are exactly

    m (u+1) (D+1)

scalar coefficients.  This file represents those coefficients directly
as a finite coordinate space and packages them into the block
polynomials used by `StepanovLemma652`.
-/

/-- Indices `(i,j,l)` for the scalar coefficient of `x^l` in `e_{ij}`.-/
abbrev StepanovUnknownIndex (m u D : ℕ) :=
  Fin m × (Fin (u + 1) × Fin (D + 1))

/-- The scalar unknowns occurring in (6.22).-/
abbrev StepanovUnknowns (F : Type*) (m u D : ℕ) :=
  StepanovUnknownIndex m u D → F

variable {F : Type*} [Field F] [DecidableEq F]

/-- The polynomial `e_{ij}(x)` reconstructed from its `D+1`
coefficient coordinates.-/
noncomputable def stepanovInnerPolynomial
    {m u D : ℕ}
    (v : StepanovUnknowns F m u D)
    (i : Fin m) (j : Fin (u + 1)) :
    Polynomial F :=
  (Polynomial.ofFn (D + 1))
    (fun l : Fin (D + 1) => v (i, (j, l)))

/-- The block polynomial

    E_i(z) = e_{i0}(x) + e_{i1}(x) z + ... + e_{iu}(x) z^u.

After `z = x^q`, this is the `h_i(x)` appearing in Lemma 6.46 and
equation (6.22).-/
noncomputable def stepanovDecode
    {m u D : ℕ}
    (v : StepanovUnknowns F m u D)
    (i : Fin m) :
    Polynomial (Polynomial F) :=
  (Polynomial.ofFn (u + 1))
    (fun j : Fin (u + 1) => stepanovInnerPolynomial v i j)

/-- Every reconstructed `e_{ij}` has degree at most `D`.
@isnad1 id=le.0h7v.s5.4e8c241da977 from=translated src=- shape=9030560f vocab=a65887da
-/
theorem stepanovInnerPolynomial_natDegree_le
    {m u D : ℕ}
    (v : StepanovUnknowns F m u D)
    (i : Fin m) (j : Fin (u + 1)) :
    (stepanovInnerPolynomial v i j).natDegree ≤ D := by
  have hlt :
      (stepanovInnerPolynomial v i j).natDegree < D + 1 := by
    simpa [stepanovInnerPolynomial] using
      (Polynomial.ofFn_natDegree_lt
        (R := F) (n := D + 1) (Nat.succ_pos D)
        (fun l : Fin (D + 1) => v (i, (j, l))))
  omega

/-- Each block polynomial has outer degree at most `u`.
@isnad1 id=le.0h6v.s5.2e67400c89ba from=translated src=- shape=203a9dc3 vocab=170d553e
-/
theorem stepanovDecode_natDegree_le
    {m u D : ℕ}
    (v : StepanovUnknowns F m u D)
    (i : Fin m) :
    (stepanovDecode v i).natDegree ≤ u := by
  have hlt :
      (stepanovDecode v i).natDegree < u + 1 := by
    simpa [stepanovDecode] using
      (Polynomial.ofFn_natDegree_lt
        (R := Polynomial F) (n := u + 1) (Nat.succ_pos u)
        (fun j : Fin (u + 1) => stepanovInnerPolynomial v i j))
  omega

/-- All coefficients of a decoded block have inner degree at most `D`,
including coefficients beyond the outer cutoff (which are zero).
@isnad1 id=le.0h7v.s6.b22d7a66e0ea from=translated src=- shape=1dd2c81c vocab=5545061a
-/
theorem stepanovDecode_coeff_natDegree_le
    {m u D : ℕ}
    (v : StepanovUnknowns F m u D)
    (i : Fin m) (j : ℕ) :
    ((stepanovDecode v i).coeff j).natDegree ≤ D := by
  by_cases hj : j < u + 1
  · change
      (((Polynomial.ofFn (u + 1))
        (fun jj : Fin (u + 1) =>
          stepanovInnerPolynomial v i jj)).coeff j).natDegree ≤ D
    rw [Polynomial.ofFn_coeff_eq_val_of_lt _ hj]
    exact stepanovInnerPolynomial_natDegree_le
      v i ⟨j, hj⟩
  · have hge : u + 1 ≤ j := Nat.le_of_not_gt hj
    change
      (((Polynomial.ofFn (u + 1))
        (fun jj : Fin (u + 1) =>
          stepanovInnerPolynomial v i jj)).coeff j).natDegree ≤ D
    rw [Polynomial.ofFn_coeff_eq_zero_of_ge _ hge]
    simp

/-- If one decoded block is zero, then every scalar coefficient in that
`i`-slice of the unknown vector is zero.
@isnad1 id=eq.1h8v.s7.e303363f68db from=translated src=- shape=7aaffb48 vocab=953bb9a0
-/
theorem stepanovUnknown_slice_eq_zero_of_decode_eq_zero
    {m u D : ℕ}
    (v : StepanovUnknowns F m u D)
    (i : Fin m)
    (hzero : stepanovDecode v i = 0) :
    ∀ j : Fin (u + 1), ∀ l : Fin (D + 1),
      v (i, (j, l)) = 0 := by
  have houter :
      (fun j : Fin (u + 1) =>
        stepanovInnerPolynomial v i j) = 0 := by
    apply (Polynomial.injective_ofFn
      (R := Polynomial F) (u + 1))
    simpa [stepanovDecode] using hzero
  intro j l
  have hinner : stepanovInnerPolynomial v i j = 0 := by
    exact congrFun houter j
  have hcoeff :
      (fun ll : Fin (D + 1) => v (i, (j, ll))) = 0 := by
    apply (Polynomial.injective_ofFn (R := F) (D + 1))
    simpa [stepanovInnerPolynomial] using hinner
  exact congrFun hcoeff l

/-- A nonzero scalar coefficient vector decodes to a nontrivial family
of block polynomials.  This is the nonvanishing input needed by the
abstract Lemma 6.52 assembly already in the project.
@isnad1 id=ex.1h5v.s7.eaa15db08171 from=translated src=- shape=0d9884cb vocab=aba5d743
-/
theorem exists_stepanovDecode_ne_zero_of_ne_zero
    {m u D : ℕ}
    (v : StepanovUnknowns F m u D)
    (hv : v ≠ 0) :
    ∃ i : Fin m, stepanovDecode v i ≠ 0 := by
  by_contra h
  apply hv
  funext idx
  rcases idx with ⟨i, ⟨j, l⟩⟩
  have hi : stepanovDecode v i = 0 := by
    by_contra hne
    exact h ⟨i, hne⟩
  exact stepanovUnknown_slice_eq_zero_of_decode_eq_zero
    v i hi j l

/-- The dimension of the literal unknown coefficient space is exactly
`m (u+1) (D+1)`, i.e. the quantity `A` before any lower estimate is
applied.
@isnad1 id=eq.0h4v.s6.0c3a17b96f57 from=translated src=- shape=5c5bdb4d vocab=6578d092
-/
theorem stepanovUnknowns_finrank
    (F : Type*) [Field F]
    (m u D : ℕ) :
    Module.finrank F (StepanovUnknowns F m u D)
      = m * (u + 1) * (D + 1) := by
  change
    Module.finrank F
      (StepanovUnknownIndex m u D → F)
      = m * (u + 1) * (D + 1)
  rw [Module.finrank_pi]
  simp [StepanovUnknownIndex, Nat.mul_assoc]

end LN97
end MagicSquares
