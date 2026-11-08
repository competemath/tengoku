module

public import Tengoku.Seed.Data.Real.Basic
public import Tengoku.Seed.LinearAlgebra.Matrix.Rank
public import Tengoku.Seed.LinearAlgebra.Matrix.NonsingularInverse
public import Tengoku.Seed.LinearAlgebra.Basis.VectorSpace
public import Tengoku.Seed.Analysis.Calculus.ContDiff.Operations

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# A linearly independent family has a nonzero maximal minor

If `card ι` vectors in `ℝⁿ` are linearly independent, some `card ι` of the `n`
coordinates already separate them: the square submatrix on those rows is
invertible.

Mathlib has this only for **square** matrices — `Matrix.linearIndependent_cols_iff_isUnit`
and `Matrix.linearIndependent_cols_of_det_ne_zero` — where there is nothing to
choose. The rectangular statement, which is the one a genericity argument needs
because it turns *"these vectors are independent"* into *"this explicit
polynomial in the entries is nonzero"*, is absent.

## Primary surface

| declaration | says |
|---|---|
| `exists_det_ne_zero_of_linearIndependent` | an independent family has a row selection on which its determinant is nonzero |

## Why it is wanted

A parametrized genericity argument has to produce, from a subspace condition, a
*polynomial* witness in the parameters — a rational or chart-based witness costs
parameters, and there are none to spare. A maximal minor is such a witness: it is
a determinant in the entries, so polynomial, and it detects exactly the failure of
independence.

## Provenance

Written to be lifted upstream: the declarations are named as Mathlib would name
them and the proofs use no atlas definitions. The proof is the textbook one —
column rank equals row rank, so the rows span the coordinate space, and
`Module.Basis.ofSpan` extracts a basis from among them.
-/

namespace AISafetyAtlas.Analysis

open Matrix Module

/-! ## The minor as a linear functional

A genericity argument needs a *linear functional* vanishing on a subspace, and it
needs that functional to be polynomial in whatever parameters the subspace
depends on. Bordering a family `u` with a test vector and taking a maximal minor
supplies exactly that: it is linear in the test vector, it vanishes when the test
vector is in the family's span, and by `exists_det_ne_zero_of_linearIndependent`
it is nonzero for some row selection whenever it is not. -/

section MinorFunctional

variable {n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The family `u`, bordered by a test vector `y`, read on the rows `f`.-/
@[expose] public def borderedMinor (u : ι → (Fin n → ℝ)) (f : Option ι → Fin n)
    (y : Fin n → ℝ) : ℝ :=
  (Matrix.of fun a b : Option ι => (Option.elim b y u) (f a)).det

/-- Determinants are linear in a single column. Mathlib has the `add` and `smul`
forms; this is the finite-sum form they give by induction.-/
private theorem det_updateCol_sum_smul {κ : Type*} [Fintype κ] [DecidableEq κ]
    {J : Type*} [Fintype J] [DecidableEq J]
    (M : Matrix J J ℝ) (b₀ : J) (c : κ → ℝ) (v : κ → J → ℝ) :
    (M.updateCol b₀ (fun a => ∑ j, c j * v j a)).det
      = ∑ j, c j * (M.updateCol b₀ (v j)).det := by
  classical
  have key : ∀ s : Finset κ, (M.updateCol b₀ (fun a => ∑ j ∈ s, c j * v j a)).det
      = ∑ j ∈ s, c j * (M.updateCol b₀ (v j)).det := by
    intro s
    induction s using Finset.induction with
    | empty =>
      simp only [Finset.sum_empty]
      exact Matrix.det_eq_zero_of_column_eq_zero b₀ (fun i => by simp)
    | insert a s ha ih =>
      simp only [Finset.sum_insert ha]
      rw [show (fun x : J => c a * v a x + ∑ j ∈ s, c j * v j x)
          = (fun x : J => c a * v a x) + (fun x : J => ∑ j ∈ s, c j * v j x) from rfl,
        Matrix.det_updateCol_add,
        show (fun x : J => c a * v a x) = c a • v a from rfl,
        Matrix.det_updateCol_smul, ih]
  exact key Finset.univ

private theorem borderedMinor_eq_updateCol (u : ι → (Fin n → ℝ)) (f : Option ι → Fin n)
    (y : Fin n → ℝ) :
    borderedMinor u f y
      = ((Matrix.of fun a b : Option ι => (Option.elim b 0 u) (f a)).updateCol none
          (fun a => y (f a))).det := by
  classical
  refine congrArg Matrix.det ?_
  ext a b
  cases b with
  | none => simp
  | some j => simp

end MinorFunctional

end AISafetyAtlas.Analysis
