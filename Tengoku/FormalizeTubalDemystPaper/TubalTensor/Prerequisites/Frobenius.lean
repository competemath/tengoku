import Tengoku.Seed.Analysis.Complex.Polynomial.Basic
import Tengoku.Seed.FieldTheory.PrimitiveElement

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
  TubalTensor/Prerequisites/Frobenius.lean
  Theorem 1: Commutative case of Frobenius theorem on division algebras.

  Statement: Every commutative finite-dimensional division algebra over ℝ has dimension ≤ 2.
  Equivalently: if F is a field that is a finite-dimensional ℝ-algebra, then finrank ℝ F ≤ 2.

  Proof strategy:
  1. By the primitive element theorem, F = ℝ⟮α⟯ for some α.
  2. finrank ℝ F = natDegree(minpoly ℝ α).
  3. minpoly ℝ α is irreducible over ℝ.
  4. Every irreducible polynomial over ℝ has degree ≤ 2 (Mathlib: Irreducible.natDegree_le_two).
  5. Hence finrank ℝ F ≤ 2.
-/

namespace TubalTensor

open Polynomial Complex IntermediateField Module

/-- **Theorem 1 (Commutative Frobenius, weak form)**:
    Every commutative finite-dimensional division algebra over ℝ has dimension ≤ 2.-/
theorem comm_frobenius (F : Type*) [Field F] [Algebra ℝ F] [FiniteDimensional ℝ F] :
    finrank ℝ F ≤ 2 := by
  -- By the primitive element theorem, F = ℝ⟮α⟯ for some α
  obtain ⟨α, hα⟩ := Field.exists_primitive_element ℝ F
  -- α is integral over ℝ (since F is finite-dimensional)
  have hα_int : IsIntegral ℝ α := IsIntegral.of_finite ℝ α
  -- finrank ℝ F = natDegree(minpoly ℝ α)
  have hfr : finrank ℝ F = (minpoly ℝ α).natDegree := by
    have h1 := IntermediateField.adjoin.finrank hα_int
    have h2 : finrank ℝ ↥(⊤ : IntermediateField ℝ F) = finrank ℝ F :=
      LinearEquiv.finrank_eq (IntermediateField.topEquiv).toLinearEquiv
    rw [hα] at h1; linarith
  -- minpoly ℝ α is irreducible, so its degree ≤ 2
  rw [hfr]
  exact (minpoly.irreducible hα_int).natDegree_le_two

end TubalTensor
