import Tengoku.MagicSquaresFieldsLean.MagicSquares.Stepanov.Lemma652.Constraints

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace MagicSquares
namespace LN97

open Polynomial

/-!
# Coefficient constraints with a separate bound for each derivative

The bound for `s_{t,n}` grows with `n`.  Using that bound separately for
each derivative gives the equation count in (6.26), including its factor
`1/2`, instead of replacing every degree by the largest degree.
-/

abbrev StepanovVariableConstraintIndex (r M : ℕ) (N : Fin M → ℕ) :=
  (n : Fin M) × (Fin r × Fin (N n + 1))

abbrev StepanovVariableConstraintSpace (F : Type*) (r M : ℕ) (N : Fin M → ℕ) :=
  StepanovVariableConstraintIndex r M N → F

variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V]

noncomputable def polynomialFamilyVariableConstraints
    {r M : ℕ} (N : Fin M → ℕ)
    (S : V →ₗ[F] (Fin r → Fin M → Polynomial F)) :
    V →ₗ[F] StepanovVariableConstraintSpace F r M N where
  toFun := fun v idx => (S v idx.2.1 idx.1).coeff (idx.2.2 : ℕ)
  map_add' := by intro x y; funext idx; simp
  map_smul' := by intro a x; funext idx; simp

theorem polynomialFamily_eq_zero_of_variableConstraints_eq_zero
    {r M : ℕ} (N : Fin M → ℕ)
    (S : V →ₗ[F] (Fin r → Fin M → Polynomial F)) (v : V)
    (hdeg : ∀ t n, (S v t n).natDegree ≤ N n)
    (hz : polynomialFamilyVariableConstraints N S v = 0) :
    ∀ t n, S v t n = 0 := by
  intro t n
  apply polynomial_eq_zero_of_coeff_window_eq_zero _ (N n) (hdeg t n)
  intro l
  exact congrFun hz ⟨n, t, l⟩

theorem stepanovVariableConstraintSpace_finrank
    (F : Type*) [Field F] (r M : ℕ) (N : Fin M → ℕ) :
    Module.finrank F (StepanovVariableConstraintSpace F r M N) =
      r * ∑ n : Fin M, (N n + 1) := by
  rw [Module.finrank_pi]
  simp [StepanovVariableConstraintIndex, ← Finset.mul_sum]

theorem exists_nonzero_stepanovUnknown_in_variable_kernel
    {m u D r M : ℕ} {N : Fin M → ℕ}
    (T : StepanovUnknowns F m u D →ₗ[F]
      StepanovVariableConstraintSpace F r M N)
    (hcount : r * ∑ n : Fin M, (N n + 1) < m * (u + 1) * (D + 1)) :
    ∃ v : StepanovUnknowns F m u D, v ≠ 0 ∧ T v = 0 := by
  have hdim : Module.finrank F (StepanovVariableConstraintSpace F r M N) <
      Module.finrank F (StepanovUnknowns F m u D) := by
    rw [stepanovVariableConstraintSpace_finrank, stepanovUnknowns_finrank]
    exact hcount
  obtain ⟨v, hvker, hvne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
    (LinearMap.ker_ne_bot_of_finrank_lt (f := T) hdim)
  exact ⟨v, hvne, LinearMap.mem_ker.mp hvker⟩

end LN97
end MagicSquares
