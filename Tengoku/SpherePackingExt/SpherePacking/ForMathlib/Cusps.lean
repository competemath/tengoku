module
public import Tengoku.Seed.NumberTheory.ModularForms.BoundedAtCusp

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Cusps

This file proves results such as `zero_at_cusps_of_zero_at_infty`
and `bounded_at_cusps_of_bounded_at_infty`.
-/

open scoped MatrixGroups ModularForm UpperHalfPlane

/--
If `f` is bounded at `i∞` after slashing by all elements of `𝒮ℒ`, then `f` is bounded at every
cusp.-/
public theorem bounded_at_cusps_of_bounded_at_infty {f : ℍ → ℂ} {c : OnePoint ℝ} {k : ℤ}
    {𝒢 : Subgroup (GL (Fin 2) ℝ)} [𝒢.IsArithmetic] (hc : IsCusp c 𝒢)
    (hb : ∀ A ∈ 𝒮ℒ, UpperHalfPlane.IsBoundedAtImInfty (f ∣[k] A)) : c.IsBoundedAt f k := by
  rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at hc
  exact (OnePoint.isBoundedAt_iff_forall_SL2Z hc).2 fun A _ ↦ hb A ⟨A, rfl⟩
