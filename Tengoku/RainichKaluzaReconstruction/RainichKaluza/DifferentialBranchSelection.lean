import Tengoku.Seed.Algebra.Module.LinearMap.Basic
import Tengoku.Seed.Data.Real.Basic
import Tengoku.Seed.Tactic.Module

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Differential selection of the relative-sign branches

On the generic complementary plane, the two pointwise scalar covector
candidates have the form `alpha + beta` and `alpha - beta`, where `alpha` and
`beta` are the two spectral components.  Exterior differentiation is linear.
Consequently both candidates can be closed only when the two spectral
components are separately closed.

The theorem is stated for an arbitrary real-linear map `d`; it therefore
applies to the exterior derivative on one-forms in any setting where that map
has been constructed.  It does not assert that either branch is closed.
-/

namespace RainichKaluza

variable {E W : Type*}
  [AddCommGroup E] [Module ℝ E]
  [AddCommGroup W] [Module ℝ W]

/-- **Relative-sign differential selection theorem.** The sum and difference
branches are simultaneously annihilated by a linear differential operator if
and only if their two spectral components are annihilated separately.-/
theorem both_relativeSign_branches_closed_iff
    (d : E →ₗ[ℝ] W) (alpha beta : E) :
    (d (alpha + beta) = 0 ∧ d (alpha - beta) = 0) ↔
      (d alpha = 0 ∧ d beta = 0) := by
  simp only [map_add, map_sub]
  constructor
  · rintro ⟨hsum, hdiff⟩
    constructor
    · have htwo : (2 : ℝ) • d alpha = 0 := by
        calc
          (2 : ℝ) • d alpha =
              (d alpha + d beta) + (d alpha - d beta) := by module
          _ = 0 := by rw [hsum, hdiff, add_zero]
      exact (smul_eq_zero.mp htwo).resolve_left (by norm_num)
    · have htwo : (2 : ℝ) • d beta = 0 := by
        calc
          (2 : ℝ) • d beta =
              (d alpha + d beta) - (d alpha - d beta) := by module
          _ = 0 := by rw [hsum, hdiff, sub_self]
      exact (smul_eq_zero.mp htwo).resolve_left (by norm_num)
  · rintro ⟨halpha, hbeta⟩
    simp [halpha, hbeta]

/-- If the sum branch is closed, then the reflected difference branch is
closed exactly on the separately closed locus.-/
theorem reflected_branch_closed_iff_of_branch_closed
    (d : E →ₗ[ℝ] W) (alpha beta : E)
    (hplus : d (alpha + beta) = 0) :
    d (alpha - beta) = 0 ↔ d alpha = 0 ∧ d beta = 0 := by
  constructor
  · intro hminus
    exact (both_relativeSign_branches_closed_iff d alpha beta).mp
      ⟨hplus, hminus⟩
  · intro hseparate
    exact (both_relativeSign_branches_closed_iff d alpha beta).mpr
      hseparate |>.2

/-- Away from the separately closed exceptional locus, existence of a closed
relative-sign branch implies that exactly one of the two branches is closed.-/
theorem relativeSign_closed_branch_unique_of_exists
    (d : E →ₗ[ℝ] W) (alpha beta : E)
    (hexists : d (alpha + beta) = 0 ∨ d (alpha - beta) = 0)
    (hgeneric : ¬(d alpha = 0 ∧ d beta = 0)) :
    (d (alpha + beta) = 0 ∧ d (alpha - beta) ≠ 0) ∨
      (d (alpha + beta) ≠ 0 ∧ d (alpha - beta) = 0) := by
  rcases hexists with hplus | hminus
  · left
    refine ⟨hplus, ?_⟩
    intro hminus
    exact hgeneric <|
      (both_relativeSign_branches_closed_iff d alpha beta).mp ⟨hplus, hminus⟩
  · right
    refine ⟨?_, hminus⟩
    intro hplus
    exact hgeneric <|
      (both_relativeSign_branches_closed_iff d alpha beta).mp ⟨hplus, hminus⟩

end RainichKaluza
