import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_Algebra_IsStandardSmooth_exists_isStandardSmoothOfRelativeDimension_of_field.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_Algebra_IsStandardSmooth_exists_isStandardSmoothOfRelativeDimension_of_field

set_option autoImplicit false

/--
@isnad1 id=ex.0h2v.s5.6bcd03deae8e from=translated src=- shape=a5f58e2b vocab=d232a636
-/
theorem solution
    {k : Type*} [Field k] {B : Type*} [CommRing B] [Algebra k B]
    [Algebra.IsStandardSmooth k B] :
    ∃ n, Algebra.IsStandardSmoothOfRelativeDimension n k B := by
  obtain ⟨ι, σ, hσ, hι, ⟨P⟩⟩ := (inferInstance : Algebra.IsStandardSmooth k B).out
  exact ⟨P.dimension, ⟨ι, σ, hσ, hι, P, rfl⟩⟩
