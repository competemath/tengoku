import Tengoku
import Tengoku.FltAnthropic.Theorems.Thm_AlgebraicGeometry_eq_of_isStandardSmoothOfRelativeDimension_appLE_of_smoothOfRelativeDimension
import Tengoku.FltAnthropic.Theorems.Thm_AlgebraicGeometry_exists_isStandardSmoothOfRelativeDimension_appLE_fiberToSpecResidueField

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_AlgebraicGeometry_smoothOfRelativeDimension_of_smooth_of_forall_fiber.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_AlgebraicGeometry_smoothOfRelativeDimension_of_smooth_of_forall_fiber

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

/--
@isnad1 id=smoothof.1h4v.s5.ca8a9d963c58 from=translated src=- shape=de275df6 vocab=fecbb647
-/
theorem solution
    {X Y : Scheme.{u}} (f : X ⟶ Y) [Smooth f] (n : ℕ)
    (h : ∀ y : Y, SmoothOfRelativeDimension n (f.fiberToSpecResidueField y)) :
    SmoothOfRelativeDimension n f := by
  refine ⟨fun x => ?_⟩
  obtain ⟨U, hU, V, hV, hxV, e, hstd⟩ := Smooth.exists_isStandardSmooth f x

  obtain ⟨m, hm⟩ : ∃ m : ℕ, (f.appLE U V e).hom.IsStandardSmoothOfRelativeDimension m := by
    letI := (f.appLE U V e).hom.toAlgebra
    have : Algebra.IsStandardSmooth Γ(Y, U) Γ(X, V) := hstd
    obtain ⟨ι, σ, _, _, ⟨P⟩⟩ := this
    exact ⟨P.dimension, P.isStandardSmoothOfRelativeDimension rfl⟩

  obtain ⟨U', V', hV', hxV', e', hm'⟩ :=
    AlgebraicGeometry.exists_isStandardSmoothOfRelativeDimension_appLE_fiberToSpecResidueField f x m U hU V hV hxV e hm
  have hmn : m = n :=
    AlgebraicGeometry.eq_of_isStandardSmoothOfRelativeDimension_appLE_of_smoothOfRelativeDimension
      (f.fiberToSpecResidueField (f.base x)) n (h (f.base x)) m U' V' hV' (f.asFiber x) hxV' e' hm'
  subst hmn
  exact ⟨U, hU, V, hV, hxV, e, hm⟩
