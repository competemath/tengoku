import Tengoku
import Tengoku.FltAnthropic.Theorems.Thm_IsIntegrallyClosed_integralClosure_eq_adjoin_and_etale_and_finite_of_eq_mul_pow

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_AlgebraicGeometry_existsUnique_lift_fromNormalization_kummer_of_isAffineOpen.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_open`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_AlgebraicGeometry_existsUnique_lift_fromNormalization_kummer_of_isAffineOpen

set_option autoImplicit false

universe u

open _root_.CategoryTheory open _root_.CategoryTheory.Limits open _root_.AlgebraicGeometry open _root_.Polynomial open _root_.AlgebraicGeometry.Polynomial open _root_.TopologicalSpace open _root_.Opposite

namespace KummerChart

variable {X : Scheme.{u}} [IsIntegral X]

section KummerAlgebra

variable (k : ℕ) (g : X.functionField)

end KummerAlgebra

section Yside

variable (k : ℕ) (g : X.functionField)

end Yside

section Alg

variable (k : ℕ) (g : X.functionField)

theorem isIntegrallyClosed_sections (V : X.Opens) [Nonempty V] (hV : IsAffineOpen V)
    (hnorm : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x)) : IsIntegrallyClosed Γ(X, V) := by
  letI (y : PrimeSpectrum Γ(X, V)) : Algebra Γ(X, V) (X.presheaf.stalk (hV.fromSpec y)) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf _
  have hloc (P : Ideal Γ(X, V)) [hP : P.IsPrime] :
      IsLocalization.AtPrime (X.presheaf.stalk (hV.fromSpec ⟨P, hP⟩)) P :=
    hV.isLocalization_stalk' ⟨P, hP⟩ (hV.isoSpec.inv _).2
  exact IsIntegrallyClosed.of_isLocalization_maximal
    (Rₚ := fun P _ => X.presheaf.stalk (hV.fromSpec ⟨P, inferInstance⟩)) (fun P _ => hnorm _)

end Alg

section UP

variable (k : ℕ) (g : X.functionField)

variable (V : X.Opens) [Nonempty V] (hV : IsAffineOpen V)

end UP

section Geom

variable (k : ℕ) (g : X.functionField)

end Geom

end KummerChart
