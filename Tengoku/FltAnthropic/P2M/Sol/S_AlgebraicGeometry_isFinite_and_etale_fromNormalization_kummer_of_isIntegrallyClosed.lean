import Tengoku
import Tengoku.FltAnthropic.Theorems.Thm_IsIntegrallyClosed_integralClosure_eq_adjoin_and_etale_and_finite_of_eq_mul_pow

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_AlgebraicGeometry_isFinite_and_etale_fromNormalization_kummer_of_isIntegrallyClosed.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_open`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_AlgebraicGeometry_isFinite_and_etale_fromNormalization_kummer_of_isIntegrallyClosed

set_option autoImplicit false

universe u

open _root_.CategoryTheory open _root_.CategoryTheory.Limits open _root_.AlgebraicGeometry open _root_.Polynomial open _root_.AlgebraicGeometry.Polynomial

namespace KFEAux
open AlgebraicGeometry.Scheme
variable {X : Scheme.{u}} [IsIntegral X]

end KFEAux

namespace KFEAux
open AlgebraicGeometry.Scheme
variable {X : Scheme.{u}} [IsIntegral X]

/--
@isnad1 id=isintegr.2h2v.s8.ea34b5400c53 from=translated src=- shape=7ddbb05d vocab=53d30996
-/
theorem isIntegrallyClosed_sections (hnorm : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (V : X.affineOpens) (hη : genericPoint X ∈ (V : X.Opens)) : IsIntegrallyClosed Γ(X, (V : X.Opens)) := by
  haveI : Nonempty (V : X.Opens) := ⟨⟨_, hη⟩⟩
  haveI : IsDomain Γ(X, (V : X.Opens)) := IsIntegral.component_integral (V : X.Opens)
  refine IsIntegrallyClosed.of_localization_maximal fun p hp hmax => ?_
  let y : PrimeSpectrum Γ(X, (V : X.Opens)) := ⟨p, hmax.isPrime⟩
  have hy : V.2.fromSpec y ∈ (V : X.Opens) := by
    have : V.2.fromSpec y ∈ Set.range (V.2.fromSpec) := Set.mem_range_self y
    rwa [V.2.range_fromSpec] at this
  letI := TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨V.2.fromSpec y, hy⟩
  haveI hloc : IsLocalization p.primeCompl (X.presheaf.stalk (V.2.fromSpec y)) := V.2.isLocalization_stalk' y hy
  exact (hnorm _).of_equiv
    (IsLocalization.algEquiv p.primeCompl (X.presheaf.stalk (V.2.fromSpec y)) (Localization.AtPrime p)).toRingEquiv

end KFEAux

namespace KFEAux
open AlgebraicGeometry.Scheme
variable {X : Scheme.{u}} [IsIntegral X]

end KFEAux

namespace KFEAux
open AlgebraicGeometry.Scheme
variable {X : Scheme.{u}} [IsIntegral X]

end KFEAux
