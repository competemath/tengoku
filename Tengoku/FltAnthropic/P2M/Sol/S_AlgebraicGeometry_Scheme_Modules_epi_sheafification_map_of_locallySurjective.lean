import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms solution` (it only prints; the queue checks the axioms of every declaration). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_epi_sheafification_map_of_locallySurjective.lean`: wrote out 7 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 4 `p2m_export`, 3 `p2m_open`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_epi_sheafification_map_of_locallySurjective

set_option autoImplicit false

universe u

open _root_.CategoryTheory open _root_.CategoryTheory.Limits open _root_.AlgebraicGeometry open _root_.Opposite open _root_.TopologicalSpace

universe v v' u'

namespace PresheafOfModules
export _root_.PresheafOfModules (sheafification map toSheafify IsLocallyInjective toPresheaf sheafifyMap obj IsLocallySurjective)
open _root_.PresheafOfModules

variable {C : Type u'} [Category.{v'} C] {J : GrothendieckTopology C}
  {R₀ : Cᵒᵖ ⥤ RingCat.{u}} {R : Sheaf J RingCat.{u}} (α : R₀ ⟶ R.obj)
  [Presheaf.IsLocallyInjective J α] [Presheaf.IsLocallySurjective J α]
  [HasSheafify J AddCommGrpCat.{v}] [J.WEqualsLocallyBijective AddCommGrpCat.{v}]

/--
@isnad1 id=epi.0h8v.s9.2558a7342f77 from=translated src=- shape=02be0133 vocab=9a65df05
-/
theorem epi_sheafification_map_of_isLocallySurjective {P Q : PresheafOfModules.{v} R₀}
    (ψ : P ⟶ Q) [Presheaf.IsLocallySurjective J ((toPresheaf R₀).map ψ)] :
    Epi ((sheafification.{v} α).map ψ) := by
  apply (SheafOfModules.toSheaf.{v} R).epi_of_epi_map
  change Epi ((presheafToSheaf J AddCommGrpCat.{v}).map ((toPresheaf R₀).map ψ))
  haveI : Sheaf.IsLocallySurjective
      ((presheafToSheaf J AddCommGrpCat.{v}).map ((toPresheaf R₀).map ψ)) := by
    change Presheaf.IsLocallySurjective J (CategoryTheory.sheafifyMap J ((toPresheaf R₀).map ψ))
    haveI : Presheaf.IsLocallySurjective J
        (CategoryTheory.toSheafify J ((toPresheaf R₀).obj P) ≫
          CategoryTheory.sheafifyMap J ((toPresheaf R₀).map ψ)) := by
      rw [← CategoryTheory.toSheafify_naturality]
      infer_instance
    exact Presheaf.isLocallySurjective_of_isLocallySurjective J
      (CategoryTheory.toSheafify J ((toPresheaf R₀).obj P)) _
  infer_instance

end PresheafOfModules

namespace AlgebraicGeometry
export _root_.AlgebraicGeometry (Scheme Scheme.Modules)
namespace Scheme
export _root_.AlgebraicGeometry.Scheme (ringCatSheaf Modules Opens grothendieckTopology PresheafOfModules)
namespace Modules
export _root_.AlgebraicGeometry.Scheme.Modules (toPresheaf)
open _root_.AlgebraicGeometry.Scheme.Modules open _root_.AlgebraicGeometry.Scheme open _root_.AlgebraicGeometry

variable {X : Scheme.{u}}

/--
@isnad1 id=epi.1h4v.s17.e98bfe2a469a from=translated src=- shape=138898e9 vocab=2950cc7e
-/
theorem _root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_epi_sheafification_map_of_locallySurjective.solution {P Q : X.PresheafOfModules} (ψ : P ⟶ Q)
    (h : ∀ (U : X.Opens) (s : Q.obj (op U)), ∀ x ∈ U, ∃ (V : X.Opens) (i : V ≤ U),
      x ∈ V ∧ Q.map (homOfLE i).op s ∈ Set.range (ψ.app (op V))) :
    Epi ((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map ψ) := by
  haveI : Presheaf.IsLocallySurjective (Opens.grothendieckTopology X)
      ((PresheafOfModules.toPresheaf X.ringCatSheaf.obj).map ψ) :=
    ⟨fun {U} s x hx => by
      obtain ⟨V, i, hxV, t, ht⟩ := h U s x hx
      exact ⟨V, homOfLE i, ⟨t, ht⟩, hxV⟩⟩
  exact PresheafOfModules.epi_sheafification_map_of_isLocallySurjective (𝟙 X.ringCatSheaf.obj) ψ

end AlgebraicGeometry.Scheme.Modules
