import Tengoku
import Tengoku.FltAnthropic.Theorems.Thm_AlgebraicGeometry_Smooth_isDomain_and_isIntegrallyClosed_stalk
import Tengoku.FltAnthropic.Theorems.Thm_AlgebraicGeometry_IsIntegral_isIntegrallyClosed_sections_of_forall_isIntegrallyClosed_stalk

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms solution` (it only prints; the queue checks the axioms of every declaration). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_AlgebraicGeometry_isIntegrallyClosed_sections_of_smooth_of_forall_isIntegrallyClosed_sections.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_AlgebraicGeometry_isIntegrallyClosed_sections_of_smooth_of_forall_isIntegrallyClosed_sections

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

/--
@isnad1 id=isintegr.2h4v.s9.df975c34d318 from=translated src=- shape=2c97d171 vocab=d964fc65
-/
theorem solution
    {X Y : Scheme.{u}} (f : X ⟶ Y) [Smooth f] [IsIntegral X] [IsIntegral Y]
    (hY : ∀ V : Y.Opens, IsAffineOpen V → IsIntegrallyClosed Γ(Y, V))
    (U : X.Opens) (hU : IsAffineOpen U) : IsIntegrallyClosed Γ(X, U) := by
  refine AlgebraicGeometry.IsIntegral.isIntegrallyClosed_sections_of_forall_isIntegrallyClosed_stalk
    (X := X) (fun x => ?_) U hU

  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, -⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (f.base x)) isOpen_univ
  replace hV : IsAffineOpen (V : Y.Opens) := hV

  haveI : IsAffine (V : Scheme.{u}) := hV
  have hne : Nonempty (V : Scheme.{u}) := ⟨⟨f.base x, hxV⟩⟩
  haveI : IsIntegral (V : Scheme.{u}) := isIntegral_of_isOpenImmersion (Scheme.Opens.ι V)
  haveI : IsDomain Γ((V : Scheme.{u}), ⊤) := inferInstance
  haveI : IsIntegrallyClosed Γ((V : Scheme.{u}), ⊤) := by
    haveI : IsIntegrallyClosed Γ(Y, V) := hY V hV
    exact IsIntegrallyClosed.of_equiv (Scheme.Opens.topIso V).commRingCatIsoToRingEquiv.symm

  haveI : Smooth (f ∣_ V) := inferInstance
  have hx' : x ∈ f ⁻¹ᵁ V := hxV
  have h2 := (AlgebraicGeometry.Smooth.isDomain_and_isIntegrallyClosed_stalk (f ∣_ V) ⟨x, hx'⟩).2
  have e2 : ((f ⁻¹ᵁ V : X.Opens) : Scheme.{u}).presheaf.stalk ⟨x, hx'⟩ ≅ X.presheaf.stalk x :=
    (f ⁻¹ᵁ V).stalkIso ⟨x, hx'⟩
  haveI := h2
  exact IsIntegrallyClosed.of_equiv e2.commRingCatIsoToRingEquiv

