import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_AlgebraicGeometry_IsClosedImmersion_isClosed_iInf_preimage_and_quasiCompact.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_AlgebraicGeometry_IsClosedImmersion_isClosed_iInf_preimage_and_quasiCompact

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u v

/--
@isnad1 id=and.3h7v.s9.f1c677b1c50f from=translated src=- shape=e8a730fb vocab=51796e11
-/
theorem solution
    {B E P : Scheme.{u}} (m : E ⟶ P) (hm : IsClosedImmersion m) (πP : P ⟶ B)
    {ι : Type v} [Finite ι] (W : ι → P.Opens)
    (hW : IsClosed ((⨅ j, W j : P.Opens) : Set P)) (hW' : QuasiCompact ((⨅ j, W j).ι ≫ πP)) :
    IsClosed ((⨅ j, m ⁻¹ᵁ (W j) : E.Opens) : Set E) ∧
      QuasiCompact ((⨅ j, m ⁻¹ᵁ (W j)).ι ≫ m ≫ πP) := by
  classical
  haveI : Fintype ι := Fintype.ofFinite ι
  have coe_iInf : ∀ {Z : Scheme.{u}} (V : ι → Z.Opens),
      ((⨅ j, V j : Z.Opens) : Set Z) = ⋂ j, (V j : Set Z) := by
    intro Z V
    rw [← Finset.inf_univ_eq_iInf, TopologicalSpace.Opens.coe_finset_inf, Finset.inf_univ_eq_iInf,
      Set.iInf_eq_iInter]
    rfl
  have key : (⨅ j, m ⁻¹ᵁ (W j)) = m ⁻¹ᵁ (⨅ j, W j) := by
    apply TopologicalSpace.Opens.ext
    rw [coe_iInf, Scheme.Hom.coe_preimage, coe_iInf, Set.preimage_iInter]
    rfl
  rw [key]
  refine ⟨?_, ?_⟩
  · rw [Scheme.Hom.coe_preimage]
    exact hW.preimage m.continuous
  · have h : (m ⁻¹ᵁ (⨅ j, W j)).ι ≫ m ≫ πP = (m ∣_ (⨅ j, W j)) ≫ (⨅ j, W j).ι ≫ πP := by
      rw [← Category.assoc (m ∣_ _), morphismRestrict_ι, Category.assoc]
    rw [h]
    haveI := hm
    haveI := hW'
    infer_instance
