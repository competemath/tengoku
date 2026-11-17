import Tengoku.Seed.AlgebraicGeometry.IdealSheaf.Functorial
import Tengoku.Seed.AlgebraicGeometry.Cover.Open

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_AlgebraicGeometry_Scheme_IdealSheafData_eq_of_forall_comap_openCover_eq.lean`: wrote out 5 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 3 `p2m_export`, 2 `p2m_open`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_eq_of_forall_comap_openCover_eq

set_option autoImplicit false

universe u

open _root_.CategoryTheory open _root_.CategoryTheory.Limits open _root_.AlgebraicGeometry

namespace AlgebraicGeometry
export _root_.AlgebraicGeometry (Scheme Scheme.IdealSheafData)
namespace Scheme
export _root_.AlgebraicGeometry.Scheme (OpenCover affineOpens isBasis_affineOpens Opens IdealSheafData Cover)
namespace IdealSheafData
export _root_.AlgebraicGeometry.Scheme.IdealSheafData (ideal ext_of_iSup_eq_top comap ideal_comap_of_isOpenImmersion)
open _root_.AlgebraicGeometry.Scheme.IdealSheafData open _root_.AlgebraicGeometry.Scheme open _root_.AlgebraicGeometry

theorem eq_of_forall_comap_openCover_eq_aux
    {X : Scheme.{u}} (𝒰 : X.OpenCover) {I J : X.IdealSheafData}
    (h : ∀ i, I.comap (𝒰.f i) = J.comap (𝒰.f i)) : I = J := by
  refine ext_of_iSup_eq_top
    (fun p : Σ i, (𝒰.X i).affineOpens => ⟨𝒰.f p.1 ''ᵁ (p.2 : (𝒰.X p.1).Opens),
      p.2.2.image_of_isOpenImmersion _⟩) ?_ ?_
  · refine top_le_iff.mp fun x _ => ?_
    obtain ⟨y, hy⟩ := 𝒰.covers x
    obtain ⟨_, ⟨W, hW, rfl⟩, hyW, -⟩ :=
      (𝒰.X (𝒰.idx x)).isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ y) isOpen_univ
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨𝒰.idx x, ⟨W, hW⟩⟩, ⟨y, hyW, hy⟩⟩
  · rintro ⟨i, W⟩
    have hW := congrArg (fun K : (𝒰.X i).IdealSheafData => K.ideal W) (h i)
    simp only [ideal_comap_of_isOpenImmersion] at hW
    exact Ideal.comap_injective_of_surjective _
      (ConcreteCategory.bijective_of_isIso ((𝒰.f i).appIso (W : (𝒰.X i).Opens)).inv).2 hW

end AlgebraicGeometry.Scheme.IdealSheafData

/--
@isnad1 id=eq.1h4v.s6.d6ecdb4956f0 from=translated src=- shape=8c3faf64 vocab=506de0c5
-/
theorem solution
    {X : Scheme.{u}} (𝒰 : X.OpenCover) {I J : X.IdealSheafData}
    (h : ∀ i, I.comap (𝒰.f i) = J.comap (𝒰.f i)) : I = J :=
  AlgebraicGeometry.Scheme.IdealSheafData.eq_of_forall_comap_openCover_eq_aux 𝒰 h
