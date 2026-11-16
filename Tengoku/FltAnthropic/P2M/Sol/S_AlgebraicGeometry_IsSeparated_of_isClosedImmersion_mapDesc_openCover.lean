import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_AlgebraicGeometry_IsSeparated_of_isClosedImmersion_mapDesc_openCover.lean`: wrote out 4 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_export`, 2 `p2m_open`, 1 `p2m_open_scoped`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_AlgebraicGeometry_IsSeparated_of_isClosedImmersion_mapDesc_openCover

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry
export _root_.AlgebraicGeometry (IsZariskiLocalAtTarget Scheme Scheme.Pullback.openCoverOfLeftRight Scheme.OpenCover IsClosedImmersion IsSeparated IsZariskiLocalAtTarget.of_openCover)
open _root_.AlgebraicGeometry

universe u

open scoped _root_.AlgebraicGeometry.IsSeparated in

theorem IsSeparated.of_isClosedImmersion_mapDesc_openCover_proof
    {N S : Scheme.{u}} (g : N ⟶ S) (𝒰 : Scheme.OpenCover.{u} N)
    (h : ∀ i j : 𝒰.I₀, IsClosedImmersion (pullback.mapDesc (𝒰.f i) (𝒰.f j) g)) :
    IsSeparated g := by
  constructor
  refine IsZariskiLocalAtTarget.of_openCover (P := @IsClosedImmersion)
    (Scheme.Pullback.openCoverOfLeftRight 𝒰 𝒰 g g) fun ij => ?_
  obtain ⟨i, j⟩ := ij
  have hsq := pullback_map_diagonal_isPullback (𝒰.f i) (𝒰.f j) g
  change IsClosedImmersion (pullback.snd (pullback.diagonal g)
    (pullback.map (𝒰.f i ≫ g) (𝒰.f j ≫ g) g g (𝒰.f i) (𝒰.f j) (𝟙 _) (Category.comp_id _) (Category.comp_id _)))
  have key : hsq.isoPullback.inv ≫ pullback.mapDesc (𝒰.f i) (𝒰.f j) g = pullback.snd (pullback.diagonal g)
      (pullback.map (𝒰.f i ≫ g) (𝒰.f j ≫ g) g g (𝒰.f i) (𝒰.f j) (𝟙 _) (Category.comp_id _) (Category.comp_id _)) := by
    rw [Iso.inv_comp_eq]
    exact hsq.isoPullback_hom_snd.symm
  rw [← key]
  haveI := h i j
  infer_instance

end AlgebraicGeometry

open _root_.AlgebraicGeometry open _root_.P2MW.S_AlgebraicGeometry_IsSeparated_of_isClosedImmersion_mapDesc_openCover.AlgebraicGeometry

universe u

theorem solution
    {N S : Scheme.{u}} (g : N ⟶ S) (𝒰 : Scheme.OpenCover.{u} N)
    (h : ∀ i j : 𝒰.I₀, IsClosedImmersion (pullback.mapDesc (𝒰.f i) (𝒰.f j) g)) :
    IsSeparated g :=
  AlgebraicGeometry.IsSeparated.of_isClosedImmersion_mapDesc_openCover_proof g 𝒰 h
