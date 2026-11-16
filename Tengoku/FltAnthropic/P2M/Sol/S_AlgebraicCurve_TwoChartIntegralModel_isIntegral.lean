import Tengoku.Seed.AlgebraicGeometry.Morphisms.Flat
import Tengoku.Seed.RingTheory.Flat.TorsionFree
import Tengoku.Seed.RingTheory.DedekindDomain.Basic
import Tengoku.Seed.AlgebraicGeometry.Properties
import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_AlgebraicCurve_TwoChartIntegralModel

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_AlgebraicCurve_TwoChartIntegralModel_isIntegral.lean`: wrote out 6 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 2 `p2m_export`, 1 `p2m_open`, 3 `p2m_reactivate`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_AlgebraicCurve_TwoChartIntegralModel_isIntegral

set_option autoImplicit false

noncomputable section

namespace AlgebraicCurve
export _root_.AlgebraicCurve (TwoChartIntegralModel)
namespace TwoChartIntegralModel
export _root_.AlgebraicCurve.TwoChartIntegralModel (chartAlg XMid fFin fInf ιFin ιInf glue_condition mem_range_ιFin_or_mem_range_ιInf)
open _root_.AlgebraicCurve.TwoChartIntegralModel open _root_.AlgebraicCurve

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

universe u

variable (R : Type u) [CommRing R] (F : Type u) [Field F] [Algebra R F] (j : F) [Fact (j ≠ 0)]

/--
@isnad1 id=isdomain.0h3v.s6.9a224a47d8a9 from=translated src=- shape=553fed7c vocab=2cb094d1
-/
scoped instance isDomain_chartAlg' (S : Set F) : IsDomain (CommRingCat.of (chartAlg R F S)) :=
  inferInstanceAs (IsDomain (chartAlg R F S))

/--
@isnad1 id=nonempty.0h3v.s9.d9fa10d0cad0 from=translated src=- shape=5df62743 vocab=50ceb593
-/
theorem range_ιFin_inter_range_ιInf_nonempty :
    (Set.range (ιFin R F j).base ∩ Set.range (ιInf R F j).base).Nonempty := by
  obtain ⟨z⟩ : Nonempty (XMid R F j) := inferInstance
  refine ⟨(fFin R F j ≫ ιFin R F j).base z, ⟨(fFin R F j).base z, ?_⟩, ⟨(fInf R F j).base z, ?_⟩⟩
  · rw [Scheme.Hom.comp_base, TopCat.comp_app]
  · rw [glue_condition, Scheme.Hom.comp_base, TopCat.comp_app]

/--
@isnad1 id=ispreirr.0h5v.s8.59806ec49fa5 from=translated src=- shape=d30636c0 vocab=6b66975b
-/
theorem isPreirreducible_range_of_irreducibleSpace {Y : Scheme.{u}} [IrreducibleSpace Y]
    (f : Y ⟶ AlgebraicCurve.TwoChartIntegralModel R F j) : IsPreirreducible (Set.range f.base) := by
  rw [← Set.image_univ]
  exact ((IrreducibleSpace.isIrreducible_univ Y).image f.base
    f.continuous.continuousOn).isPreirreducible

/--
@isnad1 id=irreduci.0h3v.s6.fda7eb6c9319 from=translated src=- shape=731acf8a vocab=7a10ef64
-/
theorem irreducibleSpace : IrreducibleSpace (AlgebraicCurve.TwoChartIntegralModel R F j) := by
  have hU₁o : IsOpen (Set.range (ιFin R F j).base) := (ιFin R F j).isOpenEmbedding.isOpen_range
  have hU₂o : IsOpen (Set.range (ιInf R F j).base) := (ιInf R F j).isOpenEmbedding.isOpen_range
  have hU₁i : IsPreirreducible (Set.range (ιFin R F j).base) :=
    isPreirreducible_range_of_irreducibleSpace R F j _
  have hU₂i : IsPreirreducible (Set.range (ιInf R F j).base) :=
    isPreirreducible_range_of_irreducibleSpace R F j _
  have hmeet := range_ιFin_inter_range_ιInf_nonempty R F j
  have h₁ : Set.range (ιFin R F j).base ⊆
      closure (Set.range (ιFin R F j).base ∩ Set.range (ιInf R F j).base) :=
    subset_closure_inter_of_isPreirreducible_of_isOpen hU₁i hU₂o hmeet
  have h₂ : Set.range (ιInf R F j).base ⊆
      closure (Set.range (ιFin R F j).base ∩ Set.range (ιInf R F j).base) := by
    rw [Set.inter_comm]
    exact subset_closure_inter_of_isPreirreducible_of_isOpen hU₂i hU₁o
      (by rwa [Set.inter_comm] at hmeet)
  have hcov : Set.range (ιFin R F j).base ∪ Set.range (ιInf R F j).base = Set.univ :=
    Set.eq_univ_of_forall (mem_range_ιFin_or_mem_range_ιInf R F j)
  have hdense : closure (Set.range (ιFin R F j).base ∩ Set.range (ιInf R F j).base) = Set.univ :=
    Set.eq_univ_of_univ_subset (hcov ▸ Set.union_subset h₁ h₂)
  have hpre : IsPreirreducible (Set.univ : Set (AlgebraicCurve.TwoChartIntegralModel R F j)) := by
    rw [← hdense]
    exact (hU₁i.open_subset (hU₁o.inter hU₂o) Set.inter_subset_left).closure
  obtain ⟨x, -⟩ := hmeet
  exact { isPreirreducible_univ := hpre, toNonempty := ⟨x⟩ }

/--
@isnad1 id=isreduce.0h3v.s5.73b7610b1170 from=translated src=- shape=216d8d42 vocab=f48b784e
-/
theorem isReduced : IsReduced (AlgebraicCurve.TwoChartIntegralModel R F j) := by
  have (x : AlgebraicCurve.TwoChartIntegralModel R F j) :
      _root_.IsReduced ((AlgebraicCurve.TwoChartIntegralModel R F j).presheaf.stalk x) := by
    rcases mem_range_ιFin_or_mem_range_ιInf R F j x with ⟨y, rfl⟩ | ⟨y, rfl⟩
    · exact isReduced_of_injective _
        (asIso <| (ιFin R F j).stalkMap y).commRingCatIsoToRingEquiv.injective
    · exact isReduced_of_injective _
        (asIso <| (ιInf R F j).stalkMap y).commRingCatIsoToRingEquiv.injective
  exact isReduced_of_isReduced_stalk _

/--
@isnad1 id=isintegr.0h3v.s5.398f4612a91e from=translated src=- shape=216d8d42 vocab=6bc1229b
-/
theorem isIntegral_impl : IsIntegral (AlgebraicCurve.TwoChartIntegralModel R F j) :=
  haveI := isReduced R F j
  haveI := irreducibleSpace R F j
  isIntegral_of_irreducibleSpace_of_isReduced _

end AlgebraicCurve.TwoChartIntegralModel
open scoped _root_.P2MW.S_AlgebraicCurve_TwoChartIntegralModel_isIntegral.AlgebraicCurve _root_.P2MW.S_AlgebraicCurve_TwoChartIntegralModel_isIntegral.AlgebraicCurve.TwoChartIntegralModel
open scoped _root_.P2MW.S_AlgebraicCurve_TwoChartIntegralModel_isIntegral.AlgebraicCurve

end
open scoped _root_.P2MW.S_AlgebraicCurve_TwoChartIntegralModel_isIntegral.AlgebraicCurve _root_.P2MW.S_AlgebraicCurve_TwoChartIntegralModel_isIntegral.AlgebraicCurve.TwoChartIntegralModel

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry _root_.AlgebraicCurve.TwoChartIntegralModel _root_.P2MW.S_AlgebraicCurve_TwoChartIntegralModel_isIntegral.AlgebraicCurve.TwoChartIntegralModel in
/--
@isnad1 id=isintegr.0h3v.s5.398f4612a91e from=translated src=- shape=216d8d42 vocab=6bc1229b
-/
theorem solution.{u} (R : Type u) [CommRing R] (F : Type u) [Field F] [Algebra R F] (j : F) [Fact (j ≠ 0)] :
    IsIntegral (AlgebraicCurve.TwoChartIntegralModel R F j) :=
  AlgebraicCurve.TwoChartIntegralModel.isIntegral_impl R F j
