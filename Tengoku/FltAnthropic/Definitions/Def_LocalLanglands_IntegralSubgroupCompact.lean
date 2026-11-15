import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_LocalLanglands_LocalHeckeInstance

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

namespace FLT.SpectralSide

/--
@isnad1 id=compacts.0h3v.s4.00f8198121d8 from=translated src=- shape=b0cf41a4 vocab=2eb9a92b
-/
instance instCompactSpaceMatrix {m n R : Type*} [TopologicalSpace R] [CompactSpace R] :
    CompactSpace (Matrix m n R) :=
  inferInstanceAs <| CompactSpace (m → n → R)

/--
@isnad1 id=compacts.0h1v.s6.155ba2a32904 from=translated src=- shape=43a8678d vocab=80b36bab
-/
theorem gl2_compactSpace (R : Type*) [CommRing R] [TopologicalSpace R]
    [IsTopologicalRing R] [T2Space R] [CompactSpace R] :
    CompactSpace (GL (Fin 2) R) := inferInstance

/--
@isnad1 id=iscompac.1h2v.s8.545146d4bed5 from=translated src=- shape=b497a764 vocab=c2c4afdc
-/
theorem isCompact_coe_integralSubgroup (R : Type*) [CommRing R] [TopologicalSpace R]
    [IsTopologicalRing R] [T2Space R] [CompactSpace R]
    (K : Type*) [Field K] [Algebra R K] [TopologicalSpace K]
    (hcont : Continuous (algebraMap R K)) :
    IsCompact ((LocalGL2.integralSubgroup R K : Set (GL (Fin 2) K))) := by
  haveI : CompactSpace (GL (Fin 2) R) := gl2_compactSpace R
  have hmapcont : Continuous (Matrix.GeneralLinearGroup.map (n := Fin 2) (algebraMap R K)) := by
    unfold Matrix.GeneralLinearGroup.map
    refine Continuous.units_map _ ?_
    exact continuous_matrix fun i j =>
      hcont.comp ((continuous_apply j).comp (continuous_apply i))
  have hr : IsCompact
      (Set.range ⇑(Matrix.GeneralLinearGroup.map (n := Fin 2) (algebraMap R K))) :=
    isCompact_range hmapcont
  simpa [LocalGL2.integralSubgroup, MonoidHom.coe_range] using hr

/--
@isnad1 id=iscompac.0h1v.s8.cd5553d079e5 from=translated src=- shape=6331d28a vocab=e4d4ce94
-/
theorem isCompact_coe_integralSubgroup_padic (p : ℕ) [Fact p.Prime] :
    IsCompact ((LocalGL2.integralSubgroup ℤ_[p] ℚ_[p] : Set (GL (Fin 2) ℚ_[p]))) :=
  isCompact_coe_integralSubgroup ℤ_[p] ℚ_[p] continuous_subtype_val

/--
@isnad1 id=compacts.0h1v.s10.7e2fdf803745 from=translated src=- shape=a9c5b27d vocab=0a2771d3
-/
theorem compactSpace_integralSubgroup_padic (p : ℕ) [Fact p.Prime] :
    CompactSpace (LocalGL2.integralSubgroup ℤ_[p] ℚ_[p]) :=
  isCompact_iff_compactSpace.mp (isCompact_coe_integralSubgroup_padic p)

end FLT.SpectralSide
