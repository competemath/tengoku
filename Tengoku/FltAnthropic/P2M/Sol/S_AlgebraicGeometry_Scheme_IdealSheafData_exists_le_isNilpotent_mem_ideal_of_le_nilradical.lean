import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_AlgebraicGeometry_Scheme_IdealSheafData_exists_le_isNilpotent_mem_ideal_of_le_nilradical.lean`: wrote out 3 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_export`, 2 `p2m_open`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_exists_le_isNilpotent_mem_ideal_of_le_nilradical

set_option autoImplicit false

universe u

open _root_.CategoryTheory open _root_.AlgebraicGeometry open _root_.TopologicalSpace open _root_.Opposite

namespace AlgebraicGeometry
export _root_.AlgebraicGeometry (Scheme.IdealSheafData.ideal_iInf Scheme.IdealSheafData.ideal_bot HasAffineProperty Scheme.IdealSheafData.radical_ideal Scheme.Hom Scheme.IdealSheafData.ideal_map Scheme.Hom.image_preimage_eq_opensRange_inf QuasiCompact IsAffine quasiSeparatedSpace_iff_quasiSeparated Scheme.IdealSheafData.ideal_pow Scheme Scheme.IdealSheafData.zero_eq_bot HasAffineProperty.iff_of_isAffine Scheme.IdealSheafData.ext_of_iSup_eq_top Scheme.IdealSheafData.ideal_mono Scheme.Opens.ι_apply IsAffineOpen QuasiSeparated Scheme.Hom.ker_apply Scheme.Opens Scheme.Hom.appLE_map Scheme.IdealSheafData.ofIdealTop Scheme.Opens.opensRange_ι Scheme.Hom.comp_apply Scheme.Opens.ι_appLE Scheme.IdealSheafData.ofIdealTop_ideal Scheme.IdealSheafData)
open _root_.AlgebraicGeometry

namespace ThickAffNilExt

variable {X : Scheme.{u}}

/--
@isnad1 id=eq.1h3v.s7.9b9a1d280cdc from=translated src=- shape=c3d9d9a7 vocab=9547322a
-/
theorem image_preimage_eq {V : X.Opens} {W : X.Opens} (hWV : W ≤ V) : V.ι ''ᵁ V.ι ⁻¹ᵁ W = W := by
  rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι, inf_eq_right.mpr hWV]

end ThickAffNilExt

end AlgebraicGeometry
