import Tengoku.FltAnthropic.Definitions.Def_ModularCurve_UVCrossingModel

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_ModularCurve_UVCrossingModel_U_mul_V.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_ModularCurve_UVCrossingModel_U_mul_V

open ModularCurve ModularCurve.UVCrossingModel

/--
@isnad1 id=eq.0h2v.s6.200f11cba866 from=translated src=- shape=45e1a3e1 vocab=66deb2ad
-/
theorem solution {W : Type*} [CommRing W] (π : W) :
    U π * V π = const π π :=
  by
  show Ideal.Quotient.mk _ _ * Ideal.Quotient.mk _ _ = Ideal.Quotient.mk _ _
  rw [← map_mul, Ideal.Quotient.mk_eq_mk_iff_sub_mem]
  exact Ideal.subset_span rfl
