import Tengoku.FltAnthropic.Definitions.Def_LocalLanglands_HeckeCosetLocal
import Tengoku.FltAnthropic.Definitions.Def_LocalLanglands_HeckeCosetSystem
import Tengoku.FltAnthropic.Theorems.Thm_LocalGL2_finite_image_integralSubgroup_mul_singleton

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_HeckeIntegralSeam_exists_isHeckeCosetSystem_integralSubgroup_diagPi.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_HeckeIntegralSeam_exists_isHeckeCosetSystem_integralSubgroup_diagPi

set_option autoImplicit false

open scoped Pointwise
open LocalGL2 HeckeIntegralSeam

namespace CosetExists

/--
@isnad1 id=isheckec.1h7v.s5.0f37a3820d4c from=translated src=- shape=593b3c84 vocab=b0642f4d
-/
theorem isHeckeCosetSystem_comp_equiv {G : Type*} [Group G] {U : Subgroup G} {g : G} {ι κ : Type*}
    {reps : ι → G} (h : IsHeckeCosetSystem U g reps) (e : κ ≃ ι) :
    IsHeckeCosetSystem U g (reps ∘ e) := by
  refine ⟨fun k => h.mem_doubleCoset (e k), fun x hx => ?_, fun k k' hkk' => ?_⟩
  · obtain ⟨i, hi⟩ := h.covers x hx
    exact ⟨e.symm i, by simpa using hi⟩
  · exact e.injective (h.mk_injective hkk')

end CosetExists

open CosetExists in
/--
@isnad1 id=ex.2h3v.s8.a37ad2828999 from=translated src=- shape=a7f64c61 vocab=df42e325
-/
theorem solution
    {R : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {K : Type} [Field K] [Algebra R K] [IsFractionRing R K]
    {ϖ : R} (hϖ : Irreducible ϖ) [Finite (R ⧸ Ideal.span {ϖ})]
    (hϖ0 : algebraMap R K ϖ ≠ 0) :
    ∃ (n : ℕ) (rT : Fin n → GL (Fin 2) K),
      HeckeIntegralSeam.IsHeckeCosetSystem (LocalGL2.integralSubgroup R K) (LocalGL2.diagPi ϖ hϖ0) rT := by
  classical
  have hfin := LocalGL2.finite_image_integralSubgroup_mul_singleton (R := R) (K := K) hϖ (diagPi ϖ hϖ0)
  have hsys := canonical_isHeckeCosetSystem hfin
  refine ⟨hfin.toFinset.card, _, isHeckeCosetSystem_comp_equiv hsys hfin.toFinset.equivFin.symm⟩
