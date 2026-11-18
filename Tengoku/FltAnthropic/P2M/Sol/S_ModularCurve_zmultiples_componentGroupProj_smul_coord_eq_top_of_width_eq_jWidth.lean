import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_ModularCurve_ComponentGroup
import Tengoku.FltAnthropic.Definitions.Def_ModularCurve_JWidth
import Tengoku.FltAnthropic.Theorems.Thm_ModularCurve_zmultiples_componentGroupProj_smul_coord_eq_top_of_pairwise_coprime

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_ModularCurve_zmultiples_componentGroupProj_smul_coord_eq_top_of_width_eq_jWidth.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_ModularCurve_zmultiples_componentGroupProj_smul_coord_eq_top_of_width_eq_jWidth

open ModularCurve

namespace P2mS3jWidthGen

variable {K : Type*} [Field K] [DecidableEq K]

theorem coprime_jWidth_of_ne {a b : K} (hab : a ≠ b) : (jWidth a).Coprime (jWidth b) := by
  unfold jWidth
  by_cases ha0 : a = 0
  · have hb0 : b ≠ 0 := fun h => hab (ha0.trans h.symm)
    rw [ite_eq_left ha0, ite_eq_right hb0]
    split_ifs <;> decide
  · rw [ite_eq_right ha0]
    by_cases ha : a = 1728
    · have hb : b ≠ 1728 := fun h => hab (ha.trans h.symm)
      rw [ite_eq_left ha]
      by_cases hb0 : b = 0
      · rw [ite_eq_left hb0]; decide
      · rw [ite_eq_right hb0, ite_eq_right hb]; decide
    · rw [ite_eq_right ha]
      exact Nat.coprime_one_left _

end P2mS3jWidthGen

theorem solution
    {K : Type*} [Field K] [DecidableEq K] {ι : Type*} [Fintype ι] (e : ι → ℕ)
    (j : ι → K) (hj : Function.Injective j) (he : ∀ s, e s = jWidth (j s)) (s₀ : ι) :
    AddSubgroup.zmultiples (componentGroupProj e ((e s₀ : ℤ) •
      (LinearMap.proj s₀ : (ι → ℤ) →ₗ[ℤ] ℤ).comp (characterLattice ι).subtype)) = ⊤ := by
  refine ModularCurve.zmultiples_componentGroupProj_smul_coord_eq_top_of_pairwise_coprime e
    (fun s t hst => ?_) s₀
  show (e s).Coprime (e t)
  rw [he s, he t]
  exact P2mS3jWidthGen.coprime_jWidth_of_ne (fun h => hst (hj h))
