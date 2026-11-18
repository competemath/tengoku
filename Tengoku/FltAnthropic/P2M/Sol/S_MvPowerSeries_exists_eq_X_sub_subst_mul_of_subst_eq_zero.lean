import Tengoku
import Tengoku.FltAnthropic.Theorems.Thm_MvPowerSeries_exists_eq_X_sub_subst_mul_add_subst_of_constantCoeff_eq_zero

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_MvPowerSeries_exists_eq_X_sub_subst_mul_of_subst_eq_zero.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_MvPowerSeries_exists_eq_X_sub_subst_mul_of_subst_eq_zero

set_option autoImplicit false

universe u

open MvPowerSeries

namespace FactorThmGC7

variable {k : Type u} [CommRing k]

noncomputable abbrev Sb (φ : PowerSeries k) : Fin 2 → PowerSeries k := ![(PowerSeries.X : PowerSeries k), φ]

/--
@isnad1 id=hassubst.1h2v.s6.f3d2f4e1362f from=translated src=- shape=1e0f51b9 vocab=04e728da
-/
theorem hasSubst_Sb {φ : PowerSeries k} (hφ : PowerSeries.constantCoeff φ = 0) : HasSubst (Sb φ) := by
  apply hasSubst_of_constantCoeff_zero
  intro s
  fin_cases s
  · show MvPowerSeries.constantCoeff (PowerSeries.X : PowerSeries k) = 0
    exact PowerSeries.constantCoeff_X
  · show MvPowerSeries.constantCoeff φ = 0
    exact hφ

end FactorThmGC7

open FactorThmGC7 in
/--
@isnad1 id=ex.2h3v.s8.c9719abe24c1 from=translated src=- shape=29846bc6 vocab=570a1e29
-/
theorem solution
    {R : Type u} [CommRing R] (f : MvPowerSeries (Fin 2) R)
    (φ : PowerSeries R) (hφ0 : PowerSeries.constantCoeff φ = 0)
    (hroot : MvPowerSeries.subst ![(PowerSeries.X : PowerSeries R), φ] f = 0) :
    ∃ M : MvPowerSeries (Fin 2) R,
      f = (X 1 - PowerSeries.subst (X 0 : MvPowerSeries (Fin 2) R) φ) * M := by
  classical
  set φX : MvPowerSeries (Fin 2) R := PowerSeries.subst (X 0 : MvPowerSeries (Fin 2) R) φ with hφX

  obtain ⟨Q, hQ⟩ := MvPowerSeries.exists_eq_X_sub_subst_mul_add_subst_of_constantCoeff_eq_zero R φ hφ0 f

  have hb : HasSubst (fun _ : Unit => (X 0 : MvPowerSeries (Fin 2) R)) :=
    hasSubst_of_constantCoeff_zero (fun _ => constantCoeff_X 0)
  have hcomp : MvPowerSeries.subst ![(X 0 : MvPowerSeries (Fin 2) R), φX] f =
      MvPowerSeries.subst (fun _ : Unit => (X 0 : MvPowerSeries (Fin 2) R))
        (MvPowerSeries.subst ![(PowerSeries.X : PowerSeries R), φ] f) := by
    rw [subst_comp_subst_apply (hasSubst_Sb hφ0) hb]
    congr 1
    funext s
    refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun l => l.elim0) j) s
    · show (X 0 : MvPowerSeries (Fin 2) R) = subst (fun _ : Unit => (X 0 : MvPowerSeries (Fin 2) R)) (Sb φ 0)
      simp only [Sb, Matrix.cons_val_zero]
      exact (subst_X hb ()).symm
    · show φX = subst (fun _ : Unit => (X 0 : MvPowerSeries (Fin 2) R)) (Sb φ 1)
      simp only [Sb, Matrix.cons_val_one, Matrix.head_cons]
      rw [hφX, PowerSeries.subst_def]
      rfl
  have hrem : MvPowerSeries.subst ![(X 0 : MvPowerSeries (Fin 2) R), φX] f = 0 := by
    rw [hcomp, hroot, ← coe_substAlgHom hb, map_zero]
  exact ⟨Q, by rw [hQ, hrem, add_zero]⟩
