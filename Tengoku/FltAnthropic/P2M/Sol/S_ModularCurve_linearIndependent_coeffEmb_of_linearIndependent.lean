import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_ModularCurve_LaurentCoeff

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_ModularCurve_linearIndependent_coeffEmb_of_linearIndependent.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_ModularCurve_linearIndependent_coeffEmb_of_linearIndependent

set_option autoImplicit false

open ModularCurve

universe u v

/--
@isnad1 id=linearin.1h3v.s8.d9b23f10e3eb from=translated src=- shape=f8baaa62 vocab=ea0d9171
-/
theorem solution
    (L : Type u) [Field L] [CharZero L]
    {ι : Type v} {v : ι → LaurentSeries ℚ} (hv : LinearIndependent ℚ v) :
    LinearIndependent L (fun i => coeffEmb L (v i)) := by
  classical
  rw [linearIndependent_iff'] at hv ⊢
  intro s g hg i hi
  let b := Module.Free.chooseBasis ℚ L

  have hcoeff : ∀ (k) (n : ℤ), ∑ j ∈ s, b.repr (g j) k * (v j).coeff n = 0 := by
    intro k n
    have h := congrArg (fun x : LaurentSeries L => b.repr (x.coeff n) k) hg
    simp only [HahnSeries.coeff_sum, HahnSeries.coeff_smul, smul_eq_mul, coeffEmb_coeff, HahnSeries.coeff_zero,
      map_zero, Finsupp.zero_apply, map_sum, Finsupp.coe_finsetSum, Finset.sum_apply] at h
    rw [← h]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [mul_comm (g j), ← Algebra.smul_def, map_smul, Finsupp.smul_apply, smul_eq_mul, mul_comm]

  have hrepr : ∀ k, b.repr (g i) k = 0 := by
    intro k
    refine hv s (fun j => b.repr (g j) k) ?_ i hi
    ext n
    rw [HahnSeries.coeff_sum, HahnSeries.coeff_zero]
    simp only [HahnSeries.coeff_smul, smul_eq_mul]
    exact hcoeff k n
  exact b.repr.map_eq_zero_iff.mp (Finsupp.ext fun k => hrepr k)
