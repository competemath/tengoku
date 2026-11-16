import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_AlgebraicCurve_TwoChartIntegralModel

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_AlgebraicCurve_TwoChartIntegralModel_isLocalization_chartAlg.lean`: wrote out 3 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 2 `p2m_export`, 1 `p2m_open`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_AlgebraicCurve_TwoChartIntegralModel_isLocalization_chartAlg

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgebraicCurve
export _root_.AlgebraicCurve (TwoChartIntegralModel.chartAlg TwoChartIntegralModel TwoChartIntegralModel.chartBaseChange)
namespace TwoChartIntegralModel
export _root_.AlgebraicCurve.TwoChartIntegralModel (chartAlg mem_chartAlg_iff chartBaseChange coe_chartBaseChange chartBaseChange_algebraMap)
open _root_.AlgebraicCurve.TwoChartIntegralModel open _root_.AlgebraicCurve

section H5ring

variable (R : Type u) [CommRing R] (F : Type u) [Field F] [Algebra R F]
variable (R' : Type u) [CommRing R'] [Algebra R R'] [Algebra R' F] [IsScalarTower R R' F]
variable (M : Submonoid R) [IsLocalization M R']

/--
@isnad1 id=ex.1h6v.s8.d812ec75f02a from=translated src=- shape=87cec4c9 vocab=5c21a21f
-/
theorem exists_algebraMap_mul_mem_adjoin_of_isLocalization (S : Set F) {x : F}
    (hx : x ∈ Algebra.adjoin R' S) :
    ∃ m : M, algebraMap R F m * x ∈ Algebra.adjoin R S := by
  induction hx using Algebra.adjoin_induction with
  | mem y hy => exact ⟨1, by rw [OneMemClass.coe_one, map_one, one_mul]; exact Algebra.subset_adjoin hy⟩
  | algebraMap a =>
    obtain ⟨⟨r, m⟩, h⟩ := IsLocalization.surj M a
    refine ⟨m, ?_⟩
    have : algebraMap R F m * algebraMap R' F a = algebraMap R F r := by
      rw [IsScalarTower.algebraMap_apply R R' F (m : R), IsScalarTower.algebraMap_apply R R' F r,
        ← map_mul, mul_comm, h]
    rw [this]
    exact Subalgebra.algebraMap_mem _ r
  | add y z _ _ hy hz =>
    obtain ⟨m, hm⟩ := hy
    obtain ⟨n, hn⟩ := hz
    refine ⟨m * n, ?_⟩
    have : algebraMap R F ↑(m * n) * (y + z) =
        algebraMap R F n * (algebraMap R F m * y) + algebraMap R F m * (algebraMap R F n * z) := by
      rw [Submonoid.coe_mul, map_mul]; ring
    rw [this]
    exact add_mem (mul_mem (Subalgebra.algebraMap_mem _ _) hm)
      (mul_mem (Subalgebra.algebraMap_mem _ _) hn)
  | mul y z _ _ hy hz =>
    obtain ⟨m, hm⟩ := hy
    obtain ⟨n, hn⟩ := hz
    refine ⟨m * n, ?_⟩
    have : algebraMap R F ↑(m * n) * (y * z) =
        (algebraMap R F m * y) * (algebraMap R F n * z) := by
      rw [Submonoid.coe_mul, map_mul]; ring
    rw [this]
    exact mul_mem hm hn

/--
@isnad1 id=ex.1h6v.s8.05f4ebafceec from=translated src=- shape=87cec4c9 vocab=f210c728
-/
theorem exists_algebraMap_mul_mem_chartAlg_of_isLocalization (S : Set F) {x : F}
    (hx : x ∈ chartAlg R' F S) :
    ∃ m : M, algebraMap R F m * x ∈ chartAlg R F S := by
  classical
  obtain ⟨p, hmonic, hroot⟩ := (mem_chartAlg_iff R' F).mp hx
  have hcoeff : ∀ i, ∃ m : M, algebraMap R F m * (p.coeff i : F) ∈ Algebra.adjoin R S :=
    fun i => exists_algebraMap_mul_mem_adjoin_of_isLocalization R F R' M S (p.coeff i).2
  choose m hm using hcoeff
  set mm : M := ∏ i ∈ Finset.range (p.natDegree + 1), m i with hmm
  have hdiv : ∀ i ≤ p.natDegree, algebraMap R F mm * (p.coeff i : F) ∈ Algebra.adjoin R S := by
    intro i hi
    have hmem : i ∈ Finset.range (p.natDegree + 1) := Finset.mem_range.mpr (Nat.lt_succ_of_le hi)
    rw [hmm, ← Finset.mul_prod_erase _ _ hmem, Submonoid.coe_mul, map_mul, Submonoid.coe_finsetProd,
      map_prod, mul_comm (algebraMap R F (m i)), mul_assoc]
    exact mul_mem (prod_mem fun c _ => Subalgebra.algebraMap_mem _ _) (hm i)
  have hmmA : algebraMap R F mm ∈ Algebra.adjoin R S := Subalgebra.algebraMap_mem _ _
  set q : Polynomial F := (p.map (algebraMap (Algebra.adjoin R' S) F)).scaleRoots (algebraMap R F mm)
    with hq
  have hqmonic : q.Monic := (Polynomial.monic_scaleRoots_iff _).mpr (hmonic.map _)
  have hqroot : q.eval (algebraMap R F mm * x) = 0 := by
    rw [hq, Polynomial.scaleRoots_eval_mul, Polynomial.eval_map, hroot, mul_zero]
  have hqcoeff : ∀ i, q.coeff i ∈ Algebra.adjoin R S := by
    intro i
    rw [hq, Polynomial.coeff_scaleRoots, Polynomial.coeff_map, hmonic.natDegree_map]
    by_cases hi : i < p.natDegree
    · obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le (Nat.one_le_iff_ne_zero.mpr (by omega) :
        1 ≤ p.natDegree - i)
      rw [hk, pow_add, pow_one, Subalgebra.algebraMap_def, Algebra.algebraMap_self_apply,
        show (p.coeff i : F) * (algebraMap R F mm * algebraMap R F mm ^ k) =
          algebraMap R F mm ^ k * (algebraMap R F mm * (p.coeff i : F)) by ring]
      exact mul_mem (pow_mem hmmA k) (hdiv i hi.le)
    · rcases (not_lt.mp hi).lt_or_eq with hlt | heq
      · rw [Polynomial.coeff_eq_zero_of_natDegree_lt hlt, map_zero, zero_mul]
        exact zero_mem _
      · rw [← heq, hmonic.coeff_natDegree, map_one, one_mul, Nat.sub_self, pow_zero]
        exact one_mem _
  have hlifts : q ∈ Polynomial.lifts (algebraMap (Algebra.adjoin R S) F) :=
    (Polynomial.lifts_iff_coeff_lifts q).mpr fun i => ⟨⟨q.coeff i, hqcoeff i⟩, rfl⟩
  obtain ⟨q', hq'q, -, hq'monic⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hlifts hqmonic
  refine ⟨mm, (mem_chartAlg_iff R F).mpr ⟨q', hq'monic, ?_⟩⟩
  rw [Polynomial.eval₂_eq_eval_map, hq'q, hqroot]

omit [IsLocalization M R'] in
/--
@isnad1 id=injectiv.0h4v.s9.c284a80ad36f from=translated src=- shape=9f28f346 vocab=5ec4939a
-/
theorem chartBaseChange_injective (S : Set F) : Function.Injective (chartBaseChange R F R' S) :=
  fun x y h => Subtype.ext (by simpa only [coe_chartBaseChange] using congrArg Subtype.val h)

end H5ring

end AlgebraicCurve.TwoChartIntegralModel

open _root_.AlgebraicCurve.TwoChartIntegralModel _root_.P2MW.S_AlgebraicCurve_TwoChartIntegralModel_isLocalization_chartAlg.AlgebraicCurve.TwoChartIntegralModel in

/--
@isnad1 id=islocali.0h5v.s10.4b45c052e707 from=translated src=- shape=23e2a461 vocab=7b25b416
-/
theorem solution
    (R : Type u) [CommRing R] (F : Type u) [Field F] [Algebra R F]
    (R' : Type u) [CommRing R'] [Algebra R R'] [Algebra R' F] [IsScalarTower R R' F]
    (M : Submonoid R) [IsLocalization M R'] (S : Set F) :
    letI : Algebra (AlgebraicCurve.TwoChartIntegralModel.chartAlg R F S)
        (AlgebraicCurve.TwoChartIntegralModel.chartAlg R' F S) :=
      (AlgebraicCurve.TwoChartIntegralModel.chartBaseChange R F R' S).toAlgebra
    IsLocalization (M.map (algebraMap R (AlgebraicCurve.TwoChartIntegralModel.chartAlg R F S)))
      (AlgebraicCurve.TwoChartIntegralModel.chartAlg R' F S) := by
  letI : Algebra (chartAlg R F S) (chartAlg R' F S) := (chartBaseChange R F R' S).toAlgebra
  refine (isLocalization_iff _ _).mpr ⟨?_, ?_, ?_⟩
  · rintro ⟨_, m, hm, rfl⟩
    rw [RingHom.algebraMap_toAlgebra, chartBaseChange_algebraMap]
    exact (IsLocalization.map_units R' (⟨m, hm⟩ : M)).map _
  · intro z
    obtain ⟨m, hm⟩ := exists_algebraMap_mul_mem_chartAlg_of_isLocalization R F R' M S z.2
    refine ⟨(⟨_, hm⟩, ⟨algebraMap R (chartAlg R F S) m, Submonoid.mem_map_of_mem _ m.2⟩),
      Subtype.ext ?_⟩
    simp only [RingHom.algebraMap_toAlgebra, Subalgebra.coe_mul, coe_chartBaseChange,
      Subalgebra.coe_algebraMap]
    exact mul_comm _ _
  · intro x y h
    rw [RingHom.algebraMap_toAlgebra] at h
    exact ⟨1, by rw [chartBaseChange_injective R F R' S h]⟩
