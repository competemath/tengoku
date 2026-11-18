import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_ModularCurve_X0
import Tengoku.FltAnthropic.Theorems.Thm_LaurentSeries_coeff_pow_char

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_ModularCurve_qExpand_linearIndependent_pow.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_ModularCurve_qExpand_linearIndependent_pow

set_option autoImplicit false

open Polynomial

open ModularCurve in

theorem solution (κ : Type*) [Field κ] (q : ℕ) [Fact q.Prime] [CharP κ q]
    (j : LaurentSeries κ) (hj : j.coeff (-1) ≠ 0) (e : Fin q → LaurentSeries κ)
    (h : ∑ m, ModularCurve.qExpand κ q (e m) * j ^ (m : ℕ) = 0) : ∀ m, e m = 0 := by
  classical
  have hq : q.Prime := Fact.out
  haveI : CharP (LaurentSeries κ) q :=
    charP_of_injective_algebraMap (algebraMap κ (LaurentSeries κ)).injective q
  let P : Subfield (LaurentSeries κ) := (qExpand κ q).fieldRange

  have hP : ∀ x ∈ P, ∀ n : ℤ, ¬ (q : ℤ) ∣ n → x.coeff n = 0 := by
    rintro x ⟨y, rfl⟩ n hn
    exact qExpand_coeff_of_not_dvd _ _ hn
  have hjP : j ∉ P := by
    intro hjm
    apply hj (hP j hjm (-1) ?_)
    intro hd
    have h1 := Int.le_of_dvd one_pos (Int.dvd_neg.mp hd)
    have h2 := hq.two_le
    omega

  have hjq : j ^ q ∈ P := by
    refine ⟨j.map (frobenius κ q), ?_⟩
    ext n
    rw [LaurentSeries.coeff_pow_char]
    by_cases hn : (q : ℤ) ∣ n
    · obtain ⟨m, rfl⟩ := hn
      have hq0 : (q : ℤ) ≠ 0 := by exact_mod_cast hq.ne_zero
      rw [qExpand_coeff_mul, HahnSeries.map_coeff, ite_eq_left ⟨m, rfl⟩, Int.mul_ediv_cancel_left _ hq0,
        frobenius_def]
    · rw [qExpand_coeff_of_not_dvd _ _ hn, ite_eq_right hn]

  set a : P := ⟨j ^ q, hjq⟩ with ha
  have hirr : Irreducible (X ^ q - C a) := by
    refine X_pow_sub_C_irreducible_of_prime hq fun b hb => ?_
    apply hjP
    have hb' : ((b : LaurentSeries κ)) ^ q = j ^ q := by
      have := congrArg (fun z : P => (z : LaurentSeries κ)) hb
      simpa using this
    have hbj : (b : LaurentSeries κ) = j := by
      have h0 : ((b : LaurentSeries κ) - j) ^ q = 0 := by rw [sub_pow_char, hb', sub_self]
      exact sub_eq_zero.mp (pow_eq_zero_iff (hq.ne_zero) |>.mp h0)
    rw [← hbj]; exact b.2

  have hmin : minpoly P j = X ^ q - C a := by
    symm
    refine minpoly.eq_of_irreducible_of_monic hirr ?_ (monic_X_pow_sub_C a hq.ne_zero)
    rw [map_sub, map_pow, aeval_X, aeval_C, sub_eq_zero]
    rfl
  have hdeg : (minpoly P j).natDegree = q := by
    rw [hmin, natDegree_X_pow_sub_C]

  have hli := linearIndependent_pow (K := P) j
  rw [hdeg] at hli
  have hli' := Fintype.linearIndependent_iff.mp hli
    (fun m => (⟨qExpand κ q (e m), ⟨e m, rfl⟩⟩ : P)) ?_
  · intro m
    have := congrArg (fun z : P => (z : LaurentSeries κ)) (hli' m)
    simp only [ZeroMemClass.coe_zero] at this
    exact (qExpand κ q).injective (by rw [this, map_zero])
  · rw [← h]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [Subfield.smul_def, smul_eq_mul]
