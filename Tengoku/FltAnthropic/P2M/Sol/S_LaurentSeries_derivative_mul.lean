import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_LaurentSeries_derivative_mul.lean`: wrote out 2 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_export`, 1 `p2m_open`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_LaurentSeries_derivative_mul

set_option autoImplicit false

open HahnSeries

namespace LaurentSeries
export _root_.LaurentSeries (derivative hasseDeriv_coeff derivative_apply)
namespace R1
open _root_.LaurentSeries

variable {R : Type*} [CommRing R]

noncomputable def thetaR (f : LaurentSeries R) : LaurentSeries R :=
  single (1 : ℤ) (1 : R) * LaurentSeries.derivative R f

/--
@isnad1 id=eq.0h3v.s9.d065c564f19d from=translated src=- shape=b283b290 vocab=6bd292bd
-/
theorem coeff_single_one_mul_derivative_add_one (f : LaurentSeries R) (m : ℤ) :
    (single (1 : ℤ) (1 : R) * LaurentSeries.derivative R f).coeff (m + 1) =
      ((m + 1 : ℤ) : R) * f.coeff (m + 1) := by
  rw [HahnSeries.coeff_single_mul_add, one_mul, LaurentSeries.derivative_apply,
    LaurentSeries.hasseDeriv_coeff, Ring.choose_one_right, zsmul_eq_mul]
  simp only [Nat.cast_one]

/--
@isnad1 id=eq.0h3v.s9.1a1de92c89bb from=translated src=- shape=3f27470d vocab=3068972c
-/
theorem coeff_single_one_mul_derivative (f : LaurentSeries R) (n : ℤ) :
    (single (1 : ℤ) (1 : R) * LaurentSeries.derivative R f).coeff n = (n : R) * f.coeff n := by
  have h := coeff_single_one_mul_derivative_add_one f (n - 1)
  simp only [sub_add_cancel] at h
  exact h

/--
@isnad1 id=eq.0h3v.s6.8fd89bca9f0f from=translated src=- shape=36319ad0 vocab=4a53192e
-/
theorem coeff_thetaR (f : LaurentSeries R) (n : ℤ) : (thetaR f).coeff n = (n : R) * f.coeff n :=
  coeff_single_one_mul_derivative f n

/--
@isnad1 id=le.0h2v.s5.d958cb5b2ec3 from=translated src=- shape=daaeb034 vocab=f2455556
-/
theorem support_thetaR_subset (f : LaurentSeries R) : (thetaR f).support ⊆ f.support := by
  intro n hn
  rw [HahnSeries.mem_support, coeff_thetaR] at hn
  rw [HahnSeries.mem_support]
  exact right_ne_zero_of_mul hn

/--
@isnad1 id=eq.0h3v.s8.7f634f3a77fa from=translated src=- shape=a4882fc9 vocab=423b505a
-/
theorem thetaR_mul (f g : LaurentSeries R) : thetaR (f * g) = thetaR f * g + f * thetaR g := by
  ext n
  rw [HahnSeries.coeff_add, coeff_thetaR, HahnSeries.coeff_mul,
    HahnSeries.coeff_mul_left' f.isPWO_support (support_thetaR_subset f),
    HahnSeries.coeff_mul_right' g.isPWO_support (support_thetaR_subset g),
    Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun ij hij => ?_
  rw [Finset.mem_antidiagonal] at hij
  obtain ⟨-, -, hsum⟩ := hij
  rw [coeff_thetaR, coeff_thetaR, ← hsum, Int.cast_add]
  ring

/--
@isnad1 id=injectiv.0h1v.s8.097e19342b9e from=translated src=- shape=eac687ce vocab=90fcc112
-/
theorem single_one_mul_injective : Function.Injective fun x : LaurentSeries R => single (1 : ℤ) (1 : R) * x := by
  intro x y h
  ext n
  have h' := congrArg (fun w : LaurentSeries R => w.coeff (n + 1)) h
  simpa [HahnSeries.coeff_single_mul_add] using h'

/--
@isnad1 id=eq.0h3v.s10.a9cae0b9dca0 from=translated src=- shape=0eb746e6 vocab=c9fb9739
-/
theorem main (f g : LaurentSeries R) :
    LaurentSeries.derivative R (f * g) =
      LaurentSeries.derivative R f * g + f * LaurentSeries.derivative R g := by
  apply single_one_mul_injective
  show single (1 : ℤ) (1 : R) * LaurentSeries.derivative R (f * g) =
    single (1 : ℤ) (1 : R) * (LaurentSeries.derivative R f * g + f * LaurentSeries.derivative R g)
  have h := thetaR_mul f g
  simp only [thetaR] at h
  rw [h]; ring

end LaurentSeries.R1

/--
@isnad1 id=eq.0h3v.s10.a9cae0b9dca0 from=translated src=- shape=0eb746e6 vocab=c9fb9739
-/
theorem solution {R : Type*} [CommRing R] (f g : LaurentSeries R) :
    LaurentSeries.derivative R (f * g) =
      LaurentSeries.derivative R f * g + f * LaurentSeries.derivative R g :=
  LaurentSeries.R1.main f g
