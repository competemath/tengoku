import Tengoku.Seed.RingTheory.LaurentSeries
import Tengoku.Seed.RingTheory.Derivation.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
Formal differentiation of Laurent series, including the product rule and
the characteristic-p coefficient obstruction used in Lemma 2.2.
-/

namespace PiIrrationality

open HahnSeries

/--
@isnad1 id=eq.0h3v.s8.a745e5a20d87 from=translated src=- shape=a713723b vocab=ccd67ae4
-/
theorem laurent_derivative_coeff {R : Type*} [CommRing R]
    (f : LaurentSeries R) (n : ℤ) :
    (LaurentSeries.derivative R f).coeff n = (n + 1 : ℤ) * f.coeff (n + 1) := by
  simp [LaurentSeries.derivative, LaurentSeries.hasseDeriv_coeff, zsmul_eq_mul]

private theorem euler_coeff {R : Type*} [CommRing R]
    (f : LaurentSeries R) (n : ℤ) :
    (single 1 1 * LaurentSeries.derivative R f).coeff n = (n : R) * f.coeff n := by
  simp [coeff_single_mul]

private theorem euler_support_subset {R : Type*} [CommRing R]
    (f : LaurentSeries R) :
    (single 1 1 * LaurentSeries.derivative R f).support ⊆ f.support := by
  intro n hn
  simp only [mem_support, euler_coeff, ne_eq] at hn ⊢
  exact fun h => hn (by rw [h, mul_zero])

/--
@isnad1 id=eq.0h3v.s10.a9cae0b9dca0 from=translated src=- shape=0eb746e6 vocab=c9fb9739
-/
theorem laurent_derivative_mul {R : Type*} [CommRing R]
    (f g : LaurentSeries R) :
    LaurentSeries.derivative R (f * g) =
      LaurentSeries.derivative R f * g + f * LaurentSeries.derivative R g := by
  have he : single 1 1 * LaurentSeries.derivative R (f * g) =
      (single 1 1 * LaurentSeries.derivative R f) * g +
        f * (single 1 1 * LaurentSeries.derivative R g) := by
    ext n
    rw [euler_coeff, coeff_mul, coeff_add,
      coeff_mul_left' f.isPWO_support (euler_support_subset f),
      coeff_mul_right' g.isPWO_support (euler_support_subset g),
      Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro ij hij
    have hs : ij.1 + ij.2 = n := (Finset.mem_antidiagonal.mp hij).2.2
    rw [euler_coeff, euler_coeff, ← hs, Int.cast_add]
    ring
  rw [show f * (single 1 1 * LaurentSeries.derivative R g) =
    single 1 1 * (f * LaurentSeries.derivative R g) by ring] at he
  have h := congrArg (fun x : LaurentSeries R => single (-1) 1 * x) he
  simpa only [mul_add, ← mul_assoc, single_mul_single, neg_add_cancel,
    one_mul, single_zero_one, mul_one] using h

noncomputable def laurentDerivation (R : Type*) [CommRing R] :
    Derivation R (LaurentSeries R) (LaurentSeries R) where
  toFun f := LaurentSeries.derivative R f
  map_add' f g := (LaurentSeries.derivative R).map_add f g
  map_smul' r f := by
    ext n
    simp [Algebra.smul_def, HahnSeries.algebraMap_apply', PowerSeries.algebraMap_eq, C_apply,
      LaurentSeries.derivative]
  map_one_eq_zero' := by
    ext n
    simp [LaurentSeries.derivative, ← single_zero_one, LaurentSeries.hasseDeriv_single]
  leibniz' f g := by
    change LaurentSeries.derivative R (f * g) =
      f * LaurentSeries.derivative R g + g * LaurentSeries.derivative R f
    rw [laurent_derivative_mul]
    ring

/--
@isnad1 id=eq.0h3v.s8.b30c78494a6b from=translated src=- shape=2d532560 vocab=d3521582
-/
theorem laurent_derivative_neg_coeff {R : Type*} [CommRing R]
    (f : LaurentSeries R) (j : ℤ) :
    (LaurentSeries.derivative R f).coeff (-j - 1) = -(j : R) * f.coeff (-j) := by
  simp

/--
@isnad1 id=eq.1h3v.s9.669f585ee400 from=translated src=- shape=2f29554f vocab=4176529a
-/
theorem laurent_derivative_coeff_zero {p : ℕ} (f : LaurentSeries (ZMod p))
    (j : ℤ) (hj : (p : ℤ) ∣ j) :
    (LaurentSeries.derivative (ZMod p) f).coeff (-j - 1) = 0 := by
  rw [laurent_derivative_neg_coeff, (ZMod.intCast_zmod_eq_zero_iff_dvd j p).2 hj]
  simp

end PiIrrationality
