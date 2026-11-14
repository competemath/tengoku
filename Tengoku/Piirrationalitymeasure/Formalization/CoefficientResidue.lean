import Tengoku.Piirrationalitymeasure.Formalization.PartialFractionIdentity
import Tengoku.Piirrationalitymeasure.Formalization.LaurentDerivative

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Residue preservation for the Mobius substitution in (4.1)--(4.5). -/

namespace PiIrrationality

open HahnSeries Polynomial

local instance : CharZero (LaurentSeries ℚ) := algebraRat.charZero _
noncomputable local instance : Algebra ℚ (LaurentSeries ℚ) := HahnSeries.powerSeriesAlgebra ℤ ℚ
noncomputable local instance : Algebra ℤ (LaurentSeries ℚ) := Ring.toIntAlgebra _

noncomputable def laurentResidue : LaurentSeries ℚ →ₗ[ℚ] ℚ where
  toFun f := f.coeff (-1)
  map_add' _ _ := coeff_add
  map_smul' _ _ := coeff_smul

/--
@isnad1 id=eq.0h1v.s8.8fe6ddd181ea from=translated src=- shape=383acd39 vocab=881d14d9
-/
theorem laurentResidue_derivation (f : LaurentSeries ℚ) :
    laurentResidue (laurentDerivation ℚ f) = 0 := by
  change (LaurentSeries.derivative ℚ f).coeff (-1) = 0
  rw [laurent_derivative_coeff]
  norm_num

/--
@isnad1 id=eq.0h2v.s8.e08ba0986ea6 from=translated src=- shape=4df9be10 vocab=c1dd1fd8
-/
theorem laurentResidue_const_mul (c : ℚ) (f : LaurentSeries ℚ) :
    laurentResidue ((c : LaurentSeries ℚ) * f) = c * laurentResidue f := by
  change ((c : LaurentSeries ℚ) * f).coeff (-1) = c * f.coeff (-1)
  rw [← eq_ratCast (HahnSeries.C : ℚ →+* LaurentSeries ℚ) c, HahnSeries.C_apply,
    coeff_single_mul]
  simp

/--
@isnad1 id=eq.0h1v.s8.83463c33e0ee from=translated src=- shape=7071e9b5 vocab=cf8874e9
-/
theorem laurentDerivation_intCast (c : ℤ) :
    laurentDerivation ℚ (c : LaurentSeries ℚ) = 0 := by
  cases c with
  | ofNat n => exact Derivation.map_natCast _ n
  | negSucc n =>
    simp only [Int.cast_negSucc, map_neg, Derivation.map_natCast, neg_zero]

/--
@isnad1 id=eq.0h2v.s9.2f65dc2b6c21 from=translated src=- shape=721c398c vocab=45721442
-/
theorem laurentResidue_polynomial_mul_derivation (t : LaurentSeries ℚ) (P : Polynomial ℤ) :
    laurentResidue (aeval t P * laurentDerivation ℚ t) = 0 := by
  have hex : ∃ f : LaurentSeries ℚ, laurentDerivation ℚ f = aeval t P * laurentDerivation ℚ t := by
    induction P using Polynomial.induction_on' with
    | add P Q hP hQ =>
      obtain ⟨f, hf⟩ := hP
      obtain ⟨g, hg⟩ := hQ
      exact ⟨f + g, by rw [map_add, hf, hg, map_add, add_mul]⟩
    | monomial k c =>
      refine ⟨(c : LaurentSeries ℚ) * t ^ (k + 1) / (k + 1), ?_⟩
      have hd : laurentDerivation ℚ (k + 1 : LaurentSeries ℚ) = 0 := by
        simpa only [Nat.cast_add, Nat.cast_one] using
          (laurentDerivation ℚ).map_natCast (k + 1)
      rw [(laurentDerivation ℚ).leibniz_div_const _ _ hd, Derivation.leibniz,
        laurentDerivation_intCast, Derivation.leibniz_pow, aeval_monomial]
      simp only [smul_eq_mul, nsmul_eq_mul, Nat.add_sub_cancel, mul_zero,
        add_zero, algebraMap_int_eq, Int.coe_castRingHom]
      push_cast
      have hk : (k + 1 : LaurentSeries ℚ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
      field_simp
  obtain ⟨f, hf⟩ := hex
  rw [← hf]
  exact laurentResidue_derivation f

/--
@isnad1 id=eq.3h2v.s10.bb7325ae30a1 from=translated src=- shape=cfdfd38b vocab=06eb19d6
-/
theorem laurentResidue_polePair_mul_derivation (t : LaurentSeries ℚ) (j : ℕ)
    (hj : 0 < j) (hp : 5 + t ≠ 0) (hm : 5 - t ≠ 0) :
    laurentResidue ((1 / (5 + t) ^ (j + 1) + 1 / (5 - t) ^ (j + 1)) *
      laurentDerivation ℚ t) = 0 := by
  let f : LaurentSeries ℚ :=
    ((5 - t) ^ (-(j : ℤ)) - (5 + t) ^ (-(j : ℤ))) / j
  have hf : laurentDerivation ℚ f =
      (1 / (5 + t) ^ (j + 1) + 1 / (5 - t) ^ (j + 1)) * laurentDerivation ℚ t := by
    dsimp only [f]
    rw [(laurentDerivation ℚ).leibniz_div_const _ _ ((laurentDerivation ℚ).map_natCast j),
      map_sub, Derivation.leibniz_zpow, Derivation.leibniz_zpow,
      map_sub, map_add]
    rw [show laurentDerivation ℚ (5 : LaurentSeries ℚ) = 0 from
      Derivation.map_natCast _ 5]
    simp only [zero_sub, zero_add, smul_eq_mul, zsmul_eq_mul]
    rw [show -(j : ℤ) - 1 = -((j + 1 : ℕ) : ℤ) by omega]
    simp only [zpow_neg, zpow_natCast]
    push_cast
    have hj' : (j : LaurentSeries ℚ) ≠ 0 := by exact_mod_cast hj.ne'
    field_simp [hj', hp, hm]
    ring
  rw [← hf]
  exact laurentResidue_derivation f

noncomputable def mobiusLaurent : LaurentSeries ℚ :=
  -5 * (1 + single 1 1) / (1 - single 1 1)

/--
@isnad1 id=ne.0h0v.s7.6099636bf772 from=translated src=- shape=8b0efe77 vocab=19212807
-/
theorem laurentX_ne_zero : (single 1 1 : LaurentSeries ℚ) ≠ 0 := by simp

/--
@isnad1 id=ne.0h0v.s8.9a5790765f59 from=translated src=- shape=c6a920e4 vocab=2440ae72
-/
theorem one_sub_laurentX_ne_zero : (1 - single 1 1 : LaurentSeries ℚ) ≠ 0 := by
  intro h
  have hc := congrArg (fun f : LaurentSeries ℚ => f.coeff 0) h
  norm_num at hc

/--
@isnad1 id=eq.0h0v.s9.f980d81ac941 from=translated src=- shape=a9a7bcdc vocab=5f5ac8b7
-/
theorem mobiusLaurent_add_five :
    mobiusLaurent + 5 = -10 * single 1 1 / (1 - single 1 1) := by
  unfold mobiusLaurent
  field_simp [one_sub_laurentX_ne_zero]
  ring

/--
@isnad1 id=eq.0h0v.s8.3dc5160d9b76 from=translated src=- shape=a502512e vocab=9f646ac7
-/
theorem five_sub_mobiusLaurent :
    5 - mobiusLaurent = 10 / (1 - single 1 1) := by
  unfold mobiusLaurent
  field_simp [one_sub_laurentX_ne_zero]
  ring

/--
@isnad1 id=ne.0h0v.s6.305ad5b3d478 from=translated src=- shape=b4ca3b3c vocab=3ac53995
-/
theorem mobiusLaurent_add_five_ne_zero : mobiusLaurent + 5 ≠ 0 := by
  rw [mobiusLaurent_add_five]
  exact div_ne_zero (mul_ne_zero (by norm_num) laurentX_ne_zero) one_sub_laurentX_ne_zero

/--
@isnad1 id=ne.0h0v.s6.328f42a7dbc0 from=translated src=- shape=375bc617 vocab=e0f5eb98
-/
theorem five_sub_mobiusLaurent_ne_zero : 5 - mobiusLaurent ≠ 0 := by
  rw [five_sub_mobiusLaurent]
  exact div_ne_zero (by norm_num) one_sub_laurentX_ne_zero

/--
@isnad1 id=eq.0h0v.s9.9d4d2ab8867d from=translated src=- shape=bcb40f47 vocab=57ae43e4
-/
theorem mobiusLaurent_derivation :
    laurentDerivation ℚ mobiusLaurent = -10 / (1 - single 1 1) ^ 2 := by
  have hx : laurentDerivation ℚ (single 1 1) = 1 := by
    change LaurentSeries.derivative ℚ (single 1 1) = 1
    simp [LaurentSeries.derivative, LaurentSeries.hasseDeriv_single, single_zero_one]
  unfold mobiusLaurent
  rw [Derivation.leibniz_div, Derivation.leibniz, map_add, map_sub, hx]
  rw [map_neg]
  rw [show laurentDerivation ℚ (5 : LaurentSeries ℚ) = 0 from
    Derivation.map_natCast _ 5]
  simp only [Derivation.map_one_eq_zero, zero_add, zero_sub, smul_eq_mul]
  field_simp [one_sub_laurentX_ne_zero]
  ring

/--
@isnad1 id=eq.0h0v.s9.5e87500ad1cf from=translated src=- shape=9e237902 vocab=4cb2fed7
-/
theorem mobiusLaurent_logarithmic_pair :
    (1 / (5 + mobiusLaurent) + 1 / (5 - mobiusLaurent)) *
      laurentDerivation ℚ mobiusLaurent = single (-1) 1 := by
  rw [add_comm 5 mobiusLaurent, mobiusLaurent_add_five, five_sub_mobiusLaurent,
    mobiusLaurent_derivation]
  have hx : (single (-1) 1 : LaurentSeries ℚ) = (single 1 1)⁻¹ := by
    simp only [inv_single, inv_one]
  rw [hx]
  field_simp [one_sub_laurentX_ne_zero, laurentX_ne_zero]
  ring

noncomputable def mobiusDensity (n : ℕ) : LaurentSeries ℚ :=
  (5 * mobiusLaurent ^ (2 * 1857 * n) *
    (mobiusLaurent ^ 4 + 6 * mobiusLaurent ^ 2 + 25) ^ (3714 * n) /
      (25 - mobiusLaurent ^ 2) ^ (5570 * n + 1)) * laurentDerivation ℚ mobiusLaurent

/--
@isnad1 id=eq.0h1v.s6.4ba60d9cbd0b from=translated src=- shape=3d27beb4 vocab=f18223cb
-/
theorem mobiusDensity_residue (n : ℕ) :
    laurentResidue (mobiusDensity n) = laurentCoeffRat n 0 := by
  have hp : 5 + mobiusLaurent ≠ 0 := by
    simpa only [add_comm] using mobiusLaurent_add_five_ne_zero
  have hm : mobiusLaurent - 5 ≠ 0 := by
    exact sub_ne_zero.mpr (sub_ne_zero.mp five_sub_mobiusLaurent_ne_zero).symm
  unfold mobiusDensity
  rw [rationalFunction_partialFractions n _ mobiusLaurent_add_five_ne_zero hm,
    add_mul, map_add, laurentResidue_polynomial_mul_derivation, zero_add,
    Finset.sum_mul, map_sum]
  rw [Finset.sum_eq_single (0 : Fin (5570 * n + 1))]
  · simp only [Fin.val_zero, Nat.cast_zero, zero_add, pow_one, mul_assoc,
      laurentResidue_const_mul, mobiusLaurent_logarithmic_pair]
    simp [laurentResidue]
  · intro j hj hj0
    rw [mul_assoc, laurentResidue_const_mul,
      laurentResidue_polePair_mul_derivation _ _ (by
        have h : j.val ≠ 0 := fun h => hj0 (Fin.ext h)
        omega) hp five_sub_mobiusLaurent_ne_zero, mul_zero]
  · simp

end PiIrrationality
