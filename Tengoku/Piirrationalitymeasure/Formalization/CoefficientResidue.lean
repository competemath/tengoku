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

theorem laurentResidue_derivation (f : LaurentSeries ℚ) :
    laurentResidue (laurentDerivation ℚ f) = 0 := by
  change (LaurentSeries.derivative ℚ f).coeff (-1) = 0
  rw [laurent_derivative_coeff]
  norm_num

theorem laurentResidue_const_mul (c : ℚ) (f : LaurentSeries ℚ) :
    laurentResidue ((c : LaurentSeries ℚ) * f) = c * laurentResidue f := by
  change ((c : LaurentSeries ℚ) * f).coeff (-1) = c * f.coeff (-1)
  rw [← eq_ratCast (HahnSeries.C : ℚ →+* LaurentSeries ℚ) c, HahnSeries.C_apply,
    coeff_single_mul]
  simp

theorem laurentDerivation_intCast (c : ℤ) :
    laurentDerivation ℚ (c : LaurentSeries ℚ) = 0 := by
  cases c with
  | ofNat n => exact Derivation.map_natCast _ n
  | negSucc n =>
    simp only [Int.cast_negSucc, map_neg, Derivation.map_natCast, neg_zero]

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

theorem laurentX_ne_zero : (single 1 1 : LaurentSeries ℚ) ≠ 0 := by simp

theorem one_sub_laurentX_ne_zero : (1 - single 1 1 : LaurentSeries ℚ) ≠ 0 := by
  intro h
  have hc := congrArg (fun f : LaurentSeries ℚ => f.coeff 0) h
  norm_num at hc

theorem mobiusLaurent_add_five :
    mobiusLaurent + 5 = -10 * single 1 1 / (1 - single 1 1) := by
  unfold mobiusLaurent
  field_simp [one_sub_laurentX_ne_zero]
  ring

theorem five_sub_mobiusLaurent :
    5 - mobiusLaurent = 10 / (1 - single 1 1) := by
  unfold mobiusLaurent
  field_simp [one_sub_laurentX_ne_zero]
  ring

theorem mobiusLaurent_add_five_ne_zero : mobiusLaurent + 5 ≠ 0 := by
  rw [mobiusLaurent_add_five]
  exact div_ne_zero (mul_ne_zero (by norm_num) laurentX_ne_zero) one_sub_laurentX_ne_zero

theorem five_sub_mobiusLaurent_ne_zero : 5 - mobiusLaurent ≠ 0 := by
  rw [five_sub_mobiusLaurent]
  exact div_ne_zero (by norm_num) one_sub_laurentX_ne_zero

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
