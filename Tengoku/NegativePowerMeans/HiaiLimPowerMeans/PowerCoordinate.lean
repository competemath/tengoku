import Tengoku.NegativePowerMeans.HiaiLimPowerMeans.Scalar

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Scalar power-mean coordinates

The spectral comparator in the paper is obtained by applying this scalar
function independently to each ordered eigenvalue coordinate.
-/

namespace HiaiLimPowerMeans

open Finset
open scoped BigOperators

/-- A scalar weighted power mean, without imposing normalization of `w`.-/
noncomputable def powerCoordinate {m : ℕ}
    (w x : Fin m → ℝ) (t : ℝ) : ℝ :=
  (∑ j, w j * (x j) ^ t) ^ t⁻¹

lemma powerCoordinate_nonneg {m : ℕ} {w x : Fin m → ℝ} {t : ℝ}
    (hw : ∀ j, 0 ≤ w j) (hx : ∀ j, 0 ≤ x j) :
    0 ≤ powerCoordinate w x t := by
  apply Real.rpow_nonneg
  exact Finset.sum_nonneg fun j _ ↦ mul_nonneg (hw j) (Real.rpow_nonneg (hx j) t)

lemma powerCoordinate_pos {m : ℕ} [NeZero m]
    {w x : Fin m → ℝ} {t : ℝ}
    (hw : ∀ j, 0 < w j) (hx : ∀ j, 0 < x j) :
    0 < powerCoordinate w x t := by
  apply Real.rpow_pos_of_pos
  exact Finset.sum_pos
    (fun j _ ↦ mul_pos (hw j) (Real.rpow_pos_of_pos (hx j) t)) Finset.univ_nonempty

/-- Raising a positive scalar power mean back to any nonzero order recovers
the weighted sum from which it was defined.-/
theorem powerCoordinate_rpow_order_of_ne {m : ℕ} [NeZero m]
    {w x : Fin m → ℝ} {t : ℝ}
    (hw : ∀ j, 0 < w j) (hx : ∀ j, 0 < x j) (ht : t ≠ 0) :
    (powerCoordinate w x t) ^ t = ∑ j, w j * (x j) ^ t := by
  let s : ℝ := ∑ j, w j * (x j) ^ t
  have hs : 0 < s := Finset.sum_pos
    (fun j _ ↦ mul_pos (hw j) (Real.rpow_pos_of_pos (hx j) t))
    Finset.univ_nonempty
  unfold powerCoordinate
  change (s ^ t⁻¹) ^ t = s
  rw [← Real.rpow_mul hs.le]
  simp [ht]

/-- Positive-order specialization of `powerCoordinate_rpow_order_of_ne`.-/
theorem powerCoordinate_rpow_order {m : ℕ} [NeZero m]
    {w x : Fin m → ℝ} {t : ℝ}
    (hw : ∀ j, 0 < w j) (hx : ∀ j, 0 < x j) (ht : 0 < t) :
    (powerCoordinate w x t) ^ t = ∑ j, w j * (x j) ^ t :=
  powerCoordinate_rpow_order_of_ne hw hx ht.ne'

/-- Division identity for a nonzero-order scalar power mean.-/
theorem powerCoordinate_div_rpow_of_ne {m : ℕ} [NeZero m]
    {w x : Fin m → ℝ} {y t : ℝ}
    (hw : ∀ j, 0 < w j) (hx : ∀ j, 0 < x j) (hy : 0 < y) (ht : t ≠ 0) :
    (powerCoordinate w x t / y) ^ t =
      ∑ j, w j * (x j / y) ^ t := by
  rw [Real.div_rpow (powerCoordinate_pos hw hx).le hy.le,
    powerCoordinate_rpow_order_of_ne hw hx ht]
  simp_rw [Real.div_rpow (hx _).le hy.le]
  rw [Finset.sum_div]
  congr 1
  funext j
  ring

/-- Positive-order specialization of `powerCoordinate_div_rpow_of_ne`.-/
theorem powerCoordinate_div_rpow {m : ℕ} [NeZero m]
    {w x : Fin m → ℝ} {y t : ℝ}
    (hw : ∀ j, 0 < w j) (hx : ∀ j, 0 < x j) (hy : 0 < y) (ht : 0 < t) :
    (powerCoordinate w x t / y) ^ t =
      ∑ j, w j * (x j / y) ^ t :=
  powerCoordinate_div_rpow_of_ne hw hx hy ht.ne'

/-- Coordinatewise monotonicity of the scalar positive power mean.-/
theorem powerCoordinate_mono {m : ℕ} {w x z : Fin m → ℝ} {t : ℝ}
    (hw : ∀ j, 0 ≤ w j) (hx : ∀ j, 0 ≤ x j)
    (hxz : ∀ j, x j ≤ z j) (ht : 0 < t) :
    powerCoordinate w x t ≤ powerCoordinate w z t := by
  apply Real.rpow_le_rpow
  · exact Finset.sum_nonneg fun j _ ↦ mul_nonneg (hw j) (Real.rpow_nonneg (hx j) t)
  · exact Finset.sum_le_sum fun j _ ↦ mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (hx j) (hxz j) ht.le) (hw j)
  · exact inv_nonneg.2 ht.le

/-- The scalar identity used when the positive-order result is inverted:
the inverse of the order-`t` mean of inverse inputs is the order-`-t`
mean of the original inputs.-/
theorem inv_powerCoordinate_invs {m : ℕ} [NeZero m]
    {w a : Fin m → ℝ} {t : ℝ}
    (hw : ∀ j, 0 < w j) (ha : ∀ j, 0 < a j) :
    (powerCoordinate w (fun j ↦ (a j)⁻¹) t)⁻¹ =
      powerCoordinate w a (-t) := by
  have hsum :
      (∑ j, w j * ((a j)⁻¹) ^ t) = ∑ j, w j * (a j) ^ (-t) := by
    apply Finset.sum_congr rfl
    intro j _
    rw [Real.rpow_neg_eq_inv_rpow]
  have hbase : 0 < ∑ j, w j * (a j) ^ (-t) :=
    Finset.sum_pos
      (fun j _ ↦ mul_pos (hw j) (Real.rpow_pos_of_pos (ha j) (-t)))
      Finset.univ_nonempty
  unfold powerCoordinate
  rw [hsum, inv_neg]
  exact (Real.rpow_neg hbase.le t⁻¹).symm

end HiaiLimPowerMeans
