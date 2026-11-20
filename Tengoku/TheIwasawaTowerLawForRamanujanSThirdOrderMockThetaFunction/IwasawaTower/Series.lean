import Tengoku.TheIwasawaTowerLawForRamanujanSThirdOrderMockThetaFunction.IwasawaTower.Basic
import Tengoku.Seed.Algebra.CharP.Lemmas
import Tengoku.Seed.RingTheory.PowerSeries.Ideal
import Tengoku.Seed.RingTheory.PowerSeries.Order
import Tengoku.Seed.Tactic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Characteristic-three auxiliary series

Author: Joesph D. Burke III.
-/

noncomputable section

open scoped BigOperators

namespace IwasawaTower.Series

open Finset PowerSeries

abbrev 𝔽₃ := ZMod 3
abbrev PS := PowerSeries 𝔽₃

instance : CharP PS 3 := charP_of_injective_algebraMap' 𝔽₃ 3

/-- The power-series uniformizer, written `Y` in the paper.-/
def Y : PS := PowerSeries.X

/-- The series `X = 1 - Y`.-/
def X : PS := 1 - Y

/-- `Aᵣ = ∏_{j=1}^r (1 + X^j)`.-/
def A (r : ℕ) : PS :=
  ∏ j ∈ Finset.range r, (1 + X ^ (j + 1))

/-- `Lᵣ = ∑_{j=1}^r X^j/(1+X^j)`.-/
def L (r : ℕ) : PS :=
  ∑ j ∈ Finset.range r, X ^ (j + 1) * (1 + X ^ (j + 1))⁻¹

/-- The technical second-order sum used by the precise block expansion.-/
def M (r : ℕ) : PS :=
  ∑ j ∈ Finset.range r,
    X ^ (j + 1) * (1 + X ^ (j + 1))⁻¹ ^ 2

/-- `F_N = ∑_{r<N} X^(r+1) Aᵣ²`.-/
def F (N : ℕ) : PS :=
  ∑ r ∈ Finset.range N, X ^ (r + 1) * A r ^ 2

/-- `W_N = ∑_{r<N} X^(r+1) Aᵣ²(1-Lᵣ)`.-/
def W (N : ℕ) : PS :=
  ∑ r ∈ Finset.range N, X ^ (r + 1) * A r ^ 2 * (1 - L r)

/-- The factor `Aᵣ` with its `j`th factor removed.-/
def AExcept (r j : ℕ) : PS :=
  ∏ l ∈ (Finset.range r).erase j, (1 + X ^ (l + 1))

/-- A denominator-free form of `W_N`, useful for trusted finite computation.-/
def WPolynomial (N : ℕ) : PS :=
  ∑ r ∈ Finset.range N,
    (X ^ (r + 1) * A r ^ 2 -
      ∑ j ∈ Finset.range r,
        X ^ (r + 1) * X ^ (j + 1) * (1 + X ^ (j + 1)) * AExcept r j ^ 2)

/-- The correction series needed only for the strong `W` theorem.-/
def H (N : ℕ) : PS :=
  ∑ r ∈ Finset.range N,
    X ^ (r + 1) * A r ^ 2 * ((1 - L r) ^ 2 - M r)

/-- Congruence modulo `Y^n`, expressed by explicit divisibility.-/
def ModY (n : ℕ) (f g : PS) : Prop :=
  ∃ q, f - g = Y ^ n * q

/-- Divisibility by `Y^n`.-/
def Vanishes (n : ℕ) (f : PS) : Prop :=
  ∃ q, f = Y ^ n * q

/-- A coefficient-normalized exact order assertion.-/
def HasLeading (n : ℕ) (c : 𝔽₃) (f : PS) : Prop :=
  ModY (n + 1) f (PowerSeries.C c * Y ^ n)

@[simp] theorem constantCoeff_Y : constantCoeff Y = 0 := by simp [Y]

@[simp] theorem constantCoeff_X : constantCoeff X = 1 := by simp [X, Y]

@[simp] theorem constantCoeff_one_add_X_pow (j : ℕ) :
    constantCoeff (1 + X ^ j) = 2 := by
  simp [X, Y]
  norm_num

theorem one_add_X_pow_constant_ne_zero (j : ℕ) :
    constantCoeff (1 + X ^ j) ≠ 0 := by
  rw [constantCoeff_one_add_X_pow]
  decide

@[simp] theorem one_add_X_pow_mul_inv (j : ℕ) :
    (1 + X ^ j) * (1 + X ^ j)⁻¹ = 1 :=
  PowerSeries.mul_inv_cancel _ (one_add_X_pow_constant_ne_zero j)

@[simp] theorem inv_one_add_X_pow_mul (j : ℕ) :
    (1 + X ^ j)⁻¹ * (1 + X ^ j) = 1 :=
  PowerSeries.inv_mul_cancel _ (one_add_X_pow_constant_ne_zero j)

theorem X_pow_three_pow (a : ℕ) :
    X ^ (3 ^ a) = 1 - Y ^ (3 ^ a) := by
  rw [X, sub_pow_char_pow]
  simp

private theorem A_eq_factor_mul_except {r j : ℕ} (hj : j < r) :
    A r = (1 + X ^ (j + 1)) * AExcept r j := by
  rw [A, AExcept]
  exact (Finset.mul_prod_erase (Finset.range r)
    (fun l ↦ 1 + X ^ (l + 1)) (Finset.mem_range.mpr hj)).symm

private theorem cancel_square_divisor (a b c d : PS) (h : d * d⁻¹ = 1) :
    a * (d * b) ^ 2 * (c * d⁻¹) = a * c * d * b ^ 2 := by
  rw [pow_two]
  calc
    a * ((d * b) * (d * b)) * (c * d⁻¹) =
        (d * d⁻¹) * (a * c * d * (b * b)) := by ac_rfl
    _ = a * c * d * b ^ 2 := by rw [h, one_mul, pow_two]

private theorem weighted_A_sq_mul_L (r : ℕ) :
    X ^ (r + 1) * A r ^ 2 * L r =
      ∑ j ∈ Finset.range r,
        X ^ (r + 1) * X ^ (j + 1) * (1 + X ^ (j + 1)) * AExcept r j ^ 2 := by
  rw [L, mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [A_eq_factor_mul_except (Finset.mem_range.mp hj)]
  exact cancel_square_divisor _ _ _ _ (one_add_X_pow_mul_inv (j + 1))

/-- The displayed definition of `W_N` agrees exactly with its denominator-free
finite polynomial form.-/
theorem W_eq_WPolynomial (N : ℕ) : W N = WPolynomial N := by
  simp only [W, WPolynomial]
  apply Finset.sum_congr rfl
  intro r hr
  rw [mul_sub, mul_one, weighted_A_sq_mul_L]

namespace ModY

theorem refl (n : ℕ) (f : PS) : ModY n f f :=
  ⟨0, by simp⟩

theorem trans {n : ℕ} {f g h : PS} (hfg : ModY n f g) (hgh : ModY n g h) :
    ModY n f h := by
  obtain ⟨q, hq⟩ := hfg
  obtain ⟨r, hr⟩ := hgh
  refine ⟨q + r, ?_⟩
  rw [mul_add, ← hq, ← hr]
  ring

theorem add {n : ℕ} {f f' g g' : PS} (hf : ModY n f f') (hg : ModY n g g') :
    ModY n (f + g) (f' + g') := by
  obtain ⟨q, hq⟩ := hf
  obtain ⟨r, hr⟩ := hg
  refine ⟨q + r, ?_⟩
  rw [mul_add, ← hq, ← hr]
  ring

theorem neg {n : ℕ} {f g : PS} (h : ModY n f g) : ModY n (-f) (-g) := by
  obtain ⟨q, hq⟩ := h
  refine ⟨-q, ?_⟩
  rw [mul_neg, ← hq]
  ring

theorem sub {n : ℕ} {f f' g g' : PS} (hf : ModY n f f') (hg : ModY n g g') :
    ModY n (f - g) (f' - g') :=
  by simpa [sub_eq_add_neg] using add hf (neg hg)

theorem mul {n : ℕ} {f f' g g' : PS} (hf : ModY n f f') (hg : ModY n g g') :
    ModY n (f * g) (f' * g') := by
  obtain ⟨q, hq⟩ := hf
  obtain ⟨r, hr⟩ := hg
  refine ⟨q * g + f' * r, ?_⟩
  calc
    f * g - f' * g' = (f - f') * g + f' * (g - g') := by ring
    _ = (Y ^ n * q) * g + f' * (Y ^ n * r) := by rw [hq, hr]
    _ = Y ^ n * (q * g + f' * r) := by ring

theorem mul_left (a : PS) {n : ℕ} {f g : PS} (h : ModY n f g) :
    ModY n (a * f) (a * g) :=
  mul (refl n a) h

theorem mul_right (a : PS) {n : ℕ} {f g : PS} (h : ModY n f g) :
    ModY n (f * a) (g * a) :=
  mul h (refl n a)

theorem pow {n : ℕ} {f g : PS} (h : ModY n f g) : ∀ e : ℕ,
    ModY n (f ^ e) (g ^ e)
  | 0 => by simpa using refl n (1 : PS)
  | e + 1 => by
      simpa [pow_succ] using mul (pow h e) h

theorem mono {m n : ℕ} (hmn : m ≤ n) {f g : PS} (h : ModY n f g) : ModY m f g := by
  obtain ⟨q, hq⟩ := h
  refine ⟨Y ^ (n - m) * q, ?_⟩
  rw [← mul_assoc, ← pow_add, Nat.add_sub_of_le hmn, hq]

end ModY

namespace Vanishes

theorem one_zero (f : PS) : Vanishes 0 f := ⟨f, by simp⟩

theorem mono {m n : ℕ} (hmn : m ≤ n) {f : PS} (h : Vanishes n f) : Vanishes m f := by
  obtain ⟨q, hq⟩ := h
  refine ⟨Y ^ (n - m) * q, ?_⟩
  rw [← mul_assoc, ← pow_add, Nat.add_sub_of_le hmn, hq]

theorem add {n : ℕ} {f g : PS} (hf : Vanishes n f) (hg : Vanishes n g) :
    Vanishes n (f + g) := by
  obtain ⟨q, rfl⟩ := hf
  obtain ⟨r, rfl⟩ := hg
  exact ⟨q + r, by rw [mul_add]⟩

theorem neg {n : ℕ} {f : PS} (hf : Vanishes n f) : Vanishes n (-f) := by
  obtain ⟨q, rfl⟩ := hf
  exact ⟨-q, by rw [mul_neg]⟩

theorem sub {n : ℕ} {f g : PS} (hf : Vanishes n f) (hg : Vanishes n g) :
    Vanishes n (f - g) := by simpa [sub_eq_add_neg] using add hf (neg hg)

theorem mul {m n : ℕ} {f g : PS} (hf : Vanishes m f) (hg : Vanishes n g) :
    Vanishes (m + n) (f * g) := by
  obtain ⟨q, rfl⟩ := hf
  obtain ⟨r, rfl⟩ := hg
  refine ⟨q * r, ?_⟩
  rw [pow_add]
  ring

theorem mul_left (a : PS) {n : ℕ} {f : PS} (hf : Vanishes n f) :
    Vanishes n (a * f) := by
  simpa [zero_add] using mul (one_zero a) hf

theorem mul_right (a : PS) {n : ℕ} {f : PS} (hf : Vanishes n f) :
    Vanishes n (f * a) := by
  simpa [add_zero] using mul hf (one_zero a)

theorem of_modY_zero {n : ℕ} {f : PS} (h : ModY n f 0) : Vanishes n f := by
  obtain ⟨q, hq⟩ := h
  exact ⟨q, by simpa using hq⟩

theorem modY_zero {n : ℕ} {f : PS} (h : Vanishes n f) : ModY n f 0 := by
  obtain ⟨q, hq⟩ := h
  exact ⟨q, by simpa using hq⟩

end Vanishes

end IwasawaTower.Series
