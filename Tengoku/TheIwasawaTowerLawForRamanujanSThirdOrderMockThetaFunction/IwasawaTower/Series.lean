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

/--
@isnad1 id=eq.0h0v.s6.e8d0a8927526 from=translated src=- shape=8b3e5d3e vocab=008ae7ac
-/
@[simp] theorem constantCoeff_Y : constantCoeff Y = 0 := by simp [Y]

/--
@isnad1 id=eq.0h0v.s6.7db921009cfd from=translated src=- shape=8b3e5d3e vocab=8f46520d
-/
@[simp] theorem constantCoeff_X : constantCoeff X = 1 := by simp [X, Y]

/--
@isnad1 id=eq.0h1v.s7.7fdaf76a9f2c from=translated src=- shape=aa6fc749 vocab=1595c8c9
-/
@[simp] theorem constantCoeff_one_add_X_pow (j : ℕ) :
    constantCoeff (1 + X ^ j) = 2 := by
  simp [X, Y]
  norm_num

/--
@isnad1 id=ne.0h1v.s7.ae272c790ba8 from=translated src=- shape=aa6fc749 vocab=1595c8c9
-/
theorem one_add_X_pow_constant_ne_zero (j : ℕ) :
    constantCoeff (1 + X ^ j) ≠ 0 := by
  rw [constantCoeff_one_add_X_pow]
  decide

/--
@isnad1 id=eq.0h1v.s7.a30d34f60d12 from=translated src=- shape=30be1cf5 vocab=de3b0585
-/
@[simp] theorem one_add_X_pow_mul_inv (j : ℕ) :
    (1 + X ^ j) * (1 + X ^ j)⁻¹ = 1 :=
  PowerSeries.mul_inv_cancel _ (one_add_X_pow_constant_ne_zero j)

/--
@isnad1 id=eq.0h1v.s7.38154644b89d from=translated src=- shape=9cd8f0f9 vocab=de3b0585
-/
@[simp] theorem inv_one_add_X_pow_mul (j : ℕ) :
    (1 + X ^ j)⁻¹ * (1 + X ^ j) = 1 :=
  PowerSeries.inv_mul_cancel _ (one_add_X_pow_constant_ne_zero j)

/--
@isnad1 id=eq.0h1v.s7.cb853d84e57f from=translated src=- shape=ac7f4b22 vocab=fbc6bb5f
-/
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
finite polynomial form.
@isnad1 id=eq.0h1v.s3.b8933e70e0b2 from=translated src=- shape=b70c6bb1 vocab=fc22dbe2
-/
theorem W_eq_WPolynomial (N : ℕ) : W N = WPolynomial N := by
  simp only [W, WPolynomial]
  apply Finset.sum_congr rfl
  intro r hr
  rw [mul_sub, mul_one, weighted_A_sq_mul_L]

namespace ModY

/--
@isnad1 id=mody.0h2v.s3.167cdb6dd4a0 from=translated src=- shape=3105397a vocab=eb476a4c
-/
theorem refl (n : ℕ) (f : PS) : ModY n f f :=
  ⟨0, by simp⟩

/--
@isnad1 id=mody.2h4v.s4.94f4b5ee78e1 from=translated src=- shape=31ac16df vocab=eb476a4c
-/
theorem trans {n : ℕ} {f g h : PS} (hfg : ModY n f g) (hgh : ModY n g h) :
    ModY n f h := by
  obtain ⟨q, hq⟩ := hfg
  obtain ⟨r, hr⟩ := hgh
  refine ⟨q + r, ?_⟩
  rw [mul_add, ← hq, ← hr]
  ring

/--
@isnad1 id=mody.2h5v.s6.4dbd7a20f9b3 from=translated src=- shape=745f8771 vocab=b74fd430
-/
theorem add {n : ℕ} {f f' g g' : PS} (hf : ModY n f f') (hg : ModY n g g') :
    ModY n (f + g) (f' + g') := by
  obtain ⟨q, hq⟩ := hf
  obtain ⟨r, hr⟩ := hg
  refine ⟨q + r, ?_⟩
  rw [mul_add, ← hq, ← hr]
  ring

/--
@isnad1 id=mody.1h3v.s6.3bacf9a1b85b from=translated src=- shape=35f2b1d7 vocab=96550b9b
-/
theorem neg {n : ℕ} {f g : PS} (h : ModY n f g) : ModY n (-f) (-g) := by
  obtain ⟨q, hq⟩ := h
  refine ⟨-q, ?_⟩
  rw [mul_neg, ← hq]
  ring

/--
@isnad1 id=mody.2h5v.s6.bbc566d81608 from=translated src=- shape=745f8771 vocab=aad99c00
-/
theorem sub {n : ℕ} {f f' g g' : PS} (hf : ModY n f f') (hg : ModY n g g') :
    ModY n (f - g) (f' - g') :=
  by simpa [sub_eq_add_neg] using add hf (neg hg)

/--
@isnad1 id=mody.2h5v.s6.f7e8daa12e24 from=translated src=- shape=745f8771 vocab=e80ef37e
-/
theorem mul {n : ℕ} {f f' g g' : PS} (hf : ModY n f f') (hg : ModY n g g') :
    ModY n (f * g) (f' * g') := by
  obtain ⟨q, hq⟩ := hf
  obtain ⟨r, hr⟩ := hg
  refine ⟨q * g + f' * r, ?_⟩
  calc
    f * g - f' * g' = (f - f') * g + f' * (g - g') := by ring
    _ = (Y ^ n * q) * g + f' * (Y ^ n * r) := by rw [hq, hr]
    _ = Y ^ n * (q * g + f' * r) := by ring

/--
@isnad1 id=mody.1h4v.s5.a433c3ca2603 from=translated src=- shape=f2925527 vocab=e80ef37e
-/
theorem mul_left (a : PS) {n : ℕ} {f g : PS} (h : ModY n f g) :
    ModY n (a * f) (a * g) :=
  mul (refl n a) h

/--
@isnad1 id=mody.1h4v.s5.05a3ae56738c from=translated src=- shape=4f09ca54 vocab=e80ef37e
-/
theorem mul_right (a : PS) {n : ℕ} {f g : PS} (h : ModY n f g) :
    ModY n (f * a) (g * a) :=
  mul h (refl n a)

/--
@isnad1 id=mody.1h4v.s6.6aeff4d1c25a from=translated src=- shape=338157e2 vocab=edbc2ead
-/
theorem pow {n : ℕ} {f g : PS} (h : ModY n f g) : ∀ e : ℕ,
    ModY n (f ^ e) (g ^ e)
  | 0 => by simpa using refl n (1 : PS)
  | e + 1 => by
      simpa [pow_succ] using mul (pow h e) h

/--
@isnad1 id=mody.2h4v.s4.a4f787dd2477 from=translated src=- shape=16feddf5 vocab=f738b2f0
-/
theorem mono {m n : ℕ} (hmn : m ≤ n) {f g : PS} (h : ModY n f g) : ModY m f g := by
  obtain ⟨q, hq⟩ := h
  refine ⟨Y ^ (n - m) * q, ?_⟩
  rw [← mul_assoc, ← pow_add, Nat.add_sub_of_le hmn, hq]

end ModY

namespace Vanishes

/--
@isnad1 id=vanishes.0h1v.s3.6e8a5bb9bd83 from=translated src=- shape=c455abe0 vocab=bb6bf0ec
-/
theorem one_zero (f : PS) : Vanishes 0 f := ⟨f, by simp⟩

/--
@isnad1 id=vanishes.2h3v.s4.e7f63495fd68 from=translated src=- shape=6ebc4754 vocab=1af8feef
-/
theorem mono {m n : ℕ} (hmn : m ≤ n) {f : PS} (h : Vanishes n f) : Vanishes m f := by
  obtain ⟨q, hq⟩ := h
  refine ⟨Y ^ (n - m) * q, ?_⟩
  rw [← mul_assoc, ← pow_add, Nat.add_sub_of_le hmn, hq]

/--
@isnad1 id=vanishes.2h3v.s5.4f68ce84bfc5 from=translated src=- shape=d203bb48 vocab=86101176
-/
theorem add {n : ℕ} {f g : PS} (hf : Vanishes n f) (hg : Vanishes n g) :
    Vanishes n (f + g) := by
  obtain ⟨q, rfl⟩ := hf
  obtain ⟨r, rfl⟩ := hg
  exact ⟨q + r, by rw [mul_add]⟩

/--
@isnad1 id=vanishes.1h2v.s5.71b41b7e528a from=translated src=- shape=d086edac vocab=0965fb70
-/
theorem neg {n : ℕ} {f : PS} (hf : Vanishes n f) : Vanishes n (-f) := by
  obtain ⟨q, rfl⟩ := hf
  exact ⟨-q, by rw [mul_neg]⟩

/--
@isnad1 id=vanishes.2h3v.s5.d1e0cb1165bc from=translated src=- shape=d203bb48 vocab=6493dac9
-/
theorem sub {n : ℕ} {f g : PS} (hf : Vanishes n f) (hg : Vanishes n g) :
    Vanishes n (f - g) := by simpa [sub_eq_add_neg] using add hf (neg hg)

/--
@isnad1 id=vanishes.2h4v.s5.8bcad4d39243 from=translated src=- shape=fe1f177a vocab=f9de1c29
-/
theorem mul {m n : ℕ} {f g : PS} (hf : Vanishes m f) (hg : Vanishes n g) :
    Vanishes (m + n) (f * g) := by
  obtain ⟨q, rfl⟩ := hf
  obtain ⟨r, rfl⟩ := hg
  refine ⟨q * r, ?_⟩
  rw [pow_add]
  ring

/--
@isnad1 id=vanishes.1h3v.s5.f24cf079298a from=translated src=- shape=37bea723 vocab=02b85c42
-/
theorem mul_left (a : PS) {n : ℕ} {f : PS} (hf : Vanishes n f) :
    Vanishes n (a * f) := by
  simpa [zero_add] using mul (one_zero a) hf

/--
@isnad1 id=vanishes.1h3v.s5.4780189fca54 from=translated src=- shape=ee0db43f vocab=02b85c42
-/
theorem mul_right (a : PS) {n : ℕ} {f : PS} (hf : Vanishes n f) :
    Vanishes n (f * a) := by
  simpa [add_zero] using mul hf (one_zero a)

/--
@isnad1 id=vanishes.1h2v.s5.fe9544764b9d from=translated src=- shape=352cb6cd vocab=0ef25100
-/
theorem of_modY_zero {n : ℕ} {f : PS} (h : ModY n f 0) : Vanishes n f := by
  obtain ⟨q, hq⟩ := h
  exact ⟨q, by simpa using hq⟩

/--
@isnad1 id=mody.1h2v.s5.5694c8a907cc from=translated src=- shape=01ec75a8 vocab=0ef25100
-/
theorem modY_zero {n : ℕ} {f : PS} (h : Vanishes n f) : ModY n f 0 := by
  obtain ⟨q, hq⟩ := h
  exact ⟨q, by simpa using hq⟩

end Vanishes

end IwasawaTower.Series
