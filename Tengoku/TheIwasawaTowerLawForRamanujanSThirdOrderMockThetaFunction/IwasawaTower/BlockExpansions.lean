import Tengoku.TheIwasawaTowerLawForRamanujanSThirdOrderMockThetaFunction.IwasawaTower.Series

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Three-block expansions in characteristic three

Author: Joesph D. Burke III.
-/

noncomputable section

open scoped BigOperators

namespace IwasawaTower.Series

open Finset PowerSeries

namespace ModY

theorem sum {ι : Type*} {n : ℕ} (s : Finset ι) {f g : ι → PS}
    (h : ∀ i ∈ s, ModY n (f i) (g i)) :
    ModY n (∑ i ∈ s, f i) (∑ i ∈ s, g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using ModY.refl n 0
  | @insert i s hi ih =>
      simpa [hi] using ModY.add (h i (by simp))
        (ih fun j hj ↦ h j (by simp [hj]))

end ModY

/-- `δ_N = X^N - 1 = -Y^N` at the powers of three used below.-/
def delta (N : ℕ) : PS := -Y ^ N

/-- The part of `A_(s+b)` after its first `s` factors.-/
def Tail (s b : ℕ) : PS :=
  ∏ j ∈ Finset.range b, (1 + X ^ (s + j + 1))

/-- The second elementary symmetric sum in the logarithmic factors.-/
def E (r : ℕ) : PS :=
  ∑ j ∈ Finset.range r,
    (X ^ (j + 1) * (1 + X ^ (j + 1))⁻¹) * L j

@[simp] theorem delta_vanishes (N : ℕ) : Vanishes N (delta N) :=
  ⟨-1, by simp [delta]⟩

theorem X_pow_eq_one_add_delta_of_power {N : ℕ} (hN : ∃ a, N = 3 ^ a) :
    X ^ N = 1 + delta N := by
  obtain ⟨a, rfl⟩ := hN
  rw [X_pow_three_pow]
  simp [delta]
  ring

private theorem factor_mul_log_term (j : ℕ) :
    (1 + X ^ (j + 1)) *
        (X ^ (j + 1) * (1 + X ^ (j + 1))⁻¹) = X ^ (j + 1) := by
  calc
    (1 + X ^ (j + 1)) *
        (X ^ (j + 1) * (1 + X ^ (j + 1))⁻¹) =
      X ^ (j + 1) *
        ((1 + X ^ (j + 1)) * (1 + X ^ (j + 1))⁻¹) := by ac_rfl
    _ = X ^ (j + 1) := by rw [one_add_X_pow_mul_inv, mul_one]

private theorem shifted_factor {s : ℕ} {e : PS} (hs : X ^ s = 1 + e) (j : ℕ) :
    1 + X ^ (s + j + 1) =
      (1 + X ^ (j + 1)) *
        (1 + e * (X ^ (j + 1) * (1 + X ^ (j + 1))⁻¹)) := by
  rw [show s + j + 1 = s + (j + 1) by omega, pow_add, hs]
  have hf := factor_mul_log_term j
  calc
    1 + (1 + e) * X ^ (j + 1) =
        (1 + X ^ (j + 1)) + e * X ^ (j + 1) := by ring
    _ = (1 + X ^ (j + 1)) +
        e * ((1 + X ^ (j + 1)) *
          (X ^ (j + 1) * (1 + X ^ (j + 1))⁻¹)) := by rw [hf]
    _ = (1 + X ^ (j + 1)) *
        (1 + e * (X ^ (j + 1) * (1 + X ^ (j + 1))⁻¹)) := by ring

private theorem product_one_add_mod {N b : ℕ} {e : PS} (he : Vanishes N e) :
    ModY (2 * N)
      (∏ j ∈ Finset.range b,
        (1 + e * (X ^ (j + 1) * (1 + X ^ (j + 1))⁻¹)))
      (1 + e * L b) := by
  induction b with
  | zero => simp [L, ModY.refl]
  | succ b ih =>
      let q := X ^ (b + 1) * (1 + X ^ (b + 1))⁻¹
      have hmul : ModY (2 * N)
          ((∏ j ∈ Finset.range b,
              (1 + e * (X ^ (j + 1) * (1 + X ^ (j + 1))⁻¹))) * (1 + e * q))
          ((1 + e * L b) * (1 + e * q)) :=
        ModY.mul_right (1 + e * q) ih
      have hee : Vanishes (2 * N) (e * e) := by
        simpa [two_mul] using Vanishes.mul he he
      have hdrop : ModY (2 * N)
          ((1 + e * L b) * (1 + e * q))
          (1 + e * (L b + q)) := by
        obtain ⟨u, hu⟩ := Vanishes.mul_right (L b * q) hee
        refine ⟨u, ?_⟩
        calc
          (1 + e * L b) * (1 + e * q) - (1 + e * (L b + q)) =
              (e * e) * (L b * q) := by ring
          _ = Y ^ (2 * N) * u := hu
      simpa [Finset.prod_range_succ, L, Finset.sum_range_succ, q,
        Nat.add_assoc] using ModY.trans hmul hdrop

private theorem product_one_add_second_order {N b : ℕ} {e : PS}
    (he : Vanishes N e) :
    ModY (3 * N)
      (∏ j ∈ Finset.range b,
        (1 + e * (X ^ (j + 1) * (1 + X ^ (j + 1))⁻¹)))
      (1 + e * L b + e ^ 2 * E b) := by
  induction b with
  | zero => simp [L, E, ModY.refl]
  | succ b ih =>
      let q := X ^ (b + 1) * (1 + X ^ (b + 1))⁻¹
      have hmul := ModY.mul_right (1 + e * q) ih
      have he3 : Vanishes (3 * N) (e ^ 3) := by
        obtain ⟨u, hu⟩ := he
        refine ⟨u ^ 3, ?_⟩
        rw [hu, mul_pow, ← pow_mul]
        congr 2
        omega
      have hdrop : ModY (3 * N)
          ((1 + e * L b + e ^ 2 * E b) * (1 + e * q))
          (1 + e * (L b + q) + e ^ 2 * (E b + q * L b)) := by
        obtain ⟨u, hu⟩ := Vanishes.mul_right (E b * q) he3
        refine ⟨u, ?_⟩
        calc
          (1 + e * L b + e ^ 2 * E b) * (1 + e * q) -
              (1 + e * (L b + q) + e ^ 2 * (E b + q * L b)) =
              e ^ 3 * (E b * q) := by ring
          _ = Y ^ (3 * N) * u := hu
      simpa [Finset.prod_range_succ, L, E, Finset.sum_range_succ, q,
        mul_comm q] using ModY.trans hmul hdrop

/-- First-order expansion of a shifted tail, modulo `Y^(2N)`.-/
theorem tail_first_order {N s b : ℕ} {e : PS} (he : Vanishes N e)
    (hs : X ^ s = 1 + e) :
    ModY (2 * N) (Tail s b) (A b * (1 + e * L b)) := by
  have hp := product_one_add_mod (b := b) he
  have hexact : Tail s b =
      A b * ∏ j ∈ Finset.range b,
        (1 + e * (X ^ (j + 1) * (1 + X ^ (j + 1))⁻¹)) := by
    rw [Tail, A]
    simp_rw [shifted_factor hs]
    rw [Finset.prod_mul_distrib]
  rw [hexact]
  exact ModY.mul_left (A b) hp

/-- Second-order expansion of a shifted tail, modulo `Y^(3N)`.-/
theorem tail_second_order {N s b : ℕ} {e : PS} (he : Vanishes N e)
    (hs : X ^ s = 1 + e) :
    ModY (3 * N) (Tail s b) (A b * (1 + e * L b + e ^ 2 * E b)) := by
  have hp := product_one_add_second_order (b := b) he
  have hexact : Tail s b =
      A b * ∏ j ∈ Finset.range b,
        (1 + e * (X ^ (j + 1) * (1 + X ^ (j + 1))⁻¹)) := by
    rw [Tail, A]
    simp_rw [shifted_factor hs]
    rw [Finset.prod_mul_distrib]
  rw [hexact]
  exact ModY.mul_left (A b) hp

private theorem log_term_square (j : ℕ) :
    (X ^ (j + 1) * (1 + X ^ (j + 1))⁻¹) ^ 2 =
      X ^ (j + 1) * (1 + X ^ (j + 1))⁻¹ -
        X ^ (j + 1) * (1 + X ^ (j + 1))⁻¹ ^ 2 := by
  let z := X ^ (j + 1)
  let d := 1 + z
  have hd : d * d⁻¹ = 1 := by
    simpa [d, z] using one_add_X_pow_mul_inv (j + 1)
  have hz : z ^ 2 = z * d - z := by
    simp [d]
    ring
  change (z * d⁻¹) ^ 2 = z * d⁻¹ - z * d⁻¹ ^ 2
  calc
    (z * d⁻¹) ^ 2 = z ^ 2 * d⁻¹ ^ 2 := by ring
    _ = (z * d - z) * d⁻¹ ^ 2 := by rw [hz]
    _ = z * d⁻¹ - z * d⁻¹ ^ 2 := by
      rw [pow_two]
      calc
        (z * d - z) * (d⁻¹ * d⁻¹) =
            z * d⁻¹ * (d * d⁻¹) - z * (d⁻¹ * d⁻¹) := by ring
        _ = z * d⁻¹ - z * (d⁻¹ * d⁻¹) := by rw [hd, mul_one]

/-- In characteristic three the second elementary symmetric sum has this
form in terms of `L` and `M`.-/
theorem E_eq (r : ℕ) : E r = -L r ^ 2 + L r - M r := by
  induction r with
  | zero => simp [E, L, M]
  | succ r ih =>
      let q := X ^ (r + 1) * (1 + X ^ (r + 1))⁻¹
      let m := X ^ (r + 1) * (1 + X ^ (r + 1))⁻¹ ^ 2
      have hq : q ^ 2 = q - m := by
        simpa [q, m] using log_term_square r
      have hthree : (3 : PS) = 0 := CharP.cast_eq_zero (R := PS) 3
      have hE : E (r + 1) = E r + q * L r := by
        simp [E, q, Finset.sum_range_succ]
      have hL : L (r + 1) = L r + q := by
        simp [L, q, Finset.sum_range_succ]
      have hM : M (r + 1) = M r + m := by
        simp [M, m, Finset.sum_range_succ]
      rw [hE, hL, hM, ih]
      linear_combination hq + hthree * (L r * q)

/-- Exact splitting of `A_(s+b)` into its first block and shifted tail.-/
theorem A_add (s b : ℕ) : A (s + b) = A s * Tail s b := by
  rw [A, Tail, Finset.prod_range_add]
  congr 1

/-- First-order formula for `A_(N+b)` at a power-of-three block size.-/
theorem A_one_block {N b : ℕ} (hN : ∃ a, N = 3 ^ a) :
    ModY (2 * N) (A (N + b))
      (A N * A b * (1 + delta N * L b)) := by
  rw [A_add]
  have ht := tail_first_order (b := b) (delta_vanishes N)
    (X_pow_eq_one_add_delta_of_power hN)
  simpa [mul_assoc] using ModY.mul_left (A N) ht

private theorem X_two_mul_pow {N : ℕ} (hN : ∃ a, N = 3 ^ a) :
    X ^ (2 * N) = (1 + delta N) ^ 2 := by
  rw [show 2 * N = N + N by omega, pow_add,
    X_pow_eq_one_add_delta_of_power hN]
  simp [pow_two]

private theorem two_block_error_vanishes {N : ℕ} (hN : ∃ a, N = 3 ^ a) :
    Vanishes N (X ^ (2 * N) - 1) := by
  refine ⟨-(2 : PS) + Y ^ N, ?_⟩
  rw [X_two_mul_pow hN, delta]
  ring

private theorem two_block_error_mod {N : ℕ} (hN : ∃ a, N = 3 ^ a) :
    ModY (2 * N) (X ^ (2 * N) - 1) (-delta N) := by
  have hthree : (3 : PS) = 0 := CharP.cast_eq_zero (R := PS) 3
  refine ⟨1, ?_⟩
  have hpow : Y ^ (2 * N) = (Y ^ N) ^ 2 := by
    rw [pow_two, ← pow_add]
    congr 1
    omega
  rw [X_two_mul_pow hN, delta, hpow]
  calc
    (1 + -Y ^ N) ^ 2 - 1 - - -Y ^ N =
        (Y ^ N) ^ 2 - 3 * Y ^ N := by ring
    _ = (Y ^ N) ^ 2 := by rw [hthree, zero_mul, sub_zero]
    _ = (Y ^ N) ^ 2 * 1 := by ring

private theorem two_block_error_exact {N : ℕ} (hN : ∃ a, N = 3 ^ a) :
    X ^ (2 * N) - 1 = -delta N + delta N ^ 2 := by
  have hthree : (3 : PS) = 0 := CharP.cast_eq_zero (R := PS) 3
  rw [X_two_mul_pow hN]
  linear_combination hthree * delta N

private theorem Y_pow_three_mul (N : ℕ) : Y ^ (3 * N) = (Y ^ N) ^ 3 := by
  rw [← pow_mul]
  congr 1
  omega

private theorem tail_two_blocks_second_order {N : ℕ} (hN : ∃ a, N = 3 ^ a) :
    ModY (3 * N) (Tail (2 * N) N)
      (A N * (1 - delta N * L N + delta N ^ 2 * (L N + E N))) := by
  let e := X ^ (2 * N) - 1
  have ht := tail_second_order (b := N) (two_block_error_vanishes hN)
    (show X ^ (2 * N) = 1 + e by simp [e])
  have hfactor : ModY (3 * N)
      (1 + e * L N + e ^ 2 * E N)
      (1 - delta N * L N + delta N ^ 2 * (L N + E N)) := by
    refine ⟨(2 + Y ^ N) * E N, ?_⟩
    rw [show e = X ^ (2 * N) - 1 by rfl, two_block_error_exact hN,
      delta, Y_pow_three_mul]
    ring
  exact ModY.trans ht (ModY.mul (ModY.refl (3 * N) (A N)) hfactor)

/-- Precise regrouping of `A_(3N)` through second order.-/
theorem A_three_block_precise {N : ℕ} (hN : ∃ a, N = 3 ^ a) :
    ModY (3 * N) (A (3 * N))
      (A N ^ 3 * (1 + delta N ^ 2 * M N)) := by
  have ht1 := tail_second_order (b := N) (delta_vanishes N)
    (X_pow_eq_one_add_delta_of_power hN)
  have ha2 : ModY (3 * N) (A (2 * N))
      (A N ^ 2 * (1 + delta N * L N + delta N ^ 2 * E N)) := by
    rw [show 2 * N = N + N by omega, A_add]
    convert ModY.mul_left (A N) ht1 using 1 <;> ring
  have ht2 := tail_two_blocks_second_order hN
  have hsplit : A (3 * N) = A (2 * N) * Tail (2 * N) N := by
    rw [show 3 * N = 2 * N + N by omega, A_add]
  rw [hsplit]
  have hmul := ModY.mul ha2 ht2
  have halg : ModY (3 * N)
      ((1 + delta N * L N + delta N ^ 2 * E N) *
        (1 - delta N * L N + delta N ^ 2 * (L N + E N)))
      (1 + delta N ^ 2 * M N) := by
    refine ⟨-(L N) ^ 2 + Y ^ N * E N * (L N + E N), ?_⟩
    have hthree : (3 : PS) = 0 := CharP.cast_eq_zero (R := PS) 3
    rw [delta, Y_pow_three_mul, E_eq]
    linear_combination hthree * (Y ^ N) ^ 2 *
      (-L N ^ 2 + L N - M N)
  have hscaled := ModY.mul_left (A N ^ 3) halg
  exact ModY.trans (by convert hmul using 1 <;> ring) hscaled

theorem constantCoeff_M (N : ℕ) : constantCoeff (M N) = (N : 𝔽₃) := by
  have hinv : (2 : 𝔽₃)⁻¹ = 2 :=
    ZMod.inv_eq_of_mul_eq_one 3 2 2 (by decide)
  have hsq : (2 : 𝔽₃) ^ 2 = 1 := by decide
  rw [M, map_sum]
  simp [hinv, hsq]

theorem M_vanishes_one_of_three_dvd {N : ℕ} (hN : 3 ∣ N) : Vanishes 1 (M N) := by
  have hc : constantCoeff (M N) = 0 := by
    rw [constantCoeff_M]
    exact (CharP.cast_eq_zero_iff 𝔽₃ 3 N).2 hN
  obtain ⟨q, hq⟩ := PowerSeries.X_dvd_iff.mpr hc
  exact ⟨q, by simpa [Y] using hq⟩

/-- The precision actually needed to propagate the leading term of `A_N²-1`.-/
theorem A_three_block_cube {N : ℕ} (hpos : 0 < N) (hdiv : 3 ∣ N)
    (hN : ∃ a, N = 3 ^ a) :
    ModY (2 * N + 1) (A (3 * N)) (A N ^ 3) := by
  have hprec := ModY.mono (by omega : 2 * N + 1 ≤ 3 * N)
    (A_three_block_precise hN)
  have hd2 : Vanishes (2 * N) (delta N ^ 2) := by
    obtain ⟨u, hu⟩ := delta_vanishes N
    refine ⟨u ^ 2, ?_⟩
    rw [hu, mul_pow, ← pow_mul]
    congr 2
    omega
  have hcorr : Vanishes (2 * N + 1) (delta N ^ 2 * M N) := by
    simpa using Vanishes.mul hd2 (M_vanishes_one_of_three_dvd hdiv)
  have hdrop : ModY (2 * N + 1)
      (A N ^ 3 * (1 + delta N ^ 2 * M N)) (A N ^ 3) := by
    obtain ⟨u, hu⟩ := Vanishes.mul_left (A N ^ 3) hcorr
    exact ⟨u, by calc
      A N ^ 3 * (1 + delta N ^ 2 * M N) - A N ^ 3 =
          A N ^ 3 * (delta N ^ 2 * M N) := by ring
      _ = Y ^ (2 * N + 1) * u := hu⟩
  exact ModY.trans hprec hdrop

/-- First-order formula for a tail shifted by two blocks.-/
theorem tail_two_blocks {N b : ℕ} (hN : ∃ a, N = 3 ^ a) :
    ModY (2 * N) (Tail (2 * N) b) (A b * (1 - delta N * L b)) := by
  let e := X ^ (2 * N) - 1
  have he : Vanishes N e := two_block_error_vanishes hN
  have hs : X ^ (2 * N) = 1 + e := by simp [e]
  have ht := tail_first_order (b := b) he hs
  have hem : ModY (2 * N) e (-delta N) := two_block_error_mod hN
  have hone : ModY (2 * N) (1 + e * L b) (1 - delta N * L b) := by
    simpa [sub_eq_add_neg] using ModY.add (ModY.refl (2 * N) 1)
      (ModY.mul_right (L b) hem)
  exact ModY.trans ht (ModY.mul (ModY.refl (2 * N) (A b)) hone)

private theorem mul_linear_delta (N : ℕ) (u v : PS) :
    ModY (2 * N)
      ((1 + delta N * u) * (1 + delta N * v))
      (1 + delta N * (u + v)) := by
  refine ⟨u * v, ?_⟩
  rw [delta]
  have hpow : Y ^ (2 * N) = (Y ^ N) ^ 2 := by
    rw [pow_two, ← pow_add]
    congr 1
    omega
  rw [hpow]
  ring

private theorem delta_double_eq_neg (N : ℕ) (u : PS) :
    1 + delta N * (u + u) = 1 - delta N * u := by
  have hthree : (3 : PS) = 0 := CharP.cast_eq_zero (R := PS) 3
  linear_combination hthree * (delta N * u)

private theorem square_one_plus_delta (N : ℕ) (u : PS) :
    ModY (2 * N) ((1 + delta N * u) ^ 2) (1 - delta N * u) := by
  have h := mul_linear_delta N u u
  rw [pow_two]
  exact ModY.trans h (by rw [delta_double_eq_neg]; exact ModY.refl _ _)

private theorem one_plus_mul_one_minus_delta (N : ℕ) (u v : PS) :
    ModY (2 * N)
      ((1 + delta N * u) * (1 - delta N * v))
      (1 + delta N * (u - v)) := by
  simpa [sub_eq_add_neg] using mul_linear_delta N u (-v)

/-- First-order formula for `A_(2N+b)`.-/
theorem A_two_blocks {N b : ℕ} (hN : ∃ a, N = 3 ^ a) :
    ModY (2 * N) (A (2 * N + b))
      (A N ^ 2 * A b * (1 + delta N * (L N - L b))) := by
  have hfirst : ModY (2 * N) (A (2 * N))
      (A N * A N * (1 + delta N * L N)) := by
    simpa [two_mul] using A_one_block (b := N) hN
  have htail := tail_two_blocks (b := b) hN
  rw [A_add]
  have hmul := ModY.mul hfirst htail
  have hlin := one_plus_mul_one_minus_delta N (L N) (L b)
  have hscaled := ModY.mul_left (A N ^ 2 * A b) hlin
  have hreassoc : ModY (2 * N) (A (2 * N) * Tail (2 * N) b)
      (A N ^ 2 * A b *
        ((1 + delta N * L N) * (1 - delta N * L b))) := by
    convert hmul using 1 <;> ring
  exact ModY.trans hreassoc hscaled

private theorem weight_one_block {N b : ℕ} (hN : ∃ a, N = 3 ^ a) :
    X ^ (N + b + 1) = X ^ (b + 1) * (1 + delta N) := by
  rw [show N + b + 1 = N + (b + 1) by omega, pow_add,
    X_pow_eq_one_add_delta_of_power hN]
  ring

private theorem weight_two_blocks {N b : ℕ} (hN : ∃ a, N = 3 ^ a) :
    ModY (2 * N) (X ^ (2 * N + b + 1))
      (X ^ (b + 1) * (1 - delta N)) := by
  have he := two_block_error_mod hN
  have hx : ModY (2 * N) (X ^ (2 * N)) (1 - delta N) := by
    simpa [sub_eq_add_neg] using ModY.add (ModY.refl (2 * N) 1) he
  rw [show 2 * N + b + 1 = 2 * N + (b + 1) by omega, pow_add]
  simpa [mul_comm] using ModY.mul_left (X ^ (b + 1)) hx

/-- First-order expansion of a weighted `F` summand in the second block.-/
theorem F_summand_one_block {N b : ℕ} (hN : ∃ a, N = 3 ^ a) :
    ModY (2 * N)
      (X ^ (N + b + 1) * A (N + b) ^ 2)
      (A N ^ 2 * (X ^ (b + 1) * A b ^ 2) *
        (1 + delta N * (1 - L b))) := by
  have ha := A_one_block (b := b) hN
  have hasq := ModY.pow ha 2
  have hw : ModY (2 * N) (X ^ (N + b + 1))
      (X ^ (b + 1) * (1 + delta N)) := by
    rw [weight_one_block hN]
    exact ModY.refl _ _
  have hmul := ModY.mul hw hasq
  have hsquare := square_one_plus_delta N (L b)
  have hfactor := one_plus_mul_one_minus_delta N 1 (L b)
  let B := A N ^ 2 * (X ^ (b + 1) * A b ^ 2)
  have hscaledSquare := ModY.mul_left (B * (1 + delta N)) hsquare
  have hscaledFactor := ModY.mul_left B hfactor
  have hstart : ModY (2 * N)
      (X ^ (N + b + 1) * A (N + b) ^ 2)
      (B * ((1 + delta N) * (1 + delta N * L b) ^ 2)) := by
    convert hmul using 1 <;> simp only [B] <;> ring
  have hmiddle : ModY (2 * N)
      (B * ((1 + delta N) * (1 + delta N * L b) ^ 2))
      (B * ((1 + delta N) * (1 - delta N * L b))) := by
    convert hscaledSquare using 1 <;> ring
  have hend : ModY (2 * N)
      (B * ((1 + delta N) * (1 - delta N * L b)))
      (B * (1 + delta N * (1 - L b))) := by
    convert hscaledFactor using 1 <;> ring
  exact ModY.trans hstart (ModY.trans hmiddle hend)

/-- First-order expansion of a weighted `F` summand in the third block.-/
theorem F_summand_two_blocks {N b : ℕ} (hN : ∃ a, N = 3 ^ a) :
    ModY (2 * N)
      (X ^ (2 * N + b + 1) * A (2 * N + b) ^ 2)
      (A N ^ 4 * (X ^ (b + 1) * A b ^ 2) *
        (1 - delta N * (1 + L N - L b))) := by
  have ha := A_two_blocks (b := b) hN
  have hasq := ModY.pow ha 2
  have hw := weight_two_blocks (b := b) hN
  have hmul := ModY.mul hw hasq
  have hsquare := square_one_plus_delta N (L N - L b)
  have hfactor := mul_linear_delta N (-1) (-(L N - L b))
  let B := A N ^ 4 * (X ^ (b + 1) * A b ^ 2)
  have hscaledSquare := ModY.mul_left (B * (1 - delta N)) hsquare
  have hscaledFactor := ModY.mul_left B hfactor
  have hstart : ModY (2 * N)
      (X ^ (2 * N + b + 1) * A (2 * N + b) ^ 2)
      (B * ((1 - delta N) * (1 + delta N * (L N - L b)) ^ 2)) := by
    convert hmul using 1 <;> simp only [B] <;> ring
  have hmiddle : ModY (2 * N)
      (B * ((1 - delta N) * (1 + delta N * (L N - L b)) ^ 2))
      (B * ((1 - delta N) * (1 - delta N * (L N - L b)))) := by
    convert hscaledSquare using 1 <;> ring
  have hend : ModY (2 * N)
      (B * ((1 - delta N) * (1 - delta N * (L N - L b))))
      (B * (1 - delta N * (1 + L N - L b))) := by
    convert hscaledFactor using 1 <;> ring
  exact ModY.trans hstart (ModY.trans hmiddle hend)

private theorem F_three_split (N : ℕ) :
    F (3 * N) = F N +
      (∑ b ∈ Finset.range N, X ^ (N + b + 1) * A (N + b) ^ 2) +
      (∑ b ∈ Finset.range N, X ^ (2 * N + b + 1) * A (2 * N + b) ^ 2) := by
  simp only [F]
  rw [show 3 * N = N + (N + N) by omega, Finset.sum_range_add,
    Finset.sum_range_add]
  have hidx (b : ℕ) : N + (N + b) = 2 * N + b := by omega
  simp_rw [hidx]
  ring

private theorem sum_first_block_target (N : ℕ) :
    (∑ b ∈ Finset.range N,
      A N ^ 2 * (X ^ (b + 1) * A b ^ 2) *
        (1 + delta N * (1 - L b))) =
      A N ^ 2 * F N + delta N * A N ^ 2 * W N := by
  simp_rw [show ∀ b : ℕ,
      A N ^ 2 * (X ^ (b + 1) * A b ^ 2) *
          (1 + delta N * (1 - L b)) =
        A N ^ 2 * (X ^ (b + 1) * A b ^ 2) +
          (delta N * A N ^ 2) *
            (X ^ (b + 1) * A b ^ 2 * (1 - L b)) by
      intro b
      ring]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  rfl

private theorem sum_second_block_target (N : ℕ) :
    (∑ b ∈ Finset.range N,
      A N ^ 4 * (X ^ (b + 1) * A b ^ 2) *
        (1 - delta N * (1 + L N - L b))) =
      A N ^ 4 * F N - delta N * A N ^ 4 * (L N * F N + W N) := by
  simp_rw [show ∀ b : ℕ,
      A N ^ 4 * (X ^ (b + 1) * A b ^ 2) *
          (1 - delta N * (1 + L N - L b)) =
        A N ^ 4 * (X ^ (b + 1) * A b ^ 2) -
          (delta N * A N ^ 4) *
            (L N * (X ^ (b + 1) * A b ^ 2) +
              X ^ (b + 1) * A b ^ 2 * (1 - L b)) by
      intro b
      ring]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    Finset.sum_add_distrib, ← Finset.mul_sum]
  rfl

/-- The precise three-block identity for `F`, retaining all terms that can
contribute below `Y^(2N)`.  This is the characteristic-three engine of the
tower proof and does not assume any multiplicative recurrence.-/
theorem F_three_block_precise {N : ℕ} (hN : ∃ a, N = 3 ^ a) :
    ModY (2 * N) (F (3 * N))
      (F N * (1 + A N ^ 2 + A N ^ 4) +
        delta N *
          (A N ^ 2 * (1 - A N ^ 2) * W N -
            A N ^ 4 * L N * F N)) := by
  have hfirst : ModY (2 * N)
      (∑ b ∈ Finset.range N, X ^ (N + b + 1) * A (N + b) ^ 2)
      (∑ b ∈ Finset.range N,
        A N ^ 2 * (X ^ (b + 1) * A b ^ 2) *
          (1 + delta N * (1 - L b))) :=
    ModY.sum _ fun b hb ↦ F_summand_one_block hN
  have hsecond : ModY (2 * N)
      (∑ b ∈ Finset.range N, X ^ (2 * N + b + 1) * A (2 * N + b) ^ 2)
      (∑ b ∈ Finset.range N,
        A N ^ 4 * (X ^ (b + 1) * A b ^ 2) *
          (1 - delta N * (1 + L N - L b))) :=
    ModY.sum _ fun b hb ↦ F_summand_two_blocks hN
  rw [F_three_split]
  have hall := ModY.add (ModY.add (ModY.refl (2 * N) (F N)) hfirst) hsecond
  rw [sum_first_block_target, sum_second_block_target] at hall
  refine ModY.trans hall ?_
  exact ⟨0, by ring⟩

private def logTerm (j : ℕ) : PS :=
  X ^ (j + 1) * (1 + X ^ (j + 1))⁻¹

private def logSlope (j : ℕ) : PS :=
  X ^ (j + 1) * (1 + X ^ (j + 1))⁻¹ ^ 2

private def logCurve (j : ℕ) : PS :=
  (X ^ (j + 1)) ^ 2 * (1 + X ^ (j + 1))⁻¹ ^ 3

private theorem shifted_log_term_second_order_exact {s j : ℕ} {e : PS}
    (hs : X ^ s = 1 + e) :
    logTerm (s + j) -
        (logTerm j + e * logSlope j - e ^ 2 * logCurve j) =
      e ^ 3 *
        ((X ^ (j + 1)) ^ 3 *
          (1 + X ^ (s + j + 1))⁻¹ * (1 + X ^ (j + 1))⁻¹ ^ 3) := by
  let z := X ^ (j + 1)
  let d := 1 + z
  let d' := 1 + (1 + e) * z
  have hd : d * d⁻¹ = 1 := by
    simpa [d, z] using one_add_X_pow_mul_inv (j + 1)
  have hd' : d' * d'⁻¹ = 1 := by
    have hp : d' = 1 + X ^ (s + j + 1) := by
      rw [show s + j + 1 = s + (j + 1) by omega, pow_add, hs]
    rw [hp]
    exact one_add_X_pow_mul_inv (s + j + 1)
  have hfirst :
      (1 + e) * z * d'⁻¹ - z * d⁻¹ = e * z * d'⁻¹ * d⁻¹ := by
    calc
      (1 + e) * z * d'⁻¹ - z * d⁻¹ =
          ((1 + e) * z * d - z * d') * (d'⁻¹ * d⁻¹) := by
            calc
              (1 + e) * z * d'⁻¹ - z * d⁻¹ =
                  (1 + e) * z * d'⁻¹ * (d * d⁻¹) -
                    z * d⁻¹ * (d' * d'⁻¹) := by rw [hd, hd', mul_one, mul_one]
              _ = ((1 + e) * z * d - z * d') * (d'⁻¹ * d⁻¹) := by ring
      _ = e * z * d'⁻¹ * d⁻¹ := by simp [d', d]; ring
  have hinv₁ : d'⁻¹ * d⁻¹ - d⁻¹ ^ 2 =
      -e * z * d'⁻¹ * d⁻¹ ^ 2 := by
    calc
      d'⁻¹ * d⁻¹ - d⁻¹ ^ 2 =
          d'⁻¹ * d⁻¹ * (d * d⁻¹) - d⁻¹ ^ 2 * (d' * d'⁻¹) := by
            rw [hd, hd', mul_one, mul_one]
      _ = (d - d') * d'⁻¹ * d⁻¹ ^ 2 := by ring
      _ = -e * z * d'⁻¹ * d⁻¹ ^ 2 := by simp [d', d]; ring
  have hinv₂ : d⁻¹ - d'⁻¹ = e * z * d'⁻¹ * d⁻¹ := by
    calc
      d⁻¹ - d'⁻¹ = d⁻¹ * (d' * d'⁻¹) - d'⁻¹ * (d * d⁻¹) := by
        rw [hd, hd', mul_one, mul_one]
      _ = (d' - d) * d'⁻¹ * d⁻¹ := by ring
      _ = e * z * d'⁻¹ * d⁻¹ := by
        have hsub : d' - d = e * z := by simp only [d', d]; ring
        rw [hsub]
  have hsecond :
      e * z * d'⁻¹ * d⁻¹ - e * (z * d⁻¹ ^ 2) +
          e ^ 2 * (z ^ 2 * d⁻¹ ^ 3) =
        e ^ 3 * (z ^ 3 * d'⁻¹ * d⁻¹ ^ 3) := by
    calc
      e * z * d'⁻¹ * d⁻¹ - e * (z * d⁻¹ ^ 2) +
          e ^ 2 * (z ^ 2 * d⁻¹ ^ 3) =
        e * z * (d'⁻¹ * d⁻¹ - d⁻¹ ^ 2) +
          e ^ 2 * (z ^ 2 * d⁻¹ ^ 3) := by ring
      _ = e ^ 2 * z ^ 2 * d⁻¹ ^ 2 * (d⁻¹ - d'⁻¹) := by
        rw [hinv₁]
        ring
      _ = e ^ 3 * (z ^ 3 * d'⁻¹ * d⁻¹ ^ 3) := by rw [hinv₂]; ring
  have hmain : (1 + e) * z * d'⁻¹ -
      (z * d⁻¹ + e * (z * d⁻¹ ^ 2) - e ^ 2 * (z ^ 2 * d⁻¹ ^ 3)) =
      e ^ 3 * (z ^ 3 * d'⁻¹ * d⁻¹ ^ 3) := by
    rw [show (1 + e) * z * d'⁻¹ -
        (z * d⁻¹ + e * (z * d⁻¹ ^ 2) - e ^ 2 * (z ^ 2 * d⁻¹ ^ 3)) =
      ((1 + e) * z * d'⁻¹ - z * d⁻¹) - e * (z * d⁻¹ ^ 2) +
        e ^ 2 * (z ^ 2 * d⁻¹ ^ 3) by ring, hfirst]
    exact hsecond
  have hzshift : X ^ (s + j + 1) = (1 + e) * z := by
    rw [show s + j + 1 = s + (j + 1) by omega, pow_add, hs]
  simp only [logTerm, logSlope, logCurve]
  rw [hzshift]
  simpa only [z, d, d'] using hmain

private theorem shifted_log_term_second_order {N s j : ℕ} {e : PS}
    (he : Vanishes N e) (hs : X ^ s = 1 + e) :
    ModY (3 * N) (logTerm (s + j))
      (logTerm j + e * logSlope j - e ^ 2 * logCurve j) := by
  obtain ⟨u, hu⟩ := he
  refine ⟨u ^ 3 *
      ((X ^ (j + 1)) ^ 3 * (1 + X ^ (s + j + 1))⁻¹ *
        (1 + X ^ (j + 1))⁻¹ ^ 3), ?_⟩
  rw [shifted_log_term_second_order_exact hs, hu, mul_pow, ← pow_mul]
  rw [Nat.mul_comm N 3]
  ring

private theorem shifted_log_term_first_order {N s j : ℕ} {e : PS}
    (he : Vanishes N e) (hs : X ^ s = 1 + e) :
    ModY (2 * N) (logTerm (s + j)) (logTerm j + e * logSlope j) := by
  have hprec := ModY.mono (by omega : 2 * N ≤ 3 * N)
    (shifted_log_term_second_order (j := j) he hs)
  have he2 : Vanishes (2 * N) (e ^ 2) := by
    rw [pow_two]
    convert Vanishes.mul he he using 1 <;> omega
  have hdrop : ModY (2 * N)
      (logTerm j + e * logSlope j - e ^ 2 * logCurve j)
      (logTerm j + e * logSlope j) := by
    simpa using ModY.sub (ModY.refl (2 * N) (logTerm j + e * logSlope j))
      (Vanishes.modY_zero (Vanishes.mul_right (logCurve j) he2))
  exact ModY.trans hprec hdrop

private theorem logSlope_add_logCurve (j : ℕ) :
    logSlope j + logCurve j = logTerm j - logTerm j ^ 3 := by
  let z := X ^ (j + 1)
  let d := 1 + z
  have hd : d * d⁻¹ = 1 := by
    simpa [d, z] using one_add_X_pow_mul_inv (j + 1)
  have hone : 1 - z * d⁻¹ = d⁻¹ := by
    calc
      1 - z * d⁻¹ = d * d⁻¹ - z * d⁻¹ := by rw [hd]
      _ = d⁻¹ := by simp [d]; ring
  have hlocal : z * d⁻¹ ^ 2 + z ^ 2 * d⁻¹ ^ 3 =
      z * d⁻¹ - (z * d⁻¹) ^ 3 := by
    symm
    calc
      z * d⁻¹ - (z * d⁻¹) ^ 3 =
          (z * d⁻¹) * (1 - z * d⁻¹) * (1 + z * d⁻¹) := by ring
      _ = z * d⁻¹ ^ 2 + z ^ 2 * d⁻¹ ^ 3 := by rw [hone]; ring
  simpa only [logTerm, logSlope, logCurve, z, d] using hlocal

private theorem log_term_three_blocks {N j : ℕ} (hN : ∃ a, N = 3 ^ a) :
    ModY (3 * N)
      (logTerm j + logTerm (N + j) + logTerm (2 * N + j))
      (delta N ^ 2 * (logTerm j - logTerm j ^ 3)) := by
  let e := X ^ (2 * N) - 1
  have h₁ := shifted_log_term_second_order (j := j) (delta_vanishes N)
    (X_pow_eq_one_add_delta_of_power hN)
  have h₂ := shifted_log_term_second_order (j := j)
    (two_block_error_vanishes hN)
    (show X ^ (2 * N) = 1 + e by simp [e])
  have hall := ModY.add (ModY.add (ModY.refl (3 * N) (logTerm j)) h₁) h₂
  refine ModY.trans hall ?_
  refine ⟨-(2 + Y ^ N) * logCurve j, ?_⟩
  have hthree : (3 : PS) = 0 := CharP.cast_eq_zero (R := PS) 3
  rw [two_block_error_exact hN,
    ← logSlope_add_logCurve, delta, Y_pow_three_mul]
  linear_combination hthree * (logTerm j - Y ^ (2 * N) * logCurve j)

private theorem L_three_split (N : ℕ) :
    L (3 * N) = ∑ j ∈ Finset.range N,
      (logTerm j + logTerm (N + j) + logTerm (2 * N + j)) := by
  simp only [L, logTerm]
  rw [show 3 * N = N + (N + N) by omega, Finset.sum_range_add,
    Finset.sum_range_add]
  have hidx (j : ℕ) : N + (N + j) = 2 * N + j := by omega
  simp_rw [hidx]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  ring

/-- Precise logarithmic three-block identity.  Its remainder is cubic in the
block error, so it is valid through `Y^(3N)`.-/
theorem L_three_block_precise {N : ℕ} (hN : ∃ a, N = 3 ^ a) :
    ModY (3 * N) (L (3 * N)) (delta N ^ 2 * (L N - L N ^ 3)) := by
  rw [L_three_split]
  have hall : ModY (3 * N)
      (∑ j ∈ Finset.range N,
        (logTerm j + logTerm (N + j) + logTerm (2 * N + j)))
      (∑ j ∈ Finset.range N,
        delta N ^ 2 * (logTerm j - logTerm j ^ 3)) :=
    ModY.sum (Finset.range N) fun j hj ↦ log_term_three_blocks (j := j) hN
  refine ModY.trans hall ?_
  refine ⟨0, ?_⟩
  rw [← Finset.mul_sum]
  simp only [L, logTerm]
  rw [Finset.sum_sub_distrib, ← sum_pow_char]
  ring

private theorem logSlope_eq_logTerm_sub_sq (j : ℕ) :
    logSlope j = logTerm j - logTerm j ^ 2 := by
  have h := log_term_square j
  simp only [logSlope, logTerm] at h ⊢
  linear_combination h

private theorem log_slope_three_blocks {N j : ℕ} (hN : ∃ a, N = 3 ^ a) :
    ModY (3 * N)
      (logSlope j + logSlope (N + j) + logSlope (2 * N + j))
      (delta N ^ 2 * logSlope j) := by
  let d := delta N
  let l := logTerm j
  let m := logSlope j
  let c := logCurve j
  let e := X ^ (2 * N) - 1
  have h₁l := shifted_log_term_second_order (j := j) (delta_vanishes N)
    (X_pow_eq_one_add_delta_of_power hN)
  have h₂l₀ := shifted_log_term_second_order (j := j)
    (two_block_error_vanishes hN)
    (show X ^ (2 * N) = 1 + e by simp [e])
  have h₂target : ModY (3 * N)
      (l + e * m - e ^ 2 * c)
      (l - d * m + d ^ 2 * (m - c)) := by
    refine ⟨-(2 - d) * c, ?_⟩
    rw [show e = X ^ (2 * N) - 1 by rfl, two_block_error_exact hN]
    dsimp only [d]
    rw [delta, Y_pow_three_mul]
    ring
  have h₂l : ModY (3 * N) (logTerm (2 * N + j))
      (l - d * m + d ^ 2 * (m - c)) := by
    exact ModY.trans (by simpa only [l, m, c] using h₂l₀) h₂target
  have h₁ : ModY (3 * N) (logSlope (N + j))
      ((l + d * m - d ^ 2 * c) - (l + d * m - d ^ 2 * c) ^ 2) := by
    rw [logSlope_eq_logTerm_sub_sq]
    exact ModY.sub h₁l (ModY.pow h₁l 2)
  have h₂ : ModY (3 * N) (logSlope (2 * N + j))
      ((l - d * m + d ^ 2 * (m - c)) -
        (l - d * m + d ^ 2 * (m - c)) ^ 2) := by
    rw [logSlope_eq_logTerm_sub_sq]
    exact ModY.sub h₂l (ModY.pow h₂l 2)
  have hall := ModY.add
    (ModY.add (ModY.refl (3 * N) (logSlope j)) h₁) h₂
  refine ModY.trans hall ?_
  have hm : m = l - l ^ 2 := by
    simpa only [m, l] using logSlope_eq_logTerm_sub_sq j
  have hc : c = l ^ 2 - l ^ 3 := by
    have h := logSlope_add_logCurve j
    change m + c = l - l ^ 3 at h
    rw [hm] at h
    linear_combination h
  let q : PS := -(l ^ 4 + l ^ 3 + l ^ 2) +
    d * (l ^ 6 - l ^ 4 + l ^ 3 - l ^ 2)
  refine ⟨-q, ?_⟩
  have hthree : (3 : PS) = 0 := CharP.cast_eq_zero (R := PS) 3
  rw [logSlope_eq_logTerm_sub_sq j]
  rw [hm, hc]
  dsimp only [q, d, l, m, c]
  rw [delta, Y_pow_three_mul]
  linear_combination hthree *
    (-logTerm j *
      ((-Y ^ N) ^ 4 * logTerm j ^ 5 -
        2 * (-Y ^ N) ^ 4 * logTerm j ^ 4 +
        2 * (-Y ^ N) ^ 4 * logTerm j ^ 3 -
        (-Y ^ N) ^ 4 * logTerm j ^ 2 -
        (-Y ^ N) ^ 3 * logTerm j ^ 3 +
        (-Y ^ N) ^ 3 * logTerm j ^ 2 -
        (-Y ^ N) ^ 3 * logTerm j +
        2 * (-Y ^ N) ^ 2 * logTerm j ^ 3 -
        4 * (-Y ^ N) ^ 2 * logTerm j ^ 2 +
        2 * (-Y ^ N) ^ 2 * logTerm j + logTerm j - 1))

private theorem M_three_split (N : ℕ) :
    M (3 * N) = ∑ j ∈ Finset.range N,
      (logSlope j + logSlope (N + j) + logSlope (2 * N + j)) := by
  simp only [M, logSlope]
  rw [show 3 * N = N + (N + N) by omega, Finset.sum_range_add,
    Finset.sum_range_add]
  have hidx (j : ℕ) : N + (N + j) = 2 * N + j := by omega
  simp_rw [hidx]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  ring

/-- Exact-order recurrence for the second-order logarithmic correction.-/
theorem M_three_block_precise {N : ℕ} (hN : ∃ a, N = 3 ^ a) :
    ModY (3 * N) (M (3 * N)) (delta N ^ 2 * M N) := by
  rw [M_three_split]
  have hall : ModY (3 * N)
      (∑ j ∈ Finset.range N,
        (logSlope j + logSlope (N + j) + logSlope (2 * N + j)))
      (∑ j ∈ Finset.range N, delta N ^ 2 * logSlope j) :=
    ModY.sum (Finset.range N) fun j hj ↦ log_slope_three_blocks (j := j) hN
  refine ModY.trans hall ?_
  refine ⟨0, ?_⟩
  rw [← Finset.mul_sum]
  simp only [M, logSlope]
  ring

private theorem shifted_log_term {N s j : ℕ} {e : PS} (he : Vanishes N e)
    (hs : X ^ s = 1 + e) :
    ModY N
      (X ^ (s + j + 1) * (1 + X ^ (s + j + 1))⁻¹)
      (X ^ (j + 1) * (1 + X ^ (j + 1))⁻¹) := by
  let z := X ^ (j + 1)
  let d := 1 + z
  let d' := 1 + (1 + e) * z
  have hd : d * d⁻¹ = 1 := by
    simpa [d, z] using one_add_X_pow_mul_inv (j + 1)
  have hd' : d' * d'⁻¹ = 1 := by
    have hp : d' = 1 + X ^ (s + j + 1) := by
      rw [show s + j + 1 = s + (j + 1) by omega, pow_add, hs]
    rw [hp]
    exact one_add_X_pow_mul_inv (s + j + 1)
  have hdiff :
      z * (1 + e) * d'⁻¹ - z * d⁻¹ =
        e * (z * d'⁻¹ * d⁻¹) := by
    calc
      z * (1 + e) * d'⁻¹ - z * d⁻¹ =
          (z * (1 + e) * d - z * d') * (d'⁻¹ * d⁻¹) := by
            calc
              z * (1 + e) * d'⁻¹ - z * d⁻¹ =
                  z * (1 + e) * d'⁻¹ * (d * d⁻¹) -
                    z * d⁻¹ * (d' * d'⁻¹) := by rw [hd, hd', mul_one, mul_one]
              _ = (z * (1 + e) * d - z * d') * (d'⁻¹ * d⁻¹) := by ring
      _ = e * (z * d'⁻¹ * d⁻¹) := by simp [d', d]; ring
  obtain ⟨u, hu⟩ := he
  refine ⟨u * (z * d'⁻¹ * d⁻¹), ?_⟩
  rw [show s + j + 1 = s + (j + 1) by omega, pow_add, hs]
  change (1 + e) * z * d'⁻¹ - z * d⁻¹ = _
  rw [mul_comm (1 + e) z]
  rw [hdiff, hu]
  ring

private theorem L_add (s b : ℕ) :
    L (s + b) = L s +
      ∑ j ∈ Finset.range b,
        X ^ (s + j + 1) * (1 + X ^ (s + j + 1))⁻¹ := by
  rw [L, Finset.sum_range_add]
  congr 1

private theorem L_shift {N s b : ℕ} {e : PS} (he : Vanishes N e)
    (hs : X ^ s = 1 + e) :
    ModY N (L (s + b)) (L s + L b) := by
  rw [L_add]
  have hsum : ModY N
      (∑ j ∈ Finset.range b,
        X ^ (s + j + 1) * (1 + X ^ (s + j + 1))⁻¹)
      (∑ j ∈ Finset.range b,
        X ^ (j + 1) * (1 + X ^ (j + 1))⁻¹) :=
    ModY.sum _ fun j hj ↦ shifted_log_term he hs
  simpa [L] using ModY.add (ModY.refl N (L s)) hsum

/-- Coarse logarithmic-sum formula in the second block.-/
theorem L_one_block {N b : ℕ} (hN : ∃ a, N = 3 ^ a) :
    ModY N (L (N + b)) (L N + L b) :=
  L_shift (delta_vanishes N) (X_pow_eq_one_add_delta_of_power hN)

/-- Coarse logarithmic-sum formula in the third block.-/
theorem L_two_blocks {N b : ℕ} (hN : ∃ a, N = 3 ^ a) :
    ModY N (L (2 * N + b)) (-L N + L b) := by
  let e := X ^ (2 * N) - 1
  have hshift : ModY N (L (2 * N + b)) (L (2 * N) + L b) :=
    L_shift (two_block_error_vanishes hN) (by simp [e])
  have htwo : ModY N (L (2 * N)) (L N + L N) := by
    simpa [two_mul] using L_one_block (b := N) hN
  have hreplace := ModY.add htwo (ModY.refl N (L b))
  have hthree : (3 : PS) = 0 := CharP.cast_eq_zero (R := PS) 3
  refine ModY.trans hshift (ModY.trans hreplace ?_)
  exact ⟨0, by
    have heq : L N + L N = -L N := by linear_combination hthree * L N
    rw [heq]
    ring⟩

private theorem shifted_logSlope {N s j : ℕ} {e : PS} (he : Vanishes N e)
    (hs : X ^ s = 1 + e) :
    ModY N (logSlope (s + j)) (logSlope j) := by
  have hl := shifted_log_term (j := j) he hs
  rw [logSlope_eq_logTerm_sub_sq, logSlope_eq_logTerm_sub_sq]
  exact ModY.sub hl (ModY.pow hl 2)

private theorem M_add (s b : ℕ) :
    M (s + b) = M s + ∑ j ∈ Finset.range b, logSlope (s + j) := by
  rw [M, Finset.sum_range_add]
  congr 1

private theorem M_shift {N s b : ℕ} {e : PS} (he : Vanishes N e)
    (hs : X ^ s = 1 + e) :
    ModY N (M (s + b)) (M s + M b) := by
  rw [M_add]
  have hsum : ModY N
      (∑ j ∈ Finset.range b, logSlope (s + j))
      (∑ j ∈ Finset.range b, logSlope j) :=
    ModY.sum _ fun j hj ↦ shifted_logSlope he hs
  simpa only [M, logSlope] using ModY.add (ModY.refl N (M s)) hsum

/-- Coarse second-order-sum formula in the second block.-/
theorem M_one_block {N b : ℕ} (hN : ∃ a, N = 3 ^ a) :
    ModY N (M (N + b)) (M N + M b) :=
  M_shift (delta_vanishes N) (X_pow_eq_one_add_delta_of_power hN)

/-- Coarse second-order-sum formula in the third block.-/
theorem M_two_blocks {N b : ℕ} (hN : ∃ a, N = 3 ^ a) :
    ModY N (M (2 * N + b)) (-M N + M b) := by
  let e := X ^ (2 * N) - 1
  have hshift : ModY N (M (2 * N + b)) (M (2 * N) + M b) :=
    M_shift (two_block_error_vanishes hN) (by simp [e])
  have htwo : ModY N (M (2 * N)) (M N + M N) := by
    simpa [two_mul] using M_one_block (b := N) hN
  have hreplace := ModY.add htwo (ModY.refl N (M b))
  have hthree : (3 : PS) = 0 := CharP.cast_eq_zero (R := PS) 3
  refine ModY.trans hshift (ModY.trans hreplace ?_)
  exact ⟨0, by
    have heq : M N + M N = -M N := by linear_combination hthree * M N
    rw [heq]
    ring⟩

private theorem L_shift_precise {N s b : ℕ} {e : PS} (he : Vanishes N e)
    (hs : X ^ s = 1 + e) :
    ModY (2 * N) (L (s + b)) (L s + L b + e * M b) := by
  rw [L_add]
  have hsum : ModY (2 * N)
      (∑ j ∈ Finset.range b,
        X ^ (s + j + 1) * (1 + X ^ (s + j + 1))⁻¹)
      (∑ j ∈ Finset.range b, (logTerm j + e * logSlope j)) :=
    ModY.sum _ fun j hj ↦ by
      simpa only [logTerm] using shifted_log_term_first_order (j := j) he hs
  have hall := ModY.add (ModY.refl (2 * N) (L s)) hsum
  refine ModY.trans hall ?_
  refine ⟨0, ?_⟩
  rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  simp only [L, M, logTerm, logSlope]
  ring

/-- First-order logarithmic formula in the second block, retaining the term
needed by the precise `W` expansion.-/
theorem L_one_block_precise {N b : ℕ} (hN : ∃ a, N = 3 ^ a) :
    ModY (2 * N) (L (N + b)) (L N + L b + delta N * M b) :=
  L_shift_precise (delta_vanishes N) (X_pow_eq_one_add_delta_of_power hN)

/-- First-order logarithmic formula in the third block.-/
theorem L_two_blocks_precise {N b : ℕ} (hN : ∃ a, N = 3 ^ a) :
    ModY (2 * N) (L (2 * N + b))
      (-L N + L b + delta N * (M N - M b)) := by
  let e := X ^ (2 * N) - 1
  have hshift := L_shift_precise (b := b) (two_block_error_vanishes hN)
    (show X ^ (2 * N) = 1 + e by simp [e])
  have htwo : ModY (2 * N) (L (2 * N))
      (L N + L N + delta N * M N) := by
    simpa [two_mul] using L_one_block_precise (b := N) hN
  change ModY (2 * N) (L (2 * N + b))
    (L (2 * N) + L b + e * M b) at hshift
  have hreplace : ModY (2 * N)
      (L (2 * N) + L b + e * M b)
      (L N + L N + delta N * M N + (L b + e * M b)) := by
    convert ModY.add htwo (ModY.refl (2 * N) (L b + e * M b)) using 1 <;> ring
  refine ModY.trans hshift (ModY.trans hreplace ?_)
  refine ⟨M b, ?_⟩
  have hthree : (3 : PS) = 0 := CharP.cast_eq_zero (R := PS) 3
  have hpow : Y ^ (2 * N) = (Y ^ N) ^ 2 := by
    rw [pow_two, ← pow_add]
    congr 1
    omega
  rw [show e = X ^ (2 * N) - 1 by rfl, two_block_error_exact hN,
    delta, hpow]
  linear_combination hthree * L N

private theorem drop_delta_linear (N : ℕ) (u v : PS) :
    ModY N (u * (1 + delta N * v)) u := by
  refine ⟨-(u * v), ?_⟩
  rw [delta]
  ring

private theorem F_summand_one_block_coarse {N b : ℕ} (hN : ∃ a, N = 3 ^ a) :
    ModY N (X ^ (N + b + 1) * A (N + b) ^ 2)
      (A N ^ 2 * (X ^ (b + 1) * A b ^ 2)) := by
  refine ModY.trans (ModY.mono (by omega) (F_summand_one_block (b := b) hN)) ?_
  simpa using drop_delta_linear N
    (A N ^ 2 * (X ^ (b + 1) * A b ^ 2)) (1 - L b)

private theorem F_summand_two_blocks_coarse {N b : ℕ} (hN : ∃ a, N = 3 ^ a) :
    ModY N (X ^ (2 * N + b + 1) * A (2 * N + b) ^ 2)
      (A N ^ 4 * (X ^ (b + 1) * A b ^ 2)) := by
  refine ModY.trans (ModY.mono (by omega) (F_summand_two_blocks (b := b) hN)) ?_
  have h := drop_delta_linear N
    (A N ^ 4 * (X ^ (b + 1) * A b ^ 2)) (-(1 + L N - L b))
  convert h using 1 <;> ring

private theorem H_three_split (N : ℕ) :
    H (3 * N) = H N +
      (∑ b ∈ Finset.range N,
        X ^ (N + b + 1) * A (N + b) ^ 2 *
          ((1 - L (N + b)) ^ 2 - M (N + b))) +
      (∑ b ∈ Finset.range N,
        X ^ (2 * N + b + 1) * A (2 * N + b) ^ 2 *
          ((1 - L (2 * N + b)) ^ 2 - M (2 * N + b))) := by
  simp only [H]
  rw [show 3 * N = N + (N + N) by omega, Finset.sum_range_add,
    Finset.sum_range_add]
  have hidx (b : ℕ) : N + (N + b) = 2 * N + b := by omega
  simp_rw [hidx]
  ring

private theorem sum_H_first_target (N : ℕ) :
    (∑ b ∈ Finset.range N,
      (A N ^ 2 * (X ^ (b + 1) * A b ^ 2)) *
        ((1 - (L N + L b)) ^ 2 - (M N + M b))) =
      A N ^ 2 * (H N + L N * W N + (L N ^ 2 - M N) * F N) := by
  have hthree : (3 : PS) = 0 := CharP.cast_eq_zero (R := PS) 3
  simp_rw [show ∀ b : ℕ,
      (A N ^ 2 * (X ^ (b + 1) * A b ^ 2)) *
          ((1 - (L N + L b)) ^ 2 - (M N + M b)) =
        A N ^ 2 *
          (X ^ (b + 1) * A b ^ 2 * ((1 - L b) ^ 2 - M b) +
            L N * (X ^ (b + 1) * A b ^ 2 * (1 - L b)) +
            (L N ^ 2 - M N) * (X ^ (b + 1) * A b ^ 2)) by
      intro b
      linear_combination hthree *
        (A N ^ 2 * (X ^ (b + 1) * A b ^ 2) * L N * (L b - 1))]
  rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum]
  rfl

private theorem sum_H_second_target (N : ℕ) :
    (∑ b ∈ Finset.range N,
      (A N ^ 4 * (X ^ (b + 1) * A b ^ 2)) *
        ((1 - (-L N + L b)) ^ 2 - (-M N + M b))) =
      A N ^ 4 * (H N - L N * W N + (L N ^ 2 + M N) * F N) := by
  have hthree : (3 : PS) = 0 := CharP.cast_eq_zero (R := PS) 3
  simp_rw [show ∀ b : ℕ,
      (A N ^ 4 * (X ^ (b + 1) * A b ^ 2)) *
          ((1 - (-L N + L b)) ^ 2 - (-M N + M b)) =
        A N ^ 4 *
          (X ^ (b + 1) * A b ^ 2 * ((1 - L b) ^ 2 - M b) -
            L N * (X ^ (b + 1) * A b ^ 2 * (1 - L b)) +
            (L N ^ 2 + M N) * (X ^ (b + 1) * A b ^ 2)) by
      intro b
      linear_combination hthree *
        (-(A N ^ 4 * (X ^ (b + 1) * A b ^ 2) * L N * (L b - 1)))]
  rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum]
  rfl

/-- Coarse three-block identity for the correction series `H`.-/
theorem H_three_block_coarse {N : ℕ} (hN : ∃ a, N = 3 ^ a) :
    ModY N (H (3 * N))
      (H N * (1 + A N ^ 2 + A N ^ 4) +
        L N * W N * (A N ^ 2 - A N ^ 4) +
        F N *
          (A N ^ 2 * (L N ^ 2 - M N) +
            A N ^ 4 * (L N ^ 2 + M N))) := by
  have hfirst : ModY N
      (∑ b ∈ Finset.range N,
        X ^ (N + b + 1) * A (N + b) ^ 2 *
          ((1 - L (N + b)) ^ 2 - M (N + b)))
      (∑ b ∈ Finset.range N,
        (A N ^ 2 * (X ^ (b + 1) * A b ^ 2)) *
          ((1 - (L N + L b)) ^ 2 - (M N + M b))) :=
    ModY.sum _ fun b hb ↦ ModY.mul
      (F_summand_one_block_coarse hN)
      (ModY.sub
        (ModY.pow (ModY.sub (ModY.refl N 1) (L_one_block hN)) 2)
        (M_one_block hN))
  have hsecond : ModY N
      (∑ b ∈ Finset.range N,
        X ^ (2 * N + b + 1) * A (2 * N + b) ^ 2 *
          ((1 - L (2 * N + b)) ^ 2 - M (2 * N + b)))
      (∑ b ∈ Finset.range N,
        (A N ^ 4 * (X ^ (b + 1) * A b ^ 2)) *
          ((1 - (-L N + L b)) ^ 2 - (-M N + M b))) :=
    ModY.sum _ fun b hb ↦ ModY.mul
      (F_summand_two_blocks_coarse hN)
      (ModY.sub
        (ModY.pow (ModY.sub (ModY.refl N 1) (L_two_blocks hN)) 2)
        (M_two_blocks hN))
  rw [H_three_split]
  have hall := ModY.add (ModY.add (ModY.refl N (H N)) hfirst) hsecond
  rw [sum_H_first_target, sum_H_second_target] at hall
  refine ModY.trans hall ?_
  exact ⟨0, by ring⟩

private theorem W_three_split (N : ℕ) :
    W (3 * N) = W N +
      (∑ b ∈ Finset.range N,
        X ^ (N + b + 1) * A (N + b) ^ 2 * (1 - L (N + b))) +
      (∑ b ∈ Finset.range N,
        X ^ (2 * N + b + 1) * A (2 * N + b) ^ 2 * (1 - L (2 * N + b))) := by
  simp only [W]
  rw [show 3 * N = N + (N + N) by omega, Finset.sum_range_add,
    Finset.sum_range_add]
  have hidx (b : ℕ) : N + (N + b) = 2 * N + b := by omega
  simp_rw [hidx]
  ring

private theorem sum_W_first_target (N : ℕ) :
    (∑ b ∈ Finset.range N,
      (A N ^ 2 * (X ^ (b + 1) * A b ^ 2)) * (1 - (L N + L b))) =
      A N ^ 2 * (W N - L N * F N) := by
  simp_rw [show ∀ b : ℕ,
      (A N ^ 2 * (X ^ (b + 1) * A b ^ 2)) * (1 - (L N + L b)) =
        A N ^ 2 *
          (X ^ (b + 1) * A b ^ 2 * (1 - L b) -
            L N * (X ^ (b + 1) * A b ^ 2)) by intro b; ring]
  rw [← Finset.mul_sum, Finset.sum_sub_distrib, ← Finset.mul_sum]
  rfl

private theorem sum_W_second_target (N : ℕ) :
    (∑ b ∈ Finset.range N,
      (A N ^ 4 * (X ^ (b + 1) * A b ^ 2)) * (1 - (-L N + L b))) =
      A N ^ 4 * (W N + L N * F N) := by
  simp_rw [show ∀ b : ℕ,
      (A N ^ 4 * (X ^ (b + 1) * A b ^ 2)) * (1 - (-L N + L b)) =
        A N ^ 4 *
          (X ^ (b + 1) * A b ^ 2 * (1 - L b) +
            L N * (X ^ (b + 1) * A b ^ 2)) by intro b; ring]
  rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum]
  rfl

private theorem W_summand_one_block_precise {N b : ℕ}
    (hN : ∃ a, N = 3 ^ a) :
    ModY (2 * N)
      (X ^ (N + b + 1) * A (N + b) ^ 2 * (1 - L (N + b)))
      (A N ^ 2 * (X ^ (b + 1) * A b ^ 2) *
        ((1 - L N - L b) + delta N *
          ((1 - L b) * (1 - L N - L b) - M b))) := by
  have hf := F_summand_one_block (b := b) hN
  have hl := ModY.sub (ModY.refl (2 * N) 1) (L_one_block_precise (b := b) hN)
  have hmul := ModY.mul hf hl
  let C := A N ^ 2 * (X ^ (b + 1) * A b ^ 2)
  let a := 1 - L b
  let c := 1 - L N - L b
  have halg : ModY (2 * N)
      (C * (1 + delta N * a) * (1 - (L N + L b + delta N * M b)))
      (C * (c + delta N * (a * c - M b))) := by
    refine ⟨-(C * a * M b), ?_⟩
    have hpow : Y ^ (2 * N) = (Y ^ N) ^ 2 := by
      rw [pow_two, ← pow_add]
      congr 1
      omega
    rw [delta, hpow]
    simp only [C, a, c]
    ring
  exact ModY.trans (by convert hmul using 1 <;> simp only [C, a] <;> ring) halg

private theorem W_summand_two_blocks_precise {N b : ℕ}
    (hN : ∃ a, N = 3 ^ a) :
    ModY (2 * N)
      (X ^ (2 * N + b + 1) * A (2 * N + b) ^ 2 * (1 - L (2 * N + b)))
      (A N ^ 4 * (X ^ (b + 1) * A b ^ 2) *
        ((1 + L N - L b) - delta N *
          ((1 + L N - L b) ^ 2 + M N - M b))) := by
  have hf := F_summand_two_blocks (b := b) hN
  have hl := ModY.sub (ModY.refl (2 * N) 1) (L_two_blocks_precise (b := b) hN)
  have hmul := ModY.mul hf hl
  refine ModY.trans hmul ?_
  refine ⟨A N ^ 4 * (X ^ (b + 1) * A b ^ 2) *
    (1 + L N - L b) * (M N - M b), ?_⟩
  have hpow : Y ^ (2 * N) = (Y ^ N) ^ 2 := by
    rw [pow_two, ← pow_add]
    congr 1
    omega
  rw [delta, hpow]
  ring

private theorem sum_W_first_precise_target (N : ℕ) :
    (∑ b ∈ Finset.range N,
      A N ^ 2 * (X ^ (b + 1) * A b ^ 2) *
        ((1 - L N - L b) + delta N *
          ((1 - L b) * (1 - L N - L b) - M b))) =
      A N ^ 2 * (W N - L N * F N) +
        delta N * A N ^ 2 * (H N - L N * W N) := by
  simp_rw [show ∀ b : ℕ,
      A N ^ 2 * (X ^ (b + 1) * A b ^ 2) *
          ((1 - L N - L b) + delta N *
            ((1 - L b) * (1 - L N - L b) - M b)) =
        A N ^ 2 *
          (X ^ (b + 1) * A b ^ 2 * (1 - L b) -
            L N * (X ^ (b + 1) * A b ^ 2)) +
        (delta N * A N ^ 2) *
          (X ^ (b + 1) * A b ^ 2 * ((1 - L b) ^ 2 - M b) -
            L N * (X ^ (b + 1) * A b ^ 2 * (1 - L b))) by
      intro b
      ring]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib,
    ← Finset.mul_sum]
  rfl

private theorem sum_W_second_precise_target (N : ℕ) :
    (∑ b ∈ Finset.range N,
      A N ^ 4 * (X ^ (b + 1) * A b ^ 2) *
        ((1 + L N - L b) - delta N *
          ((1 + L N - L b) ^ 2 + M N - M b))) =
      A N ^ 4 * (W N + L N * F N) +
        delta N * A N ^ 4 *
          (-H N + L N * W N - (L N ^ 2 + M N) * F N) := by
  simp_rw [show ∀ b : ℕ,
      A N ^ 4 * (X ^ (b + 1) * A b ^ 2) *
          ((1 + L N - L b) - delta N *
            ((1 + L N - L b) ^ 2 + M N - M b)) =
        A N ^ 4 *
          (X ^ (b + 1) * A b ^ 2 * (1 - L b) +
            L N * (X ^ (b + 1) * A b ^ 2)) +
        (delta N * A N ^ 4) *
          (-(X ^ (b + 1) * A b ^ 2 * ((1 - L b) ^ 2 - M b)) +
            L N * (X ^ (b + 1) * A b ^ 2 * (1 - L b)) -
            (L N ^ 2 + M N) * (X ^ (b + 1) * A b ^ 2)) by
      intro b
      have hthree : (3 : PS) = 0 := CharP.cast_eq_zero (R := PS) 3
      linear_combination hthree *
        (A N ^ 4 * (X ^ (b + 1) * A b ^ 2) * delta N * L N * (L b - 1))]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib,
    Finset.sum_add_distrib, Finset.sum_neg_distrib, ← Finset.mul_sum,
    ← Finset.mul_sum]
  rfl

/-- The precise three-block identity for `W`, retaining every first-order
term in `δ = X^N-1`.  This is the higher-order identity required before any
exact-order assertion for `W` can be promoted to a theorem.-/
theorem W_three_block_precise {N : ℕ} (hN : ∃ a, N = 3 ^ a) :
    ModY (2 * N) (W (3 * N))
      (W N * (1 + A N ^ 2 + A N ^ 4) +
        L N * F N * (A N ^ 4 - A N ^ 2) +
        delta N *
          ((A N ^ 2 - A N ^ 4) * (H N - L N * W N) -
            A N ^ 4 * (L N ^ 2 + M N) * F N)) := by
  have hfirst : ModY (2 * N)
      (∑ b ∈ Finset.range N,
        X ^ (N + b + 1) * A (N + b) ^ 2 * (1 - L (N + b)))
      (∑ b ∈ Finset.range N,
        A N ^ 2 * (X ^ (b + 1) * A b ^ 2) *
          ((1 - L N - L b) + delta N *
            ((1 - L b) * (1 - L N - L b) - M b))) :=
    ModY.sum _ fun b hb ↦ W_summand_one_block_precise hN
  have hsecond : ModY (2 * N)
      (∑ b ∈ Finset.range N,
        X ^ (2 * N + b + 1) * A (2 * N + b) ^ 2 * (1 - L (2 * N + b)))
      (∑ b ∈ Finset.range N,
        A N ^ 4 * (X ^ (b + 1) * A b ^ 2) *
          ((1 + L N - L b) - delta N *
            ((1 + L N - L b) ^ 2 + M N - M b))) :=
    ModY.sum _ fun b hb ↦ W_summand_two_blocks_precise hN
  rw [W_three_split]
  have hall := ModY.add (ModY.add (ModY.refl (2 * N) (W N)) hfirst) hsecond
  rw [sum_W_first_precise_target, sum_W_second_precise_target] at hall
  refine ModY.trans hall ?_
  exact ⟨0, by ring⟩

/-- The coarse three-block identity for `W`.  It is deliberately stated and
proved independently of the stronger exact-order theorem.-/
theorem W_three_block_coarse {N : ℕ} (hN : ∃ a, N = 3 ^ a) :
    ModY N (W (3 * N))
      (W N * (1 + A N ^ 2 + A N ^ 4) -
        L N * F N * (A N ^ 2 - A N ^ 4)) := by
  have hfirst : ModY N
      (∑ b ∈ Finset.range N,
        X ^ (N + b + 1) * A (N + b) ^ 2 * (1 - L (N + b)))
      (∑ b ∈ Finset.range N,
        (A N ^ 2 * (X ^ (b + 1) * A b ^ 2)) * (1 - (L N + L b))) :=
    ModY.sum _ fun b hb ↦ ModY.mul
      (F_summand_one_block_coarse hN)
      (ModY.sub (ModY.refl N 1) (L_one_block hN))
  have hsecond : ModY N
      (∑ b ∈ Finset.range N,
        X ^ (2 * N + b + 1) * A (2 * N + b) ^ 2 * (1 - L (2 * N + b)))
      (∑ b ∈ Finset.range N,
        (A N ^ 4 * (X ^ (b + 1) * A b ^ 2)) * (1 - (-L N + L b))) :=
    ModY.sum _ fun b hb ↦ ModY.mul
      (F_summand_two_blocks_coarse hN)
      (ModY.sub (ModY.refl N 1) (L_two_blocks hN))
  rw [W_three_split]
  have hall := ModY.add (ModY.add (ModY.refl N (W N)) hfirst) hsecond
  rw [sum_W_first_target, sum_W_second_target] at hall
  refine ModY.trans hall ?_
  exact ⟨0, by ring⟩

end IwasawaTower.Series
