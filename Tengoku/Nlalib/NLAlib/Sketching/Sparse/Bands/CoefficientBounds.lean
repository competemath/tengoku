/- Copyright (c) 2026 Diar Heidary.
Ported to NLAlib from commit b9da2b5d96e5fd70252e9c6551aefc92643e7d0b.
Released under the MIT license; see docs/ports/sparse-fock-MIT.txt. -/
import Tengoku.Nlalib.NLAlib.Sketching.Sparse.Bands.ScalarBounds
import Tengoku.Nlalib.NLAlib.Sketching.Sparse.FockModel.TernaryJacobi
import Tengoku.Seed.Tactic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Scalar coefficient bounds for normalized sparse-Fock bands

These are the denominator-cleared inequalities used when `m = s * b` and
the heavy Jacobi coefficient is `sqrt (b - 1)`.
-/

namespace NLAlib.SparseSketch

noncomputable section

/-- The square of the heavy coefficient, divided by the stack height, is at
most `1 / s`.

Source: ported from `SparseFockFormal.BandCoefficientBounds`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.
@isnad1 id=le.2h2v.s6.775fb253a6c7 from=translated src=- shape=c78acd62 vocab=e4969b2c
-/
theorem rho_sq_div_stack_le_inv_s {s b : ℕ} (hs : 0 < s) (hb : 1 < b) :
    Real.sqrt ((b : ℝ) - 1) ^ 2 / (((s * b : ℕ) : ℝ)) ≤ 1 / (s : ℝ) := by
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs
  have hbR : (0 : ℝ) < b := by positivity
  rw [sq_sqrt_b_sub_one hb, Nat.cast_mul]
  apply (div_le_div_iff₀ (mul_pos hsR hbR) hsR).2
  nlinarith

/-- The unsquared heavy coefficient, divided by the stack height, is also at
most `1 / s`.

Source: ported from `SparseFockFormal.BandCoefficientBounds`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.
@isnad1 id=le.2h2v.s6.9330a8d1fcc8 from=translated src=- shape=f732ce08 vocab=64cadf4a
-/
theorem rho_div_stack_le_inv_s {s b : ℕ} (hs : 0 < s) (hb : 1 < b) :
    Real.sqrt ((b : ℝ) - 1) / (((s * b : ℕ) : ℝ)) ≤ 1 / (s : ℝ) := by
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs
  have hbR : (0 : ℝ) < b := by positivity
  have hrho0 : 0 ≤ Real.sqrt ((b : ℝ) - 1) := Real.sqrt_nonneg _
  have hrhoSq := sq_sqrt_b_sub_one hb
  have hrhoLe : Real.sqrt ((b : ℝ) - 1) ≤ (b : ℝ) := by
    have hbTwo : (2 : ℝ) ≤ b := by exact_mod_cast hb
    nlinarith
  rw [Nat.cast_mul]
  apply (div_le_div_iff₀ (mul_pos hsR hbR) hsR).2
  nlinarith

/-- The normalized mixed-band heavy coefficient is nonnegative.
Source: ported from `SparseFockFormal.BandCoefficientBounds`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.
@isnad1 id=le.0h2v.s5.e429f53ac4ed from=translated src=- shape=b4641611 vocab=c3a5d388
-/
theorem rho_div_stack_nonneg {s b : ℕ} :
    0 ≤ Real.sqrt ((b : ℝ) - 1) / (((s * b : ℕ) : ℝ)) := by
  positivity

/-- The normalized heavy-heavy coefficient is nonnegative.
Source: ported from `SparseFockFormal.BandCoefficientBounds`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.
@isnad1 id=le.0h2v.s6.87503c28bb48 from=translated src=- shape=7fff48bb vocab=077beb62
-/
theorem rho_sq_div_stack_nonneg {s b : ℕ} :
    0 ≤ Real.sqrt ((b : ℝ) - 1) ^ 2 / (((s * b : ℕ) : ℝ)) := by
  positivity

/-- The exact AM--GM absorption used for the `X_+` mixed band.

Source: ported from `SparseFockFormal.BandCoefficientBounds`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.
@isnad1 id=le.2h4v.s7.deffba395108 from=translated src=- shape=b3fbf804 vocab=ea4a17c7
-/
theorem mixed_plus_absorb {s b d nu : ℕ} (hs : 0 < s) (hb : 1 < b) :
    (Real.sqrt ((b : ℝ) - 1) / (((s * b : ℕ) : ℝ)) *
      Real.sqrt ((nu : ℝ) * ((d : ℝ) + nu + 1))) ≤
      (1 / 2 : ℝ) *
        (((d : ℝ) + nu + 1) / (((s * b : ℕ) : ℝ)) +
          (nu : ℝ) / s) := by
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs
  have hbR : (0 : ℝ) < b := by positivity
  have hmR : (0 : ℝ) < ((s * b : ℕ) : ℝ) := by positivity
  have hnu : (0 : ℝ) ≤ nu := by positivity
  have hD : (0 : ℝ) ≤ (d : ℝ) + nu + 1 := by positivity
  have hh : (0 : ℝ) ≤ (b : ℝ) - 1 := by
    have hbOne : (1 : ℝ) ≤ b := by exact_mod_cast (Nat.le_of_lt hb)
    linarith
  have hsqrtMul :
      Real.sqrt ((b : ℝ) - 1) *
          Real.sqrt ((nu : ℝ) * ((d : ℝ) + nu + 1)) =
        Real.sqrt (((b : ℝ) - 1) * (nu : ℝ)) *
          Real.sqrt ((d : ℝ) + nu + 1) := by
    rw [Real.sqrt_mul hnu]
    rw [Real.sqrt_mul hh]
    ring
  have hamgm := mixed_product_into_envelope
    (show 0 ≤ ((b : ℝ) - 1) * (nu : ℝ) by positivity) hD
  have hheavy :
      (((b : ℝ) - 1) * (nu : ℝ)) / (((s * b : ℕ) : ℝ)) ≤
        (nu : ℝ) / s := by
    have hcoef := rho_sq_div_stack_le_inv_s hs hb
    rw [sq_sqrt_b_sub_one hb] at hcoef
    have hmul := mul_le_mul_of_nonneg_right hcoef hnu
    calc
      (((b : ℝ) - 1) * (nu : ℝ)) / (((s * b : ℕ) : ℝ)) =
          (((b : ℝ) - 1) / (((s * b : ℕ) : ℝ))) * (nu : ℝ) := by ring
      _ ≤ (1 / (s : ℝ)) * (nu : ℝ) := hmul
      _ = (nu : ℝ) / s := by ring
  calc
    Real.sqrt ((b : ℝ) - 1) / (((s * b : ℕ) : ℝ)) *
        Real.sqrt ((nu : ℝ) * ((d : ℝ) + nu + 1)) =
        (Real.sqrt (((b : ℝ) - 1) * (nu : ℝ)) *
          Real.sqrt ((d : ℝ) + nu + 1)) / (((s * b : ℕ) : ℝ)) := by
      rw [← hsqrtMul]
      ring
    _ ≤ ((((b : ℝ) - 1) * (nu : ℝ)) + ((d : ℝ) + nu + 1)) /
        2 / (((s * b : ℕ) : ℝ)) := by
      exact div_le_div_of_nonneg_right hamgm hmR.le
    _ ≤ (1 / 2 : ℝ) *
        (((d : ℝ) + nu + 1) / (((s * b : ℕ) : ℝ)) +
          (nu : ℝ) / s) := by
      have hsum := add_le_add_right hheavy
        (((d : ℝ) + nu + 1) / (((s * b : ℕ) : ℝ)))
      calc
        ((((b : ℝ) - 1) * (nu : ℝ)) + ((d : ℝ) + nu + 1)) /
            2 / (((s * b : ℕ) : ℝ)) =
            (1 / 2 : ℝ) *
              (((d : ℝ) + nu + 1) / (((s * b : ℕ) : ℝ)) +
                (((b : ℝ) - 1) * (nu : ℝ)) / (((s * b : ℕ) : ℝ))) := by
          ring
        _ ≤ (1 / 2 : ℝ) *
            (((d : ℝ) + nu + 1) / (((s * b : ℕ) : ℝ)) +
              (nu : ℝ) / s) :=
          mul_le_mul_of_nonneg_left hsum (by norm_num)

/-- The two `X₀` orientations are absorbed by one dense term and one sparse
term, exactly as in the grade-zero mixed row of the paper.

Source: ported from `SparseFockFormal.BandCoefficientBounds`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.
@isnad1 id=le.2h4v.s7.9faaa36f54f5 from=translated src=- shape=2e6dabd1 vocab=ea4a17c7
-/
theorem mixed_zero_absorb {s b d nu : ℕ} (hs : 0 < s) (hb : 1 < b) :
    2 * (Real.sqrt ((b : ℝ) - 1) / (((s * b : ℕ) : ℝ)) *
      Real.sqrt ((nu : ℝ) * ((d : ℝ) + nu))) ≤
      ((d : ℝ) + nu) / (((s * b : ℕ) : ℝ)) + (nu : ℝ) / s := by
  have hmR : (0 : ℝ) < ((s * b : ℕ) : ℝ) := by positivity
  have hnu : (0 : ℝ) ≤ nu := by positivity
  have hD : (0 : ℝ) ≤ (d : ℝ) + nu := by positivity
  have hh : (0 : ℝ) ≤ (b : ℝ) - 1 := by
    have hbOne : (1 : ℝ) ≤ b := by exact_mod_cast (Nat.le_of_lt hb)
    linarith
  have hsqrtMul :
      Real.sqrt ((b : ℝ) - 1) *
          Real.sqrt ((nu : ℝ) * ((d : ℝ) + nu)) =
        Real.sqrt (((b : ℝ) - 1) * (nu : ℝ)) *
          Real.sqrt ((d : ℝ) + nu) := by
    rw [Real.sqrt_mul hnu]
    rw [Real.sqrt_mul hh]
    ring
  have hamgm := mixed_product_into_envelope
    (show 0 ≤ ((b : ℝ) - 1) * (nu : ℝ) by positivity) hD
  have hcoef := rho_sq_div_stack_le_inv_s hs hb
  rw [sq_sqrt_b_sub_one hb] at hcoef
  have hheavy :
      (((b : ℝ) - 1) * (nu : ℝ)) / (((s * b : ℕ) : ℝ)) ≤
        (nu : ℝ) / s := by
    have hmul := mul_le_mul_of_nonneg_right hcoef hnu
    calc
      (((b : ℝ) - 1) * (nu : ℝ)) / (((s * b : ℕ) : ℝ)) =
          (((b : ℝ) - 1) / (((s * b : ℕ) : ℝ))) * (nu : ℝ) := by ring
      _ ≤ (1 / (s : ℝ)) * (nu : ℝ) := hmul
      _ = (nu : ℝ) / s := by ring
  calc
    2 * (Real.sqrt ((b : ℝ) - 1) / (((s * b : ℕ) : ℝ)) *
        Real.sqrt ((nu : ℝ) * ((d : ℝ) + nu))) =
        (2 / (((s * b : ℕ) : ℝ)) *
          (Real.sqrt (((b : ℝ) - 1) * (nu : ℝ)) *
            Real.sqrt ((d : ℝ) + nu))) := by
      rw [← hsqrtMul]
      ring
    _ ≤ (2 / (((s * b : ℕ) : ℝ)) *
        ((((b : ℝ) - 1) * (nu : ℝ) + ((d : ℝ) + nu)) / 2)) :=
      mul_le_mul_of_nonneg_left hamgm (by positivity)
    _ = (((b : ℝ) - 1) * (nu : ℝ)) / (((s * b : ℕ) : ℝ)) +
        ((d : ℝ) + nu) / (((s * b : ℕ) : ℝ)) := by ring
    _ ≤ ((d : ℝ) + nu) / (((s * b : ℕ) : ℝ)) + (nu : ℝ) / s := by
      linarith

/-- A directional bound `rho * nu / (s*b)` is absorbed by `nu / s`.

Source: ported from `SparseFockFormal.BandCoefficientBounds`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.
@isnad1 id=le.2h3v.s6.d18fd0c0d9d8 from=translated src=- shape=6f7ae96b vocab=64cadf4a
-/
theorem directional_absorb {s b nu : ℕ} (hs : 0 < s) (hb : 1 < b) :
    Real.sqrt ((b : ℝ) - 1) / (((s * b : ℕ) : ℝ)) * (nu : ℝ) ≤
      (nu : ℝ) / s := by
  have hcoef := rho_div_stack_le_inv_s hs hb
  calc
    Real.sqrt ((b : ℝ) - 1) / (((s * b : ℕ) : ℝ)) * (nu : ℝ) ≤
        (1 / (s : ℝ)) * (nu : ℝ) :=
      mul_le_mul_of_nonneg_right hcoef (Nat.cast_nonneg _)
    _ = (nu : ℝ) / s := by ring

end

end NLAlib.SparseSketch
