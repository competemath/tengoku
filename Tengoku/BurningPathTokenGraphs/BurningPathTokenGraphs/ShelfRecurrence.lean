import Tengoku.BurningPathTokenGraphs.BurningPathTokenGraphs.Potential
import Tengoku.Seed.Data.Nat.Sqrt

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Integer feasibility and one-step loss for the shelf recurrence

This file formalizes the integer shelf-width choice and the potential loss of
one nonterminal update. It stops before the trajectory estimates.
-/

namespace BurningPath

/--
An admissible shelf width.  The condition `2 * q ≤ w` is the division-free form of
`q ≤ ⌊w / 2⌋`.-/
def ShelfWidthAdmissible (w z q : ℕ) : Prop :=
  2 ≤ q ∧ 2 * q ≤ w ∧ z ≤ q * (w - q)

/-- `q` is the least admissible shelf width.-/
def IsLeastShelfWidth (w z q : ℕ) : Prop :=
  ShelfWidthAdmissible w z q ∧ ∀ m, ShelfWidthAdmissible w z m → q ≤ m

/--
The integer cube inequality is the square-root upper bound written as
`z ≤ √(4/3) w √w`.-/
theorem shelf_cube_bound_iff_real_upper (w z : ℕ) :
    3 * z ^ 2 ≤ 4 * w ^ 3 ↔
      (z : ℝ) ≤ Real.sqrt (4 / 3) * (w : ℝ) * Real.sqrt w := by
  let W : ℝ := w
  let Z : ℝ := z
  let B : ℝ := Real.sqrt (4 / 3) * W * Real.sqrt W
  have hcoef : Real.sqrt (4 / 3) ^ 2 = (4 / 3 : ℝ) :=
    Real.sq_sqrt (by norm_num)
  have hWsqrt : Real.sqrt W ^ 2 = W := Real.sq_sqrt (by positivity)
  have hBsq : B ^ 2 = (4 / 3) * W ^ 3 := by
    dsimp [B]
    calc
      (Real.sqrt (4 / 3) * W * Real.sqrt W) ^ 2 =
          Real.sqrt (4 / 3) ^ 2 * W ^ 2 * Real.sqrt W ^ 2 := by ring
      _ = (4 / 3) * W ^ 3 := by rw [hcoef, hWsqrt]; ring
  have hZ0 : 0 ≤ Z := by positivity
  have hB0 : 0 ≤ B := by positivity
  constructor
  · intro h
    have hR : 3 * Z ^ 2 ≤ 4 * W ^ 3 := by
      dsimp [Z, W]
      exact_mod_cast h
    change Z ≤ B
    nlinarith
  · intro h
    change Z ≤ B at h
    have hR : 3 * Z ^ 2 ≤ 4 * W ^ 3 := by nlinarith
    dsimp [Z, W] at hR
    exact_mod_cast hR

/--
For `w ≥ 144`, the explicit integer `3 * Nat.sqrt w` is admissible and is at most `w / 4`.-/
theorem three_mul_natSqrt_candidate {w z : ℕ} (hw : 144 ≤ w)
    (hcube : 3 * z ^ 2 ≤ 4 * w ^ 3) :
    ShelfWidthAdmissible w z (3 * Nat.sqrt w) ∧
      4 * (3 * Nat.sqrt w) ≤ w := by
  let s := Nat.sqrt w
  let q := 3 * s
  have hs : 12 ≤ s := by
    rw [Nat.le_sqrt]
    dsimp [s]
    omega
  have hsq : s * s ≤ w := by
    simpa [s] using Nat.sqrt_le w
  have hwlt : w < (s + 1) * (s + 1) := by
    simpa [s] using Nat.lt_succ_sqrt w
  have hq4 : 4 * q ≤ w := by
    dsimp [q]
    nlinarith
  have hzsq_le : z * z ≤ 4 * w ^ 3 := by
    simp only [pow_two] at hcube ⊢
    nlinarith
  have hwcube_lt :
      4 * w ^ 3 < (2 * w * (s + 1)) * (2 * w * (s + 1)) := by
    have hmul :=
      Nat.mul_lt_mul_of_pos_left hwlt (by positivity : 0 < 4 * w * w)
    simpa [pow_succ, Nat.mul_add, Nat.add_mul, mul_assoc, mul_left_comm, mul_comm] using hmul
  have hzlt : z < 2 * w * (s + 1) := by
    apply Nat.mul_self_lt_mul_self_iff.mp
    exact hzsq_le.trans_lt hwcube_lt
  have hqw : q ≤ w := by omega
  have hprod : 2 * w * (s + 1) ≤ q * (w - q) := by
    have h11 : 11 * w ≤ s * w := Nat.mul_le_mul_right w (by omega)
    have h9 : 9 * (s * s) ≤ 9 * w := Nat.mul_le_mul_left 9 hsq
    rw [Nat.mul_sub_left_distrib]
    apply Nat.le_sub_of_add_le
    dsimp [q]
    nlinarith
  change ShelfWidthAdmissible w z q ∧ 4 * q ≤ w
  exact ⟨⟨by omega, by omega, by omega⟩, hq4⟩

/-- Under the size bound, a least admissible integer shelf width exists.-/
theorem exists_isLeastShelfWidth {w z : ℕ} (hw : 144 ≤ w)
    (hcube : 3 * z ^ 2 ≤ 4 * w ^ 3) :
    ∃ q, IsLeastShelfWidth w z q := by
  classical
  have hex : ∃ q, ShelfWidthAdmissible w z q :=
    ⟨3 * Nat.sqrt w, (three_mul_natSqrt_candidate hw hcube).1⟩
  let q := Nat.find hex
  refine ⟨q, Nat.find_spec hex, ?_⟩
  intro m hm
  exact Nat.find_min' hex hm

/-- The same existence result under the original real square-root hypothesis.-/
theorem exists_isLeastShelfWidth_of_real_upper {w z : ℕ} (hw : 144 ≤ w)
    (hupper : (z : ℝ) ≤ Real.sqrt (4 / 3) * (w : ℝ) * Real.sqrt w) :
    ∃ q, IsLeastShelfWidth w z q :=
  exists_isLeastShelfWidth hw ((shelf_cube_bound_iff_real_upper w z).2 hupper)

/--
The least width satisfies the root-free square bound, lies below `w / 4`, and leaves at least
three quarters of `w`.-/
theorem IsLeastShelfWidth.bounds {w z q : ℕ} (hq : IsLeastShelfWidth w z q)
    (hw : 144 ≤ w) (hcube : 3 * z ^ 2 ≤ 4 * w ^ 3) :
    q ^ 2 ≤ 9 * w ∧ 4 * q ≤ w ∧ 3 * w ≤ 4 * (w - q) := by
  have hcand := three_mul_natSqrt_candidate hw hcube
  have hqq₀ : q ≤ 3 * Nat.sqrt w := hq.2 _ hcand.1
  have hqSq : q ^ 2 ≤ 9 * w := by
    nlinarith [Nat.pow_le_pow_left hqq₀ 2, Nat.sqrt_le w]
  have hq4 : 4 * q ≤ w := by omega
  refine ⟨hqSq, hq4, ?_⟩
  have hqw : q ≤ w := by omega
  omega

/-- The root-free square bound implies the advertised real inequality `q ≤ 3√w`.-/
theorem IsLeastShelfWidth.le_three_mul_sqrt {w z q : ℕ}
    (hq : IsLeastShelfWidth w z q) (hw : 144 ≤ w)
    (hcube : 3 * z ^ 2 ≤ 4 * w ^ 3) :
    (q : ℝ) ≤ 3 * Real.sqrt w := by
  have hsqR : (q : ℝ) ^ 2 ≤ 9 * (w : ℝ) := by
    exact_mod_cast (hq.bounds hw hcube).1
  have hsqrt : Real.sqrt (w : ℝ) ^ 2 = (w : ℝ) :=
    Real.sq_sqrt (by positivity)
  have hq0 : 0 ≤ (q : ℝ) := by positivity
  have hsqrt0 : 0 ≤ Real.sqrt (w : ℝ) := Real.sqrt_nonneg _
  nlinarith

/-- In real form, the remainder `a = w - q` satisfies `a ≥ 3w/4`.-/
theorem IsLeastShelfWidth.remainder_ge_three_quarters {w z q : ℕ}
    (hq : IsLeastShelfWidth w z q) (hw : 144 ≤ w)
    (hcube : 3 * z ^ 2 ≤ 4 * w ^ 3) :
    (3 / 4 : ℝ) * (w : ℝ) ≤ ((w - q : ℕ) : ℝ) := by
  have hq4 := (hq.bounds hw hcube).2.1
  have hqw : q ≤ w := by omega
  rw [Nat.cast_sub hqw]
  have hq4R : 4 * (q : ℝ) ≤ (w : ℝ) := by exact_mod_cast hq4
  norm_num
  nlinarith

/-- Minimality gives the strict lower estimate for `z`.-/
theorem IsLeastShelfWidth.minimality_lower {w z q : ℕ}
    (hq : IsLeastShelfWidth w z q) (hz : w - 1 < z) :
    (q - 1) * (w - q + 1) < z := by
  have hq2 : 2 ≤ q := hq.1.1
  have hqhalf : 2 * q ≤ w := hq.1.2.1
  have hqw : q ≤ w := by omega
  by_cases hqeq : q = 2
  · subst q
    norm_num
    rw [show w - 2 + 1 = w - 1 by omega]
    exact hz
  · have hqgt : 2 < q := by omega
    by_contra hnot
    have hzle : z ≤ (q - 1) * (w - q + 1) := by omega
    have hsub : w - (q - 1) = w - q + 1 := by omega
    have hadm : ShelfWidthAdmissible w z (q - 1) := by
      refine ⟨by omega, by omega, ?_⟩
      rwa [hsub]
    have := hq.2 (q - 1) hadm
    omega

/-- The algebraic one-step estimate from the square and minimality bounds.-/
theorem shelfPotential_update_ge_sub_44_of_bounds {w z q : ℕ}
    (hq2 : 2 ≤ q) (hqw : q ≤ w) (hsq : q ^ 2 ≤ 9 * w)
    (hminimal : (q - 1) * (w - q + 1) < z)
    (hnonterminal : 2 * (w - q) < z) :
    shelfPotential ((w - q : ℕ) : ℝ) ((z - 2 * (w - q) : ℕ) : ℝ) ≥
      shelfPotential (w : ℝ) (z : ℝ) - 44 * (w : ℝ) ^ 2 := by
  let W : ℝ := w
  let Z : ℝ := z
  let Q : ℝ := q
  let A : ℝ := (w - q : ℕ)
  have hAq : A + Q = W := by
    dsimp [A, Q, W]
    exact_mod_cast Nat.sub_add_cancel hqw
  have hA0 : 0 ≤ A := by positivity
  have hQ0 : 0 ≤ Q := by positivity
  have hW0 : 0 ≤ W := by positivity
  have hQ1 : 1 ≤ Q := by
    change (1 : ℝ) ≤ (q : ℝ)
    exact_mod_cast (show 1 ≤ q by omega)
  have hsqR : Q ^ 2 ≤ 9 * W := by
    dsimp [Q, W]
    exact_mod_cast hsq
  have hminimalR : (Q - 1) * (A + 1) < Z := by
    have hmcast : (((q - 1) * (w - q + 1) : ℕ) : ℝ) < (z : ℝ) := by
      exact_mod_cast hminimal
    simpa only [Q, A, Z, Nat.cast_mul, Nat.cast_sub (by omega : 1 ≤ q),
      Nat.cast_add, Nat.cast_one] using hmcast
  have hZmul : 4 * A * ((Q - 1) * (A + 1)) ≤ 4 * A * Z :=
    mul_le_mul_of_nonneg_left hminimalR.le (by positivity)
  have hqError : 4 * A * Q ^ 2 ≤ 36 * A * W := by
    have hmul := mul_le_mul_of_nonneg_left hsqR (show 0 ≤ 4 * A by positivity)
    nlinarith
  have hqCube : (4 / 3) * Q ^ 3 ≤ 12 * Q * W := by
    have hmul :=
      mul_le_mul_of_nonneg_left hsqR (show 0 ≤ (4 / 3 : ℝ) * Q by positivity)
    nlinarith
  have hAW : A ≤ W := by nlinarith
  have henvelope : 36 * A * W + 8 * A ^ 2 + 12 * Q * W ≤ 44 * W ^ 2 := by
    have hfactor : 0 ≤ (W - A) * (4 * W + A) :=
      mul_nonneg (sub_nonneg.mpr hAW) (by positivity)
    nlinarith
  have herror :
      4 * A * Q ^ 2 + (4 / 3) * Q ^ 3 + 8 * A ^ 2 ≤ 44 * W ^ 2 := by
    nlinarith
  have hidentity := shelfPotential_update_identity' A Z Q
  have hrealUpdate : ((z - 2 * (w - q) : ℕ) : ℝ) = Z - 2 * A := by
    dsimp [Z, A]
    rw [Nat.cast_sub (by omega : 2 * (w - q) ≤ z)]
    norm_num
  rw [hrealUpdate]
  change shelfPotential A (Z - 2 * A) ≥ shelfPotential W Z - 44 * W ^ 2
  rw [← hAq]
  nlinarith

/-- A nonterminal least-width update loses at most `45w²` of shelf potential.-/
theorem IsLeastShelfWidth.potential_update {w z q : ℕ}
    (hq : IsLeastShelfWidth w z q) (hw : 144 ≤ w) (hz : w - 1 < z)
    (hcube : 3 * z ^ 2 ≤ 4 * w ^ 3) (hnonterminal : 2 * (w - q) < z) :
    shelfPotential ((w - q : ℕ) : ℝ) ((z - 2 * (w - q) : ℕ) : ℝ) ≥
      shelfPotential (w : ℝ) (z : ℝ) - 45 * (w : ℝ) ^ 2 := by
  have hq2 : 2 ≤ q := hq.1.1
  have hqhalf : 2 * q ≤ w := hq.1.2.1
  have hqw : q ≤ w := by omega
  have hsq := (hq.bounds hw hcube).1
  have hminimal := hq.minimality_lower hz
  have h44 :=
    shelfPotential_update_ge_sub_44_of_bounds hq2 hqw hsq hminimal hnonterminal
  nlinarith [sq_nonneg (w : ℝ)]

end BurningPath
