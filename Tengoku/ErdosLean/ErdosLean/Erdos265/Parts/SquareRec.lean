import Tengoku.ErdosLean.ErdosLean.Erdos265.Parts.DiffTail

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Erdős #265 — Part U3: the square recurrence for the tail envelope

With `Henv n = P n / √(Dt n)` and `1 ≤ K P_n² D_n` (Part U2):
`Henv (n+1) ≤ 4 √K · Henv n ²`.  Two cases, `D = Dt n`, `D' = Dt (n+1)`, `x = a_n`:
* head dominates (`D/2 ≤ 1/(x(x-1))`): `x² ≤ 4/D`, and `1/√D' ≤ √K · P x`, so
  `P x / √D' ≤ √K P² x² ≤ 4√K P²/D`;
* tail dominates: `D' ≥ D/2`, and `x ≤ 1 + 1/D ≤ 2/D` (from `D ≤ 1/(x-1)`, `D ≤ 1`),
  `1/√D ≤ √K P`, so `P x/√D' ≤ √2 P x/√D ≤ 2√2 P/ D^{3/2} ≤ 4√K P²/D`.
Also `Henv n ≥ P n ≥ 1` since `Dt n ≤ 1`.

In the formal proof we square everything: the key inequality is `x² D² ≤ 16 K P² D'`
(`sq_rec_key`), from which `Henv (n+1)² ≤ (4√K · Henv n²)²`.
-/

open Filter Topology

namespace Erdos265

variable {a : ℕ → ℕ}

/-- `1 ≤ P n` (all factors are `≥ 2`).
@isnad1 id=le.1h2v.s4.d8d0fab6b7da from=translated src=- shape=4bf9a2ff vocab=76e85c7b
-/
theorem one_le_P_real (ha : IsRationalPair a) (n : ℕ) : (1 : ℝ) ≤ (P a n : ℝ) := by
  have : 1 ≤ P a n := by
    unfold P
    rw [Nat.one_le_iff_ne_zero, Finset.prod_ne_zero_iff]
    intro k _
    have := two_le_of ha k
    omega
  exact_mod_cast this

/--
@isnad1 id=eq.0h2v.s5.1e9aad0344b9 from=translated src=- shape=c9f212c2 vocab=223d9f1b
-/
theorem P_succ_real (n : ℕ) : (P a (n + 1) : ℝ) = (P a n : ℝ) * (a n : ℝ) := by
  unfold P
  rw [Finset.prod_range_succ]
  push_cast
  ring

/-- `Dt n ≤ 1`.
@isnad1 id=le.1h2v.s4.ff5f2c295b11 from=translated src=- shape=fa5a9ae9 vocab=04e85f64
-/
theorem Dt_le_one (ha : IsRationalPair a) (n : ℕ) : Dt a n ≤ 1 := by
  have h1 := Dt_le ha n
  have h2 : (2 : ℝ) ≤ (a n : ℝ) := by exact_mod_cast two_le_of ha n
  have h3 : 1 / ((a n : ℝ) - 1) ≤ 1 := by
    rw [div_le_one (by linarith)]; linarith
  linarith

/--
@isnad1 id=le.1h2v.s4.b73a50890f74 from=translated src=- shape=95bcf7d0 vocab=f059c6d7
-/
theorem one_le_Henv (ha : IsRationalPair a) (n : ℕ) : 1 ≤ Henv a n := by
  unfold Henv
  have hD := Dt_pos ha n
  have hs : 0 < Real.sqrt (Dt a n) := Real.sqrt_pos.mpr hD
  have hs1 : Real.sqrt (Dt a n) ≤ 1 := by
    rw [Real.sqrt_le_one]; exact Dt_le_one ha n
  have hP := one_le_P_real ha n
  rw [le_div_iff₀ hs]
  nlinarith

/-- The real-arithmetic core of the square recurrence.
@isnad1 id=le.6h4v.s7.1916feda8511 from=translated src=- shape=0ef26199 vocab=762a6581
-/
theorem sq_rec_key (X D D' Q : ℝ) (hX : 2 ≤ X) (hD : D = 1 / (X * (X - 1)) + D')
    (hD' : 0 < D') (hle : D ≤ 1 / (X - 1)) (h1 : 1 ≤ Q * D) (h2 : 1 ≤ Q * X ^ 2 * D') :
    X ^ 2 * D ^ 2 ≤ 16 * Q * D' := by
  have hX1 : 0 < X - 1 := by linarith
  have hXX : 0 < X * (X - 1) := by positivity
  set h := 1 / (X * (X - 1)) with hh
  have hpos : 0 < h := by positivity
  have hhX : h * (X * (X - 1)) = 1 := by rw [hh]; field_simp
  have hDpos : 0 < D := by linarith
  have hQ : 0 < Q := by
    by_contra hc; push Not at hc; nlinarith
  rcases le_or_gt D' h with hc | hc
  · -- head dominates
    have hD2 : D ≤ 2 * h := by linarith
    -- X² h ≤ 2
    have hXh : X ^ 2 * h ≤ 2 := by nlinarith
    -- X² D² ≤ 4 X² h² ≤ 8 h ; and X² h ≤ 2, so X^2 * (8h) ≤ 16
    have e1 : X ^ 2 * D ^ 2 ≤ 4 * (X ^ 2 * h) * h := by
      have : D ^ 2 ≤ (2 * h) ^ 2 := by
        apply pow_le_pow_left₀ hDpos.le hD2
      nlinarith [sq_nonneg X]
    have e2 : X ^ 2 * D ^ 2 ≤ 8 * h := by nlinarith
    -- 8 h X² ≤ 16 ≤ 16 Q X² D'
    have e3 : X ^ 2 * (8 * h) ≤ X ^ 2 * (16 * Q * D') := by nlinarith
    have hX2 : 0 < X ^ 2 := by positivity
    have e4 : 8 * h ≤ 16 * Q * D' := le_of_mul_le_mul_left e3 hX2
    linarith
  · -- tail dominates
    have hD2 : D ≤ 2 * D' := by linarith
    have hle' : D * (X - 1) ≤ 1 := by
      have := mul_le_mul_of_nonneg_right hle hX1.le
      rwa [div_mul_cancel₀ _ hX1.ne'] at this
    have hD1 : D ≤ 1 := by nlinarith
    have hXD : X * D ≤ 2 := by nlinarith
    have hXD0 : 0 ≤ X * D := by positivity
    have e1 : X ^ 2 * D ^ 2 ≤ 4 := by nlinarith
    nlinarith

end Erdos265
