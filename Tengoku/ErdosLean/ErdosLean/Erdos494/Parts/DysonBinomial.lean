import Tengoku.ErdosLean.ErdosLean.Erdos494.Defs
import Tengoku.ErdosLean.ErdosLean.Erdos494.Parts.AuxPolynomial
import Tengoku.ErdosLean.ErdosLean.Erdos494.Parts.RothLemmaTwo
import Tengoku.ErdosLean.ErdosLean.Erdos494.Parts.TaylorUpperBound
import Tengoku.ErdosLean.ErdosLean.Erdos494.Parts.RationalLowerBound

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # Erdős 494, part D3: a Thue–Siegel–Dyson theorem for `θ = (b/a)^{1/r}`.

`|θ - p/q| < q^{-κ}` has only finitely many solutions when `κ ≥ 10 √r`.  (True by Roth for
every `κ > 2`; we prove the weak exponent `10√r` by Roth's method with **two** variables,
where Roth's lemma has the elementary Wronskian proof.)

Assembly: put `t = 1/(2√r)`, pick `η` with `4√η ≤ t/10`, `η ≤ 1`.  From an
infinite set of solutions extract two reduced solutions `p1/q1`, `p2/q2` with `q1` large and
`log q2 ≥ (2/η) log q1`.  Choose `r1` large and `r2 = ⌈r1 log q1 / log q2⌉`, so that
`16 r ≤ r2 ≤ η r1`, `q1^{r1} ≤ q2^{r2} ≤ q1^{(1+η) r1}`.  `aux_polynomial` gives `c` with
height `K^{r1+r2}` and index `≥ t` at `(θ,θ)`; `roth_lemma_two` gives `(i1,i2)` of weight
`< 4√η` with `D^{(i1,i2)}P(ξ) ≠ 0`; `rational_lower_bound` gives `|D P(ξ)| ≥ q1^{-(2+η) r1}`,
`taylor_upper_bound` with `Λ = q1^{-κ r1}` gives `|D P(ξ)| ≤ C^{r1} q1^{-κ r1 (t - 4√η)}`.
Since `κ (t - 4√η) ≥ 4.5 > 2 + η`, this is absurd for `q1` large. -/

namespace Erdos494

namespace DysonAux

/-- The solution predicate.-/
def Sol (θ κ : ℝ) (pq : ℤ × ℕ) : Prop :=
  0 < pq.2 ∧ (pq.1 : ℝ) / pq.2 ≠ θ ∧ |θ - (pq.1 : ℝ) / pq.2| < (pq.2 : ℝ) ^ (-κ)

/--
@isnad1 id=eq.1h2v.s5.f8877eb454cf from=translated src=- shape=15398880 vocab=5ab3c956
-/
lemma pow_eq_exp (y : ℝ) (hy : 0 < y) (n : ℕ) : y ^ n = Real.exp (n * Real.log y) := by
  rw [Real.exp_nat_mul, Real.exp_log hy]

/--
@isnad1 id=finite.1h2v.s5.4308b2486571 from=translated src=- shape=93b3b03f vocab=aa4eb0ba
-/
lemma box_finite (T : Set (ℤ × ℕ)) (B : ℝ)
    (h : ∀ v ∈ T, |(v.1 : ℝ)| ≤ B ∧ (v.2 : ℝ) ≤ B) : T.Finite := by
  apply ((Set.finite_Icc (-(⌈B⌉₊ : ℤ)) (⌈B⌉₊ : ℤ)).prod (Set.finite_Iic ⌈B⌉₊)).subset
  intro v hv
  obtain ⟨h1, h2⟩ := h v hv
  have h1' : ((|v.1| : ℤ) : ℝ) ≤ ((⌈B⌉₊ : ℤ) : ℝ) := by
    push_cast; exact h1.trans (Nat.le_ceil B)
  have h1'' : |v.1| ≤ (⌈B⌉₊ : ℤ) := by exact_mod_cast h1'
  have h2' : v.2 ≤ ⌈B⌉₊ := by exact_mod_cast h2.trans (Nat.le_ceil B)
  exact Set.mem_prod.mpr ⟨Set.mem_Icc.mpr (abs_le.mp h1''), Set.mem_Iic.mpr h2'⟩

/--
@isnad1 id=le.3h4v.s6.c9f2afd1830a from=translated src=- shape=4f5b6682 vocab=b83b3233
-/
lemma sol_abs_le (θ κ : ℝ) (hκ : 0 ≤ κ) (p : ℤ) (q : ℕ) (hq : 0 < q)
    (h : |θ - (p : ℝ) / q| < (q : ℝ) ^ (-κ)) : |(p : ℝ)| ≤ (|θ| + 1) * q := by
  have hq' : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have h1 : (q : ℝ) ^ (-κ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hq' (by linarith)
  have h2 : |(p : ℝ) / q| ≤ |θ| + 1 := by
    have := abs_sub_abs_le_abs_sub ((p : ℝ) / q) θ
    rw [abs_sub_comm] at this
    linarith
  rw [abs_div, Nat.abs_cast, div_le_iff₀ (by linarith)] at h2
  exact h2

/-- Choice of the degrees `r1, r2`.
@isnad1 id=ex.6h4v.s8.f54446f0a19c from=translated src=- shape=3a2119c3 vocab=26a9ecc4
-/
lemma choose_degrees (r : ℕ) (hr1 : (1 : ℝ) ≤ r) (η L1 L2 : ℝ) (hη0 : 0 < η) (hη1 : η ≤ 1)
    (hηM : η * (12800 * r) = 2) (hL1 : 0 < L1) (hcon : 12800 * (r : ℝ) * L1 ≤ L2) :
    ∃ r1 r2 : ℕ, 16 * r ≤ r2 ∧ r2 ≤ r1 ∧ 1 ≤ r1 ∧ 1 ≤ r2 ∧
      (r1 : ℝ) * L1 ≤ r2 * L2 ∧ (r2 : ℝ) * L2 ≤ 2 * (r1 * L1) ∧ (r2 : ℝ) ≤ η * r1 := by
  have hM1 : (12800 : ℝ) ≤ 12800 * r := by linarith
  have hL2 : 0 < L2 := by
    have := mul_pos (by positivity : (0 : ℝ) < 12800 * r) hL1
    linarith
  set r1 := ⌈12800 * (r : ℝ) * (L2 / L1)⌉₊ with hr1def
  set r2 := ⌈(r1 : ℝ) * L1 / L2⌉₊ with hr2def
  have hρ : 12800 * (r : ℝ) ≤ L2 / L1 := (le_div_iff₀ hL1).mpr hcon
  have hR1 : 12800 * (r : ℝ) * (L2 / L1) ≤ r1 := Nat.le_ceil _
  have hR1L : 12800 * (r : ℝ) * L2 ≤ r1 * L1 := by
    have := mul_le_mul_of_nonneg_right hR1 hL1.le
    rwa [mul_assoc, div_mul_cancel₀ _ hL1.ne'] at this
  have hR1ge : 12800 * (r : ℝ) ≤ r1 := by
    have := mul_le_mul_of_nonneg_left (show (1 : ℝ) ≤ L2 / L1 by linarith)
      (by positivity : (0 : ℝ) ≤ 12800 * r)
    linarith
  have hR2a : (r1 : ℝ) * L1 / L2 ≤ r2 := Nat.le_ceil _
  have hR2b : (r2 : ℝ) < r1 * L1 / L2 + 1 := Nat.ceil_lt_add_one (by positivity)
  have hq12L : (r1 : ℝ) * L1 ≤ r2 * L2 := (div_le_iff₀ hL2).mp hR2a
  have hR2L2 : (r2 : ℝ) * L2 < r1 * L1 + L2 := by
    have := mul_lt_mul_of_pos_right hR2b hL2
    rwa [add_mul, div_mul_cancel₀ _ hL2.ne', one_mul] at this
  have hL2η : L2 ≤ η * (r1 * L1) := by
    have e : η * (12800 * r * L2) = 2 * L2 := by rw [← mul_assoc, hηM]
    have := mul_le_mul_of_nonneg_left hR1L hη0.le
    linarith
  have hR1L1 : 0 ≤ (r1 : ℝ) * L1 := by positivity
  have hupper : (r2 : ℝ) * L2 ≤ 2 * (r1 * L1) := by
    linarith [mul_le_mul_of_nonneg_right hη1 hR1L1]
  have hR2ge : 12800 * (r : ℝ) ≤ r2 := by
    have : 12800 * (r : ℝ) ≤ r1 * L1 / L2 := (le_div_iff₀ hL2).mpr hR1L
    linarith
  have hR2η : (r2 : ℝ) ≤ η * r1 := by
    have hsm : (r1 : ℝ) * L1 / L2 ≤ η * r1 / 2 := by
      rw [div_le_iff₀ hL2]
      have hL1le : L1 ≤ η / 2 * L2 := by
        have := mul_le_mul_of_nonneg_left hcon (by positivity : (0 : ℝ) ≤ η / 2)
        have e : η / 2 * (12800 * r * L1) = L1 := by
          rw [show η / 2 * (12800 * r * L1) = (η * (12800 * r)) / 2 * L1 by ring, hηM]; ring
        linarith
      have := mul_le_mul_of_nonneg_left hL1le (by positivity : (0 : ℝ) ≤ r1)
      linarith
    have hηr1 : 2 ≤ η * r1 := by
      have := mul_le_mul_of_nonneg_left hR1ge hη0.le
      linarith
    linarith
  have hR21 : (r2 : ℝ) ≤ r1 := by
    have := mul_le_mul_of_nonneg_right hη1 (by positivity : (0 : ℝ) ≤ r1)
    linarith
  have h16 : 16 * r ≤ r2 := by
    have : ((16 * r : ℕ) : ℝ) ≤ r2 := by push_cast; linarith
    exact_mod_cast this
  have h21 : r2 ≤ r1 := by exact_mod_cast hR21
  have hr1' : 1 ≤ r1 := by
    have : ((1 : ℕ) : ℝ) ≤ r1 := by push_cast; linarith
    exact_mod_cast this
  have hr2' : 1 ≤ r2 := by
    have : ((1 : ℕ) : ℝ) ≤ r2 := by push_cast; linarith
    exact_mod_cast this
  exact ⟨r1, r2, h16, h21, hr1', hr2', hq12L, hupper, hR2η⟩

/-- The final numerical contradiction.
@isnad1 id=lt.9h8v.s9.66f4decb739a from=translated src=- shape=e8109019 vocab=889a1393
-/
lemma key_lt (r1 r2 q1 q2 : ℕ) (hq1R : (0 : ℝ) < q1) (hq2R : (0 : ℝ) < q2)
    (K θ κ t : ℝ) (hK1 : 1 ≤ K) (hR1pos : (0 : ℝ) < r1) (hR21 : (r2 : ℝ) ≤ r1)
    (hupper : (r2 : ℝ) * Real.log q2 ≤ 2 * (r1 * Real.log q1))
    (hκt : 9 / 2 ≤ κ * t)
    (hL1X : 8 + 4 * (Real.log 8 + Real.log K + Real.log (|θ| + 1)) < 3 * Real.log q1)
    (hL1 : 0 ≤ Real.log q1) :
    (q1 : ℝ) ^ r1 * (q2 : ℝ) ^ r2 *
      (((r1 : ℝ) + 1) ^ 2 * ((r2 : ℝ) + 1) ^ 2 * 8 ^ (r1 + r2) * K ^ (r1 + r2) *
        (|θ| + 1) ^ (r1 + r2) * ((q1 : ℝ) ^ (-(κ * r1))) ^ t) < 1 := by
  have hlogK : 0 ≤ Real.log K := Real.log_nonneg hK1
  have hlog8 : 0 ≤ Real.log 8 := Real.log_nonneg (by norm_num)
  have hlogθ : 0 ≤ Real.log (|θ| + 1) := Real.log_nonneg (by linarith [abs_nonneg θ])
  have hR1L1 : 0 ≤ (r1 : ℝ) * Real.log q1 := mul_nonneg hR1pos.le hL1
  have hb1 : ((r1 : ℝ) + 1) ^ 2 ≤ Real.exp (2 * r1) := by
    rw [show (2 : ℝ) * r1 = ((2 : ℕ) : ℝ) * r1 by norm_num, Real.exp_nat_mul]
    gcongr
    linarith [Real.add_one_le_exp (r1 : ℝ)]
  have hb2 : ((r2 : ℝ) + 1) ^ 2 ≤ Real.exp (2 * r2) := by
    rw [show (2 : ℝ) * r2 = ((2 : ℕ) : ℝ) * r2 by norm_num, Real.exp_nat_mul]
    gcongr
    linarith [Real.add_one_le_exp (r2 : ℝ)]
  rw [pow_eq_exp _ hq1R, pow_eq_exp _ hq2R, pow_eq_exp 8 (by norm_num),
    pow_eq_exp K (by linarith), pow_eq_exp (|θ| + 1) (by positivity),
    ← Real.rpow_mul hq1R.le, Real.rpow_def_of_pos hq1R]
  calc _ ≤ Real.exp (r1 * Real.log q1) * Real.exp (r2 * Real.log q2) *
        (Real.exp (2 * r1) * Real.exp (2 * r2) *
          Real.exp (((r1 + r2 : ℕ) : ℝ) * Real.log 8) *
          Real.exp (((r1 + r2 : ℕ) : ℝ) * Real.log K) *
          Real.exp (((r1 + r2 : ℕ) : ℝ) * Real.log (|θ| + 1)) *
          Real.exp (Real.log q1 * (-(κ * r1) * t))) := by
        gcongr
    _ < 1 := by
        simp only [← Real.exp_add]
        rw [Real.exp_lt_one_iff]
        push_cast
        have e1 := mul_le_mul_of_nonneg_right hR21 hlog8
        have e2 := mul_le_mul_of_nonneg_right hR21 hlogK
        have e3 := mul_le_mul_of_nonneg_right hR21 hlogθ
        have e4 := mul_le_mul_of_nonneg_right hκt hR1L1
        have e5 := mul_lt_mul_of_pos_left hL1X hR1pos
        linarith

end DysonAux

end Erdos494
