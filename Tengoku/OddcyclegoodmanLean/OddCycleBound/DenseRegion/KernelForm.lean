import Tengoku.OddcyclegoodmanLean.OddCycleBound.DenseRegion.MixtureIntegral
import Tengoku.OddcyclegoodmanLean.OddCycleBound.DenseRegion.RhoLemma

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

open MeasureTheory intervalIntegral
open scoped BigOperators

namespace OddCycleBound.DenseRegion

/--
@isnad1 id=eq.0h5v.s8.869a4b33858d from=translated src=- shape=82ec197f vocab=f4860d52
-/
lemma beta_binom_pow (a b : ℕ) (c d : ℝ) (k : ℕ) :
    (∫ x in (0:ℝ)..1, x ^ a * (1 - x) ^ b * (c * x + d * (1 - x)) ^ k)
      = ∑ i ∈ Finset.range (k + 1),
          (Nat.choose k i : ℝ) * c ^ i * d ^ (k - i)
            * ((Nat.factorial (a + i) * Nat.factorial (b + (k - i)) : ℝ)
               / Nat.factorial ((a + i) + (b + (k - i)) + 1)) := by
  have hexp : ∀ x : ℝ, x ^ a * (1 - x) ^ b * (c * x + d * (1 - x)) ^ k
      = ∑ i ∈ Finset.range (k + 1),
          (Nat.choose k i : ℝ) * c ^ i * d ^ (k - i) * (x ^ (a + i) * (1 - x) ^ (b + (k - i))) := by
    intro x
    rw [add_pow, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [Finset.mem_range, Nat.lt_succ_iff] at hi
    have e1 : (c * x) ^ i = c ^ i * x ^ i := mul_pow c x i
    have e2 : (d * (1 - x)) ^ (k - i) = d ^ (k - i) * (1 - x) ^ (k - i) := mul_pow d (1 - x) (k - i)
    have e3 : x ^ (a + i) = x ^ a * x ^ i := pow_add x a i
    have e4 : (1 - x) ^ (b + (k - i)) = (1 - x) ^ b * (1 - x) ^ (k - i) := pow_add (1 - x) b (k - i)
    rw [e1, e2, e3, e4]; ring
  rw [intervalIntegral.integral_congr (fun x _ => hexp x),
    intervalIntegral.integral_finsetSum
      (fun i _ => Continuous.intervalIntegrable (by fun_prop) _ _)]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Finset.mem_range, Nat.lt_succ_iff] at hi
  rw [intervalIntegral.integral_const_mul, beta_nat (a + i) (b + (k - i))]

/--
@isnad1 id=eq.0h5v.s8.b68c235c1eef from=translated src=- shape=bb5f7183 vocab=95987e96
-/
lemma beta_hsym (a b : ℕ) (c d : ℝ) (k : ℕ) :
    (∫ x in (0:ℝ)..1, x ^ a * (1 - x) ^ b * (c * x + d * (1 - x)) ^ k)
      = (Nat.factorial a * Nat.factorial b * Nat.factorial k : ℝ) / Nat.factorial (a + b + k + 1)
        * hsym (List.replicate (a + 1) c ++ List.replicate (b + 1) d) k := by
  rw [beta_binom_pow a b c d k, hsym_replicate_append_replicate c d b a k, Finset.mul_sum]
  conv_rhs => rw [← Finset.sum_range_reflect]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [Finset.mem_range, Nat.lt_succ_iff] at hj
  rw [show k + 1 - 1 - j = k - j from by omega]

  have ha : (Nat.choose (j + a) a : ℝ) * Nat.factorial a * Nat.factorial j = Nat.factorial (a + j) := by
    have h := Nat.choose_mul_factorial_mul_factorial (Nat.le_add_left a j)
    rw [Nat.add_sub_cancel] at h
    rw [show a + j = j + a from by ring]; exact_mod_cast h
  have hb : (Nat.choose (k - j + b) b : ℝ) * Nat.factorial b * Nat.factorial (k - j)
      = Nat.factorial (b + (k - j)) := by
    have h := Nat.choose_mul_factorial_mul_factorial (Nat.le_add_left b (k - j))
    rw [Nat.add_sub_cancel] at h
    rw [show b + (k - j) = k - j + b from by ring]; exact_mod_cast h
  have hk : (Nat.choose k j : ℝ) * Nat.factorial j * Nat.factorial (k - j) = Nat.factorial k := by
    have h := Nat.choose_mul_factorial_mul_factorial hj
    exact_mod_cast h
  have key : (Nat.choose k j : ℝ) * Nat.factorial (a + j) * Nat.factorial (b + (k - j))
      = Nat.factorial a * Nat.factorial b * Nat.factorial k
        * (Nat.choose (j + a) a : ℝ) * (Nat.choose (k - j + b) b : ℝ) := by
    rw [← ha, ← hb, ← hk]; ring
  rw [show k - (k - j) = j from by omega]
  rw [show (a + j) + (b + (k - j)) + 1 = a + b + k + 1 from by omega]
  have hne : (Nat.factorial (a + b + k + 1) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  field_simp
  linear_combination (c ^ j * d ^ (k - j)) * key

noncomputable def Cmr (m r : ℕ) : ℝ :=
  (Nat.choose (m - 1) (2 * r - 1) : ℝ) * ((m - 2 * r : ℕ) : ℝ) / (r : ℝ)
    * (Nat.factorial (2 * r - 1) : ℝ) / (Nat.factorial (r - 1) : ℝ) ^ 2

private lemma choose_fact_cancel {m r : ℕ} (hr : r ≠ 0) (hn : 1 ≤ m - 2 * r) :
    (Nat.choose (m - 1) (2 * r - 1) : ℝ) * Nat.factorial (2 * r - 1) * Nat.factorial (m - 2 * r)
      = Nat.factorial (m - 1) := by
  have h := Nat.choose_mul_factorial_mul_factorial (show 2 * r - 1 ≤ m - 1 from by omega)
  rw [show m - 1 - (2 * r - 1) = m - 2 * r from by omega] at h
  exact_mod_cast h

/--
@isnad1 id=eq.2h2v.s7.2817e93b04ce from=translated src=- shape=5cca325a vocab=756ef923
-/
lemma Cmr_K_eq {m r : ℕ} (hr : r ≠ 0) (hn : 1 ≤ m - 2 * r) :
    Cmr m r * ((m : ℝ) / ((m - 2 * r : ℕ) : ℝ))
        * ((Nat.factorial (r - 1) * Nat.factorial (r - 1) * Nat.factorial (m - 2 * r) : ℝ)
           / Nat.factorial (m - 1))
      = (m : ℝ) / r := by
  have hchoose := choose_fact_cancel (m := m) (r := r) hr hn
  have hnR : ((m - 2 * r : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hrR : (r : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hr
  have hm1 : (Nat.factorial (m - 1) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hr1f : (Nat.factorial (r - 1) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  unfold Cmr
  field_simp
  linear_combination (m : ℝ) * hchoose

/--
@isnad1 id=eq.2h2v.s7.267d495f8582 from=translated src=- shape=65543e81 vocab=756ef923
-/
lemma Cmr_K3_eq {m r : ℕ} (hr : r ≠ 0) (hn : 1 ≤ m - 2 * r) :
    Cmr m r * ((Nat.factorial r * Nat.factorial (r - 1) * Nat.factorial (m - 2 * r - 1) : ℝ)
        / Nat.factorial (m - 1))
      = 1 := by
  have hchoose := choose_fact_cancel (m := m) (r := r) hr hn
  have hnR : ((m - 2 * r : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hrR : (r : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hr
  have hm1 : (Nat.factorial (m - 1) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hr1f : (Nat.factorial (r - 1) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hrfac : (Nat.factorial r : ℝ) = (r : ℝ) * Nat.factorial (r - 1) := by
    exact_mod_cast (Nat.mul_factorial_pred (show r ≠ 0 from hr)).symm
  have hnfac : (Nat.factorial (m - 2 * r) : ℝ) = ((m - 2 * r : ℕ) : ℝ) * Nat.factorial (m - 2 * r - 1) := by
    exact_mod_cast (Nat.mul_factorial_pred (show m - 2 * r ≠ 0 from by omega)).symm
  unfold Cmr
  rw [hnfac] at hchoose
  rw [hrfac]
  field_simp
  linear_combination hchoose

/--
@isnad1 id=eq.2h4v.s8.9be94c1835fb from=translated src=- shape=24088e16 vocab=3ec29abe
-/
lemma gform_eq {m r : ℕ} (hr : r ≠ 0) (hn : 1 ≤ m - 2 * r) (q ℓ : ℝ) :
    diagKernel m r q ℓ
      = Cmr m r * ∫ x in (0:ℝ)..1, x ^ (r - 1) * (1 - x) ^ (r - 1)
          * (((m : ℝ) / ((m - 2 * r : ℕ) : ℝ))
              * ((q * x + ℓ * (1 - x)) ^ (m - 2 * r) + ((1 - q) * x + (-ℓ) * (1 - x)) ^ (m - 2 * r))
            - x * (q * x + ℓ * (1 - x)) ^ (m - 2 * r - 1)) := by
  have hr1 : 1 ≤ r := Nat.one_le_iff_ne_zero.mpr hr
  have hG1 : (∫ x in (0:ℝ)..1, x ^ (r - 1) * (1 - x) ^ (r - 1) * (q * x + ℓ * (1 - x)) ^ (m - 2 * r))
      = (Nat.factorial (r - 1) * Nat.factorial (r - 1) * Nat.factorial (m - 2 * r) : ℝ)
          / Nat.factorial (m - 1)
        * hsym (List.replicate r q ++ List.replicate r ℓ) (m - 2 * r) := by
    rw [beta_hsym (r - 1) (r - 1) q ℓ (m - 2 * r), show r - 1 + 1 = r from by omega,
      show (r - 1) + (r - 1) + (m - 2 * r) + 1 = m - 1 from by omega]
  have hG2 : (∫ x in (0:ℝ)..1, x ^ (r - 1) * (1 - x) ^ (r - 1)
        * ((1 - q) * x + (-ℓ) * (1 - x)) ^ (m - 2 * r))
      = (Nat.factorial (r - 1) * Nat.factorial (r - 1) * Nat.factorial (m - 2 * r) : ℝ)
          / Nat.factorial (m - 1)
        * hsym (List.replicate r (1 - q) ++ List.replicate r (-ℓ)) (m - 2 * r) := by
    rw [beta_hsym (r - 1) (r - 1) (1 - q) (-ℓ) (m - 2 * r), show r - 1 + 1 = r from by omega,
      show (r - 1) + (r - 1) + (m - 2 * r) + 1 = m - 1 from by omega]
  have hG3 : (∫ x in (0:ℝ)..1, x ^ r * (1 - x) ^ (r - 1) * (q * x + ℓ * (1 - x)) ^ (m - 2 * r - 1))
      = (Nat.factorial r * Nat.factorial (r - 1) * Nat.factorial (m - 2 * r - 1) : ℝ)
          / Nat.factorial (m - 1)
        * hsym (List.replicate (r + 1) q ++ List.replicate r ℓ) (m - 2 * r - 1) := by
    rw [beta_hsym r (r - 1) q ℓ (m - 2 * r - 1), show r - 1 + 1 = r from by omega,
      show r + (r - 1) + (m - 2 * r - 1) + 1 = m - 1 from by omega]
  have hpt : Set.EqOn
      (fun x => x ^ (r - 1) * (1 - x) ^ (r - 1)
        * (((m : ℝ) / ((m - 2 * r : ℕ) : ℝ))
            * ((q * x + ℓ * (1 - x)) ^ (m - 2 * r) + ((1 - q) * x + (-ℓ) * (1 - x)) ^ (m - 2 * r))
          - x * (q * x + ℓ * (1 - x)) ^ (m - 2 * r - 1)))
      (fun x => ((m : ℝ) / ((m - 2 * r : ℕ) : ℝ)) * (x ^ (r - 1) * (1 - x) ^ (r - 1)
            * (q * x + ℓ * (1 - x)) ^ (m - 2 * r))
          + ((m : ℝ) / ((m - 2 * r : ℕ) : ℝ)) * (x ^ (r - 1) * (1 - x) ^ (r - 1)
            * ((1 - q) * x + (-ℓ) * (1 - x)) ^ (m - 2 * r))
          - x ^ r * (1 - x) ^ (r - 1) * (q * x + ℓ * (1 - x)) ^ (m - 2 * r - 1))
      (Set.uIcc 0 1) := by
    intro x _
    dsimp only
    rw [show x ^ r = x ^ (r - 1) * x from by rw [← pow_succ, Nat.sub_add_cancel hr1]]
    ring
  rw [intervalIntegral.integral_congr hpt,
    intervalIntegral.integral_sub
      (Continuous.intervalIntegrable (by fun_prop) _ _)
      (Continuous.intervalIntegrable (by fun_prop) _ _),
    intervalIntegral.integral_add
      (Continuous.intervalIntegrable (by fun_prop) _ _)
      (Continuous.intervalIntegrable (by fun_prop) _ _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    hG1, hG2, hG3]
  unfold diagKernel
  linear_combination
    (-(hsym (List.replicate r q ++ List.replicate r ℓ) (m - 2 * r))
      - hsym (List.replicate r (1 - q) ++ List.replicate r (-ℓ)) (m - 2 * r)) * Cmr_K_eq hr hn
    + hsym (List.replicate (r + 1) q ++ List.replicate r ℓ) (m - 2 * r - 1) * Cmr_K3_eq hr hn

/--
@isnad1 id=lt.2h2v.s5.00ed363468bd from=translated src=- shape=cc55dc97 vocab=ce5c8346
-/
lemma Cmr_pos {m r : ℕ} (hr : r ≠ 0) (hn : 1 ≤ m - 2 * r) : 0 < Cmr m r := by
  have hc : 0 < (Nat.choose (m - 1) (2 * r - 1) : ℝ) :=
    mod_cast Nat.choose_pos (show 2 * r - 1 ≤ m - 1 from by omega)
  have hn0 : 0 < ((m - 2 * r : ℕ) : ℝ) := mod_cast (show 0 < m - 2 * r from by omega)
  have hr0 : 0 < (r : ℝ) := mod_cast Nat.pos_of_ne_zero hr
  have hf1 : 0 < (Nat.factorial (2 * r - 1) : ℝ) := mod_cast Nat.factorial_pos _
  have hf2 : 0 < (Nat.factorial (r - 1) : ℝ) := mod_cast Nat.factorial_pos _
  unfold Cmr
  exact div_pos (mul_pos (div_pos (mul_pos hc hn0) hr0) hf1) (by positivity)

/--
@isnad1 id=eq.2h5v.s8.26a8c9d2fed4 from=translated src=- shape=7defcd7c vocab=a4154407
-/
lemma bracket_eq_rho {m r : ℕ} (hn : 1 ≤ m - 2 * r) (q ℓ x : ℝ) (hx : x ≠ 0) :
    ((m : ℝ) / ((m - 2 * r : ℕ) : ℝ))
        * ((q * x + ℓ * (1 - x)) ^ (m - 2 * r) + ((1 - q) * x + (-ℓ) * (1 - x)) ^ (m - 2 * r))
      - x * (q * x + ℓ * (1 - x)) ^ (m - 2 * r - 1)
      = x ^ (m - 2 * r) * rho (m - 2 * r) m ((q * x + ℓ * (1 - x)) / x) := by
  set n := m - 2 * r with hndef
  have hn1 : 1 ≤ n := hn
  have h1 : x ^ n * ((q * x + ℓ * (1 - x)) / x) ^ n = (q * x + ℓ * (1 - x)) ^ n := by
    rw [div_pow]; field_simp
  have h2 : x ^ n * (1 - (q * x + ℓ * (1 - x)) / x) ^ n = ((1 - q) * x + (-ℓ) * (1 - x)) ^ n := by
    rw [show (1 : ℝ) - (q * x + ℓ * (1 - x)) / x = ((1 - q) * x + (-ℓ) * (1 - x)) / x from by
      field_simp; ring, div_pow]; field_simp
  have h3 : x ^ n * ((q * x + ℓ * (1 - x)) / x) ^ (n - 1) = x * (q * x + ℓ * (1 - x)) ^ (n - 1) := by
    rw [div_pow, show x ^ n = x ^ (n - 1) * x from by rw [← pow_succ, Nat.sub_add_cancel hn1]]
    field_simp
  rw [rho, show x ^ n * ((m / (n : ℝ)) * (((q * x + ℓ * (1 - x)) / x) ^ n
        + (1 - (q * x + ℓ * (1 - x)) / x) ^ n) - ((q * x + ℓ * (1 - x)) / x) ^ (n - 1))
      = (m / (n : ℝ)) * (x ^ n * ((q * x + ℓ * (1 - x)) / x) ^ n
          + x ^ n * (1 - (q * x + ℓ * (1 - x)) / x) ^ n)
        - x ^ n * ((q * x + ℓ * (1 - x)) / x) ^ (n - 1) from by ring, h1, h2, h3]

/--
@isnad1 id=le.3h5v.s7.f99f9ec82330 from=translated src=- shape=967c4aaf vocab=8ba776ab
-/
lemma diagKernel_nonneg_of_rho {m r t : ℕ} (hr : r ≠ 0) (ht : m - 2 * r = 2 * t + 1) (q ℓ : ℝ)
    (hrho : ∀ x, 0 < x → x ≤ 1 → 0 ≤ rho (2 * t + 1) m ((q * x + ℓ * (1 - x)) / x)) :
    0 ≤ diagKernel m r q ℓ := by
  have hn : 1 ≤ m - 2 * r := by omega
  rw [gform_eq hr hn]
  apply mul_nonneg (le_of_lt (Cmr_pos hr hn))
  apply intervalIntegral.integral_nonneg (by norm_num : (0:ℝ) ≤ 1)
  intro x hx
  refine mul_nonneg (mul_nonneg (pow_nonneg hx.1 _) (pow_nonneg (by linarith [hx.2]) _)) ?_
  rcases eq_or_lt_of_le hx.1 with hx0 | hx0
  · rw [← hx0, ht]
    rw [show q * (0:ℝ) + ℓ * (1 - 0) = ℓ from by ring,
      show (1 - q) * (0:ℝ) + (-ℓ) * (1 - 0) = -ℓ from by ring, Odd.neg_pow ⟨t, by ring⟩]
    apply le_of_eq; ring
  · rw [bracket_eq_rho hn q ℓ x (ne_of_gt hx0), ht]
    exact mul_nonneg (pow_nonneg (le_of_lt hx0) _) (hrho x hx0 hx.2)

/--
@isnad1 id=le.3h5v.s6.61f55ee45590 from=translated src=- shape=74df34bc vocab=ea1ef95a
-/
theorem diagKernel_nonneg_two_r_ge {m r t : ℕ} (hr : r ≠ 0) (ht : m - 2 * r = 2 * t + 1)
    (h2r : 2 * t + 1 ≤ 2 * r) (q ℓ : ℝ) : 0 ≤ diagKernel m r q ℓ := by
  refine diagKernel_nonneg_of_rho hr ht q ℓ (fun x _ _ => ?_)
  exact rho_empty t m (by exact_mod_cast (show 2 * (2 * t + 1) ≤ m from by omega)) _

/--
@isnad1 id=le.4h5v.s6.3bff0fbb8d38 from=translated src=- shape=f881079a vocab=40f4c799
-/
theorem diagKernel_nonneg_le_zero {m r t : ℕ} (hr : r ≠ 0) (ht : m - 2 * r = 2 * t + 1)
    (q ℓ : ℝ) (hq : q ≤ 1 / 2) (hl : ℓ ≤ 0) : 0 ≤ diagKernel m r q ℓ := by
  refine diagKernel_nonneg_of_rho hr ht q ℓ (fun x hx0 hx1 => ?_)
  apply rho_window_left t m (by exact_mod_cast (show 2 * t + 1 ≤ m from by omega))
  rw [div_le_iff₀ hx0]
  nlinarith [mul_nonneg (le_of_lt hx0) (by linarith : (0:ℝ) ≤ 1 / 2 - q),
    mul_nonpos_of_nonpos_of_nonneg hl (by linarith : (0:ℝ) ≤ 1 - x)]

end OddCycleBound.DenseRegion
