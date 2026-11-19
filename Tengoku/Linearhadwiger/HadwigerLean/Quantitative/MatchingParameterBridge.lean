import Tengoku.Linearhadwiger.HadwigerLean.Quantitative.Constants
import Tengoku.Linearhadwiger.HadwigerLean.Quantitative.MatchingApplication

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Compatibility of the matching and Theorem 2 parameters

The matching theorem uses a covering error xi. The rounding step chooses it
as gamma/(4r), making its power-small codegree parameter exactly the mu
already fixed by the paper's final constant calculation.
-/

namespace HadwigerLean.Theorem2

noncomputable def matchingXi (ε : ℝ) : ℝ :=
  gamma ε / (4 * (r ε : ℝ))

/--
@isnad1 id=lt.2h1v.s5.e6aed91205be from=translated src=- shape=91c05246 vocab=f4502224
-/
theorem matchingXi_pos {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    0 < matchingXi ε := by
  have hrN : 0 < r ε := by
    have h := r_ge_four hε hε1
    omega
  have hrpos : 0 < (r ε : ℝ) := by exact_mod_cast hrN
  unfold matchingXi
  exact div_pos (gamma_pos hε) (by positivity)

/--
@isnad1 id=le.2h1v.s5.2c4a1c3809a1 from=translated src=- shape=1317b60f vocab=f4502224
-/
theorem matchingXi_le_one {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    matchingXi ε ≤ 1 := by
  have hr4 : (4 : ℝ) ≤ (r ε : ℝ) := by
    exact_mod_cast r_ge_four hε hε1
  have hrpos : 0 < (r ε : ℝ) := by linarith
  unfold matchingXi gamma
  apply (div_le_iff₀ (by positivity : 0 < 4 * (r ε : ℝ))).2
  nlinarith [hε1]

/--
@isnad1 id=eq.2h1v.s5.2e909112c86d from=translated src=- shape=7fcfc3e1 vocab=fd279342
-/
theorem mu_eq_matchingMu {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    mu ε = matchingMu (r ε) (matchingXi ε) := by
  have hrN : 0 < r ε := by
    have h := r_ge_four hε hε1
    omega
  have hrpos : 0 < (r ε : ℝ) := by exact_mod_cast hrN
  unfold mu matchingMu matchingXi gamma
  congr 1
  field_simp
  ring

/--
@isnad1 id=le.2h2v.s6.d2066a670093 from=translated src=- shape=cce6ebc7 vocab=d094e263
-/
theorem n0_implies_sampling_scale {ε : ℝ} {n : ℕ}
    (hε : 0 < ε) (hn : n0 ε ≤ n) :
    1000000 * (r ε : ℝ) ^ 4 ≤
      (mu ε) ^ 4 * (n : ℝ) := by
  have hμ := mu_pos hε
  have hceil :
      1000000 * (r ε : ℝ) ^ 4 * ((mu ε)⁻¹) ^ 4 + 12 / ε ≤
        (n0 ε : ℝ) := by
    unfold n0
    exact Nat.le_ceil _
  have hnReal : (n0 ε : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hraw :
      1000000 * (r ε : ℝ) ^ 4 * ((mu ε)⁻¹) ^ 4 ≤
        (n : ℝ) := by
    have hpos : 0 ≤ 12 / ε := by positivity
    linarith
  have hcancel : ((mu ε)⁻¹) ^ 4 * (mu ε) ^ 4 = 1 := by
    rw [← mul_pow, inv_mul_cancel₀ (ne_of_gt hμ), one_pow]
  calc
    1000000 * (r ε : ℝ) ^ 4 =
        (1000000 * (r ε : ℝ) ^ 4 * ((mu ε)⁻¹) ^ 4) *
          (mu ε) ^ 4 := by
            rw [mul_assoc, hcancel, mul_one]
    _ ≤ (n : ℝ) * (mu ε) ^ 4 :=
      mul_le_mul_of_nonneg_right hraw (pow_nonneg hμ.le _)
    _ = (mu ε) ^ 4 * (n : ℝ) := by ring

/--
@isnad1 id=le.1h2v.s5.9817dc93cbbf from=translated src=- shape=5e16870a vocab=0df9d9e1
-/
theorem n0_implies_order_bound {ε : ℝ} {n : ℕ}
    (hn : n0 ε ≤ n) :
    12 / ε ≤ (n : ℝ) := by
  have hceil :
      1000000 * (r ε : ℝ) ^ 4 * ((mu ε)⁻¹) ^ 4 + 12 / ε ≤
        (n0 ε : ℝ) := by
    unfold n0
    exact Nat.le_ceil _
  have hnReal : (n0 ε : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnonneg : 0 ≤
      1000000 * (r ε : ℝ) ^ 4 * ((mu ε)⁻¹) ^ 4 := by positivity
  linarith
/--
@isnad1 id=le.3h2v.s6.b1923bedbd92 from=translated src=- shape=2f50ef10 vocab=ad017e5f
-/
theorem matchingXi_vertex_budget {ε : ℝ} {n : ℕ}
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hn : 1 ≤ n) :
    matchingXi ε * ((r ε : ℝ) * (n : ℝ) + 2) ≤
      gamma ε * (n : ℝ) / 2 := by
  have hr4 : (4 : ℝ) ≤ (r ε : ℝ) := by
    exact_mod_cast r_ge_four hε hε1
  have hrpos : 0 < (r ε : ℝ) := by linarith
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hprod : (4 : ℝ) ≤ (r ε : ℝ) * (n : ℝ) := by
    nlinarith [mul_nonneg (by linarith : 0 ≤ (r ε : ℝ) - 4)
      (by linarith : 0 ≤ (n : ℝ) - 1)]
  have hγ := (gamma_pos hε).le
  unfold matchingXi
  calc
    gamma ε / (4 * (r ε : ℝ)) *
        ((r ε : ℝ) * (n : ℝ) + 2) =
      gamma ε * ((r ε : ℝ) * (n : ℝ) + 2) /
        (4 * (r ε : ℝ)) := by ring
    _ ≤ gamma ε * (2 * (r ε : ℝ) * (n : ℝ)) /
        (4 * (r ε : ℝ)) := by
          gcongr
          nlinarith [hprod]
    _ = gamma ε * (n : ℝ) / 2 := by field_simp; ring

/--
@isnad1 id=le.2h2v.s5.26b2539afd05 from=translated src=- shape=7091eb51 vocab=fdbe11b3
-/
theorem n0_implies_gamma_reserve {ε : ℝ} {n : ℕ}
    (hε : 0 < ε) (hn : n0 ε ≤ n) :
    1 ≤ gamma ε * (n : ℝ) / 2 := by
  have horder := n0_implies_order_bound hn
  have hscaled := mul_le_mul_of_nonneg_left horder hε.le
  have hcancel : ε * (12 / ε) = 12 := by field_simp
  rw [hcancel] at hscaled
  unfold gamma
  nlinarith [hscaled]
/--
@isnad1 id=le.4h3v.s6.43c1ca578876 from=translated src=- shape=d1319c3b vocab=ad017e5f
-/
theorem matchingXi_card_budget {ε N : ℝ} {n : ℕ}
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hn : 1 ≤ n)
    (hN : N ≤ (r ε : ℝ) * (n : ℝ) + 2) :
    matchingXi ε * N ≤ gamma ε * (n : ℝ) / 2 := by
  calc
    matchingXi ε * N ≤
        matchingXi ε * ((r ε : ℝ) * (n : ℝ) + 2) :=
      mul_le_mul_of_nonneg_left hN (matchingXi_pos hε hε1).le
    _ ≤ gamma ε * (n : ℝ) / 2 :=
      matchingXi_vertex_budget hε hε1 hn

/--
@isnad1 id=le.2h2v.s5.f1b1df415939 from=translated src=- shape=aee6dd80 vocab=25d94d11
-/
theorem n0_implies_gamma_n_ge_two {ε : ℝ} {n : ℕ}
    (hε : 0 < ε) (hn : n0 ε ≤ n) :
    2 ≤ gamma ε * (n : ℝ) := by
  have h := n0_implies_gamma_reserve hε hn
  linarith
end HadwigerLean.Theorem2
