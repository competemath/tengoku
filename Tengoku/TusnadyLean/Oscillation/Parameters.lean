import Tengoku.Seed.Analysis.SpecialFunctions.Log.Base
import Tengoku.Seed.Analysis.Complex.ExponentialBounds
import Tengoku.Seed.Data.Nat.Find
import Tengoku.Seed.Tactic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Integer scale selection for the finite-oscillation proof. -/
namespace Oscillation.Parameters
noncomputable section

def Admissible (b : ℝ) (n k : ℕ) : Prop :=
  (k + 1 : ℝ) * b ^ k / b ^ 5 ≤ n

/--
@isnad1 id=ex.2h2v.s5.2185d83de43d from=translated src=- shape=9c375137 vocab=917f3421
-/
theorem exists_maximal_scale {b : ℝ} (hb : 2 ≤ b) (n : ℕ) (hn : 1 ≤ n) :
    ∃ k, Admissible b n k ∧ ∀ m, Admissible b n m → m ≤ k := by
  classical
  have hbp : 0 < b := by linarith
  obtain ⟨B, hB⟩ := exists_nat_gt ((n : ℝ) * b ^ 5)
  have hbound : ∀ m, Admissible b n m → m ≤ B := by
    intro m hm
    have hpow : (1 : ℝ) ≤ b ^ m := one_le_pow₀ (by linarith)
    have hmR : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    have hl : (m : ℝ) ≤ (m + 1) * b ^ m := by nlinarith
    have hhm : (m + 1 : ℝ) * b ^ m ≤ n * b ^ 5 :=
      (div_le_iff₀ (by positivity)).mp hm
    have : (m : ℝ) < B := lt_of_le_of_lt (hl.trans hhm) hB
    exact (by exact_mod_cast this : m < B).le
  have hzero : Admissible b n 0 := by
    have hp : (1 : ℝ) ≤ b ^ 5 := one_le_pow₀ (by linarith)
    have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
    simp only [Admissible, Nat.cast_zero, zero_add, pow_zero, one_mul]
    exact (div_le_one (by positivity)).mpr hp |>.trans hnR
  refine ⟨Nat.findGreatest (Admissible b n) B,
    Nat.findGreatest_spec (Nat.zero_le B) hzero, ?_⟩
  intro m hm
  exact Nat.le_findGreatest (hbound m hm) hm

/--
@isnad1 id=and.3h3v.s7.af6a1b1f01f8 from=translated src=- shape=16883cb3 vocab=d69f5a22
-/
theorem maximal_scale_bounds {b : ℝ} (hb : 2 ≤ b) {n k : ℕ}
    (hk : Admissible b n k) (hmax : ∀ m, Admissible b n m → m ≤ k) :
    (k + 1 : ℝ) * b ^ k / b ^ 5 ≤ n ∧
    (n : ℝ) < 2 * (k + 1 : ℝ) * b ^ k / b ^ 4 := by
  have hbp : 0 < b := by linarith
  have hnxt : (n : ℝ) < (k + 2 : ℝ) * b ^ (k + 1) / b ^ 5 := by
    by_contra hh
    have ha : Admissible b n (k + 1) := by
      unfold Admissible
      norm_num [Nat.cast_add, Nat.cast_one, add_assoc] at *
      exact hh
    have := hmax (k + 1) ha
    omega
  refine ⟨hk, hnxt.trans_le ?_⟩
  have hr : (k + 2 : ℝ) ≤ 2 * (k + 1 : ℝ) := by have := Nat.cast_nonneg (α := ℝ) k; linarith
  have hrewrite : (k + 2 : ℝ) * b ^ (k + 1) / b ^ 5 =
      (k + 2 : ℝ) * b ^ k / b ^ 4 := by
    rw [pow_succ]
    field_simp
  rw [hrewrite]
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hr (by positivity))
    (by positivity)

/--
@isnad1 id=le.3h3v.s6.9b04cbfeb36a from=translated src=- shape=175918c5 vocab=fdcb2b3e
-/
lemma density_bound {b : ℝ} (hb : 8 ≤ b) {n k : ℕ}
    (hk : Admissible b n k) (hmax : ∀ m, Admissible b n m → m ≤ k) :
    (n : ℝ) ≤ (k + 1 : ℝ) * b ^ k / (4 * b ^ 3) := by
  have hbp : 0 < b := by linarith
  apply (maximal_scale_bounds (by linarith) hk hmax).2.le.trans
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  have hnon : 0 ≤ (k + 1 : ℝ) * b ^ k * b ^ 3 := by positivity
  nlinarith [mul_nonneg hnon (sub_nonneg.mpr hb)]

/--
@isnad1 id=lt.3h3v.s6.4c551a9e3029 from=translated src=- shape=049b054d vocab=a08a5faa
-/
lemma logarithmic_scale {L n k : ℕ} (_hL : 1 ≤ L) (hn : 1 ≤ n)
    (hmax : ∀ m, Admissible ((2 : ℝ) ^ L) n m → m ≤ k) :
    Real.logb 2 (n : ℝ) < (L + 1 : ℝ) * (k + 1 : ℝ) := by
  let b : ℝ := 2 ^ L
  have hb : 1 ≤ b := one_le_pow₀ (by norm_num)
  have hbp : 0 < b := by dsimp [b]; positivity
  have hnxt : (n : ℝ) < (k + 2 : ℝ) * b ^ (k + 1) / b ^ 5 := by
    by_contra hh
    have ha : Admissible b n (k + 1) := by
      unfold Admissible
      norm_num [Nat.cast_add, Nat.cast_one, add_assoc] at *
      exact hh
    have := hmax (k + 1) ha
    omega
  have hpow : (k + 2 : ℝ) ≤ (2 : ℝ) ^ (k + 1) := by
    exact_mod_cast Nat.lt_two_pow_self (n := k + 1)
  have hnPow : (n : ℝ) < (2 : ℝ) ^ ((L + 1) * (k + 1)) := by
    calc
      (n : ℝ) < (k + 2 : ℝ) * b ^ (k + 1) / b ^ 5 := hnxt
      _ ≤ (k + 2 : ℝ) * b ^ (k + 1) :=
        div_le_self (by positivity) (one_le_pow₀ hb)
      _ ≤ (2 : ℝ) ^ (k + 1) * b ^ (k + 1) := by gcongr
      _ = (2 : ℝ) ^ ((L + 1) * (k + 1)) := by
        dsimp [b]
        rw [← pow_mul, ← pow_add]
        congr 1
        ring
  have hlog := Real.logb_lt_logb (by norm_num : (1 : ℝ) < 2)
    (by exact_mod_cast (by omega : 0 < n)) hnPow
  simpa [Real.logb_pow] using hlog

/--
@isnad1 id=ex.0h1v.s5.76eec0a0aa38 from=translated src=- shape=a00371cc vocab=c0715d49
-/
theorem exists_base (A : ℝ) : ∃ L : ℕ, 4 ≤ L ∧ 4 * (A + 5) ≤ (L : ℝ) := by
  obtain ⟨L, hL⟩ := exists_nat_ge (max (4 : ℝ) (4 * (A + 5)))
  exact ⟨L, by exact_mod_cast (le_max_left _ _).trans hL,
    (le_max_right _ _).trans hL⟩

/--
@isnad1 id=le.2h2v.s7.1fcf0820c20e from=translated src=- shape=4a3586e7 vocab=253be381
-/
lemma failure_exponent {A : ℝ} (hA : 0 < A) {L : ℕ}
    (hL : 4 * (A + 5) ≤ (L : ℝ)) :
    A + Real.log 2 ≤ Real.log ((2 : ℝ) ^ L) / 2 - 2 * Real.log 2 - 5 / 4 := by
  rw [Real.log_pow]
  have hlo : (2 / 3 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hhi : Real.log 2 ≤ 1 := by linarith [Real.log_two_lt_d9]
  nlinarith [mul_nonneg (show 0 ≤ (L : ℝ) / 2 - 3 by linarith)
    (sub_nonneg.mpr hlo)]

/--
@isnad1 id=eq.0h2v.s6.372facb01898 from=translated src=- shape=cdf63806 vocab=5da60944
-/
lemma coloring_union (A : ℝ) (n : ℕ) :
    (2 : ℝ) ^ n * Real.exp (-(A + Real.log 2) * n) = Real.exp (-A * n) := by
  have hpow : (2 : ℝ) ^ n = Real.exp ((n : ℝ) * Real.log 2) := by
    rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]
  rw [hpow, ← Real.exp_add]
  congr 1
  ring

/--
@isnad1 id=eq.1h1v.s5.7084401c3967 from=translated src=- shape=4d639000 vocab=72659d50
-/
lemma rpow_three_halves (x : ℝ) (hx : 0 ≤ x) :
    x ^ (3 / 2 : ℝ) = x * Real.sqrt x := by
  rcases hx.eq_or_lt with h | h
  · subst x; norm_num
  · rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num,
      Real.rpow_add h, Real.rpow_one, ← Real.sqrt_eq_rpow]

/-- A positive constant sufficient for the existential main theorem.-/
def thresholdConstant (b : ℝ) (L : ℕ) : ℝ :=
  (1 / (b ^ 5 * (L + 1 : ℝ))) ^ (3 / 2 : ℝ) / 8

/--
@isnad1 id=lt.1h2v.s4.4642632263eb from=translated src=- shape=9141f3a7 vocab=7efb9027
-/
lemma thresholdConstant_pos {b : ℝ} (hb : 0 < b) (L : ℕ) :
    0 < thresholdConstant b L := by unfold thresholdConstant; positivity

/--
@isnad1 id=eq.2h3v.s7.92d6c7f6a208 from=translated src=- shape=7d9722d5 vocab=8e90cfc8
-/
lemma threshold_rewrite {b : ℝ} (hb : 0 < b) (L : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    thresholdConstant b L * x ^ (3 / 2 : ℝ) =
      (x / (b ^ 5 * (L + 1 : ℝ))) ^ (3 / 2 : ℝ) / 8 := by
  unfold thresholdConstant
  rw [div_mul_eq_mul_div, ← Real.mul_rpow (by positivity) hx]
  congr 2
  ring

/--
@isnad1 id=le.4h5v.s7.f13f5863ca94 from=translated src=- shape=ef7aa80b vocab=51baca97
-/
lemma threshold_below_scale {b : ℝ} (hb : 2 ≤ b) {L n k : ℕ} {x : ℝ}
    (hx : 0 ≤ x) (hxk : x ≤ (L + 1 : ℝ) * (k + 1 : ℝ))
    (hk : Admissible b n k) :
    thresholdConstant b L * x ^ (3 / 2 : ℝ) ≤
      (n : ℝ) * Real.sqrt (k + 1 : ℝ) / (8 * b ^ k) := by
  have hbp : 0 < b := by linarith
  have hB : 0 < b ^ 5 := by positivity
  have hL : 0 < (L + 1 : ℝ) := by positivity
  have hxdiv : x / (b ^ 5 * (L + 1 : ℝ)) ≤ (k + 1 : ℝ) / b ^ 5 := by
    apply (div_le_div_iff₀ (mul_pos hB hL) hB).mpr
    nlinarith [mul_le_mul_of_nonneg_right hxk hB.le]
  have hδ : (1 : ℝ) ≤ b ^ 5 := one_le_pow₀ (by linarith)
  have hy : 0 ≤ (k + 1 : ℝ) / b ^ 5 := by positivity
  have hroot : Real.sqrt ((k + 1 : ℝ) / b ^ 5) ≤ Real.sqrt (k + 1 : ℝ) :=
    Real.sqrt_le_sqrt (div_le_self (by positivity) hδ)
  rw [threshold_rewrite hbp L hx]
  calc
    (x / (b ^ 5 * (L + 1 : ℝ))) ^ (3 / 2 : ℝ) / 8
      ≤ ((k + 1 : ℝ) / b ^ 5) ^ (3 / 2 : ℝ) / 8 := by gcongr
    _ = ((k + 1 : ℝ) / b ^ 5) * Real.sqrt ((k + 1 : ℝ) / b ^ 5) / 8 := by
      rw [rpow_three_halves _ hy]
    _ ≤ ((k + 1 : ℝ) / b ^ 5) * Real.sqrt (k + 1 : ℝ) / 8 := by gcongr
    _ ≤ (n : ℝ) * Real.sqrt (k + 1 : ℝ) / (8 * b ^ k) := by
      apply (div_le_div_iff₀ (by norm_num) (by positivity)).mpr
      have hh := mul_le_mul_of_nonneg_right hk (Real.sqrt_nonneg (k + 1 : ℝ))
      convert (mul_le_mul_of_nonneg_right hh (by norm_num : (0 : ℝ) ≤ 8)) using 1 <;> ring

/--
@isnad1 id=lt.5h5v.s7.b99e148ce25f from=translated src=- shape=300525fc vocab=63e02c22
-/
lemma threshold_small {b : ℝ} (hb : 2 ≤ b) {L n k : ℕ} {x : ℝ}
    (hx : 0 ≤ x) (hxk : x ≤ (L + 1 : ℝ) * (k + 1 : ℝ))
    (hk : Admissible b n k) (hnM : (n : ℝ) < b ^ k) :
    thresholdConstant b L * x ^ (3 / 2 : ℝ) < 1 := by
  have hbp : 0 < b := by linarith
  have hB : 0 < b ^ 5 := by positivity
  have hL : 0 < (L + 1 : ℝ) := by positivity
  have hh : (k + 1 : ℝ) / b ^ 5 < 1 := by
    have hi : (k + 1 : ℝ) * b ^ k / b ^ 5 < b ^ k := hk.trans_lt hnM
    apply (div_lt_one hB).mpr
    have hip := (div_lt_iff₀ hB).mp hi
    nlinarith [show 0 < b ^ k by positivity]
  have hxdiv : x / (b ^ 5 * (L + 1 : ℝ)) ≤ (k + 1 : ℝ) / b ^ 5 := by
    apply (div_le_div_iff₀ (mul_pos hB hL) hB).mpr
    nlinarith [mul_le_mul_of_nonneg_right hxk hB.le]
  rw [threshold_rewrite hbp L hx]
  have he : (x / (b ^ 5 * (L + 1 : ℝ))) ^ (3 / 2 : ℝ) ≤ 1 := by
    exact Real.rpow_le_one (by positivity) (hxdiv.trans hh.le) (by norm_num)
  linarith

/-- The explicit constant chosen in the manuscript.-/
def paperConstant (b : ℝ) (L : ℕ) : ℝ := 1 / (b ^ 8 * (L + 1 : ℝ) ^ (3 / 2 : ℝ))

/--
@isnad1 id=lt.1h2v.s4.2af47ccdd423 from=translated src=- shape=9141f3a7 vocab=06c9333f
-/
lemma paperConstant_pos {b : ℝ} (hb : 0 < b) (L : ℕ) : 0 < paperConstant b L := by
  unfold paperConstant; positivity

/--
@isnad1 id=le.1h2v.s4.5d6c403b52df from=translated src=- shape=c26ab622 vocab=7bbb4d4e
-/
lemma paperConstant_le_threshold {b : ℝ} (hb : 64 ≤ b) (L : ℕ) :
    paperConstant b L ≤ thresholdConstant b L := by
  have hbp : 0 < b := by linarith
  have hL : 0 < (L + 1 : ℝ) := by positivity
  have hs : 8 ≤ Real.sqrt b := by
    have hh := Real.sqrt_le_sqrt hb
    norm_num at hh
    exact hh
  have hs2 := Real.sq_sqrt hbp.le
  have hroot : 8 * Real.sqrt b ≤ b := by nlinarith
  have hfive : Real.sqrt (b ^ 5) = b ^ 2 * Real.sqrt b := by
    rw [show b ^ 5 = (b ^ 2) ^ 2 * b by ring, Real.sqrt_mul (by positivity),
      Real.sqrt_sq (sq_nonneg b)]
  unfold paperConstant thresholdConstant
  rw [Real.div_rpow (by norm_num) (by positivity), Real.one_rpow,
    Real.mul_rpow (by positivity) (by positivity), div_div]
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  rw [rpow_three_halves _ (by positivity), hfive]
  have he := mul_le_mul_of_nonneg_left hroot
    (show 0 ≤ b ^ 7 * (L + 1 : ℝ) ^ (3 / 2 : ℝ) by positivity)
  nlinarith

end
end Oscillation.Parameters
