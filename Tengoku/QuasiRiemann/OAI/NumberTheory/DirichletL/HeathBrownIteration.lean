import Tengoku.Seed.Analysis.SpecificLimits.Basic
import Tengoku.Seed.Tactic.FieldSimp
import Tengoku.Seed.Tactic.NormNum
import Tengoku.Seed.Tactic.Linarith
import Tengoku.Seed.Tactic.Positivity
import Tengoku.Seed.Tactic.Ring

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace OAI

namespace SevenEighths.HeathBrownIteration

noncomputable section

def step (x : ℝ) : ℝ := (6 * x - 4) / (3 * x - 1)

/--
@isnad1 id=eq.1h1v.s7.a03cbb71b32c from=translated src=- shape=4f5c027e vocab=ad07730c
-/
theorem step_sub (x : ℝ) (hx : (4 / 3 : ℝ) ≤ x) :
    step x - 4 / 3 = 2 * (x - 4 / 3) / (3 * x - 1) := by
  have hd : 3 * x - 1 ≠ 0 := by linarith
  apply (eq_div_iff hd).mpr
  unfold step
  rw [sub_mul, div_mul_cancel₀ _ hd]
  ring

/--
@isnad1 id=lt.1h1v.s5.bf76da53d4f7 from=translated src=- shape=c36eb009 vocab=3fa1e645
-/
theorem step_gt {x : ℝ} (hx : (4 / 3 : ℝ) < x) :
    (4 / 3 : ℝ) < step x := by
  have h := step_sub x hx.le
  have hp : 0 < 2 * (x - 4 / 3) / (3 * x - 1) :=
    div_pos (mul_pos (by norm_num) (sub_pos.mpr hx)) (by linarith)
  linarith

/--
@isnad1 id=le.1h1v.s7.258d6a61e076 from=translated src=- shape=58184dd7 vocab=ad07730c
-/
theorem step_error_le {x : ℝ} (hx : (4 / 3 : ℝ) ≤ x) :
    step x - 4 / 3 ≤ (2 / 3 : ℝ) * (x - 4 / 3) := by
  rw [step_sub x hx]
  apply (div_le_iff₀ (by linarith : 0 < 3 * x - 1)).mpr
  nlinarith [sq_nonneg (x - 4 / 3)]

/--
@isnad1 id=lt.1h1v.s5.2533d13a6c6b from=translated src=- shape=f4be80a9 vocab=3fa1e645
-/
theorem step_lt {x : ℝ} (hx : (4 / 3 : ℝ) < x) : step x < x := by
  have h := step_error_le hx.le
  linarith

def exponent : ℕ → ℝ
  | 0 => 2
  | n + 1 => step (exponent n)

/--
@isnad1 id=and.0h1v.s5.77832a030b19 from=translated src=- shape=7bfd1e05 vocab=d2c262d3
-/
theorem exponent_bounds (n : ℕ) :
    (4 / 3 : ℝ) < exponent n ∧ exponent n ≤ 2 := by
  induction n with
  | zero => norm_num [exponent]
  | succ n ih =>
    exact ⟨step_gt ih.1, (step_lt ih.1).le.trans ih.2⟩

/--
@isnad1 id=le.0h1v.s6.19a5a2e3cc01 from=translated src=- shape=4568cfad vocab=89812dc9
-/
theorem exponent_error_le (n : ℕ) :
    exponent n - 4 / 3 ≤ (2 / 3 : ℝ) ^ (n + 1) := by
  induction n with
  | zero => norm_num [exponent]
  | succ n ih =>
    calc
      exponent (n + 1) - 4 / 3 ≤ (2 / 3 : ℝ) * (exponent n - 4 / 3) :=
        step_error_le (exponent_bounds n).1.le
      _ ≤ (2 / 3 : ℝ) * (2 / 3 : ℝ) ^ (n + 1) :=
        mul_le_mul_of_nonneg_left ih (by norm_num)
      _ = (2 / 3 : ℝ) ^ (n + 1 + 1) := by rw [pow_succ]; ring

/--
@isnad1 id=ex.1h1v.s5.03fd9103918a from=translated src=- shape=593c154d vocab=4f7b04c5
-/
theorem exists_exponent_lt {ε : ℝ} (hε : 0 < ε) :
    ∃ n : ℕ, exponent n < 4 / 3 + ε := by
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hε (by norm_num : (2 / 3 : ℝ) < 1)
  refine ⟨n, ?_⟩
  have hp : (2 / 3 : ℝ) ^ (n + 1) ≤ (2 / 3 : ℝ) ^ n := by
    rw [pow_succ]
    exact mul_le_of_le_one_right (pow_nonneg (by norm_num) _) (by norm_num)
  have he := exponent_error_le n
  linarith

/--
@isnad1 id=ex.1h4v.s7.8f209309166e from=translated src=- shape=c7fccd53 vocab=36d50a0d
-/
theorem finite_improvement {P : ℝ → Prop} (hstart : P 2)
    (himprove : ∀ x : ℝ, (4 / 3 : ℝ) < x → x ≤ 2 → P x → P (step x))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ x : ℝ, (4 / 3 : ℝ) < x ∧ x ≤ 2 ∧ x < 4 / 3 + ε ∧ P x := by
  have hp (n : ℕ) : P (exponent n) := by
    induction n with
    | zero => exact hstart
    | succ n ih => exact himprove _ (exponent_bounds n).1 (exponent_bounds n).2 ih
  obtain ⟨n, hn⟩ := exists_exponent_lt hε
  exact ⟨exponent n, (exponent_bounds n).1, (exponent_bounds n).2, hn, hp n⟩

end

end SevenEighths.HeathBrownIteration

end OAI
