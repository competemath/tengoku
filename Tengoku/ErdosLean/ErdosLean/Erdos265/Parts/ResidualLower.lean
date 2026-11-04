import Tengoku.ErdosLean.ErdosLean.Erdos265.Parts.RatTails

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Erdős #265 — Part U6: the second residual is a positive rational gap

`Eres n = T/(1-T) - V` with `T = T n < 1` (eventually).
* Positivity: with `x_k = 1/a_k`, `1/(a_k-1) = g(x_k)`, `g x = x/(1-x)`; `g` is strictly
  superadditive on `[0,1)` (`g(x+y) - g x - g y = xy(2-x-y)/((1-x)(1-y)(1-x-y)) > 0`), so
  `g(∑ x_k) > ∑ g(x_k)` as soon as the tail has two positive terms (it has infinitely many).
  (Formally: `x_k/(1-x_k) ≤ x_k/(1-S)` termwise, strictly for the first term.)
* Denominator: `T/(1-T) = r/(bP - r)` with `r = bP·T ∈ ℤ`, and `V = s/(d Ps)`, so
  `Eres n ∈ (1/((bP - r) d Ps)) ℤ`, hence `1 ≤ b d P_n² Eres n`.
-/

open Filter Topology

namespace Erdos265

variable {a : ℕ → ℕ}

lemma recip_pos' (ha : IsRationalPair a) (m : ℕ) : 0 < recip a m := by
  have h : (2 : ℝ) ≤ a m := by exact_mod_cast two_le_of ha m
  unfold recip
  exact div_pos one_pos (by linarith)

lemma recipS_eq_recip (ha : IsRationalPair a) (m : ℕ) :
    recipS a m = recip a m / (1 - recip a m) := by
  have h : (2 : ℝ) ≤ a m := by exact_mod_cast two_le_of ha m
  have h0 : (a m : ℝ) ≠ 0 := by intro h'; linarith
  have h1 : (a m : ℝ) - 1 ≠ 0 := by intro h'; linarith
  unfold recipS recip
  rw [one_sub_div h0, div_div_div_cancel_right₀ h0]

theorem Eres_pos_of (ha : IsRationalPair a) {n : ℕ} (hT : T a n < 1) : 0 < Eres a n := by
  have hSpos : 0 < T a n := T_pos ha n
  have h1S : 0 < 1 - T a n := by linarith
  have hsum : Summable (fun k => recip a (k + n)) :=
    (summable_nat_add_iff n).2 (summable_recip ha)
  have hsumS : Summable (fun k => recipS a (k + n)) :=
    (summable_nat_add_iff n).2 (summable_recipS ha)
  have hTdef : T a n = ∑' k, recip a (k + n) := rfl
  have hVdef : V a n = ∑' k, recipS a (k + n) := rfl
  have hle : ∀ k, recip a (k + n) ≤ T a n := fun k => by
    rw [hTdef]
    exact hsum.le_tsum k (fun j _ => (recip_pos' ha _).le)
  have hlt0 : recip a n < T a n := by
    have := tail_eq_add_tail_succ (summable_recip ha) n
    have hp := T_pos ha (n + 1)
    unfold T
    unfold T at hp
    linarith
  have hpt : ∀ k, recipS a (k + n) ≤ recip a (k + n) / (1 - T a n) := fun k => by
    rw [recipS_eq_recip ha]
    exact div_le_div_of_nonneg_left (recip_pos' ha _).le h1S (by linarith [hle k])
  have hpt0 : recipS a (0 + n) < recip a (0 + n) / (1 - T a n) := by
    rw [recipS_eq_recip ha]
    rw [zero_add]
    exact div_lt_div_of_pos_left (recip_pos' ha _) h1S (by linarith)
  have hV : V a n < T a n / (1 - T a n) := by
    rw [hVdef]
    calc ∑' k, recipS a (k + n) < ∑' k, recip a (k + n) / (1 - T a n) :=
          Summable.tsum_lt_tsum hpt hpt0 hsumS (hsum.div_const _)
      _ = T a n / (1 - T a n) := by rw [tsum_div_const, ← hTdef]
  unfold Eres
  linarith

theorem Eres_pos (ha : IsRationalPair a) : ∀ᶠ n in atTop, 0 < Eres a n := by
  have hT : ∀ᶠ n in atTop, T a n < 1 :=
    (tail_tendsto_zero (recip a)).eventually (gt_mem_nhds one_pos)
  exact hT.mono fun n hn => Eres_pos_of ha hn

end Erdos265
