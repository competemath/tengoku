import Tengoku.ErdosLean.ErdosLean.DuffinSchaeffer.Parts.Mertens

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Duffin–Schaeffer — Part 10: few integers with many large prime factors (KM Lemma 7.3)

`#{n ≤ x : ∑_{p | n, p ≥ t} 1/p ≥ c} ≪ x exp(-t^{e^{c-1}})`,
`c ∈ [1, 10]`.  KM cite Lemma 7.2 (Hall–Tenenbaum); an elementary replacement suffices:
with `T = t^{e^{c-1}}`, `1_{…} ≤ e^{-T} ∏_{p | n, p ≥ T} e^{2T/p}`, expand
`∏_{p|n,p≥T} e^{2T/p} = ∑_{d | n, d sqfree, p|d ⇒ p ≥ T} ∏_{p|d}(e^{2T/p} - 1)`, swap sums and use
`∑_{p ≥ T} (e^{2T/p}-1)/p ≪ T ∑_{p≥T} 1/p² ≪ 1`.
-/

open Finset

namespace DuffinSchaeffer

/-- Rankin-type expansion: `∑_{n ≤ N} ∏_{p | n, p ≥ T} (1 + g p) ≤ N ∏_{p ≤ N, p ≥ T} (1 + g p / p)`.-/
lemma sum_prod_one_add_le (N : ℕ) (T : ℝ) (g : ℕ → ℝ) (hg : ∀ p, 0 ≤ g p) :
    ∑ n ∈ Icc 1 N, ∏ p ∈ n.primeFactors.filter (fun p : ℕ => T ≤ (p : ℝ)), (1 + g p) ≤
      (N : ℝ) * ∏ p ∈ (Icc 1 N).filter (fun p : ℕ => p.Prime ∧ T ≤ (p : ℝ)),
        (1 + g p / p) := by
  classical
  set P := (Icc 1 N).filter (fun p : ℕ => p.Prime ∧ T ≤ (p : ℝ)) with hPdef
  have hsub : ∀ n ∈ Icc 1 N, n.primeFactors.filter (fun p : ℕ => T ≤ (p : ℝ)) ⊆ P := by
    intro n hn p hp
    simp only [mem_filter, Nat.mem_primeFactors] at hp
    obtain ⟨⟨hpp, hpn, hn0⟩, hT⟩ := hp
    simp only [hPdef, mem_filter, mem_Icc] at hn ⊢
    exact ⟨⟨hpp.one_lt.le, (Nat.le_of_dvd (by omega) hpn).trans hn.2⟩, hpp, hT⟩
  have step1 : ∀ n ∈ Icc 1 N,
      ∏ p ∈ n.primeFactors.filter (fun p : ℕ => T ≤ (p : ℝ)), (1 + g p)
        = ∑ A ∈ P.powerset, if A ⊆ n.primeFactors.filter (fun p : ℕ => T ≤ (p : ℝ))
            then ∏ p ∈ A, g p else 0 := by
    intro n hn
    rw [prod_one_add, ← sum_filter]
    apply sum_congr _ (fun _ _ => rfl)
    ext A
    simp only [mem_powerset, mem_filter]
    exact ⟨fun h => ⟨h.trans (hsub n hn), h⟩, fun h => h.2⟩
  rw [sum_congr rfl step1, sum_comm]
  have hIcc : Icc 1 N = Ioc 0 N := by ext; simp; omega
  have step2 : ∀ A ∈ P.powerset,
      ∑ n ∈ Icc 1 N, (if A ⊆ n.primeFactors.filter (fun p : ℕ => T ≤ (p : ℝ))
          then ∏ p ∈ A, g p else 0) ≤ (N : ℝ) * ∏ p ∈ A, (g p / p) := by
    intro A hA
    rw [← sum_filter, sum_const, nsmul_eq_mul]
    have hApr : ∀ p ∈ A, p.Prime := fun p hp => ((mem_filter.1 (mem_powerset.1 hA hp)).2).1
    have hcard : ((Icc 1 N).filter
        (fun n => A ⊆ n.primeFactors.filter (fun p : ℕ => T ≤ (p : ℝ)))).card
          ≤ N / ∏ p ∈ A, p := by
      rw [← Nat.Ioc_filter_dvd_card_eq_div, ← hIcc]
      apply card_le_card
      intro n hn
      simp only [mem_filter] at hn ⊢
      refine ⟨hn.1, ?_⟩
      apply Finset.prod_primes_dvd
      · intro p hp; exact Nat.prime_iff.1 (hApr p hp)
      · intro p hp
        have := hn.2 hp
        simp only [mem_filter, Nat.mem_primeFactors] at this
        exact this.1.2.1
    have hG : 0 ≤ ∏ p ∈ A, g p := prod_nonneg (fun p _ => hg p)
    calc (((Icc 1 N).filter
          (fun n => A ⊆ n.primeFactors.filter (fun p : ℕ => T ≤ (p : ℝ)))).card : ℝ)
            * ∏ p ∈ A, g p
          ≤ ((N / ∏ p ∈ A, p : ℕ) : ℝ) * ∏ p ∈ A, g p := by
          exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hG
      _ ≤ ((N : ℝ) / ∏ p ∈ A, (p : ℝ)) * ∏ p ∈ A, g p := by
          gcongr; rw [← Nat.cast_prod]; exact Nat.cast_div_le
      _ = (N : ℝ) * ∏ p ∈ A, (g p / p) := by
          rw [prod_div_distrib]; try ring
  calc _ ≤ ∑ A ∈ P.powerset, (N : ℝ) * ∏ p ∈ A, (g p / p) := sum_le_sum step2
    _ = _ := by rw [← mul_sum, prod_one_add]

/-- `e^u - 1 ≤ 8u` for `0 ≤ u ≤ 2`.-/
lemma exp_sub_one_le_eight_mul (u : ℝ) (h0 : 0 ≤ u) (h2 : u ≤ 2) :
    Real.exp u - 1 ≤ 8 * u := by
  have h1 : -u + 1 ≤ Real.exp (-u) := Real.add_one_le_exp (-u)
  have hprod : Real.exp u * Real.exp (-u) = 1 := by rw [← Real.exp_add]; simp
  have hle : Real.exp u - 1 ≤ u * Real.exp u := by nlinarith [Real.exp_pos u]
  have he2 : Real.exp u ≤ 8 := by
    have : Real.exp u ≤ Real.exp 2 := Real.exp_le_exp.2 h2
    have he : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
    have : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
    nlinarith [Real.exp_pos 1]
  nlinarith

end DuffinSchaeffer
