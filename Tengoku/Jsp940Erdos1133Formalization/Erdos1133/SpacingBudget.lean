import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Fixed spacing and strict integer zero-count budgets for the multipeak
construction. The choices depend only on the packet bounds, not on the nodes. -/

noncomputable section

namespace Erdos1133

/-- A large integer spacing simultaneously controls within-period packet tails
and tails from the other periods.-/
theorem exists_packet_spacing (C S : ℝ) (hC : 0 < C) (hS : 0 ≤ S) (ρ : ℕ) :
    ∃ K : ℕ, 0 < K ∧
      let D : ℝ := ((2*ρ+1)*K : ℕ)
      1 ≤ D ∧ 2*(ρ : ℝ) < D ∧
        (4*C/D^2)*S ≤ 1 ∧ (C/D^2)*S^2 ≤ 1 := by
  obtain ⟨K, hKg⟩ := exists_nat_gt (1+4*C*S+C*S^2)
  have hCS : 0 ≤ C*S := mul_nonneg hC.le hS
  have hCS2 : 0 ≤ C*S^2 := mul_nonneg hC.le (sq_nonneg S)
  have hK1 : (1 : ℝ) < K := by nlinarith
  have hK : 0 < K := by exact_mod_cast (lt_trans zero_lt_one hK1)
  refine ⟨K, hK, ?_⟩
  let D : ℝ := ((2*ρ+1)*K : ℕ)
  change 1 ≤ D ∧ 2*(ρ : ℝ) < D ∧ (4*C/D^2)*S ≤ 1 ∧ (C/D^2)*S^2 ≤ 1
  have hDeq : D = (2*(ρ : ℝ)+1)*(K : ℝ) := by dsimp [D]; push_cast; rfl
  have hρ : (0 : ℝ) ≤ ρ := Nat.cast_nonneg _
  have hKD : (K : ℝ) ≤ D := by rw [hDeq]; nlinarith
  have hD1 : 1 ≤ D := hK1.le.trans hKD
  have hρD : 2*(ρ : ℝ) < D := by rw [hDeq]; nlinarith
  have hDsq : D ≤ D^2 := by nlinarith
  have hfirst : 4*C*S ≤ D^2 := by nlinarith
  have hsecond : C*S^2 ≤ D^2 := by nlinarith
  have hpos : 0 < D^2 := by positivity
  refine ⟨hD1, hρD, ?_, ?_⟩
  · rw [div_mul_eq_mul_div]
    exact (div_le_one hpos).mpr hfirst
  · rw [div_mul_eq_mul_div]
    exact (div_le_one hpos).mpr hsecond

/-- A linear number of peaks eventually strictly exceeds twice the excess
Fourier degree plus one. Both subtractions in the conclusion are in `ℕ`.-/
theorem exists_strict_zero_budget (η : ℝ) (hη : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ c m : ℕ,
      η*(n : ℝ) ≤ c → n ≤ m →
      (m : ℝ) ≤ n+δ*n → 2*(m-n) < c-1 := by
  obtain ⟨n₀, hn₀⟩ := exists_nat_gt (4/η)
  refine ⟨η/8, by positivity, n₀, ?_⟩
  intro n hn c m hpeaks hnm hm
  have hnreal : (n₀ : ℝ) ≤ n := by exact_mod_cast hn
  have hfour : 4 < η*(n : ℝ) := by
    have hlarge : 4/η < (n : ℝ) := hn₀.trans_le hnreal
    have hh := (div_lt_iff₀ hη).mp hlarge
    nlinarith
  have hc : 2 ≤ c := by
    have hh : (4 : ℝ) < c := hfour.trans_le hpeaks
    exact_mod_cast (show (2 : ℝ) ≤ c by linarith)
  have hsub : ((m-n : ℕ) : ℝ) = (m : ℝ)-n := Nat.cast_sub hnm
  have hcsub : ((c-1 : ℕ) : ℝ) = (c : ℝ)-1 := by
    rw [Nat.cast_sub (show 1 ≤ c by omega)]
    norm_num
  have hstrict : 2*((m-n : ℕ) : ℝ) < ((c-1 : ℕ) : ℝ) := by
    rw [hsub, hcsub]
    nlinarith
  exact_mod_cast hstrict

end Erdos1133
