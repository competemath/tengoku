import Tengoku.Twinprime.TwinPrime.Analytic.Vaughan
import Tengoku.Twinprime.TwinPrime.Analytic.CharacterLogInterval

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Masked coefficients for Vaughan boxes

The two coefficients retain the strict lower cutoffs and the common upper
cutoff. Their bounds are uniform on every finite set, so dyadic padding
does not change the coefficient energy budget. Natural endpoints zero and
one are included.
-/

noncomputable section

open Finset
open scoped ArithmeticFunction.Moebius

namespace TwinPrime.Analytic

/-- The Möbius coefficient restricted to `U < m ≤ T`.-/
def vaughanBoxA (U T m : ℕ) : ℂ :=
  if U < m ∧ m ≤ T then ((μ m : ℝ) : ℂ) else 0

/-- The nonnegative divisor coefficient restricted to `V < n ≤ T`.-/
def vaughanBoxB (V T n : ℕ) : ℂ :=
  if V < n ∧ n ≤ T then (vaughanBeta V n : ℂ) else 0

/--
@isnad1 id=eq.1h3v.s5.ae07e432d91c from=translated src=- shape=73bc1f1d vocab=36bd2678
-/
theorem vaughanBoxA_eq_moebius (U T m : ℕ) (hm : U < m ∧ m ≤ T) :
    vaughanBoxA U T m = ((μ m : ℝ) : ℂ) := by simp [vaughanBoxA, hm]

/--
@isnad1 id=eq.1h3v.s5.8dcd896daa36 from=translated src=- shape=45ab8a0b vocab=e15bdd5c
-/
theorem vaughanBoxB_eq_beta (V T n : ℕ) (hn : V < n ∧ n ≤ T) :
    vaughanBoxB V T n = (vaughanBeta V n : ℂ) := by simp [vaughanBoxB, hn]

/--
@isnad1 id=eq.1h3v.s4.2584dbcffa4a from=translated src=- shape=8b1e8a39 vocab=a27ad1b7
-/
theorem vaughanBoxA_eq_zero_of_le (U T m : ℕ) (hm : m ≤ U) :
    vaughanBoxA U T m = 0 := by simp [vaughanBoxA, not_lt.mpr hm]

/--
@isnad1 id=eq.1h3v.s4.aa52153257ff from=translated src=- shape=8b1e8a39 vocab=fff2d440
-/
theorem vaughanBoxB_eq_zero_of_le (V T n : ℕ) (hn : n ≤ V) :
    vaughanBoxB V T n = 0 := by simp [vaughanBoxB, not_lt.mpr hn]

/--
@isnad1 id=eq.1h3v.s4.c7b25bccbbed from=translated src=- shape=b774f2c7 vocab=49fe44cd
-/
theorem vaughanBoxA_eq_zero_of_gt (U T m : ℕ) (hm : T < m) :
    vaughanBoxA U T m = 0 := by simp [vaughanBoxA, not_le.mpr hm]

/--
@isnad1 id=eq.1h3v.s4.a55063755846 from=translated src=- shape=b774f2c7 vocab=4aa171b6
-/
theorem vaughanBoxB_eq_zero_of_gt (V T n : ℕ) (hn : T < n) :
    vaughanBoxB V T n = 0 := by simp [vaughanBoxB, not_le.mpr hn]

/-- The Möbius coefficient has norm at most one, with no cutoff assumptions.
@isnad1 id=le.0h3v.s4.4dbf57db99e2 from=translated src=- shape=62338dc4 vocab=3a69ce4f
-/
theorem norm_vaughanBoxA_le_one (U T m : ℕ) : ‖vaughanBoxA U T m‖ ≤ 1 := by
  unfold vaughanBoxA
  split_ifs
  · rw [Complex.norm_real, Real.norm_eq_abs]
    exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := m)
  · simp

/-- A supported divisor coefficient is bounded by the common logarithmic endpoint.
At `T=0` or `T=1`, this states that the masked coefficient vanishes.
@isnad1 id=le.0h3v.s4.365841b6dce6 from=translated src=- shape=27f46b0d vocab=ca9f9547
-/
theorem norm_vaughanBoxB_le_log (V T n : ℕ) :
    ‖vaughanBoxB V T n‖ ≤ Real.log (T : ℝ) := by
  unfold vaughanBoxB
  split_ifs with hn
  · rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (vaughanBeta_nonneg V n)]
    exact (vaughanBeta_le_log V n).trans (log_natCast_mono hn.2)
  · simpa using Real.log_natCast_nonneg T

/--
@isnad1 id=le.0h5v.s5.f65cc934ad80 from=translated src=- shape=8db20ed6 vocab=cb0bb7f3
-/
theorem norm_vaughanBoxA_mul_vaughanBoxB_le_log (U V T m n : ℕ) :
    ‖vaughanBoxA U T m * vaughanBoxB V T n‖ ≤ Real.log (T : ℝ) := by
  rw [norm_mul]
  exact (mul_le_mul (norm_vaughanBoxA_le_one U T m) (norm_vaughanBoxB_le_log V T n)
    (norm_nonneg _) zero_le_one).trans_eq (one_mul _)

/-- The first coefficient's energy is at most the cardinality of any finite set.
@isnad1 id=le.0h3v.s5.fa09005c5ede from=translated src=- shape=ed5d6514 vocab=1b966f99
-/
theorem sum_norm_vaughanBoxA_sq_le_card (U T : ℕ) (s : Finset ℕ) :
    (∑ m ∈ s, ‖vaughanBoxA U T m‖ ^ 2) ≤ (s.card : ℝ) := by
  calc
    _ ≤ ∑ _ ∈ s, (1 : ℝ) := by
      apply sum_le_sum
      intro m _
      simpa using pow_le_pow_left₀ (norm_nonneg _) (norm_vaughanBoxA_le_one U T m) 2
    _ = _ := by simp

/-- The second coefficient's energy is at most cardinality times `log² T`.
@isnad1 id=le.0h3v.s6.4b397458f781 from=translated src=- shape=ea09ea43 vocab=e28a5def
-/
theorem sum_norm_vaughanBoxB_sq_le_card (V T : ℕ) (s : Finset ℕ) :
    (∑ n ∈ s, ‖vaughanBoxB V T n‖ ^ 2) ≤ (s.card : ℝ) * (Real.log (T : ℝ)) ^ 2 := by
  calc
    _ ≤ ∑ _ ∈ s, (Real.log (T : ℝ)) ^ 2 := by
      apply sum_le_sum
      intro n _
      exact pow_le_pow_left₀ (norm_nonneg _) (norm_vaughanBoxB_le_log V T n) 2
    _ = _ := by simp

/-- The first coefficient's energy on an arbitrary padded dyadic cell.
@isnad1 id=le.0h4v.s6.fb69ee7f26c5 from=translated src=- shape=100f111b vocab=9bd28bad
-/
theorem sum_norm_vaughanBoxA_sq_Ico_le (U T M k : ℕ) :
    (∑ m ∈ Ico M (M + 2 ^ k), ‖vaughanBoxA U T m‖ ^ 2) ≤ (2 : ℝ) ^ k := by
  simpa only [Nat.card_Ico, Nat.add_sub_cancel_left, Nat.cast_pow, Nat.cast_ofNat] using
    sum_norm_vaughanBoxA_sq_le_card U T (Ico M (M + 2 ^ k))

/-- The second coefficient's energy on an arbitrary padded dyadic cell.
@isnad1 id=le.0h4v.s6.b75028983e1e from=translated src=- shape=c4cee108 vocab=4d4b7559
-/
theorem sum_norm_vaughanBoxB_sq_Ico_le (V T M k : ℕ) :
    (∑ n ∈ Ico M (M + 2 ^ k), ‖vaughanBoxB V T n‖ ^ 2) ≤
      (2 : ℝ) ^ k * (Real.log (T : ℝ)) ^ 2 := by
  simpa only [Nat.card_Ico, Nat.add_sub_cancel_left, Nat.cast_pow, Nat.cast_ofNat] using
    sum_norm_vaughanBoxB_sq_le_card V T (Ico M (M + 2 ^ k))

/-- A whole cell below the strict lower cutoff has zero first coefficient.
@isnad1 id=eq.2h5v.s6.ea1a408b42cf from=translated src=- shape=76e9c0be vocab=f317d31f
-/
theorem vaughanBoxA_eq_zero_on_low_cell (U T M k : ℕ) (hcell : M + 2 ^ k ≤ U + 1)
    {m : ℕ} (hm : m ∈ Ico M (M + 2 ^ k)) : vaughanBoxA U T m = 0 := by
  apply vaughanBoxA_eq_zero_of_le
  have := (mem_Ico.mp hm).2
  omega

/-- A whole cell below the strict lower cutoff has zero second coefficient.
@isnad1 id=eq.2h5v.s6.d1cfec3b7619 from=translated src=- shape=76e9c0be vocab=2a332756
-/
theorem vaughanBoxB_eq_zero_on_low_cell (V T M k : ℕ) (hcell : M + 2 ^ k ≤ V + 1)
    {n : ℕ} (hn : n ∈ Ico M (M + 2 ^ k)) : vaughanBoxB V T n = 0 := by
  apply vaughanBoxB_eq_zero_of_le
  have := (mem_Ico.mp hn).2
  omega

/--
@isnad1 id=eq.2h5v.s6.2ec271aa933f from=translated src=- shape=58e676f8 vocab=3a2782a5
-/
theorem vaughanBoxA_eq_zero_on_high_cell (U T M k : ℕ) (hcell : T < M)
    {m : ℕ} (hm : m ∈ Ico M (M + 2 ^ k)) : vaughanBoxA U T m = 0 :=
  vaughanBoxA_eq_zero_of_gt U T m (hcell.trans_le (mem_Ico.mp hm).1)

/--
@isnad1 id=eq.2h5v.s6.573cc0fb9af5 from=translated src=- shape=58e676f8 vocab=9d6ba7e2
-/
theorem vaughanBoxB_eq_zero_on_high_cell (V T M k : ℕ) (hcell : T < M)
    {n : ℕ} (hn : n ∈ Ico M (M + 2 ^ k)) : vaughanBoxB V T n = 0 :=
  vaughanBoxB_eq_zero_of_gt V T n (hcell.trans_le (mem_Ico.mp hn).1)

end TwinPrime.Analytic
