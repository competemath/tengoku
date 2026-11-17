import Tengoku.Seed.NumberTheory.Harmonic.Defs
import Tengoku.Seed.Tactic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # The exact incidence surplus and its optimal cutoff

Companion E.4 optimizes a family of lower bounds indexed by the reciprocal
medium-prime cutoff K. This is an optimization within that family only.
-/

namespace PaperC.V282.HarmonicIncidenceSurplus

/-- The surplus obtained from a medium interval (B/K,B].-/
def surplus (K : ℕ) : ℚ := (harmonic K - 2) / (K + 1)

/-- Harmonic numbers are strictly increasing.
@isnad1 id=strictmo.0h0v.s2.7224c7efba84 from=translated src=- shape=54c8eceb vocab=76293219
-/
theorem harmonic_strictMono : StrictMono harmonic := by
  apply strictMono_nat_of_lt_succ
  intro n
  rw [harmonic_succ]
  have hp : (0 : ℚ) < (n + 1 : ℕ) := by positivity
  exact lt_add_of_pos_right _ (inv_pos.mpr hp)

/-- The discrete derivative has the exact sign of 3-H_K.
@isnad1 id=eq.0h1v.s6.375c1ec43da4 from=translated src=- shape=c58183b5 vocab=374aa748
-/
theorem surplus_step (K : ℕ) :
    surplus (K + 1) - surplus K =
      (3 - harmonic K) / (((K : ℚ) + 1) * (K + 2)) := by
  unfold surplus
  rw [harmonic_succ]
  push_cast
  have h1 : (K : ℚ) + 1 ≠ 0 := by positivity
  have h2 : (K : ℚ) + 1 + 1 ≠ 0 := by positivity
  field_simp
  ring

/--
@isnad1 id=lt.0h0v.s3.ec53c0b6702f from=translated src=- shape=1ac31801 vocab=c966d5e4
-/
theorem harmonic_ten_lt_three : harmonic 10 < 3 := by
  norm_num [harmonic, Finset.sum_range_succ]

/--
@isnad1 id=eq.0h0v.s4.29c20182516d from=translated src=- shape=4683683d vocab=1754f9b4
-/
theorem harmonic_eleven_eq : harmonic 11 = 83711 / 27720 := by
  norm_num [harmonic, Finset.sum_range_succ]

/--
@isnad1 id=lt.0h0v.s3.cb83f7bd9cee from=translated src=- shape=4dcb44f2 vocab=c966d5e4
-/
theorem three_lt_harmonic_eleven : 3 < harmonic 11 := by
  rw [harmonic_eleven_eq]
  norm_num

/-- This is the rational constant printed in Theorem 7.1.
@isnad1 id=eq.0h0v.s4.0c665f20437e from=translated src=- shape=4683683d vocab=3461249f
-/
theorem surplus_eleven_eq : surplus 11 = 28271 / 332640 := by
  rw [surplus, harmonic_eleven_eq]
  norm_num

/--
@isnad1 id=lt.0h0v.s4.4c20d4e38d43 from=translated src=- shape=ed471db6 vocab=07ec4581
-/
theorem one_twelfth_lt_surplus_eleven : (1 : ℚ) / 12 < surplus 11 := by
  rw [surplus_eleven_eq]
  norm_num

/-- Beyond eleven each successive cutoff strictly decreases the surplus.
@isnad1 id=lt.1h1v.s4.9c44c84ba084 from=translated src=- shape=6bafcfd4 vocab=61b91b92
-/
theorem surplus_succ_lt {K : ℕ} (hK : 11 ≤ K) : surplus (K + 1) < surplus K := by
  have hH : 3 < harmonic K :=
    three_lt_harmonic_eleven.trans_le (harmonic_strictMono.monotone hK)
  have hd : surplus (K + 1) - surplus K < 0 := by
    rw [surplus_step]
    exact div_neg_of_neg_of_pos (by linarith) (by positivity)
  linarith

/-- Eleven uniquely maximizes the whole natural-number cutoff family.
@isnad1 id=lt.1h1v.s4.4a1ca4606606 from=translated src=- shape=604a7629 vocab=5a5f9333
-/
theorem surplus_lt_eleven_of_ne {K : ℕ} (hK : K ≠ 11) : surplus K < surplus 11 := by
  by_cases hsmall : K < 11
  · interval_cases K <;> norm_num [surplus, harmonic, Finset.sum_range_succ]
  · have hdec : StrictAnti (fun n : ℕ => surplus (n + 11)) := by
      apply strictAnti_nat_of_succ_lt
      intro n
      simpa only [Nat.add_right_comm n 1 11] using
        surplus_succ_lt (K := n + 11) (by omega)
    have hlt := hdec (show 0 < K - 11 by omega)
    simpa only [Nat.zero_add, Nat.sub_add_cancel (by omega : 11 ≤ K)] using hlt

/-- Equality in the optimal bound characterizes the selected cutoff.
@isnad1 id=le.0h1v.s3.db185a5e7df8 from=translated src=- shape=a053d75c vocab=3ea0651c
-/
theorem surplus_le_eleven (K : ℕ) : surplus K ≤ surplus 11 := by
  by_cases hK : K = 11
  · simp [hK]
  · exact (surplus_lt_eleven_of_ne hK).le

/--
@isnad1 id=iff.0h1v.s4.f2afc31e4529 from=translated src=- shape=2ead089b vocab=802ae347
-/
theorem surplus_eq_eleven_iff (K : ℕ) : surplus K = surplus 11 ↔ K = 11 := by
  constructor
  · intro h
    by_contra hn
    exact (ne_of_lt (surplus_lt_eleven_of_ne hn)) h
  · rintro rfl
    rfl

end PaperC.V282.HarmonicIncidenceSurplus
