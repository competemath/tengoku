import Tengoku.Twinprime.TwinPrime.Analytic.RationalFrequencySeparation
import Tengoku.Twinprime.TwinPrime.Analytic.CharacterLargeSieveTransfer
import Tengoku.Twinprime.TwinPrime.Analytic.AdditiveLargeSieve

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Large sieve for reduced rational frequencies

The finite family includes the unique unit at modulus one. Its separation
gives the additive large sieve, and the Gauss-sum transfer gives a weighted
primitive-character large sieve with the same explicit harmonic loss.
-/

noncomputable section

open Finset Classical

namespace TwinPrime.Analytic

local instance (q : ℕ) : Fintype (ZMod q)ˣ := Fintype.ofFinite _

/-- All reduced rational frequencies with positive denominator at most `Q`.-/
def rationalFrequencyFamily (Q : ℕ) : Finset (Σ q : ℕ, (ZMod q)ˣ) :=
  (Icc 1 Q).sigma fun _ => univ

/-- A canonical real representative of a reduced rational frequency.-/
def rationalFrequency (p : Σ q : ℕ, (ZMod q)ˣ) : ℝ :=
  ((p.2 : ZMod p.1).val : ℝ) / p.1

/--
@isnad1 id=eq.0h1v.s5.1062d40789dd from=translated src=- shape=22404f6a vocab=a1bbda07
-/
theorem card_rationalFrequencyFamily (Q : ℕ) :
    (rationalFrequencyFamily Q).card = ∑ q ∈ Icc 1 Q, Nat.totient q := by
  rw [rationalFrequencyFamily, card_sigma]
  apply sum_congr rfl
  intro q hq
  haveI : NeZero q := ⟨by have := (mem_Icc.mp hq).1; omega⟩
  simp only [card_univ, ZMod.card_units_eq_totient]

/-- A uniform elementary bound for the number of reduced frequencies.
@isnad1 id=le.0h1v.s5.6e45cdbfa3a8 from=translated src=- shape=f0ddb5cf vocab=772d4645
-/
theorem sum_totient_Icc_le_sq (Q : ℕ) :
    (∑ q ∈ Icc 1 Q, Nat.totient q) ≤ Q ^ 2 := by
  calc
    _ ≤ ∑ _q ∈ Icc 1 Q, Q :=
      sum_le_sum fun q hq => (Nat.totient_le q).trans (mem_Icc.mp hq).2
    _ = _ := by simp [pow_two]

/-- The harmonic loss is at most `1 + 2 log (Q+1)`, also at `Q=0`.
@isnad1 id=le.0h1v.s6.60af4ab95307 from=translated src=- shape=b497fa63 vocab=e9d15bb3
-/
theorem harmonic_totient_sum_le_log (Q : ℕ) :
    (harmonic (∑ q ∈ Icc 1 Q, Nat.totient q) : ℝ) ≤
      1 + 2 * Real.log ((Q : ℝ) + 1) := by
  have hcard : (∑ q ∈ Icc 1 Q, Nat.totient q) ≤ (Q + 1) ^ 2 :=
    (sum_totient_Icc_le_sq Q).trans (Nat.pow_le_pow_left (by omega) 2)
  calc
    _ ≤ (harmonic ((Q + 1) ^ 2) : ℝ) := harmonic_real_mono hcard
    _ ≤ 1 + Real.log (((Q + 1) ^ 2 : ℕ) : ℝ) := harmonic_le_one_add_log _
    _ = _ := by simp only [Nat.cast_pow, Nat.cast_add, Nat.cast_one,
      Real.log_pow, Nat.cast_ofNat]

/--
@isnad1 id=le.3h3v.s8.30e75b06bf66 from=translated src=- shape=5cb555cc vocab=265fa0d7
-/
theorem rationalFrequencyFamily_separated (Q : ℕ)
    (i : Σ q : ℕ, (ZMod q)ˣ) (hi : i ∈ rationalFrequencyFamily Q)
    (j : Σ q : ℕ, (ZMod q)ˣ) (hj : j ∈ rationalFrequencyFamily Q)
    (hne : i ≠ j) :
    (1 : ℝ) / (Q : ℝ) ^ 2 ≤
      dist (rationalFrequency i : UnitAddCircle) (rationalFrequency j : UnitAddCircle) := by
  rcases i with ⟨q, u⟩
  rcases j with ⟨r, v⟩
  have hq := (mem_Icc.mp (mem_sigma.mp hi).1)
  have hr := (mem_Icc.mp (mem_sigma.mp hj).1)
  dsimp only at hq hr
  haveI : NeZero q := ⟨by omega⟩
  haveI : NeZero r := ⟨by omega⟩
  have hneq : ¬ (q = r ∧ (u : ZMod q).val = (v : ZMod r).val) := by
    rintro ⟨hqr, huv⟩
    subst r
    have huv' : u = v := Units.val_injective (ZMod.val_injective q huv)
    subst v
    exact hne rfl
  simpa only [ZMod.toAddCircle_apply, rationalFrequency] using
    unit_rational_frequency_dist_ge_inv_sq Q hq.2 hr.2 u v hneq

/-- The standard additive character has exactly the phase convention used
by the additive large sieve.
@isnad1 id=eq.0h3v.s7.789a63688831 from=translated src=- shape=6fc00f11 vocab=56d8c11d
-/
theorem stdAddChar_mul_eq_additivePhase {q : ℕ} [NeZero q]
    (u : (ZMod q)ˣ) (n : ℕ) :
    ZMod.stdAddChar ((u : ZMod q) * (n : ZMod q)) =
      additivePhase ((n : ℝ) * ((u : ZMod q).val / (q : ℝ))) := by
  have hbase : ZMod.stdAddChar (u : ZMod q) =
      additivePhase ((u : ZMod q).val / (q : ℝ)) := by
    rw [ZMod.stdAddChar_apply, ZMod.toCircle_eq_circleExp]
    rfl
  rw [← additivePhase_pow, ← hbase, ← AddChar.map_nsmul_eq_pow]
  congr 1
  simp only [nsmul_eq_mul, mul_comm]

/-- The additive large sieve over all reduced fractions, with the exact
number of frequencies retained in its harmonic factor.
@isnad1 id=le.0h4v.s8.6fd5457c9503 from=translated src=- shape=dd9cdec3 vocab=180180b3
-/
theorem rational_additive_large_sieve (Q M N : ℕ) (a : ℕ → ℂ) :
    (∑ q ∈ Icc 1 Q, ∑ u : (ZMod q)ˣ,
      ‖∑ n ∈ Ico M N, a n *
        additivePhase ((n : ℝ) * ((u : ZMod q).val / (q : ℝ)))‖ ^ 2) ≤
      (((N - M : ℕ) : ℝ) + (Q : ℝ) ^ 2 *
        (harmonic (∑ q ∈ Icc 1 Q, Nat.totient q) : ℝ)) *
          ∑ n ∈ Ico M N, ‖a n‖ ^ 2 := by
  by_cases hQ : Q = 0
  · subst Q
    simp only [Icc_eq_empty_of_lt (by norm_num : 0 < 1), sum_empty,
      Nat.cast_zero, zero_pow (by norm_num : 2 ≠ 0), zero_mul, add_zero]
    positivity
  have hQ0 : (0 : ℝ) < Q := by exact_mod_cast Nat.pos_of_ne_zero hQ
  have h := additive_large_sieve_of_separated (rationalFrequencyFamily Q)
    rationalFrequency a M N (1 / (Q : ℝ) ^ 2) (by positivity)
    (rationalFrequencyFamily_separated Q)
  rw [card_rationalFrequencyFamily] at h
  simpa only [rationalFrequencyFamily, sum_sigma, rationalFrequency,
    div_div_eq_mul_div, div_one, mul_comm] using h

/-- Weighted primitive-character large sieve obtained from the additive
estimate. The inverse character is kept to match the positive additive phase.
@isnad1 id=le.0h4v.s8.7735576d36b7 from=translated src=- shape=b4dd72b1 vocab=fa6797cc
-/
theorem primitive_character_large_sieve (Q M N : ℕ) (a : ℕ → ℂ) :
    (∑ q ∈ Icc 1 Q, (q : ℝ) / Nat.totient q *
      (∑ χ ∈ (univ : Finset (DirichletCharacter ℂ q)).filter (fun χ => χ.IsPrimitive),
        ‖∑ n ∈ Ico M N, a n * χ⁻¹ n‖ ^ 2)) ≤
      (((N - M : ℕ) : ℝ) + (Q : ℝ) ^ 2 *
        (harmonic (∑ q ∈ Icc 1 Q, Nat.totient q) : ℝ)) *
          ∑ n ∈ Ico M N, ‖a n‖ ^ 2 := by
  apply le_trans _ (rational_additive_large_sieve Q M N a)
  apply sum_le_sum
  intro q hq
  haveI : NeZero q := ⟨by have := (mem_Icc.mp hq).1; omega⟩
  have h := primitive_character_largeSieve_transfer (q := q) (Ico M N) a
  simp only [stdAddChar_mul_eq_additivePhase] at h
  convert h using 1 <;> congr
  exact Subsingleton.elim _ _

/-- An explicit logarithmic form of the rational additive large sieve.
@isnad1 id=le.0h4v.s8.2f00ac9cc355 from=translated src=- shape=9c264e25 vocab=ee3760ea
-/
theorem rational_additive_large_sieve_log (Q M N : ℕ) (a : ℕ → ℂ) :
    (∑ q ∈ Icc 1 Q, ∑ u : (ZMod q)ˣ,
      ‖∑ n ∈ Ico M N, a n *
        additivePhase ((n : ℝ) * ((u : ZMod q).val / (q : ℝ)))‖ ^ 2) ≤
      (((N - M : ℕ) : ℝ) + (Q : ℝ) ^ 2 *
        (1 + 2 * Real.log ((Q : ℝ) + 1))) *
          ∑ n ∈ Ico M N, ‖a n‖ ^ 2 := by
  apply (rational_additive_large_sieve Q M N a).trans
  apply mul_le_mul_of_nonneg_right _ (sum_nonneg fun _ _ => sq_nonneg _)
  exact add_le_add le_rfl (mul_le_mul_of_nonneg_left
    (harmonic_totient_sum_le_log Q) (sq_nonneg _))

/-- A finite unconditional primitive-character large sieve with an explicit
logarithmic loss. No distribution or maximal-sum estimate is assumed.
@isnad1 id=le.0h4v.s8.fe87dc3f598f from=translated src=- shape=af082214 vocab=7b2f9665
-/
theorem primitive_character_large_sieve_log (Q M N : ℕ) (a : ℕ → ℂ) :
    (∑ q ∈ Icc 1 Q, (q : ℝ) / Nat.totient q *
      (∑ χ ∈ (univ : Finset (DirichletCharacter ℂ q)).filter (fun χ => χ.IsPrimitive),
        ‖∑ n ∈ Ico M N, a n * χ⁻¹ n‖ ^ 2)) ≤
      (((N - M : ℕ) : ℝ) + (Q : ℝ) ^ 2 *
        (1 + 2 * Real.log ((Q : ℝ) + 1))) *
          ∑ n ∈ Ico M N, ‖a n‖ ^ 2 := by
  apply (primitive_character_large_sieve Q M N a).trans
  apply mul_le_mul_of_nonneg_right _ (sum_nonneg fun _ _ => sq_nonneg _)
  exact add_le_add le_rfl (mul_le_mul_of_nonneg_left
    (harmonic_totient_sum_le_log Q) (sq_nonneg _))

end TwinPrime.Analytic
