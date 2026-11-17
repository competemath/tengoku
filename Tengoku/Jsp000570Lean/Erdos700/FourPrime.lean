import Tengoku.Jsp000570Lean.Erdos700.Minimum
import Tengoku.Jsp000570Lean.Erdos700.IntDigitSupport
import Tengoku.Jsp000570Lean.Erdos700.PrimeSource
import Tengoku.Jsp000570Lean.Erdos700.Arithmetic
import Tengoku.Jsp000570Lean.Erdos700.ParameterP
import Tengoku.Jsp000570Lean.Erdos700.PairADigits
import Tengoku.Jsp000570Lean.Erdos700.ParameterBC
import Tengoku.Jsp000570Lean.Erdos700.ParameterDigits
import Tengoku.Jsp000570Lean.Erdos700.RowExpansions

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace Erdos700.FourPrime

/-- A four-prime equality criterion for the binomial-gcd minimum.
The offset-dependent separation and cubic base-size conditions suffice.
This local theorem does not assume Maynard's theorem.
@isnad1 id=eq.8h4v.s7.f3c396c13a46 from=translated src=- shape=c62750a0 vocab=ce43385f
-/
theorem four_prime_exact_cubic (P A B C : ℕ)
    (hA : 1 ≤ A) (hB : 3*A ≤ B) (hC : 3*B-A+1 ≤ C) (hPsize : 12*C^3 ≤ P)
    (hP : P.Prime) (hPA : (P+A).Prime) (hPB : (P+B).Prime) (hPC : (P+C).Prime) :
    f (P*(P+A)*(P+B)*(P+C)) = P*(P+A)*(P+B) := by
  let p : ℤ := P
  let a : ℤ := A
  let b : ℤ := B
  let c : ℤ := C
  let N : ℕ := P*(P+A)*(P+B)*(P+C)
  have ha : 1 ≤ a := by dsimp [a, b, c, p]; exact_mod_cast hA
  have hb : 3*a ≤ b := by dsimp [a, b, c, p]; exact_mod_cast hB
  have hA3B : A ≤ 3*B := by omega
  have hcCast : ((3*B-A+1 : ℕ) : ℤ) ≤ (C : ℤ) := by exact_mod_cast hC
  have hc : 3*b-a+1 ≤ c := by
    simpa [a, b, c, Nat.cast_sub hA3B] using hcCast
  have hp : 12*c^3 ≤ p := by dsimp [a, b, c, p]; exact_mod_cast hPsize
  have hp0 : 0 < p := by dsimp [a, b, c, p]; exact_mod_cast hP.pos
  have ha0 : 0 ≤ a := by omega
  have hb0 : 0 ≤ b := by omega
  have hc0 : 0 ≤ c := Int.natCast_nonneg C
  have habI : a < b := by have h := Bounds.a_less_b a b c ha hb hc; omega
  have hbcI : b < c := by have h := Bounds.b_less_c a b c ha hb hc; omega
  have hab : A < B := by dsimp [a, b] at habI; exact_mod_cast habI
  have hbc : B < C := by dsimp [b, c] at hbcI; exact_mod_cast hbcI
  have hcastA : ((P+A : ℕ) : ℤ) = p+a := by simp [p, a]
  have hcastB : ((P+B : ℕ) : ℤ) = p+b := by simp [p, b]
  have hcastC : ((P+C : ℕ) : ℤ) = p+c := by simp [p, c]
  have hNi : (N : ℤ) = p*(p+a)*(p+b)*(p+c) := by simp [N, p, a, b, c]
  have hpN : P ∣ N := ⟨(P+A)*(P+B)*(P+C), by dsimp [N]; ring⟩
  have hpaN : P+A ∣ N := ⟨P*(P+B)*(P+C), by dsimp [N]; ring⟩
  have hpbN : P+B ∣ N := ⟨P*(P+A)*(P+C), by dsimp [N]; ring⟩
  have hpcN : P+C ∣ N := ⟨P*(P+A)*(P+B), by dsimp [N]; ring⟩
  have hbp := ParameterDigits.digit_bounds_p a b c p ha hb hc hp
  have hba := ParameterDigits.digit_bounds_a a b c p ha hb hc hp
  have hbb := ParameterDigits.digit_bounds_b a b c p ha hb hc hp
  have hbcD := ParameterDigits.digit_bounds_c a b c p ha hb hc hp
  have row_p : (N : ℤ)/(p) =
      1*(p)^3+(a+b+c)*(p)^2+(a*b+a*c+b*c)*(p)+(a*b*c) := by
    rw [hNi]
    simpa using RowExpansions.row_p p a b c hp0
  have row_a : (N : ℤ)/(p+a) =
      1*(p+a)^3+(b+c-3*a)*(p+a)^2+(b*c-2*a*(b+c)+3*a^2-1)*(p+a)+(p+a-a*(b-a)*(c-a)) := by
    rw [hNi]
    simpa using RowExpansions.row_a p a b c hp0 ha0
  have row_b : (N : ℤ)/(p+b) =
      1*(p+b)^3+(a+c-3*b-1)*(p+b)^2+(p+b-((2*b-a)*c+2*a*b-3*b^2))*(p+b)+(b*(b-a)*(c-b)) := by
    rw [hNi]
    simpa using RowExpansions.row_b p a b c hp0 hb0
  have row_c : (N : ℤ)/(p+c) =
      0*(p+c)^3+(p+c-(3*c-a-b))*(p+c)^2+(3*c^2-2*c*(a+b)+a*b-1)*(p+c)+(p+c-c*(c-a)*(c-b)) := by
    rw [hNi]
    simpa using RowExpansions.row_c p a b c hp0 hc0
  apply f_eq_three_prime_product N P (P+A) (P+B) (P+C) rfl hP hPA hPB hPC
    (by omega) (by omega) (by omega)
  intro k hk1 hk2
  have hkpos : 0 < (k : ℤ) := by exact_mod_cast (show 0 < k by omega)
  have hkne : (k : ℤ) ≠ 0 := ne_of_gt hkpos
  have hhalf : 2*(k : ℤ) ≤ p*(p+a)*(p+b)*(p+c) := by
    rw [← hNi]
    exact_mod_cast (show 2*k ≤ N by omega)
  have source_p (hm : ¬ (P) ∣ N.choose k) :
      ∃ u v w : ℤ, (k : ℤ) = (p)*(u*(p)^2+v*(p)+w) ∧
        0 ≤ u ∧ u ≤ a+b+c ∧ 0 ≤ v ∧ v ≤ a*b+a*c+b*c ∧ 0 ≤ w ∧ w ≤ a*b*c := by
    have hsmall := ParameterDigits.parameter_quotient_lt_cube a b c p (k : ℤ) (p)
      ha hb hc hp hhalf (by omega)
    have core := exists_int_three_digits_of_not_dvd_choose (P) N k
      (1) (a+b+c) (a*b+a*c+b*c) (a*b*c)
    exact core hP hpN hm hsmall hbp.1 hbp.2.1 hbp.2.2.1 hbp.2.2.2.1
      hbp.2.2.2.2.1 hbp.2.2.2.2.2 row_p
  have source_a (hm : ¬ (P+A) ∣ N.choose k) :
      ∃ u v w : ℤ, (k : ℤ) = (p+a)*(u*(p+a)^2+v*(p+a)+w) ∧
        0 ≤ u ∧ u ≤ b+c-3*a ∧ 0 ≤ v ∧ v ≤ b*c-2*a*(b+c)+3*a^2-1 ∧ 0 ≤ w ∧ w ≤ p+a-a*(b-a)*(c-a) := by
    have hsmall := ParameterDigits.parameter_quotient_lt_cube a b c p (k : ℤ) (p+a)
      ha hb hc hp hhalf (by omega)
    have core := exists_int_three_digits_of_not_dvd_choose (P+A) N k
      (1) (b+c-3*a) (b*c-2*a*(b+c)+3*a^2-1) (p+a-a*(b-a)*(c-a))
    simp only [hcastA] at core
    exact core hPA hpaN hm hsmall hba.1 hba.2.1 hba.2.2.1 hba.2.2.2.1
      hba.2.2.2.2.1 hba.2.2.2.2.2 row_a
  have source_b (hm : ¬ (P+B) ∣ N.choose k) :
      ∃ u v w : ℤ, (k : ℤ) = (p+b)*(u*(p+b)^2+v*(p+b)+w) ∧
        0 ≤ u ∧ u ≤ a+c-3*b-1 ∧ 0 ≤ v ∧ v ≤ p+b-((2*b-a)*c+2*a*b-3*b^2) ∧ 0 ≤ w ∧ w ≤ b*(b-a)*(c-b) := by
    have hsmall := ParameterDigits.parameter_quotient_lt_cube a b c p (k : ℤ) (p+b)
      ha hb hc hp hhalf (by omega)
    have core := exists_int_three_digits_of_not_dvd_choose (P+B) N k
      (1) (a+c-3*b-1) (p+b-((2*b-a)*c+2*a*b-3*b^2)) (b*(b-a)*(c-b))
    simp only [hcastB] at core
    exact core hPB hpbN hm hsmall hbb.1 hbb.2.1 hbb.2.2.1 hbb.2.2.2.1
      hbb.2.2.2.2.1 hbb.2.2.2.2.2 row_b
  have target_b (hm : ¬ (P+B) ∣ N.choose k) :
      (k : ℤ)/(p+b)%(p+b) ≤ b*(b-a)*(c-b) ∧
      (k : ℤ)/(p+b)/(p+b)%(p+b) ≤ p+b-((2*b-a)*c+2*a*b-3*b^2) ∧
      (k : ℤ)/(p+b)/(p+b)/(p+b)%(p+b) ≤ a+c-3*b-1 := by
    have core := int_lucas_three_digit_bounds (P+B) N k
      (1) (a+c-3*b-1) (p+b-((2*b-a)*c+2*a*b-3*b^2)) (b*(b-a)*(c-b))
    simp only [hcastB] at core
    exact core hPB hm hbb.1 hbb.2.1 hbb.2.2.1 hbb.2.2.2.1
      hbb.2.2.2.2.1 hbb.2.2.2.2.2 row_b
  have target_c (hm : ¬ (P+C) ∣ N.choose k) :
      (k : ℤ)/(p+c)%(p+c) ≤ p+c-c*(c-a)*(c-b) ∧
      (k : ℤ)/(p+c)/(p+c)%(p+c) ≤ 3*c^2-2*c*(a+b)+a*b-1 ∧
      (k : ℤ)/(p+c)/(p+c)/(p+c)%(p+c) ≤ p+c-(3*c-a-b) := by
    have core := int_lucas_three_digit_bounds (P+C) N k
      (0) (p+c-(3*c-a-b)) (3*c^2-2*c*(a+b)+a*b-1) (p+c-c*(c-a)*(c-b))
    simp only [hcastC] at core
    exact core hPC hm hbcD.1 hbcD.2.1 hbcD.2.2.1 hbcD.2.2.2.1
      hbcD.2.2.2.2.1 hbcD.2.2.2.2.2 row_c
  unfold NoTwoMissing
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rintro ⟨hmp, hma⟩
    obtain ⟨u, v, w, hs, hu0, hu, hv0, hv, hw0, hw⟩ := source_a hma
    have hdiv := missing_prime_dvd_int_source (P+A) P N k
      (u*(p+a)^2+v*(p+a)+w) hPA hP (by omega) hpN hmp
      (by simpa only [hcastA] using hs)
    obtain ⟨huZ, hvZ, hwZ⟩ := Arithmetic.pairAP_zero_digits p a b c u v w
      (by omega) hu0 hv0 hw0 hu hv hw hdiv
    rw [huZ, hvZ, hwZ] at hs
    simp at hs
    exact hkne (by exact_mod_cast hs)
  · rintro ⟨hmp, hmb⟩
    obtain ⟨u, v, w, hs, hu0, hu, hv0, hv, hw0, hw⟩ := source_p hmp
    have hdiv := missing_prime_dvd_int_source P (P+B) N k
      (u*p^2+v*p+w) hP hPB (by omega) hpbN hmb hs
    rw [hcastB] at hdiv
    obtain ⟨hlow, hmiddle, hhigh⟩ := target_b hmb
    have heq : p+b-b = p := by ring
    exact ParameterP.pairPB_global_digits a b c (p+b) u v w (k : ℤ)
      ha hb hc (by omega) hu0 hu hv0 hv hw0 hw
      (by simpa only [heq] using hdiv) (by simpa only [heq] using hs)
      hkne hlow hmiddle hhigh
  · rintro ⟨hmp, hmc⟩
    obtain ⟨u, v, w, hs, hu0, hu, hv0, hv, hw0, hw⟩ := source_p hmp
    have hdiv := missing_prime_dvd_int_source P (P+C) N k
      (u*p^2+v*p+w) hP hPC (by omega) hpcN hmc hs
    rw [hcastC] at hdiv
    obtain ⟨hlow, hmiddle, _⟩ := target_c hmc
    have heq : p+c-c = p := by ring
    exact ParameterP.pairPC_global_digits a b c (p+c) u v w (k : ℤ)
      ha hb hc (by omega) hu0 hu hv0 hv hw0 hw
      (by simpa only [heq] using hdiv) (by simpa only [heq] using hs)
      hkne hlow hmiddle
  · rintro ⟨hma, hmb⟩
    obtain ⟨u, v, w, hs, hu0, hu, hv0, hv, hw0, hw⟩ := source_a hma
    have hdiv := missing_prime_dvd_int_source (P+A) (P+B) N k
      (u*(p+a)^2+v*(p+a)+w) hPA hPB (by omega) hpbN hmb
      (by simpa only [hcastA] using hs)
    rw [hcastB] at hdiv
    obtain ⟨hlow, hmiddle, hhigh⟩ := target_b hmb
    have heq : p+b-(b-a) = p+a := by ring
    exact PairADigits.pairAB_global_digits a b c (p+b) u v w (k : ℤ)
      ha hb hc (by omega) hu0 hu hv0 hv hw0 (by simpa only [heq] using hw)
      (by simpa only [heq] using hdiv) (by simpa only [heq] using hs)
      hkne hlow hmiddle hhigh
  · rintro ⟨hma, hmc⟩
    obtain ⟨u, v, w, hs, hu0, hu, hv0, hv, hw0, hw⟩ := source_a hma
    have hdiv := missing_prime_dvd_int_source (P+A) (P+C) N k
      (u*(p+a)^2+v*(p+a)+w) hPA hPC (by omega) hpcN hmc
      (by simpa only [hcastA] using hs)
    rw [hcastC] at hdiv
    obtain ⟨hlow, hmiddle, _⟩ := target_c hmc
    have heq : p+c-(c-a) = p+a := by ring
    exact PairADigits.pairAC_global_digits a b c (p+c) u v w (k : ℤ)
      ha hb hc (by omega) hu0 hu hv0 hv hw0 (by simpa only [heq] using hw)
      (by simpa only [heq] using hdiv) (by simpa only [heq] using hs)
      hkne hlow hmiddle
  · rintro ⟨hmb, hmc⟩
    obtain ⟨u, v, w, hs, hu0, hu, hv0, hv, hw0, hw⟩ := source_b hmb
    have hdiv := missing_prime_dvd_int_source (P+B) (P+C) N k
      (u*(p+b)^2+v*(p+b)+w) hPB hPC (by omega) hpcN hmc
      (by simpa only [hcastB] using hs)
    rw [hcastC] at hdiv
    obtain ⟨hlow, hmiddle, _⟩ := target_c hmc
    exact ParameterBC.pairBC_actual_digits a b c p u v w (k : ℤ)
      ha hb hc hp hu0 hv0 hw0 hu hv hw hkpos hs hdiv hlow hmiddle

/-- The version-4 boundary criterion retains its published statement and
declaration name; its quintic size bound implies the new cubic bound.
@isnad1 id=eq.8h4v.s7.82b5ee5fa0b6 from=translated src=- shape=c62750a0 vocab=ce43385f
-/
theorem four_prime_exact_boundary (P A B C : ℕ)
    (hA : 1 ≤ A) (hB : 3*A ≤ B) (hC : 3*B-A+1 ≤ C) (hPsize : 100*C^5 ≤ P)
    (hP : P.Prime) (hPA : (P+A).Prime) (hPB : (P+B).Prime) (hPC : (P+C).Prime) :
    f (P*(P+A)*(P+B)*(P+C)) = P*(P+A)*(P+B) := by
  have hC1 : 1 ≤ C := by omega
  have hpow : C^3 ≤ C^5 := pow_le_pow_right₀ hC1 (by decide : 3 ≤ 5)
  have hPcubic : 12*C^3 ≤ P := by
    calc
      12*C^3 ≤ 100*C^3 := by omega
      _ ≤ 100*C^5 := Nat.mul_le_mul_left 100 hpow
      _ ≤ P := hPsize
  exact four_prime_exact_cubic P A B C hA hB hC hPcubic hP hPA hPB hPC

/-- The version-3 linear separation criterion retains its published statement
and declaration name as a corollary of the offset-dependent criterion.
@isnad1 id=eq.8h4v.s7.47b495bad7fb from=translated src=- shape=2b9d6987 vocab=d856c695
-/
theorem four_prime_exact_linear (P A B C : ℕ)
    (hA : 1 ≤ A) (hB : 3*A ≤ B) (hC : 3*B+1 ≤ C) (hPsize : 100*C^5 ≤ P)
    (hP : P.Prime) (hPA : (P+A).Prime) (hPB : (P+B).Prime) (hPC : (P+C).Prime) :
    f (P*(P+A)*(P+B)*(P+C)) = P*(P+A)*(P+B) := by
  have hCboundary : 3*B-A+1 ≤ C := by omega
  exact four_prime_exact_boundary P A B C hA hB hCboundary hPsize hP hPA hPB hPC

/-- The version-2 quadratic separation criterion follows from the new linear
criterion; its published statement and declaration name are preserved.
@isnad1 id=eq.8h4v.s7.a72053c82058 from=translated src=- shape=f486b9bb vocab=ce43385f
-/
theorem four_prime_exact_relaxed (P A B C : ℕ)
    (hA : 1 ≤ A) (hB : 3*A ≤ B) (hC : B*(B-A)+B+1 ≤ C) (hPsize : 100*C^5 ≤ P)
    (hP : P.Prime) (hPA : (P+A).Prime) (hPB : (P+B).Prime) (hPC : (P+C).Prime) :
    f (P*(P+A)*(P+B)*(P+C)) = P*(P+A)*(P+B) := by
  have hBA : 2 ≤ B-A := by omega
  have hClinear : 3*B+1 ≤ C := by
    have hmul := Nat.mul_le_mul_left B hBA
    nlinarith
  exact four_prime_exact_linear P A B C hA hB hClinear hPsize hP hPA hPB hPC

/-- The original separation criterion is retained as a corollary of the
relaxed theorem. This preserves the declaration submitted in the v1 packet.
@isnad1 id=eq.8h4v.s7.083160860d1d from=translated src=- shape=0d313e7d vocab=d856c695
-/
theorem four_prime_exact (P A B C : ℕ)
    (hA : 1 ≤ A) (hB : 3*A ≤ B) (hC : 10*B^2 ≤ C) (hPsize : 100*C^5 ≤ P)
    (hP : P.Prime) (hPA : (P+A).Prime) (hPB : (P+B).Prime) (hPC : (P+C).Prime) :
    f (P*(P+A)*(P+B)*(P+C)) = P*(P+A)*(P+B) := by
  have hBB : B*(B-A) ≤ B^2 := by
    calc
      B*(B-A) ≤ B*B := Nat.mul_le_mul_left B (Nat.sub_le B A)
      _ = B^2 := by ring
  have hB3 : 3 ≤ B := by omega
  have hRelax : B*(B-A)+B+1 ≤ C := by nlinarith
  exact four_prime_exact_relaxed P A B C hA hB hRelax hPsize hP hPA hPB hPC

end Erdos700.FourPrime
