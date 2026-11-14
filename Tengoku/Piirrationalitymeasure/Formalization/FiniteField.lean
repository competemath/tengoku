import Tengoku
import Tengoku.Piirrationalitymeasure.Formalization.Denominator

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
Finite-field support and antiderivative lemmas for the deletion argument.
The polynomial is written in `y = t^2`, so its support interval is the one
appearing in the paper's equations (2.18)--(2.20).
-/

namespace PiIrrationality

noncomputable def finiteFieldQuadratic (p : ℕ) : Polynomial (ZMod p) :=
  Polynomial.X ^ 2 + Polynomial.C 6 * Polynomial.X + Polynomial.C 25

noncomputable def finiteFieldLinear (p : ℕ) : Polynomial (ZMod p) :=
  Polynomial.C 25 - Polynomial.X

noncomputable def finiteFieldH (p A B C : ℕ) : Polynomial (ZMod p) :=
  Polynomial.X ^ A * (finiteFieldQuadratic p) ^ B *
    (finiteFieldLinear p) ^ (p - 1 - C)

theorem finiteFieldQuadratic_natDegree_le (p : ℕ) [Fact p.Prime] :
    (finiteFieldQuadratic p).natDegree ≤ 2 := by
  unfold finiteFieldQuadratic
  have hlin : (Polynomial.C 6 * Polynomial.X : Polynomial (ZMod p)).natDegree ≤ 2 := by
    exact le_trans Polynomial.natDegree_mul_le (by simp)
  have htwo : (Polynomial.X ^ 2 : Polynomial (ZMod p)).natDegree ≤ 2 := by
    simpa using (show (2 : ℕ) ≤ 2 from le_rfl)
  have hsum : (Polynomial.X ^ 2 + Polynomial.C 6 * Polynomial.X : Polynomial (ZMod p)).natDegree ≤ 2 := by
    exact (Polynomial.natDegree_add_le _ _).trans (max_le htwo hlin)
  exact (Polynomial.natDegree_add_le _ _).trans (max_le hsum (by simp))

theorem finiteFieldLinear_natDegree_le (p : ℕ) [Fact p.Prime] :
    (finiteFieldLinear p).natDegree ≤ 1 := by
  unfold finiteFieldLinear
  rw [sub_eq_add_neg]
  exact (Polynomial.natDegree_add_le _ _).trans (by simp)

theorem finiteFieldH_natDegree_le (p A B C : ℕ) [Fact p.Prime] :
    (finiteFieldH p A B C).natDegree ≤ A + 2 * B + (p - 1 - C) := by
  unfold finiteFieldH
  have hmul1 := Polynomial.natDegree_mul_le
      (p := (Polynomial.X ^ A * (finiteFieldQuadratic p) ^ B : Polynomial (ZMod p)))
      (q := (finiteFieldLinear p) ^ (p - 1 - C))
  have hmul2 := Polynomial.natDegree_mul_le
      (p := (Polynomial.X ^ A : Polynomial (ZMod p)))
      (q := (finiteFieldQuadratic p) ^ B)
  have hpowQ := Polynomial.natDegree_pow_le (p := finiteFieldQuadratic p) (n := B)
  have hpowR := Polynomial.natDegree_pow_le
      (p := finiteFieldLinear p) (n := p - 1 - C)
  have hxa : (Polynomial.X ^ A : Polynomial (ZMod p)).natDegree = A :=
    Polynomial.natDegree_X_pow A
  calc
    _ ≤ (Polynomial.X ^ A * (finiteFieldQuadratic p) ^ B).natDegree +
        (finiteFieldLinear p ^ (p - 1 - C)).natDegree := hmul1
    _ ≤ (Polynomial.X ^ A).natDegree + (finiteFieldQuadratic p ^ B).natDegree +
        (finiteFieldLinear p ^ (p - 1 - C)).natDegree := by omega
    _ ≤ A + 2 * B + (p - 1 - C) := by
      have hq := finiteFieldQuadratic_natDegree_le p
      have hr := finiteFieldLinear_natDegree_le p
      have hqb : ((finiteFieldQuadratic p) ^ B).natDegree ≤ 2 * B := by
        calc
          _ ≤ B * (finiteFieldQuadratic p).natDegree := hpowQ
          _ ≤ 2 * B := by
            simpa [Nat.mul_comm] using Nat.mul_le_mul_left B hq
      have hrb : ((finiteFieldLinear p) ^ (p - 1 - C)).natDegree ≤ p - 1 - C := by
        calc
          _ ≤ (p - 1 - C) * (finiteFieldLinear p).natDegree := hpowR
          _ ≤ p - 1 - C := by
            simpa using Nat.mul_le_mul_left (p - 1 - C) hr
      omega

theorem finiteFieldH_coeff_zero_of_lt (p A B C r : ℕ) [Fact p.Prime]
    (hr : r < A) : (finiteFieldH p A B C).coeff r = 0 := by
  have hdvd : (Polynomial.X ^ A : Polynomial (ZMod p)) ∣ finiteFieldH p A B C := by
    refine ⟨(finiteFieldQuadratic p) ^ B * (finiteFieldLinear p) ^ (p - 1 - C), ?_⟩
    simp [finiteFieldH, mul_assoc]
  exact (Polynomial.X_pow_dvd_iff.mp hdvd) r hr

theorem finiteFieldH_coeff_zero_of_gt (p A B C r : ℕ) [Fact p.Prime]
    (hr : A + 2 * B + (p - 1 - C) < r) :
    (finiteFieldH p A B C).coeff r = 0 := by
  exact Polynomial.coeff_eq_zero_of_natDegree_lt
    (lt_of_le_of_lt (finiteFieldH_natDegree_le p A B C) hr)

theorem finiteFieldH_obstructionFree_of_interval (p A B C : ℕ) [Fact p.Prime]
    (hobs : ∀ r, A ≤ r → r ≤ A + 2 * B + (p - 1 - C) → ¬ p ∣ r + 1) :
    obstructionFree p (finiteFieldH p A B C) := by
  intro r hr
  by_cases hlow : r < A
  · exact finiteFieldH_coeff_zero_of_lt p A B C r hlow
  by_cases hupp : A + 2 * B + (p - 1 - C) < r
  · exact finiteFieldH_coeff_zero_of_gt p A B C r hupp
  exfalso
  exact hobs r (Nat.le_of_not_gt hlow) (Nat.le_of_not_gt hupp) hr

noncomputable def evenLift (p : ℕ) (f : Polynomial (ZMod p)) : Polynomial (ZMod p) :=
  ∑ r ∈ f.support, Polynomial.monomial (2 * r) (f.coeff r)

def evenObstructionFree (p : ℕ) (f : Polynomial (ZMod p)) : Prop :=
  ∀ r, p ∣ 2 * r + 1 → f.coeff r = 0

theorem finiteFieldH_evenObstructionFree_of_interval (p A B C : ℕ)
    [Fact p.Prime]
    (hobs : ∀ r, A ≤ r → r ≤ A + 2 * B + (p - 1 - C) →
      ¬ p ∣ 2 * r + 1) :
    evenObstructionFree p (finiteFieldH p A B C) := by
  intro r hr
  by_cases hlow : r < A
  · exact finiteFieldH_coeff_zero_of_lt p A B C r hlow
  by_cases hupp : A + 2 * B + (p - 1 - C) < r
  · exact finiteFieldH_coeff_zero_of_gt p A B C r hupp
  exact False.elim (hobs r (Nat.le_of_not_gt hlow) (Nat.le_of_not_gt hupp) hr)

noncomputable def evenPolynomialPrimitive (p : ℕ) [Fact p.Prime]
    (f : Polynomial (ZMod p)) : Polynomial (ZMod p) :=
  ∑ r ∈ f.support,
    Polynomial.monomial (2 * r + 1)
      (if ((2 * r + 1 : ℕ) : ZMod p) = 0 then 0
       else f.coeff r / ((2 * r + 1 : ℕ) : ZMod p))

theorem evenPolynomialPrimitive_derivative (p : ℕ) [Fact p.Prime]
    (f : Polynomial (ZMod p)) (hf : evenObstructionFree p f) :
    Polynomial.derivative (evenPolynomialPrimitive p f) = evenLift p f := by
  unfold evenPolynomialPrimitive evenLift
  rw [Polynomial.derivative_sum]
  apply Finset.sum_congr rfl
  intro r hr
  rw [Polynomial.derivative_monomial]
  have hrc : f.coeff r ≠ 0 := Polynomial.mem_support_iff.mp hr
  have hnot : ¬ p ∣ 2 * r + 1 := by
    intro hd
    exact hrc (hf r hd)
  have hcast : ((2 * r + 1 : ℕ) : ZMod p) ≠ 0 := by
    intro hz
    exact hnot ((ZMod.natCast_eq_zero_iff _ _).mp hz)
  have hcast' : ((r : ZMod p) * 2 + 1) ≠ 0 := by
    simpa [Nat.cast_mul, Nat.cast_add, mul_comm] using hcast
  have hcast'' : (2 * (r : ZMod p) + 1) ≠ 0 := by
    simpa [mul_comm] using hcast'
  simp [hcast'']

theorem even_obstruction_avoids_low (p A E : ℕ) [Fact p.Prime]
    (hp5 : 5 < p) (hE : 2 * E + 3 ≤ p) :
    ∀ r, A ≤ r → r ≤ E → ¬ p ∣ 2 * r + 1 := by
  intro r hA hEr hdiv
  rcases hdiv with ⟨k, hk⟩
  have hp : 2 ≤ p := (Fact.out : Nat.Prime p).two_le
  have h2r : 2 * r ≤ 2 * E := Nat.mul_le_mul_left 2 hEr
  have hsmall0 : 2 * r + 1 ≤ 2 * E + 1 := by omega
  have hsmall1 : 2 * E + 1 < p := by omega
  have hsmall : 2 * r + 1 < p := lt_of_le_of_lt hsmall0 hsmall1
  by_cases hkzero : k = 0
  · subst k
    omega
  · have hkpos : 0 < k := Nat.pos_of_ne_zero hkzero
    have hple : p ≤ p * k := Nat.le_mul_of_pos_right p hkpos
    rw [← hk] at hple
    omega

theorem even_obstruction_avoids_high (p A E : ℕ) [Fact p.Prime]
    (hp5 : 5 < p) (hA : p + 1 ≤ 2 * A)
    (hE : 2 * E + 3 ≤ 3 * p) :
    ∀ r, A ≤ r → r ≤ E → ¬ p ∣ 2 * r + 1 := by
  intro r hAr hEr hdiv
  rcases hdiv with ⟨k, hk⟩
  have h2r : 2 * r ≤ 2 * E := Nat.mul_le_mul_left 2 hEr
  have hlow0 : p + 1 ≤ 2 * r := by omega
  have hlow' : p + 2 ≤ 2 * r + 1 := by omega
  have hupp0 : 2 * r + 3 ≤ 3 * p := by omega
  have hupp' : 2 * r + 1 + 2 ≤ 3 * p := by omega
  have hkpos : 0 < k := by
    by_contra hk0
    have : k = 0 := Nat.eq_zero_of_not_pos hk0
    subst k
    omega
  have hkge2 : 2 ≤ k := by
    by_contra hk2
    have hkone : k = 1 := by omega
    subst k
    omega
  have hkle2 : k ≤ 2 := by
    by_contra hk3
    have hkge3 : 3 ≤ k := by omega
    have h3p : 3 * p ≤ p * k := by
      simpa [Nat.mul_comm] using Nat.mul_le_mul_left p hkge3
    rw [← hk] at h3p
    omega
  have hkval : k = 2 := by omega
  subst k
  omega

theorem finiteField_support_end_low_bound (p A B C : ℕ) [Fact p.Prime]
    (hp5 : 5 < p) (hCp : C ≤ p - 1)
    (hC : A + 2 * B + (p + 1) / 2 ≤ C) :
    2 * (A + 2 * B + (p - 1 - C)) + 3 ≤ p := by
  have hpprime : Nat.Prime p := Fact.out
  have hpmod : p % 2 = 1 := by
    rcases hpprime.eq_two_or_odd with htwo | hodd
    · omega
    · exact hodd
  omega

theorem finiteField_support_end_high_bound (p A B C : ℕ) [Fact p.Prime]
    (hp5 : 5 < p) (hCp : C ≤ p - 1)
    (hA : p + 1 ≤ 2 * A)
    (hC : A + 2 * B ≤ C + (p - 1) / 2) :
    2 * (A + 2 * B + (p - 1 - C)) + 3 ≤ 3 * p := by
  have hpprime : Nat.Prime p := Fact.out
  have hpmod : p % 2 = 1 := by
    rcases hpprime.eq_two_or_odd with htwo | hodd
    · omega
    · exact hodd
  omega

theorem finiteFieldH_evenObstructionFree_low_bound (p A B C : ℕ)
    [Fact p.Prime] (hp5 : 5 < p) (hCp : C ≤ p - 1)
    (hC : A + 2 * B + (p + 1) / 2 ≤ C) :
    evenObstructionFree p (finiteFieldH p A B C) := by
  apply finiteFieldH_evenObstructionFree_of_interval
  exact even_obstruction_avoids_low p A
    (A + 2 * B + (p - 1 - C)) hp5
    (finiteField_support_end_low_bound p A B C hp5 hCp hC)

theorem finiteFieldH_evenObstructionFree_high_bound (p A B C : ℕ)
    [Fact p.Prime] (hp5 : 5 < p) (hCp : C ≤ p - 1)
    (hA : p + 1 ≤ 2 * A)
    (hC : A + 2 * B ≤ C + (p - 1) / 2) :
    evenObstructionFree p (finiteFieldH p A B C) := by
  apply finiteFieldH_evenObstructionFree_of_interval
  exact even_obstruction_avoids_high p A
    (A + 2 * B + (p - 1 - C)) hp5 hA
    (finiteField_support_end_high_bound p A B C hp5 hCp hA hC)

end PiIrrationality
