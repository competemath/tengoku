import Tengoku
import Tengoku.Piirrationalitymeasure.Formalization.BinomialExpansion

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
Definitions for the reduced least common multiple in Section 2.3.
-/

namespace PiIrrationality

def lcmRange (n : ℕ) : ℕ :=
  (Finset.Icc 1 n).lcm id

/--
@isnad1 id=dvd.2h2v.s4.749a050b9711 from=translated src=- shape=0ee06065 vocab=c18cea34
-/
theorem dvd_lcmRange (n k : ℕ) (hk : 1 ≤ k) (hkn : k ≤ n) :
    k ∣ lcmRange n := by
  unfold lcmRange
  exact Finset.dvd_lcm (Finset.mem_Icc.mpr ⟨hk, hkn⟩)

def removablePrime (n p : ℕ) : Prop :=
  Nat.Prime p ∧ 5 < p ∧
    Nat.sqrt (7430 * n) < p ∧ p ≤ 7430 * n ∧
    (Int.fract (((1857 * n : ℕ) : ℚ) / p + 1 / 2) +
      2 * Int.fract (((3714 * n : ℕ) : ℚ) / p)) <
      Int.fract (((5570 * n : ℕ) : ℚ) / p)

/--
@isnad1 id=lt.1h2v.s5.be710e9e18ae from=translated src=- shape=4c5cafb2 vocab=26900bf7
-/
theorem removablePrime_square_gt (n p : ℕ)
    (hp : removablePrime n p) : 7430 * n < p ^ 2 := by
  rcases hp with ⟨hprime, h5, hsqrt, hupper, hcond⟩
  exact (Nat.sqrt_lt').mp hsqrt

/--
@isnad1 id=iff.0h4v.s8.6457e203628c from=translated src=- shape=b4e67928 vocab=d548d1a1
-/
theorem fract_condition_iff_floor_condition (a b c u : ℚ) :
    Int.fract (a * u + 1 / 2) + 2 * Int.fract (b * u) < Int.fract (c * u) ↔
      (a + 2 * b - c) * u + 1 / 2 <
        (⌊a * u + 1 / 2⌋ : ℚ) + 2 * (⌊b * u⌋ : ℚ) - (⌊c * u⌋ : ℚ) := by
  have ha := Int.fract_add_floor (a * u + 1 / 2)
  have hb := Int.fract_add_floor (b * u)
  have hc := Int.fract_add_floor (c * u)
  constructor <;> intro h <;> linarith

/--
@isnad1 id=iff.0h2v.s8.30aa3accafff from=translated src=- shape=30191911 vocab=88c83f47
-/
theorem removablePrime_condition_iff_floor (n p : ℕ) :
    (Int.fract (((1857 * n : ℕ) : ℚ) / p + 1 / 2) +
      2 * Int.fract (((3714 * n : ℕ) : ℚ) / p)) <
      Int.fract (((5570 * n : ℕ) : ℚ) / p) ↔
      ((1857 : ℚ) + 2 * 3714 - 5570) * ((n : ℚ) / p) + 1 / 2 <
        (⌊((1857 : ℚ) * ((n : ℚ) / p) + 1 / 2)⌋ : ℚ) +
          2 * (⌊(3714 : ℚ) * ((n : ℚ) / p)⌋ : ℚ) -
          (⌊(5570 : ℚ) * ((n : ℚ) / p)⌋ : ℚ) := by
  have h := fract_condition_iff_floor_condition
    (1857 : ℚ) 3714 5570 ((n : ℚ) / p)
  simpa [Nat.cast_mul, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using h

noncomputable def removablePrimes (n : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Icc 1 (7430 * n)).filter (removablePrime n)

noncomputable def Phi (n : ℕ) : ℕ :=
  (removablePrimes n).prod id

noncomputable def reducedLcm (n : ℕ) : ℚ :=
  (lcmRange (7430 * n) : ℚ) / Phi n

noncomputable def reducedLcmNat (n : ℕ) : ℕ :=
  lcmRange (7430 * n) / Phi n

/--
@isnad1 id=mem.1h2v.s5.057d01dfbdf0 from=translated src=- shape=57507fef vocab=f685e8c7
-/
theorem removablePrime_mem_range (n p : ℕ) (hp : removablePrime n p) :
    p ∈ Finset.Icc 1 (7430 * n) := by
  rcases hp with ⟨hprime, h5, hsqrt, hupper, hcond⟩
  exact Finset.mem_Icc.mpr ⟨by omega, hupper⟩

/--
@isnad1 id=dvd.0h1v.s4.7ef0a621b3ae from=translated src=- shape=5f699161 vocab=eb17b367
-/
theorem Phi_dvd_lcmRange (n : ℕ) :
    Phi n ∣ lcmRange (7430 * n) := by
  classical
  have prod_dvd : ∀ (s : Finset ℕ),
      (∀ a ∈ s, Nat.Prime a) →
      (∀ a ∈ s, a ∣ lcmRange (7430 * n)) →
      (∀ a ∈ s, ∀ b ∈ s, a ≠ b → Nat.Coprime a b) →
      (s.prod id) ∣ lcmRange (7430 * n) := by
    intro s
    induction s using Finset.induction_on with
    | empty => intro _ _ _; simp
    | @insert a s ha ih =>
        intro hprime hdvd hpair
        have hcop : Nat.Coprime a (s.prod id) := by
          apply Nat.Coprime.prod_right
          intro b hb
          exact hpair a (by simp) b (by simp [hb]) (by
            intro hab
            exact ha (hab ▸ hb))
        have hsdvd : (s.prod id) ∣ lcmRange (7430 * n) := by
          apply ih
          · intro b hb; exact hprime b (by simp [hb])
          · intro b hb; exact hdvd b (by simp [hb])
          · intro b hb c hc hbc
            exact hpair b (by simp [hb]) c (by simp [hc]) hbc
        simpa [Finset.prod_insert, ha] using
          hcop.mul_dvd_of_dvd_of_dvd (hdvd a (by simp)) hsdvd
  apply prod_dvd (removablePrimes n)
  · intro a ha
    exact (Finset.mem_filter.mp ha).2.1
  · intro a ha
    have hmem : a ∈ Finset.Icc 1 (7430 * n) := (Finset.mem_filter.mp ha).1
    have hmem' := Finset.mem_Icc.mp hmem
    exact dvd_lcmRange (7430 * n) a hmem'.1 hmem'.2
  · intro a ha b hb hab
    have hpa := (Finset.mem_filter.mp ha).2
    have hpb := (Finset.mem_filter.mp hb).2
    exact (Nat.coprime_primes hpa.1 hpb.1).mpr hab

/--
@isnad1 id=lt.0h1v.s3.dc92b3ecb931 from=translated src=- shape=8a62b088 vocab=e7717e59
-/
theorem Phi_pos (n : ℕ) : 0 < Phi n := by
  classical
  unfold Phi
  exact Finset.prod_pos (fun p hp => (Finset.mem_filter.mp hp).2.1.pos)

/--
@isnad1 id=odd.0h1v.s2.97ab62c4aa2c from=translated src=- shape=6da4ece3 vocab=a57f15bc
-/
theorem Phi_odd (n : ℕ) : Odd (Phi n) := by
  classical
  have hprod : ∀ s : Finset ℕ, (∀ a ∈ s, Odd a) → Odd (s.prod id) := by
    intro s hs
    induction s using Finset.induction_on with
    | empty => simp
    | @insert a s ha ih =>
        have haodd : Odd a := hs a (by simp)
        have hsodd : Odd (s.prod id) := ih (by
          intro b hb
          exact hs b (by simp [hb]))
        simpa [Finset.prod_insert, ha] using haodd.mul hsodd
  apply hprod (removablePrimes n)
  intro a ha
  have hrem := (Finset.mem_filter.mp ha).2
  have hprime := hrem.1
  have h5 := hrem.2.1
  exact hprime.odd_of_ne_two (by omega)

/--
@isnad1 id=eq.0h1v.s5.c6d964be20d0 from=translated src=- shape=e2e345a7 vocab=28b49df3
-/
theorem reducedLcm_mul_Phi (n : ℕ) :
    reducedLcm n * (Phi n : ℚ) = (lcmRange (7430 * n) : ℚ) := by
  unfold reducedLcm
  have hPhi : (Phi n : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Phi_pos n))
  field_simp [hPhi]

/--
@isnad1 id=eq.0h1v.s4.a59ad7f3b398 from=translated src=- shape=27c7c617 vocab=00650e1e
-/
theorem reducedLcmNat_mul_Phi (n : ℕ) :
    reducedLcmNat n * Phi n = lcmRange (7430 * n) := by
  unfold reducedLcmNat
  exact Nat.div_mul_cancel (Phi_dvd_lcmRange n)

/--
@isnad1 id=dvd.0h1v.s4.fe52c2a42cf9 from=translated src=- shape=5f699161 vocab=33db1e9b
-/
theorem reducedLcmNat_dvd_lcmRange (n : ℕ) :
    reducedLcmNat n ∣ lcmRange (7430 * n) := by
  refine ⟨Phi n, ?_⟩
  simpa [Nat.mul_comm] using (reducedLcmNat_mul_Phi n).symm

/--
@isnad1 id=lt.1h1v.s4.027fedbae88b from=translated src=- shape=35bd48ee vocab=bc3cb656
-/
theorem reducedLcmNat_pos (n : ℕ) (hn : 0 < n) :
    0 < reducedLcmNat n := by
  have hl0 : lcmRange (7430 * n) ≠ 0 := by
    unfold lcmRange
    rw [Finset.lcm_ne_zero_iff]
    intro k hk
    exact Nat.ne_of_gt (Finset.mem_Icc.mp hk).1
  have hl : 0 < lcmRange (7430 * n) := Nat.pos_of_ne_zero hl0
  have hp : 0 < Phi n := Phi_pos n
  exact Nat.div_pos (Nat.le_of_dvd hl (Phi_dvd_lcmRange n)) hp

/--
@isnad1 id=dvd.3h4v.s5.3213bed49c0b from=translated src=- shape=7e339b2d vocab=a2e7c113
-/
theorem reducedLcm_nat_mul_dvd {L Phi j q : ℕ}
    (hPhi : Phi ∣ L) (hj : j ∣ L) (hq : Phi ∣ q) :
    j ∣ (L / Phi) * q := by
  rcases hq with ⟨r, rfl⟩
  rw [← Nat.mul_assoc, Nat.div_mul_cancel hPhi]
  exact dvd_mul_of_dvd_left hj r

/--
@isnad1 id=dvd.2h3v.s5.a2f53896fe3c from=translated src=- shape=feb34111 vocab=62e3c2e4
-/
theorem reducedLcmNat_clears_divisor
    (n j q : ℕ) (hj : j ∣ lcmRange (7430 * n))
    (hq : Phi n ∣ q) :
    j ∣ reducedLcmNat n * q := by
  exact reducedLcm_nat_mul_dvd (Phi_dvd_lcmRange n) hj hq

/--
@isnad1 id=dvd.3h3v.s5.31c8d4a026a5 from=translated src=- shape=06388242 vocab=c6fe5b8e
-/
theorem reducedLcmNat_clears_signed_divisor
    (n : ℕ) (j : ℤ) (q : ℕ)
    (hj0 : j ≠ 0) (hjbound : j.natAbs ≤ 7430 * n)
    (hq : Phi n ∣ q) :
    j.natAbs ∣ reducedLcmNat n * q := by
  have hjpos : 1 ≤ j.natAbs := by
    exact Nat.succ_le_iff.mpr (Int.natAbs_pos.mpr hj0)
  have hjL : j.natAbs ∣ lcmRange (7430 * n) :=
    dvd_lcmRange (7430 * n) j.natAbs hjpos hjbound
  exact reducedLcmNat_clears_divisor n j.natAbs q hjL hq

/--
@isnad1 id=le.1h4v.s7.87bcf379b4e9 from=translated src=- shape=3b9892a8 vocab=80f27b39
-/
theorem finiteFieldSupport_low_half (k A B C : ℤ)
    (hC : A + 2 * B + (k + 1) ≤ C) :
    A + 2 * B + (2 * k + 1) - 1 - C ≤ k - 1 := by
  linarith

/--
@isnad1 id=and.2h4v.s7.f3281d249818 from=translated src=- shape=3e3f4cf0 vocab=3b732f86
-/
theorem finiteFieldSupport_high_half (k A B C : ℤ)
    (hA : 2 * k + 2 ≤ 2 * A)
    (hC : A + 2 * B - k ≤ C) :
    k < A ∧ A + 2 * B + (2 * k + 1) - 1 - C ≤ 3 * k := by
  constructor <;> linarith

/--
@isnad1 id=eq.0h2v.s9.c3f8c82b2ab7 from=translated src=- shape=fc6a075d vocab=b10dfafb
-/
theorem derivative_pth_power_zmod (p : ℕ) [Fact p.Prime]
    (f : Polynomial (ZMod p)) :
    Polynomial.derivative (f ^ p) = 0 := by
  rw [Polynomial.derivative_pow]
  have hp : (p : ZMod p) = 0 := CharP.cast_eq_zero (ZMod p) p
  simp [hp]

/--
@isnad1 id=eq.1h2v.s9.43a108c3df64 from=translated src=- shape=56639bc1 vocab=f2cedf19
-/
theorem derivative_X_pow_succ_zero_of_dvd (p r : ℕ) [Fact p.Prime]
    (h : p ∣ r + 1) :
    Polynomial.derivative (Polynomial.X ^ (r + 1) : Polynomial (ZMod p)) = 0 := by
  rw [Polynomial.derivative_X_pow]
  rcases h with ⟨k, hk⟩
  have hp : (p : ZMod p) = 0 := CharP.cast_eq_zero (ZMod p) p
  have hz : ((r + 1 : ℕ) : ZMod p) = 0 := by
    rw [hk, Nat.cast_mul, hp, zero_mul]
  simp [hz]

/--
@isnad1 id=eq.0h3v.s10.703894582320 from=translated src=- shape=11374c98 vocab=60101c7a
-/
theorem pth_power_mul_derivative_eq_derivative_mul (p : ℕ) [Fact p.Prime]
    (U V : Polynomial (ZMod p)) :
    U ^ p * Polynomial.derivative V =
      Polynomial.derivative (U ^ p * V) := by
  rw [Polynomial.derivative_mul, derivative_pth_power_zmod]
  simp

def obstructionFree (p : ℕ) (f : Polynomial (ZMod p)) : Prop :=
  ∀ r, p ∣ r + 1 → f.coeff r = 0

noncomputable def polynomialPrimitive (p : ℕ) [Fact p.Prime]
    (f : Polynomial (ZMod p)) : Polynomial (ZMod p) :=
  ∑ r ∈ f.support,
    Polynomial.monomial (r + 1)
      (if ((r + 1 : ℕ) : ZMod p) = 0 then 0
       else f.coeff r / ((r + 1 : ℕ) : ZMod p))

/--
@isnad1 id=eq.1h2v.s9.c9d99132a24a from=translated src=- shape=feb7ae6e vocab=364f3914
-/
theorem polynomialPrimitive_derivative (p : ℕ) [Fact p.Prime]
    (f : Polynomial (ZMod p)) (hf : obstructionFree p f) :
    Polynomial.derivative (polynomialPrimitive p f) = f := by
  unfold polynomialPrimitive
  calc
    Polynomial.derivative
        (∑ r ∈ f.support,
          Polynomial.monomial (r + 1)
            (if ((r + 1 : ℕ) : ZMod p) = 0 then 0
             else f.coeff r / ((r + 1 : ℕ) : ZMod p))) =
        ∑ r ∈ f.support,
          Polynomial.derivative (Polynomial.monomial (r + 1)
            (if ((r + 1 : ℕ) : ZMod p) = 0 then 0
             else f.coeff r / ((r + 1 : ℕ) : ZMod p))) := by
      rw [Polynomial.derivative_sum]
    _ = ∑ r ∈ f.support, Polynomial.monomial r (f.coeff r) := by
      apply Finset.sum_congr rfl
      intro r hr
      rw [Polynomial.derivative_monomial]
      have hrc : f.coeff r ≠ 0 := Polynomial.mem_support_iff.mp hr
      have hnot : ¬ p ∣ r + 1 := by
        intro hd
        exact hrc (hf r hd)
      have hcast : ((r + 1 : ℕ) : ZMod p) ≠ 0 := by
        intro hz
        exact hnot ((ZMod.natCast_eq_zero_iff _ _).mp hz)
      have hcast' : ((r : ZMod p) + 1) ≠ 0 := by
        simpa [Nat.cast_add] using hcast
      simp [hcast']
    _ = f := f.as_sum_support.symm

end PiIrrationality
