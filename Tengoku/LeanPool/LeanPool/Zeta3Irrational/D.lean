/-
Copyright (c) 2026 Junqi Liu, Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junqi Liu, Jujian Zhang
-/
module

public import Tengoku

/-!
# LeanPool.Zeta3Irrational.D
-/

@[expose] public section

namespace LeanPool.Zeta3Irrational

open scoped Nat
open BigOperators

/-- The least common multiple of a finite set of natural numbers. -/
def d (s : Finset ℕ) : ℕ := s.lcm id

/--
@isnad1 id=eq.0h2v.s4.d712858ed37f from=translated src=- shape=bfb40e33 vocab=7fba80f1
-/
theorem d_insert (s : Finset ℕ) (n : ℕ) : d (insert n s) = Nat.lcm n (d s) := by
  simp only [d, Finset.lcm_insert, id_eq]
  rfl

/--
@isnad1 id=eq.0h0v.s3.900a97cbcfea from=translated src=- shape=70216182 vocab=1c473e93
-/
theorem d_empty : d (∅ : Finset ℕ) = 1 := by simp [d]

/--
@isnad1 id=dvd.1h2v.s4.0a0ffaafb0b2 from=translated src=- shape=b2bb38c8 vocab=0afcea1e
-/
theorem dvd_d_of_mem (s : Finset ℕ) (n : ℕ) (h : n ∈ s) : n ∣ d s :=
  Finset.dvd_lcm h

/--
@isnad1 id=dvd.1h2v.s4.77ecbd8d731b from=translated src=- shape=9c396fbe vocab=ea19422b
-/
theorem d_dvd_d_of_le (s t : Finset ℕ) (h : s ≤ t) : d s ∣ d t := by
  apply Finset.lcm_dvd
  intro n hn
  exact dvd_d_of_mem t n (h hn)

/--
@isnad1 id=ne.1h1v.s4.8f604567f459 from=translated src=- shape=2be05866 vocab=205a072f
-/
theorem d_ne_zero (s : Finset ℕ) (hs : 0 ∉ s) : d s ≠ 0 := by
  delta d
  simp_all

/--
@isnad1 id=eq.1h1v.s4.f222553288cb from=translated src=- shape=7ef691f2 vocab=205a072f
-/
theorem d_eq_zero (s : Finset ℕ) (hs : 0 ∈ s) : d s = 0 := by
  delta d
  simp_all

/--
@isnad1 id=or.2h3v.s4.3878734f3e48 from=translated src=- shape=9eafc4d3 vocab=b3a7df24
-/
theorem Nat_Prime_dvd_lcm {p} (hp : Nat.Prime p) (a b) (h : p ∣ Nat.lcm a b) :
    p ∣ a ∨ p ∣ b := by
  have := h.trans <| Nat.lcm_dvd_mul a b
  rwa [Nat.Prime.dvd_mul hp] at this

/--
@isnad1 id=eq.2h2v.s5.65a23df3472e from=translated src=- shape=805c953e vocab=86146fa5
-/
theorem Nat_primeFactors_lcm {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) :
    (a.lcm b).primeFactors = a.primeFactors ∪ b.primeFactors := by
  ext p
  rw [Nat.mem_primeFactors_iff_mem_primeFactorsList, Finset.mem_union,
    Nat.mem_primeFactors_iff_mem_primeFactorsList, Nat.mem_primeFactors_iff_mem_primeFactorsList]
  simp only [Nat.mem_primeFactorsList', ne_eq]
  constructor
  · rintro ⟨hp1, hp2, hp3⟩
    obtain hp4 | hp4 := Nat_Prime_dvd_lcm hp1 a b hp2
    · simp_all
    · simp_all
  · rintro (⟨hp1, hp2, hp3⟩|⟨hp1, hp2, hp3⟩)
    · refine ⟨hp1, hp2.trans <| dvd_lcm_left a b, ?_⟩
      simp_all
    · refine ⟨hp1, hp2.trans <| dvd_lcm_right a b, ?_⟩
      simp_all

private lemma Nat_lcm_pow_n (n a b : ℕ) (ha : a ≠ 0) (hb : b ≠ 0) :
    (Nat.lcm a b) ^ n = Nat.lcm (a ^ n) (b ^ n) := by
  apply Nat.eq_of_factorization_eq
  · exact pow_ne_zero n (Nat.lcm_ne_zero ha hb)
  · exact Nat.lcm_ne_zero (pow_ne_zero n ha) (pow_ne_zero n hb)
  intro p
  rw [Nat.factorization_pow, Nat.factorization_lcm ha hb,
    Nat.factorization_lcm (pow_ne_zero n ha) (pow_ne_zero n hb), Nat.factorization_pow,
    Nat.factorization_pow]
  simp_all

/--
@isnad1 id=eq.0h2v.s5.27e54f030b8f from=translated src=- shape=d7e72660 vocab=68ce1cd9
-/
theorem Nat_lcm_pow_two (a b : ℕ) : (Nat.lcm a b) ^ 2 = Nat.lcm (a ^ 2) (b ^ 2) := by
  by_cases ha : a = 0
  · simp_all
  by_cases hb : b = 0
  · simp_all
  exact Nat_lcm_pow_n 2 a b ha hb

/--
@isnad1 id=eq.0h2v.s5.beed106125e7 from=translated src=- shape=d7e72660 vocab=68ce1cd9
-/
theorem Nat_lcm_pow_three (a b : ℕ) :
    (Nat.lcm a b) ^ 3 = Nat.lcm (a ^ 3) (b ^ 3) := by
  by_cases ha : a = 0
  · simp_all
  by_cases hb : b = 0
  · simp_all
  exact Nat_lcm_pow_n 3 a b ha hb

/--
@isnad1 id=eq.0h1v.s5.4af03d4ad437 from=translated src=- shape=c634c1b5 vocab=835d27a3
-/
theorem d_sq (s : Finset ℕ) : (d s)^2 = d (s.image (· ^ 2)) := by
  induction s using Finset.induction_on with
  | empty => simp [d]
  | @insert i s hi ih =>
    rw [d_insert, Finset.image_insert, d_insert, ← ih, Nat_lcm_pow_two]

/--
@isnad1 id=eq.0h1v.s5.256924d3f2dc from=translated src=- shape=c634c1b5 vocab=835d27a3
-/
theorem d_cube (s : Finset ℕ) : (d s)^3 = d (s.image (· ^ 3)) := by
  induction s using Finset.induction_on with
  | empty => simp [d]
  | @insert i s hi ih =>
    rw [d_insert, Finset.image_insert, d_insert, ← ih, Nat_lcm_pow_three]

/--
@isnad1 id=eq.0h1v.s6.300c1d864114 from=translated src=- shape=d31889e7 vocab=12e25164
-/
theorem d_sq' (n : ℕ) :
    d (Finset.Icc 1 n)^2 = d (Finset.Icc 1 n |>.image (· ^ 2))  := d_sq _

/--
@isnad1 id=eq.0h1v.s6.a22108b2020e from=translated src=- shape=d31889e7 vocab=12e25164
-/
theorem d_cube' (n : ℕ) :
    d (Finset.Icc 1 n)^3 = d (Finset.Icc 1 n |>.image (· ^ 3))  := d_cube _

/--
@isnad1 id=lt.0h1v.s4.6c6ea67d8278 from=translated src=- shape=f995d4c0 vocab=9b79045f
-/
theorem fin_d_neq_zero (n : ℕ) : d (Finset.Icc 1 n) > 0 := by
  suffices d (Finset.Icc 1 n) ≠ 0 by omega
  apply d_ne_zero
  simp only [Finset.mem_Icc, nonpos_iff_eq_zero, one_ne_zero, zero_le, and_true, not_false_eq_true]

/--
@isnad1 id=eq.2h3v.s6.dc8ab5968b1c from=translated src=- shape=1f35a49d vocab=e1fecda1
-/
theorem lcm_factorization (m n p : ℕ) (hm : m ≠ 0) (hn : n ≠ 0) :
    (m.lcm n).factorization p = max (m.factorization p) (n.factorization p) := by
  rw [Nat.factorization_lcm hm hn]
  aesop

/--
@isnad1 id=eq.2h2v.s6.6b6c296455ea from=translated src=- shape=ad89d1af vocab=a4becf5f
-/
theorem d_factorization (s : Finset ℕ) (hs : s.Nonempty) (p : ℕ) (hs₁ : 0 ∉ s) :
    (d s).factorization p =
    (s.image fun i => i.factorization p).max' (by aesop) := by
  induction s using Finset.induction_on with
  | empty => simp only [Finset.not_nonempty_empty] at hs
  | @insert m s hm ih =>
    rw [d_insert, lcm_factorization _ _ _]
    · if hs : s.Nonempty
      then
      simp_all
      else
      simp only [Finset.not_nonempty_iff_eq_empty] at hs
      subst hs
      simp only [d_empty, Nat.factorization_one, Finsupp.coe_zero, Pi.zero_apply, zero_le,
        max_eq_left, insert_empty_eq, Finset.image_singleton, Finset.max'_singleton]
    · aesop
    · apply d_ne_zero
      aesop

/--
@isnad1 id=eq.2h2v.s6.5d505537627b from=translated src=- shape=7ec1f50f vocab=ffd63f48
-/
theorem d_factorization' (s : Finset ℕ) (hs : s.Nonempty) (p : ℕ) (hs₁ : 0 ∉ s) :
    ((d s).factorization p : ℝ) =
    (((s.image fun (i : ℕ) => (i.factorization p : ℝ)))).max' (by aesop) := by
  rw [d_factorization s hs p hs₁]
  induction s using Finset.induction_on with
  | empty => simp only [Finset.not_nonempty_empty] at hs
  | @insert m s _ ih =>
    simp_rw [Finset.image_insert]
    if hs : s.Nonempty
    then
    simp_all
    else
    aesop

/--
@isnad1 id=eq.1h1v.s5.b2846d7a4332 from=translated src=- shape=72e9423b vocab=9de5b430
-/
theorem d_primeFactors (s : Finset ℕ) (hs : 0 ∉ s) :
    (d s).primeFactors = s.sup fun i => i.primeFactors := by
   induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sup_empty, Finset.bot_eq_empty, Nat.primeFactors_eq_empty]
    right
    simp only [d_empty]
  | @insert m s hm ih =>
    simp only [Finset.mem_insert, not_or] at hs
    rw [d_insert, Nat_primeFactors_lcm (by aesop) (d_ne_zero _ (by aesop))]
    simp_all

/--
@isnad1 id=eq.0h1v.s6.f08cf69140ec from=translated src=- shape=74654cef vocab=87155ae9
-/
theorem d_factorization_eq_div_log'' (p : ℕ) :
    (d (Finset.Icc 1 0)).factorization p =
    ⌊Real.log 0 / Real.log p⌋₊ := by
  simp [d_empty]

/--
@isnad1 id=eq.1h2v.s6.f62d68251064 from=translated src=- shape=88cb7cde vocab=db07b267
-/
theorem d_factorization_eq_div_log' (n p : ℕ) (hp : Nat.Prime p) :
    (d (Finset.Icc 1 (n + 1))).factorization p =
    ⌊Real.log (n + 1) / Real.log p⌋₊ := by
  symm
  rw [Real.log_div_log]
  rw [Nat.floor_eq_iff]
  · rw [d_factorization' (s := Finset.Icc 1 (n + 1)) (hs := by exact ⟨1, by simp⟩)
      (p := p) (hs₁ := by simp)]
    · constructor
      · rw [Finset.max'_le_iff]
        intro y hy
        rw [Real.le_logb_iff_rpow_le]
        · simp only [Finset.mem_image, Finset.mem_Icc] at hy
          obtain ⟨x, hx, rfl⟩ := hy
          have h := @Nat.pow_factorization_choose_le p x 1 (by omega)
          norm_cast
          simp only [Nat.choose_one_right] at h
          linarith
        · norm_cast
          exact Nat.Prime.one_lt hp
        · norm_cast
          omega
      · rw [← sub_lt_iff_lt_add]
        · by_contra! h
          rw [Finset.max'_le_iff] at h
          set y := (Finset.image (fun i ↦ i.factorization p)
            (Finset.Icc 1 (n + 1))).max' (by aesop)
          have hy : (y : ℝ) ∈
              (Finset.image (fun i ↦ (i.factorization p : ℝ)) (Finset.Icc 1 (n + 1))) := by
            simp only [Finset.mem_image, Finset.mem_Icc, Nat.cast_inj]
            simp_rw [← Finset.mem_Icc]
            rw [← Finset.mem_image]
            exact Finset.max'_mem _ _
          specialize h (y : ℝ) hy
          rw [le_sub_iff_add_le, Real.le_logb_iff_rpow_le] at h
          · have h2 : y + 1 ∉
                (Finset.image (fun i ↦ i.factorization p) (Finset.Icc 1 (n + 1))) := by
              by_contra! hy1
              suffices y + 1 ≤ y by linarith
              exact Finset.le_max' _ _ hy1
            simp only [Finset.mem_image, Finset.mem_Icc, not_exists, not_and, and_imp] at h2
            norm_cast at h
            specialize h2 (p ^ (y + 1)) (by exact one_le_pow_of_one_le' (Nat.Prime.one_le hp) _) h
            aesop
          · norm_cast
            exact Nat.Prime.one_lt hp
          · norm_cast
            omega
  · apply Real.logb_nonneg
    · norm_cast
      exact Nat.Prime.one_lt hp
    · simp_all

/--
@isnad1 id=eq.1h2v.s6.b6360fe41ba1 from=translated src=- shape=330dde4f vocab=8e972207
-/
theorem d_factorization_eq_div_log (n p : ℕ) (hp : Nat.Prime p) :
    (d (Finset.Icc 1 n)).factorization p =
    ⌊Real.log n / Real.log p⌋₊ := by
  cases n
  · simp only [zero_lt_one, Finset.Icc_eq_empty_of_lt, d_empty, Nat.factorization_one,
    Finsupp.coe_zero, Pi.zero_apply, CharP.cast_eq_zero, Real.log_zero, zero_div, Nat.floor_zero]
  · rw [d_factorization_eq_div_log' (hp := hp)]
    simp

/--
@isnad1 id=eq.0h1v.s6.7c530bfc6e7e from=translated src=- shape=b330866c vocab=0c716f2d
-/
theorem d_eq_prod_pow' (n : ℕ) :
    d (Finset.Icc 1 (n + 1)) =
    ∏ p ∈ (((n + 1) + 1).primesBelow),
      p ^ ((Finset.Icc 1 (n + 1)).image (fun i => i.factorization p)).max' (by aesop) := by
  rw [← Nat.prod_factorization_pow_eq_self (n := d (Finset.Icc 1 (n + 1)))]
  · simp only [Finsupp.prod, Nat.support_factorization]
    rw [d_primeFactors _ (by aesop)]
    refine Finset.prod_congr ?_ ?_
    · ext p
      constructor <;> intro hp
      · rw [Finset.mem_sup] at hp
        obtain ⟨m, H, h⟩ := hp
        simp only [Finset.mem_Icc] at H
        rw [Nat.mem_primesBelow]
        simp only [Nat.mem_primeFactors, ne_eq] at h
        constructor
        · linarith [Nat.le_of_dvd (by omega) h.2.1]
        · exact h.1
      · rw [Finset.mem_sup]
        use p
        simp only [Finset.mem_Icc, Nat.mem_primeFactors, dvd_refl, ne_eq, true_and]
        rw [Nat.mem_primesBelow] at hp
        constructor
        · exact ⟨Nat.Prime.one_le hp.2, (by linarith)⟩
        · aesop
    · intro p _
      rw [d_factorization (s := Finset.Icc 1 (n + 1)) (hs := by exact ⟨1, by simp⟩)
        (p := p) (hs₁ := by simp)]
  · apply d_ne_zero
    aesop

/--
@isnad1 id=eq.0h1v.s6.6d6694b53484 from=translated src=- shape=c4b0c803 vocab=e36cd061
-/
theorem d_eq_prod_pow'' (n : ℕ) :
    d (Finset.Icc 1 (n + 1)) =
    ∏ p ∈ (((n + 1) + 1).primesBelow),
      p ^ ⌊(Real.log ((n + 1) : ℝ)) / (Real.log (p : ℝ))⌋₊ := by
  rw [d_eq_prod_pow']
  refine Finset.prod_congr rfl ?_
  intro p hp
  simp only [Nat.mem_primesBelow] at hp
  congr 1
  have eq := d_factorization_eq_div_log (n + 1) p
  simp only [Nat.cast_add, Nat.cast_one] at eq
  rw [← eq hp.2, d_factorization (s := Finset.Icc 1 (n + 1)) (hs := by exact ⟨1, by simp⟩)
    (p := p) (hs₁ := by simp)]

/--
@isnad1 id=eq.0h1v.s6.6e60c2d989f0 from=translated src=- shape=bb81a872 vocab=e36cd061
-/
theorem d_eq_prod_pow (n : ℕ) :
    d (Finset.Icc 1 n) =
    ∏ p ∈ ((n + 1).primesBelow),
      p ^ ⌊(Real.log (n : ℝ)) / (Real.log (p : ℝ))⌋₊ := by
  cases n
  · simp [d_empty]
  · rw [d_eq_prod_pow'']
    simp

end LeanPool.Zeta3Irrational
