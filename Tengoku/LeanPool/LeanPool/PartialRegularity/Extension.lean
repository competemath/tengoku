/-
Copyright (c) 2026 Evan Chen, Kenny Lau, Seewoo Lee, Ken Ono, Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Evan Chen, Kenny Lau, Seewoo Lee, Ken Ono, Jujian Zhang
-/
module

public import Tengoku
/-! # Irregular primes and Bernoulli numbers (extension)

This file proves a variant of the main result with an explicit constant: the count
of odd primes `p ≤ X` that are not `M_α(p)`-regular is bounded by `10 · X / (log X)^(2α)`. -/

@[expose] public section

namespace LeanPool.PartialRegularity.Extension

/-- A prime `p` is `m`-regular if it has no Bernoulli numerator divisor in range. -/
def isMRegular (m : ℕ) (p : ℕ) : Prop :=
  Nat.Prime p ∧ Odd p ∧
    ∀ k : ℕ, 1 ≤ k → 2 * k ≤ min m (p - 3) → ¬((p : ℤ) ∣ (bernoulli (2 * k)).num)

/-- The cutoff `M_α(p) = ⌊sqrt p / (log p)^α⌋`. -/
noncomputable def MAlpha (α : ℝ) (p : ℕ) : ℕ :=
  ⌊Real.sqrt p / (Real.log p) ^ α⌋₊

/-- The set of irregular primes up to `X` for the cutoff `M_α`. -/
noncomputable def irregularPrimesUpTo (α : ℝ) (X : ℕ) : Set ℕ :=
  {p : ℕ | p ≤ X ∧ Nat.Prime p ∧ Odd p ∧ ¬isMRegular (MAlpha α p) p}

/-- A uniform upper bound for the relevant `M_α(p)` values with `p ≤ X`. -/
noncomputable def KMaxSup (α : ℝ) (X : ℕ) : ℕ :=
  (Finset.filter (fun p => Nat.Prime p) (Finset.range (X + 1))).sup (MAlpha α) + 1

/-- Primes counted at a fixed Bernoulli index `k` in the double-counting argument. -/
noncomputable def AK (α : ℝ) (X : ℕ) (k : ℕ) : Set ℕ :=
  {p : ℕ | p ≤ X ∧ Nat.Prime p ∧ Odd p ∧ 2 * k ≤ MAlpha α p ∧
           (p : ℤ) ∣ (bernoulli (2 * k)).num}

/-- The explicit constant used for the Bernoulli-factor counting bound. -/
noncomputable def bernoulliOmegaConst : ℝ := 10

/--
@isnad1 id=lt.0h0v.s3.cca2fb4cc15a from=translated src=- shape=ffdda526 vocab=0fc72318
-/
lemma bernoulliOmegaConst_pos : bernoulliOmegaConst > 0 := by norm_num [bernoulliOmegaConst]

/--
@isnad1 id=lt.2h3v.s4.bd547221be92 from=translated src=- shape=6d2b5f8b vocab=a260797a
-/
lemma M_alpha_lt_K_max_sup (α : ℝ) (X : ℕ) (p : ℕ) (hp : Nat.Prime p) (hpX : p ≤ X) :
    MAlpha α p < KMaxSup α X := by
  have h1 : p ∈ Finset.filter (fun p => Nat.Prime p) (Finset.range (X + 1)) := by
    simpa only [Finset.mem_filter, Finset.mem_range] using ⟨by omega, hp⟩
  have h2 := Finset.le_sup h1 (f := MAlpha α)
  unfold KMaxSup
  omega

/--
@isnad1 id=le.0h2v.s5.5623dce0dd5e from=translated src=- shape=48a35437 vocab=ad5e5925
-/
lemma irregularPrimes_subset_union (α : ℝ) (X : ℕ) :
    irregularPrimesUpTo α X ⊆ ⋃ k ∈ Finset.range (KMaxSup α X), AK α X k := by
  intro p hp
  simp only [irregularPrimesUpTo, Set.mem_ofPred_eq] at hp
  obtain ⟨hpX, hprime, hodd, hnot_reg⟩ := hp
  simp only [isMRegular, hprime, hodd, true_and, not_forall, not_not] at hnot_reg
  obtain ⟨k, _, hk2, hdiv⟩ := hnot_reg
  rw [Set.mem_iUnion₂]
  have h2k_le : 2 * k ≤ MAlpha α p := (Nat.le_min.mp hk2).1
  refine ⟨k, ?_, ?_⟩
  · rw [Finset.mem_range]
    calc k ≤ 2 * k := Nat.le_mul_of_pos_left k (by norm_num : 0 < 2)
      _ ≤ MAlpha α p := h2k_le
      _ < KMaxSup α X := M_alpha_lt_K_max_sup α X p hprime hpX
  · simp only [AK, Set.mem_ofPred_eq]
    exact ⟨hpX, hprime, hodd, h2k_le, hdiv⟩

/--
@isnad1 id=eq.0h2v.s4.a319e0c8922b from=translated src=- shape=947a5929 vocab=d0378289
-/
lemma A_k_zero_empty (α : ℝ) (X : ℕ) : AK α X 0 = ∅ := by
  apply Set.eq_empty_of_forall_notMem
  intro p hp
  simp only [AK, Set.mem_ofPred_eq] at hp
  have hp_dvd : (p : ℤ) ∣ (bernoulli 0).num := by simpa using hp.2.2.2.2
  simp only [bernoulli_zero, Rat.num_one] at hp_dvd
  linarith [Int.le_of_dvd (by norm_num) hp_dvd, hp.2.1.two_le]

/--
@isnad1 id=dvd.2h2v.s4.57ee593f1fc9 from=translated src=- shape=de46092e vocab=cc897b22
-/
lemma prime_int_dvd_natAbs (p : ℕ) (z : ℤ) (_hp : Nat.Prime p)
    (hdvd : (p : ℤ) ∣ z) : p ∣ z.natAbs :=
  Int.natCast_dvd.mp hdvd

/--
@isnad1 id=ne.1h1v.s5.fdb2fc593a31 from=translated src=- shape=9a024c6d vocab=c661cc7e
-/
lemma bernoulli_two_mul_ne_zero (k : ℕ) (hk : k ≠ 0) : bernoulli (2 * k) ≠ 0 := by
  intro h
  have hre : (1 : ℝ) < 2 * k :=
    mod_cast lt_of_lt_of_le one_lt_two (show (2 : ℕ) ≤ 2 * k by omega)
  have hne : riemannZeta (2 * k) ≠ 0 := riemannZeta_ne_zero_of_one_lt_re <| by
    simp_all
  have hzeta := riemannZeta_two_mul_nat hk
  simp_all

/--
@isnad1 id=ne.1h1v.s5.4223fbde5746 from=translated src=- shape=5890f67f vocab=69d88c9b
-/
lemma bernoulli_num_natAbs_ne_zero (k : ℕ) (hk : 1 ≤ k) :
    (bernoulli (2 * k)).num.natAbs ≠ 0 := by
  simp only [ne_eq, Int.natAbs_eq_zero, Rat.num_ne_zero]
  exact bernoulli_two_mul_ne_zero k (Nat.one_le_iff_ne_zero.mp hk)

/--
@isnad1 id=le.1h3v.s5.b7c957b20422 from=translated src=- shape=885e2811 vocab=73b7ac79
-/
lemma A_k_subset_primeFactors (α : ℝ) (X : ℕ) (k : ℕ) (hk : 1 ≤ k) :
    AK α X k ⊆ ↑((bernoulli (2 * k)).num.natAbs.primeFactors) := fun p hp => by
  simp only [AK, Set.mem_ofPred_eq] at hp
  rw [Finset.mem_coe, Nat.mem_primeFactors]
  exact ⟨hp.2.1, prime_int_dvd_natAbs p _ hp.2.1 hp.2.2.2.2,
    bernoulli_num_natAbs_ne_zero k hk⟩

/--
@isnad1 id=le.1h3v.s5.0a54a30036af from=translated src=- shape=66539169 vocab=770eeb28
-/
lemma card_A_k_bound (α : ℝ) (X : ℕ) (k : ℕ) (hk : 1 ≤ k) :
    ((AK α X k).ncard : ℝ) ≤
      ArithmeticFunction.cardDistinctFactors (bernoulli (2 * k)).num.natAbs := by
  have hle := Set.ncard_le_ncard (A_k_subset_primeFactors α X k hk) (Finset.finite_toSet _)
  rw [Set.ncard_coe_finset] at hle
  rw [ArithmeticFunction.cardDistinctFactors_apply, ← List.card_toFinset
      (bernoulli (2 * k)).num.natAbs.primeFactorsList, ← Nat.primeFactors.eq_1]
  exact Nat.cast_le.mpr hle

/--
@isnad1 id=le.2h2v.s5.3428bb1b0182 from=translated src=- shape=548042b2 vocab=432c21bb
-/
lemma sorted_primes_get_ge (l : List ℕ) (hsort : l.SortedLT) (hge2 : ∀ x ∈ l, 2 ≤ x)
    (i : Fin l.length) : i.val + 2 ≤ l.get i := by
  have hmono : StrictMono l.get := List.SortedLT.strictMono_get hsort
  induction h : i.val generalizing i with
  | zero =>
    simpa only [zero_add] using hge2 (l.get i) (List.get_mem ..)
  | succ n ih =>
    have hn_lt : n < l.length := by have := h ▸ i.isLt; omega
    let j : Fin l.length := ⟨n, hn_lt⟩
    have ih_j : n + 2 ≤ l.get j := ih j rfl
    have hlt : l.get j < l.get i := hmono (by change n < i.val; omega)
    omega

/--
@isnad1 id=le.3h3v.s5.9d0215388244 from=translated src=- shape=6e4783a1 vocab=5a0b35b3
-/
lemma rat_num_natAbs_le_of_abs_le_and_den_dvd {q : ℚ} {M D : ℕ}
    (hM : |(q : ℝ)| ≤ M) (hD : q.den ∣ D) (hpos : 0 < D) : q.num.natAbs ≤ M * D := by
  have hden_le : q.den ≤ D := Nat.le_of_dvd hpos hD
  have hden_pos : (0 : ℝ) < q.den := Nat.cast_pos.mpr q.den_pos
  have key : (q.num.natAbs : ℝ) = |(q : ℝ)| * q.den := by
    rw [Rat.cast_def q, abs_div, abs_of_pos hden_pos, Nat.cast_natAbs, Int.cast_abs,
        div_mul_cancel₀ _ hden_pos.ne']
  have h : (q.num.natAbs : ℝ) ≤ M * D := calc (q.num.natAbs : ℝ)
      = |(q : ℝ)| * q.den := key
    _ ≤ M * q.den := mul_le_mul_of_nonneg_right hM (Nat.cast_nonneg _)
    _ ≤ M * D := mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hden_le) (Nat.cast_nonneg _)
  exact_mod_cast h

/--
@isnad1 id=le.1h1v.s7.e86347aa08b5 from=translated src=- shape=fc2714a4 vocab=c6851400
-/
lemma two_mul_factorial_sq_le_pow (k : ℕ) (hk : 1 ≤ k) :
    2 * ((2 * k + 1).factorial : ℕ) ^ 2 ≤ (2 * k + 1) ^ (4 * k + 3) := by
  have h1 : (2 * k + 1).factorial ≤ (2 * k + 1) ^ (2 * k + 1) := Nat.factorial_le_pow _
  have h2' : ((2 * k + 1).factorial : ℕ) ^ 2 ≤ (2 * k + 1) ^ (4 * k + 2) := by
    calc (2 * k + 1).factorial ^ 2
        ≤ ((2 * k + 1) ^ (2 * k + 1)) ^ 2 := Nat.pow_le_pow_left h1 2
      _ = (2 * k + 1) ^ (4 * k + 2) := by rw [← pow_mul]; ring_nf
  calc 2 * (2 * k + 1).factorial ^ 2
      ≤ 2 * (2 * k + 1) ^ (4 * k + 2) := Nat.mul_le_mul_left 2 h2'
    _ ≤ (2 * k + 1) * (2 * k + 1) ^ (4 * k + 2) :=
      Nat.mul_le_mul_right _ (by omega : 2 ≤ 2 * k + 1)
    _ = (2 * k + 1) ^ (4 * k + 3) := by ring

/--
@isnad1 id=le.0h1v.s6.7fc48225b2c8 from=translated src=- shape=3650b297 vocab=c6851400
-/
lemma factorial_prod_bound (k : ℕ) :
    (2 * k).factorial * (2 * k + 1).factorial ≤ ((2 * k + 1).factorial : ℕ) ^ 2 := by
  calc (2 * k).factorial * (2 * k + 1).factorial
      ≤ (2 * k + 1).factorial * (2 * k + 1).factorial :=
        Nat.mul_le_mul_right _ (Nat.factorial_le (Nat.le_succ _))
    _ = (2 * k + 1).factorial ^ 2 := by ring

/--
@isnad1 id=dvd.0h0v.s4.4df727df5f07 from=translated src=- shape=26a89cbb vocab=8955edc4
-/
lemma bernoulli_den_dvd_factorial_base : (bernoulli 2).den ∣ Nat.factorial 3 := by
  rw [bernoulli_two, Rat.den_inv_of_ne_zero (by norm_num : (6 : ℚ) ≠ 0)]
  norm_num

/--
@isnad1 id=eq.1h3v.s4.36d4ab4d572d from=translated src=- shape=5a9a2aef vocab=1b82cff7
-/
lemma gcd_mul_coprime_eq_gcd (n a d : ℕ) (hcop : a.Coprime d) : (n * a).gcd d = n.gcd d := by
  apply Nat.dvd_antisymm
  · apply Nat.dvd_gcd
    · exact (Nat.Coprime.coprime_dvd_left (Nat.gcd_dvd_right _ _) hcop.symm).dvd_mul_right.mp
        (Nat.gcd_dvd_left _ _)
    · exact Nat.gcd_dvd_right _ _
  · exact Nat.dvd_gcd (dvd_trans (Nat.gcd_dvd_left _ _) (Nat.dvd_mul_right _ _))
      (Nat.gcd_dvd_right _ _)

/--
@isnad1 id=dvd.0h2v.s4.6da757c70c90 from=translated src=- shape=5f3dc7ea vocab=b3d3753f
-/
lemma gcd_natAbs_mul_num_dvd_n (n : ℕ) (q : ℚ) : (↑n * q.num).natAbs.gcd q.den ∣ n := by
  have h1 : (↑n * q.num).natAbs = n * q.num.natAbs := by rw [Int.natAbs_mul]; rfl
  rw [h1, gcd_mul_coprime_eq_gcd n q.num.natAbs q.den q.reduced]
  exact Nat.gcd_dvd_left n q.den

/--
@isnad1 id=dvd.1h2v.s5.dbe3406a507a from=translated src=- shape=8e66b914 vocab=7d0c6c3c
-/
lemma rat_den_dvd_mul_of_int_mul (q : ℚ) (n : ℕ) (_hn : 0 < n) :
    q.den ∣ n * (↑n * q).den := by
  have h_eq :
      (↑n : ℚ).den * q.den =
        ((↑n : ℚ) * q).den *
          ((↑n : ℚ).num * q.num).natAbs.gcd ((↑n : ℚ).den * q.den) :=
    Rat.den_mul_den_eq_den_mul_gcd (↑n) q
  simp only [Rat.den_natCast, Rat.num_natCast, one_mul] at h_eq
  rw [h_eq, mul_comm]
  exact Nat.mul_dvd_mul_right (gcd_natAbs_mul_num_dvd_n n q) ((↑n * q).den)

/--
@isnad1 id=eq.0h1v.s6.85f9d02d2dfb from=translated src=- shape=e7c71688 vocab=14a23cc3
-/
lemma choose_two_k_plus_one_two_k (k : ℕ) : (2 * k + 1).choose (2 * k) = 2 * k + 1 := by
  simp_all

/--
@isnad1 id=eq.1h1v.s6.ebdcb0440dd0 from=translated src=- shape=3137d986 vocab=22bbc0f9
-/
lemma sum_bernoulli_eq_neg_mul (k : ℕ) (hk : 2 ≤ k) :
    ∑ j ∈ Finset.range (2 * k), (↑((2 * k + 1).choose j) : ℚ) * bernoulli j =
    -(↑(2 * k + 1) : ℚ) * bernoulli (2 * k) := by
  have h_sum := sum_bernoulli (2 * k + 1)
  simp only [show 2 * k + 1 ≠ 1 by omega, ite_false] at h_sum
  rw [Finset.sum_range_succ, choose_two_k_plus_one_two_k] at h_sum
  linarith

/--
@isnad1 id=dvd.2h3v.s5.a3c120865ba5 from=translated src=- shape=678aae19 vocab=cf55e375
-/
lemma den_sum_dvd_of_each_den_dvd {n : ℕ} {f : ℕ → ℚ} {D : ℕ}
    (_hD : 0 < D) (hf : ∀ j < n, (f j).den ∣ D) :
    (∑ j ∈ Finset.range n, f j).den ∣ D := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    exact (Rat.add_den_dvd_lcm _ _).trans
      (Nat.lcm_dvd (ih fun j hj => hf j (Nat.lt_succ_of_lt hj)) (hf n (Nat.lt_succ_self n)))

/--
@isnad1 id=eq.2h2v.s6.d658877f8165 from=translated src=- shape=a0ce0f61 vocab=104b735f
-/
lemma term_vanishes_for_odd_gt_one (k j : ℕ) (hj_odd : Odd j) (hj_gt : 1 < j) :
    (↑((2 * k + 1).choose j) : ℚ) * bernoulli j = 0 := by
  simp [bernoulli_eq_zero_of_odd hj_odd hj_gt]

/--
@isnad1 id=dvd.1h1v.s6.e8e2aa6b1136 from=translated src=- shape=7cbeca53 vocab=4adba23c
-/
lemma term_j_zero_den_dvd (k : ℕ) (_hk : 2 ≤ k) :
    ((↑((2 * k + 1).choose 0) : ℚ) * bernoulli 0).den ∣ (2 * k).factorial := by
  simp [bernoulli_zero]

/--
@isnad1 id=dvd.1h1v.s6.453d7f07b0d6 from=translated src=- shape=7cbeca53 vocab=4adba23c
-/
lemma term_j_one_den_dvd (k : ℕ) (hk : 2 ≤ k) :
    ((↑((2 * k + 1).choose 1) : ℚ) * bernoulli 1).den ∣ (2 * k).factorial := by
  simp only [Nat.choose_one_right, bernoulli_one]
  have hden : ((↑(2 * k + 1) : ℚ) * (-1 / 2)).den ∣ 2 := by
    have h := Rat.mul_den_dvd (↑(2 * k + 1) : ℚ) (-1 / 2)
    simpa only [Rat.den_natCast, one_mul, show ((-1 : ℚ) / 2).den = 2 from by
      norm_num [Rat.den_neg_eq_den]] using h
  exact hden.trans (Nat.factorial_dvd_factorial (by omega : 2 ≤ 2 * k))

/--
@isnad1 id=dvd.4h2v.s7.3434cd45b544 from=translated src=- shape=45cdab51 vocab=63beebd5
-/
lemma term_even_den_dvd (k m : ℕ) (_hk : 2 ≤ k) (_hm_ge : 1 ≤ m) (hm_lt : m < k)
    (ih : (bernoulli (2 * m)).den ∣ (2 * m + 1).factorial) :
    ((↑((2 * k + 1).choose (2 * m)) : ℚ) * bernoulli (2 * m)).den ∣ (2 * k).factorial := by
  have h_mul := Rat.mul_den_dvd (↑((2 * k + 1).choose (2 * m)) : ℚ) (bernoulli (2 * m))
  simp only [Rat.den_natCast, one_mul] at h_mul
  exact (h_mul.trans ih).trans (Nat.factorial_dvd_factorial (by omega))

/--
@isnad1 id=dvd.3h2v.s7.221342fecbc4 from=translated src=- shape=f0e9d3e7 vocab=63beebd5
-/
lemma each_term_den_dvd_factorial (k : ℕ) (hk : 2 ≤ k)
    (ih : ∀ m : ℕ, 1 ≤ m → m < k → (bernoulli (2 * m)).den ∣ (2 * m + 1).factorial)
    (j : ℕ) (hj : j < 2 * k) :
    ((↑((2 * k + 1).choose j) : ℚ) * bernoulli j).den ∣ (2 * k).factorial := by
  rcases Nat.even_or_odd j with ⟨m, hm_eq⟩ | ⟨m, hm_eq⟩
  · rcases m.eq_zero_or_pos with rfl | hm_pos
    · simp_all
    · have hm_lt : m < k := by omega
      simp only [hm_eq, two_mul]
      convert term_even_den_dvd k m hk hm_pos hm_lt (ih m hm_pos hm_lt) using 2 <;> ring_nf
  · rcases m.eq_zero_or_pos with rfl | hm_pos
    · simp only [hm_eq]
      exact term_j_one_den_dvd k hk
    · simp only [hm_eq,
        term_vanishes_for_odd_gt_one k (2 * m + 1) ⟨m, rfl⟩
          (by omega : 1 < 2 * m + 1),
        Rat.den_zero]
      exact Nat.one_dvd _

/--
@isnad1 id=dvd.2h1v.s7.e8fa7c40a752 from=translated src=- shape=2da926eb vocab=f12d246c
-/
lemma den_mul_factor_bernoulli_dvd_factorial (k : ℕ) (hk : 2 ≤ k)
    (ih : ∀ m : ℕ, 1 ≤ m → m < k → (bernoulli (2 * m)).den ∣ (2 * m + 1).factorial) :
    ((2 * k + 1 : ℕ) * bernoulli (2 * k)).den ∣ (2 * k).factorial := by
  have hsum_den :
      (∑ j ∈ Finset.range (2 * k),
        (↑((2 * k + 1).choose j) : ℚ) * bernoulli j).den ∣
        (2 * k).factorial :=
    den_sum_dvd_of_each_den_dvd (Nat.factorial_pos _) (each_term_den_dvd_factorial k hk ih)
  rw [sum_bernoulli_eq_neg_mul k hk] at hsum_den
  simpa only [neg_mul, Rat.den_neg_eq_den] using hsum_den

/--
@isnad1 id=dvd.2h1v.s6.f2d426cb1f2b from=translated src=- shape=007dc5a2 vocab=84ed6b13
-/
lemma bernoulli_den_dvd_factorial_step (k : ℕ) (hk : 2 ≤ k)
    (ih : ∀ m : ℕ, 1 ≤ m → m < k → (bernoulli (2 * m)).den ∣ (2 * m + 1).factorial) :
    (bernoulli (2 * k)).den ∣ (2 * k + 1).factorial := by
  calc (bernoulli (2 * k)).den
      ∣ (2 * k + 1) * ((2 * k + 1 : ℕ) * bernoulli (2 * k)).den :=
        rat_den_dvd_mul_of_int_mul (bernoulli (2 * k)) (2 * k + 1) (Nat.succ_pos _)
    _ ∣ (2 * k + 1) * (2 * k).factorial :=
        Nat.mul_dvd_mul_left _ (den_mul_factor_bernoulli_dvd_factorial k hk ih)
    _ = (2 * k + 1).factorial := by rw [← Nat.succ_eq_add_one, Nat.factorial_succ]

/--
@isnad1 id=dvd.1h1v.s5.1b70720575a2 from=translated src=- shape=26ec3e84 vocab=09bba1d5
-/
lemma bernoulli_den_dvd_factorial (k : ℕ) (hk : 1 ≤ k) :
    (bernoulli (2 * k)).den ∣ (2 * k + 1).factorial := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    rcases k with _ | ⟨_ | k⟩
    · omega
    · simp only [Nat.reduceAdd, Nat.reduceMul]
      exact bernoulli_den_dvd_factorial_base
    · apply bernoulli_den_dvd_factorial_step
      · omega
      · simp_all

/--
@isnad1 id=lt.0h0v.s5.b2184196b8ad from=translated src=- shape=19fefa96 vocab=5d10ec1f
-/
lemma pi_sq_div_six_lt_two : Real.pi ^ 2 / 6 < 2 := by
  have h2 : Real.pi ^ 2 < 3.1416 ^ 2 := sq_lt_sq' (by linarith [Real.pi_pos]) Real.pi_lt_d4
  linarith

private lemma summable_one_div_nat_pow {m : ℕ} (hm : 1 < m) :
    Summable (fun n : ℕ => (1 : ℝ) / n ^ m) := by
  simp_all

/--
@isnad1 id=le.1h1v.s6.299bef6e5d10 from=translated src=- shape=b4eba992 vocab=0fe8820b
-/
lemma tsum_inv_pow_two_mul_le (k : ℕ) (hk : 1 ≤ k) :
    ∑' (n : ℕ), (1 : ℝ) / n ^ (2 * k) ≤ Real.pi ^ 2 / 6 := by
  have h2k : 2 ≤ 2 * k := by omega
  have h2k_ne : (2 * k : ℕ) ≠ 0 := by omega
  rw [← hasSum_zeta_two.tsum_eq]
  refine Summable.tsum_le_tsum_of_inj (fun n => n) Function.injective_id
    (fun _ _ => by positivity) ?_ (summable_one_div_nat_pow h2k)
    (summable_one_div_nat_pow one_lt_two)
  intro n
  simp only [one_div]
  rcases eq_or_ne n 0 with rfl | hn0
  · simp [zero_pow h2k_ne]
  · exact inv_anti₀ (by positivity)
      (pow_le_pow_right₀ (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn0) h2k)

/--
@isnad1 id=le.1h1v.s6.d404cb67295a from=translated src=- shape=ce902ec2 vocab=daab7b39
-/
lemma denom_ge_one (k : ℕ) (_hk : 1 ≤ k) :
    1 ≤ 2 ^ (2 * k - 1) * Real.pi ^ (2 * k) :=
  one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2))
    (one_le_pow₀ (by linarith [Real.pi_gt_three]))

/--
@isnad1 id=eq.1h1v.s7.f146da0ca235 from=translated src=- shape=d7ad3f92 vocab=800223dd
-/
lemma bernoulli_eq_zeta_formula (k : ℕ) (hk : 1 ≤ k) :
    ↑(bernoulli (2 * k)) = (-1 : ℝ) ^ (k + 1) * ((2 * k).factorial : ℝ) *
      (∑' (n : ℕ), (1 : ℝ) / n ^ (2 * k)) / (2 ^ (2 * k - 1) * Real.pi ^ (2 * k)) := by
  have hdenom_pos : 0 < 2 ^ (2 * k - 1) * Real.pi ^ (2 * k) := by positivity
  have hfact_pos : 0 < ((2 * k).factorial : ℝ) := by positivity
  have heq' : (-1 : ℝ) ^ (k + 1) * (∑' (n : ℕ), (1 : ℝ) / n ^ (2 * k)) =
      2 ^ (2 * k - 1) * Real.pi ^ (2 * k) * ↑(bernoulli (2 * k)) / ↑(2 * k).factorial := by
    conv_lhs => rw [(hasSum_zeta_nat (by omega : k ≠ 0)).tsum_eq]
    have hsq : ((-1 : ℝ) ^ (k + 1)) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; simp
    field_simp
    rw [hsq, one_mul]
  field_simp [hdenom_pos.ne', hfact_pos.ne'] at heq' ⊢
  linarith

/--
@isnad1 id=le.1h1v.s7.e3fa6343ebfb from=translated src=- shape=27ed1f24 vocab=dc3a4a3f
-/
lemma bernoulli_abs_le_formula (k : ℕ) (hk : 1 ≤ k) :
    |(bernoulli (2 * k) : ℝ)| ≤
      (2 * k).factorial * (Real.pi ^ 2 / 6) /
        (2 ^ (2 * k - 1) * Real.pi ^ (2 * k)) := by
  have hdenom_pos : 0 < 2 ^ (2 * k - 1) * Real.pi ^ (2 * k) := by positivity
  have hfact_pos : 0 < ((2 * k).factorial : ℝ) := by positivity
  rw [bernoulli_eq_zeta_formula k hk, abs_div, abs_mul, abs_mul, abs_neg_one_pow, one_mul,
      abs_of_pos hfact_pos, abs_of_nonneg (tsum_nonneg (fun n => by positivity)),
      abs_of_pos hdenom_pos]
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left (tsum_inv_pow_two_mul_le k hk) hfact_pos.le)
    hdenom_pos.le

/--
@isnad1 id=le.1h1v.s7.0fd4390530bc from=translated src=- shape=307e29fd vocab=31365a86
-/
lemma formula_le_two_mul_factorial (k : ℕ) (hk : 1 ≤ k) :
    (2 * k).factorial * (Real.pi ^ 2 / 6) /
        (2 ^ (2 * k - 1) * Real.pi ^ (2 * k)) ≤
      2 * (2 * k).factorial := by
  have hfact_pos : 0 < ((2 * k).factorial : ℝ) := by positivity
  have h1 :
      (2 * k).factorial * (Real.pi ^ 2 / 6) /
          (2 ^ (2 * k - 1) * Real.pi ^ (2 * k)) ≤
        (2 * k).factorial * (Real.pi ^ 2 / 6) / 1 :=
    div_le_div_of_nonneg_left (mul_nonneg hfact_pos.le (by positivity))
      (by linarith) (denom_ge_one k hk)
  linarith [mul_lt_mul_of_pos_left pi_sq_div_six_lt_two hfact_pos]

/--
@isnad1 id=le.1h1v.s6.77ba89bdaf31 from=translated src=- shape=aac65b13 vocab=cc94f4e4
-/
lemma bernoulli_abs_le_two_mul_factorial (k : ℕ) (hk : 1 ≤ k) :
    |(bernoulli (2 * k) : ℝ)| ≤ 2 * (2 * k).factorial :=
  (bernoulli_abs_le_formula k hk).trans (formula_le_two_mul_factorial k hk)

/--
@isnad1 id=le.1h1v.s6.a4ab4a66a961 from=translated src=- shape=d7e0d430 vocab=c25ad58e
-/
lemma bernoulli_num_natAbs_le (k : ℕ) (hk : 1 ≤ k) :
    (bernoulli (2 * k)).num.natAbs ≤ (2 * k + 1) ^ (4 * k + 3) := by
  have h_abs : |(bernoulli (2 * k) : ℝ)| ≤ (2 * (2 * k).factorial : ℕ) := by
    simpa using bernoulli_abs_le_two_mul_factorial k hk
  have h1 := rat_num_natAbs_le_of_abs_le_and_den_dvd h_abs (bernoulli_den_dvd_factorial k hk)
      (Nat.factorial_pos _)
  calc (bernoulli (2 * k)).num.natAbs
      ≤ 2 * (2 * k).factorial * (2 * k + 1).factorial := h1
    _ = 2 * ((2 * k).factorial * (2 * k + 1).factorial) := by ring
    _ ≤ 2 * ((2 * k + 1).factorial ^ 2) := Nat.mul_le_mul_left 2 (factorial_prod_bound k)
    _ ≤ (2 * k + 1) ^ (4 * k + 3) := two_mul_factorial_sq_le_pow k hk

/--
@isnad1 id=ne.1h1v.s5.435b37d7bbe4 from=translated src=- shape=a240539e vocab=e79880b0
-/
lemma bernoulli_two_mul_ne_zero_1 (k : ℕ) (hk : 1 ≤ k) : bernoulli (2 * k) ≠ 0 :=
  bernoulli_two_mul_ne_zero k (Nat.one_le_iff_ne_zero.mp hk)

/--
@isnad1 id=lt.1h1v.s5.f4252b3fa0f5 from=translated src=- shape=b0a7d21d vocab=caebe891
-/
lemma bernoulli_num_natAbs_pos (k : ℕ) (hk : 1 ≤ k) :
    0 < (bernoulli (2 * k)).num.natAbs :=
  Int.natAbs_pos.mpr (Rat.num_ne_zero.mpr (bernoulli_two_mul_ne_zero_1 k hk))

/--
@isnad1 id=le.1h2v.s4.3a5e5a535225 from=translated src=- shape=da6c2e30 vocab=c39d7c39
-/
lemma descFactorial_le_factorial (n k : ℕ) (hkn : k ≤ n) :
    n.descFactorial k ≤ n.factorial := by
  calc n.descFactorial k
      ≤ (n - k).factorial * n.descFactorial k :=
        Nat.le_mul_of_pos_left _ (Nat.factorial_pos _)
    _ = n.factorial := Nat.factorial_mul_descFactorial hkn

/--
@isnad1 id=le.1h2v.s6.c7222340d27a from=translated src=- shape=d5208a85 vocab=1b5efd2d
-/
lemma two_k_add_one_le_ten_k_sub (k i : ℕ) (hi : i ∈ Finset.range (8 * k)) :
    2 * k + 1 ≤ 10 * k - i := by
  simp only [Finset.mem_range] at hi
  omega

/--
@isnad1 id=le.1h1v.s6.e9c6675fbe21 from=translated src=- shape=cea1a514 vocab=c6851400
-/
lemma factorial_ten_k_ge_power (k : ℕ) (hk : 1 ≤ k) :
    (2 * k + 1) ^ (8 * k) ≤ (10 * k).factorial := by
  calc (2 * k + 1) ^ (8 * k)
      = (2 * k + 1) ^ (Finset.range (8 * k)).card := by simp [Finset.card_range]
    _ ≤ ∏ i ∈ Finset.range (8 * k), (10 * k - i) :=
        Finset.pow_card_le_prod _ _ _ (two_k_add_one_le_ten_k_sub k)
    _ = (10 * k).descFactorial (8 * k) := (Nat.descFactorial_eq_prod_range _ _).symm
    _ ≤ (10 * k).factorial := descFactorial_le_factorial _ _ (by omega)

/--
@isnad1 id=le.1h1v.s6.385a9d7f4737 from=translated src=- shape=e2996228 vocab=cd2a3331
-/
lemma sq_add_one_le_two_sq (A : ℝ) (hA : A ≥ 1 + Real.sqrt 2) : (A + 1) ^ 2 ≤ 2 * A ^ 2 := by
  have hsqrt2_pos : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have h1 : 0 ≤ A - (1 + Real.sqrt 2) := by linarith
  have h2 : 0 ≤ A - (1 - Real.sqrt 2) := by linarith
  have factored : A^2 - 2*A - 1 = (A - (1 + Real.sqrt 2)) * (A - (1 - Real.sqrt 2)) := by
    have sq2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    nlinarith [sq2]
  nlinarith [mul_nonneg h1 h2, factored]

/--
@isnad1 id=tendsto.1h1v.s5.8d2663ea3dc6 from=translated src=- shape=37355ac5 vocab=e5fd4074
-/
lemma tendsto_sqrt_div_log_pow_atTop (α : ℝ) (_hα : 0 < α) :
    Filter.Tendsto (fun x : ℝ => Real.sqrt x / (Real.log x) ^ α) Filter.atTop Filter.atTop := by
  simp only [Real.sqrt_eq_rpow]
  have h_littleo := isLittleO_log_rpow_rpow_atTop α (by norm_num : (0 : ℝ) < 1 / 2)
  have h_ev : ∀ᶠ x in Filter.atTop,
      (x : ℝ) ^ (1 / 2 : ℝ) = 0 → (Real.log x) ^ α = 0 := by
    filter_upwards [Filter.eventually_gt_atTop 0] with x hx h
    exact absurd h (Real.rpow_pos_of_pos hx (1 / 2)).ne'
  rw [Asymptotics.isLittleO_iff_tendsto' h_ev] at h_littleo
  have h_ev_pos :
      ∀ᶠ x in Filter.atTop, 0 < (Real.log x) ^ α / x ^ (1 / 2 : ℝ) := by
    filter_upwards [Filter.eventually_gt_atTop 1] with x hx
    exact div_pos (Real.rpow_pos_of_pos (Real.log_pos hx) α)
      (Real.rpow_pos_of_pos (by linarith) (1 / 2))
  rw [show (fun x : ℝ => x ^ (1 / 2 : ℝ) / (Real.log x) ^ α) =
      (fun x : ℝ => ((Real.log x) ^ α / x ^ (1 / 2 : ℝ))⁻¹) from
    funext fun x => (inv_div _ _).symm]
  exact Filter.Tendsto.inv_tendsto_nhdsGT_zero
    (tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ h_littleo h_ev_pos)

/--
@isnad1 id=eventual.1h1v.s6.efc335dcd0ed from=translated src=- shape=b87c4e73 vocab=ae2fd7f1
-/
lemma eventually_sqrt_div_log_ge_threshold (α : ℝ) (hα : 0 < α) :
    ∀ᶠ X : ℕ in Filter.atTop, Real.sqrt X / (Real.log X) ^ α ≥ 1 + Real.sqrt 2 := by
  rw [← Nat.comap_cast_atTop (R := ℝ)]
  exact ((tendsto_sqrt_div_log_pow_atTop α hα).eventually_ge_atTop _).comap _

/--
@isnad1 id=monotone.1h1v.s6.6276d4fb87ff from=translated src=- shape=3d1acdc6 vocab=9ae4a606
-/
lemma rpow_div_log_monotoneOn (α : ℝ) (hα : 0 < α) :
    MonotoneOn (fun x : ℝ => x ^ (1 / (2 * α)) / Real.log x) {x | Real.exp (2 * α) ≤ x} := by
  have ha : 0 < 1 / (2 * α) := by positivity
  have hanti :
      AntitoneOn (fun x => Real.log x / x ^ (1 / (2 * α)))
        {x | Real.exp (2 * α) ≤ x} := by
    simpa [Set.Ici, one_div] using Real.log_div_self_rpow_antitoneOn ha
  intro x hx y hy hxy
  simp only [Set.mem_ofPred_eq] at hx hy
  have h2α_pos : 0 < 2 * α := by linarith
  have hexp_pos : 0 < Real.exp (2 * α) := Real.exp_pos _
  have hx_pos : 0 < x := lt_of_lt_of_le hexp_pos hx
  have hy_pos : 0 < y := lt_of_lt_of_le hexp_pos hy
  have hy_gt_one : 1 < y := Real.one_lt_exp_iff.mpr h2α_pos |>.trans_le hy
  have hlogy_pos : 0 < Real.log y := Real.log_pos hy_gt_one
  have hgy_pos : 0 < Real.log y / y ^ (1 / (2 * α)) :=
    div_pos hlogy_pos (Real.rpow_pos_of_pos hy_pos _)
  have hanti_xy :
      Real.log y / y ^ (1 / (2 * α)) ≤ Real.log x / x ^ (1 / (2 * α)) :=
    hanti hx hy hxy
  change x ^ (1 / (2 * α)) / Real.log x ≤ y ^ (1 / (2 * α)) / Real.log y
  have h_eq_one_div : ∀ z : ℝ, 0 < z →
      z ^ (1 / (2 * α)) / Real.log z = 1 / (Real.log z / z ^ (1 / (2 * α))) := by
    simp_all
  rw [h_eq_one_div x hx_pos, h_eq_one_div y hy_pos]
  exact one_div_le_one_div_of_le hgy_pos hanti_xy

/--
@isnad1 id=eq.3h2v.s6.107a23bcc592 from=translated src=- shape=d46ab8b2 vocab=92e14cbe
-/
lemma rpow_div_log_pow_eq_sqrt_div_log_pow (α : ℝ) (hα : 0 < α) (x : ℝ) (hx : 0 < x)
    (hlogx_pos : 0 < Real.log x) :
    (x ^ (1 / (2 * α)) / Real.log x) ^ α = Real.sqrt x / (Real.log x) ^ α := by
  rw [Real.div_rpow (Real.rpow_nonneg hx.le _) hlogx_pos.le, ← Real.rpow_mul hx.le,
      Real.sqrt_eq_rpow]
  congr 1
  field_simp

/--
@isnad1 id=monotone.1h1v.s6.ceb1a1764855 from=translated src=- shape=4ca40982 vocab=21f97b73
-/
lemma sqrt_div_log_monotoneOn (α : ℝ) (hα : 0 < α) :
    MonotoneOn (fun x : ℝ => Real.sqrt x / (Real.log x) ^ α) {x | Real.exp (2 * α) ≤ x} := by
  intro x hx y hy hxy
  simp only [Set.mem_ofPred_eq] at hx hy
  have hexp_pos : 0 < Real.exp (2 * α) := Real.exp_pos _
  have hx_pos : 0 < x := lt_of_lt_of_le hexp_pos hx
  have hy_pos : 0 < y := lt_of_lt_of_le hexp_pos hy
  have hexp_one := Real.one_lt_exp_iff.mpr (by linarith : 0 < 2 * α)
  have hlogx_pos : 0 < Real.log x := Real.log_pos (hexp_one.trans_le hx)
  have hlogy_pos : 0 < Real.log y := Real.log_pos (hexp_one.trans_le hy)
  have hmono := rpow_div_log_monotoneOn α hα hx hy hxy
  simp only
  rw [← rpow_div_log_pow_eq_sqrt_div_log_pow α hα x hx_pos hlogx_pos,
      ← rpow_div_log_pow_eq_sqrt_div_log_pow α hα y hy_pos hlogy_pos]
  exact Real.rpow_le_rpow (div_pos (Real.rpow_pos_of_pos hx_pos _) hlogx_pos).le hmono hα.le

/--
@isnad1 id=le.3h3v.s6.a5539dd91178 from=translated src=- shape=92f3243e vocab=aa08b0bd
-/
lemma sqrt_div_log_le_of_le_of_large (α : ℝ) (hα : 0 < α) (p X : ℕ)
    (hp_large : Real.exp (2 * α) ≤ p) (hpX : p ≤ X) :
    Real.sqrt p / (Real.log p) ^ α ≤ Real.sqrt X / (Real.log X) ^ α :=
  sqrt_div_log_monotoneOn α hα hp_large
    (hp_large.trans (Nat.cast_le.mpr hpX)) (Nat.cast_le.mpr hpX)

/--
@isnad1 id=eventual.1h2v.s5.8f0eced9c78d from=translated src=- shape=dbfc5e06 vocab=402c83e0
-/
lemma eventually_sqrt_div_log_ge (α : ℝ) (hα : 0 < α) (M : ℝ) :
    ∀ᶠ X : ℕ in Filter.atTop, M ≤ Real.sqrt X / (Real.log X) ^ α := by
  rw [← Nat.comap_cast_atTop (R := ℝ)]
  exact ((tendsto_sqrt_div_log_pow_atTop α hα).eventually_ge_atTop M).comap _

/--
@isnad1 id=ex.0h2v.s5.e765b6083ada from=translated src=- shape=549ace02 vocab=9d232c55
-/
lemma small_values_bounded (α : ℝ) (T : ℕ) :
    ∃ C : ℝ, ∀ p : ℕ, p < T → Real.sqrt p / (Real.log p) ^ α ≤ C := by
  rcases Nat.eq_zero_or_pos T with rfl | hT
  · exact ⟨0, fun _ hp => (Nat.not_lt_zero _ hp).elim⟩
  · let f : ℕ → ℝ := fun p => Real.sqrt p / (Real.log p) ^ α
    exact ⟨(Finset.range T).sup' (Finset.nonempty_range_iff.mpr hT.ne') f,
           fun p hp => Finset.le_sup' f (Finset.mem_range.mpr hp)⟩

/--
@isnad1 id=eventual.1h1v.s6.da25b5cb5246 from=translated src=- shape=2b4b75a1 vocab=402c83e0
-/
lemma sqrt_div_log_eventually_le (α : ℝ) (hα : 0 < α) :
    ∀ᶠ X : ℕ in Filter.atTop, ∀ p : ℕ, p ≤ X →
      Real.sqrt p / (Real.log p) ^ α ≤ Real.sqrt X / (Real.log X) ^ α := by
  let T := ⌈Real.exp (2 * α)⌉₊
  obtain ⟨C, hC⟩ := small_values_bounded α T
  have h2 : ∀ᶠ X : ℕ in Filter.atTop, Real.exp (2 * α) ≤ (X : ℝ) := by
    rw [Filter.eventually_atTop]
    exact ⟨T, fun n hn => le_trans (Nat.le_ceil _) (Nat.cast_le.mpr hn)⟩
  filter_upwards [eventually_sqrt_div_log_ge α hα C, h2] with X hX_ge_C hX_large p hpX
  by_cases hp : p < T
  · exact (hC p hp).trans hX_ge_C
  · exact sqrt_div_log_le_of_le_of_large α hα p X
      ((Nat.le_ceil _).trans (Nat.cast_le.mpr (Nat.not_lt.mp hp))) hpX

/--
@isnad1 id=eventual.1h1v.s6.487f42de2f6d from=translated src=- shape=e05b03dc vocab=a24ce664
-/
lemma K_max_sup_le_sqrt_div_log_add_one (α : ℝ) (hα : 0 < α) :
    ∀ᶠ X : ℕ in Filter.atTop,
      (KMaxSup α X : ℝ) ≤ Real.sqrt X / (Real.log X) ^ α + 1 := by
  filter_upwards [sqrt_div_log_eventually_le α hα] with X hX
  unfold KMaxSup
  simp only [Nat.cast_add, Nat.cast_one]
  suffices h :
      ((Finset.filter (fun p => Nat.Prime p) (Finset.range (X + 1))).sup
          (MAlpha α) : ℕ) ≤
        ⌊Real.sqrt X / (Real.log X) ^ α⌋₊ by
    have hfloor : (⌊Real.sqrt X / (Real.log X) ^ α⌋₊ : ℝ) ≤
        Real.sqrt X / (Real.log X) ^ α := Nat.floor_le (by positivity)
    linarith [(Nat.cast_le (α := ℝ)).mpr h]
  apply Finset.sup_le
  intro p hp
  rw [Finset.mem_filter, Finset.mem_range] at hp
  exact Nat.floor_le_floor (hX p (Nat.lt_succ_iff.mp hp.1))

/--
@isnad1 id=eq.1h2v.s7.02387d4264c2 from=translated src=- shape=a0220d89 vocab=9492968b
-/
lemma two_sq_eq (α : ℝ) (X : ℕ) (hX : (1 : ℝ) < X) :
    2 * (Real.sqrt X / (Real.log X) ^ α)^2 = 2 * (X : ℝ) / (Real.log X) ^ (2 * α) := by
  have hlogX : 0 < Real.log X := Real.log_pos (by exact_mod_cast hX)
  rw [div_pow, Real.sq_sqrt (by positivity : (0 : ℝ) ≤ X),
      ← Real.rpow_natCast ((Real.log X) ^ α) 2,
      ← Real.rpow_mul hlogX.le]
  ring_nf

/--
@isnad1 id=eventual.1h1v.s6.6c305f2806ed from=translated src=- shape=e9700ebc vocab=0b5c37cd
-/
lemma K_max_sup_sq_bound (α : ℝ) (hα : 0 < α) :
    ∀ᶠ X : ℕ in Filter.atTop,
      ((KMaxSup α X : ℝ))^2 ≤ 2 * (X : ℝ) / (Real.log X) ^ (2 * α) := by
  filter_upwards [K_max_sup_le_sqrt_div_log_add_one α hα,
      eventually_sqrt_div_log_ge_threshold α hα, Filter.eventually_gt_atTop 1]
    with X hK hA hX1
  set A := Real.sqrt X / (Real.log X) ^ α
  have hsqrt2 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hK_nonneg : (0 : ℝ) ≤ KMaxSup α X := Nat.cast_nonneg _
  calc ((KMaxSup α X : ℝ))^2
      ≤ (A + 1)^2 := sq_le_sq' (by linarith) hK
    _ ≤ 2 * A^2 := sq_add_one_le_two_sq A hA
    _ = 2 * (X : ℝ) / (Real.log X) ^ (2 * α) := two_sq_eq α X (Nat.one_lt_cast.mpr hX1)

/--
@isnad1 id=le.0h1v.s5.2ac5031f3526 from=translated src=- shape=5ae21f99 vocab=9e1c013c
-/
lemma sum_range_le_sq (K : ℕ) :
    (∑ k ∈ Finset.range K, (k : ℝ)) ≤ ((K : ℝ))^2 / 2 := by
  have h_main : (∑ k ∈ Finset.range K, (k : ℝ)) = ((K : ℝ) * ((K : ℝ) - 1)) / 2 := by
    induction K with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      push_cast
      ring
  nlinarith [sq_nonneg (K : ℝ), h_main, Nat.cast_nonneg (α := ℝ) K]

/--
@isnad1 id=le.0h2v.s5.6a277f3945c5 from=translated src=- shape=c43d75be vocab=cc815997
-/
lemma irregularPrimes_ncard_le_sum (α : ℝ) (X : ℕ) :
    ((irregularPrimesUpTo α X).ncard : ℝ) ≤
      ∑ k ∈ Finset.range (KMaxSup α X), ((AK α X k).ncard : ℝ) := by
  have h1 := Set.ncard_le_ncard (irregularPrimes_subset_union α X) <|
    Set.Finite.subset (Set.finite_Iic X) fun p hp => by
      simp only [Set.mem_iUnion, Finset.mem_range] at hp
      obtain ⟨k, _, hk⟩ := hp
      exact Set.mem_Iic.mpr hk.1
  exact_mod_cast Nat.le_trans h1 (Finset.set_ncard_biUnion_le _ _)

end LeanPool.PartialRegularity.Extension
