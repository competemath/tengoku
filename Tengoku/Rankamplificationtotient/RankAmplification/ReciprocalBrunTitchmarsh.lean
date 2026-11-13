import Tengoku.Rankamplificationtotient.RankAmplification.ShiftedCoprime
import Tengoku.Seed.NumberTheory.AbelSummation
import Tengoku.Seed.NumberTheory.Harmonic.Bounds
import Tengoku.Seed.Analysis.SpecialFunctions.Log.Base

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # Finite reciprocal Brun–Titchmarsh reductions This file contains the exact finite partial-summation and dyadic-reduction layer behind Lemma 2.3. -/

namespace RankAmplification

open Finset

noncomputable section

/-- Primes in the residue class `a (mod D)` lying in `(L,U]`.-/
def residuePrimeIntervalSet (D a L U : ℕ) : Finset ℕ :=
  (Finset.Ioc L U).filter fun q ↦ q.Prime ∧ q ≡ a [MOD D]

@[simp]
theorem mem_residuePrimeIntervalSet {D a L U q : ℕ} :
    q ∈ residuePrimeIntervalSet D a L U ↔
      L < q ∧ q ≤ U ∧ q.Prime ∧ q ≡ a [MOD D] := by
  simp [residuePrimeIntervalSet, and_assoc]

/-- The interval prime-counting function in one residue class.-/
def residuePrimeIntervalCount (D a L U : ℕ) : ℕ :=
  (residuePrimeIntervalSet D a L U).card

/-- The reciprocal mass of primes in one residue class and one interval.-/
def residuePrimeIntervalReciprocalSum (D a L U : ℕ) : ℝ :=
  ∑ q ∈ residuePrimeIntervalSet D a L U, (q : ℝ)⁻¹

theorem residuePrimeIntervalReciprocalSum_nonneg (D a L U : ℕ) :
    0 ≤ residuePrimeIntervalReciprocalSum D a L U := by
  exact Finset.sum_nonneg fun q _ ↦ inv_nonneg.mpr (Nat.cast_nonneg q)

/-- Adjacent residue-class intervals concatenate exactly.-/
theorem residuePrimeIntervalSet_union {D a L M U : ℕ} (hLM : L ≤ M) (hMU : M ≤ U) :
    residuePrimeIntervalSet D a L M ∪ residuePrimeIntervalSet D a M U =
      residuePrimeIntervalSet D a L U := by
  ext q
  simp only [mem_union, mem_residuePrimeIntervalSet]
  constructor
  · rintro (hq | hq)
    · exact ⟨hq.1, hq.2.1.trans hMU, hq.2.2⟩
    · exact ⟨hLM.trans_lt hq.1, hq.2⟩
  · intro hq
    by_cases hqM : q ≤ M
    · exact Or.inl ⟨hq.1, hqM, hq.2.2⟩
    · exact Or.inr ⟨lt_of_not_ge hqM, hq.2⟩

theorem residuePrimeIntervalSet_disjoint {D a L M U : ℕ} :
    Disjoint (residuePrimeIntervalSet D a L M) (residuePrimeIntervalSet D a M U) := by
  rw [Finset.disjoint_left]
  intro q hqLeft hqRight
  have hleft := (mem_residuePrimeIntervalSet.mp hqLeft).2.1
  have hright := (mem_residuePrimeIntervalSet.mp hqRight).1
  omega

/-- Exact additivity of reciprocal mass over adjacent intervals.-/
theorem residuePrimeIntervalReciprocalSum_consecutive {D a L M U : ℕ}
    (hLM : L ≤ M) (hMU : M ≤ U) :
    residuePrimeIntervalReciprocalSum D a L U =
      residuePrimeIntervalReciprocalSum D a L M +
        residuePrimeIntervalReciprocalSum D a M U := by
  simp only [residuePrimeIntervalReciprocalSum]
  rw [← residuePrimeIntervalSet_union hLM hMU,
    Finset.sum_union residuePrimeIntervalSet_disjoint]

/-- A reciprocal interval sum is at most its cardinality divided by the lower endpoint.-/
theorem residuePrimeIntervalReciprocalSum_le_card_mul_inv {D a L U : ℕ}
    (hL : 0 < L) :
    residuePrimeIntervalReciprocalSum D a L U ≤
      (residuePrimeIntervalCount D a L U : ℝ) * (L : ℝ)⁻¹ := by
  rw [residuePrimeIntervalReciprocalSum, residuePrimeIntervalCount]
  calc
    (∑ q ∈ residuePrimeIntervalSet D a L U, (q : ℝ)⁻¹) ≤
        ∑ _q ∈ residuePrimeIntervalSet D a L U, (L : ℝ)⁻¹ := by
      apply Finset.sum_le_sum
      intro q hq
      have hLq : L ≤ q := (mem_residuePrimeIntervalSet.mp hq).1.le
      have hLReal : (0 : ℝ) < L := by exact_mod_cast hL
      have hqReal : (0 : ℝ) < q := hLReal.trans_le (by exact_mod_cast hLq)
      exact (inv_le_inv₀ hqReal hLReal).2 (by exact_mod_cast hLq)
    _ = ((residuePrimeIntervalSet D a L U).card : ℝ) * (L : ℝ)⁻¹ := by simp

/-- The interval count is bounded by the elementary census of one residue class.-/
theorem residuePrimeIntervalCount_le_div_add_one {D a L U : ℕ} (hD : 0 < D) :
    residuePrimeIntervalCount D a L U ≤ U / D + 1 := by
  calc
    residuePrimeIntervalCount D a L U ≤
        ((Finset.range (U + 1)).filter fun q ↦ q ≡ a [MOD D]).card := by
      apply Finset.card_le_card
      intro q hq
      have hqData := mem_residuePrimeIntervalSet.mp hq
      rw [Finset.mem_filter, Finset.mem_range]
      exact ⟨Nat.lt_succ_of_le hqData.2.1, hqData.2.2.2⟩
    _ = Nat.count (· ≡ a [MOD D]) (U + 1) := by
      rw [Nat.count_eq_card_filter_range]
    _ ≤ U / D + 1 := count_modEq_le_div_add_one U a D hD

/-! ## Exact finite Abel summation -/

/-- The real indicator sequence of a finite set of natural numbers.-/
def finsetIndicator (S : Finset ℕ) (n : ℕ) : ℝ :=
  if n ∈ S then 1 else 0

@[simp]
theorem finsetIndicator_apply {S : Finset ℕ} {n : ℕ} :
    finsetIndicator S n = if n ∈ S then 1 else 0 := rfl

theorem sum_finsetIndicator_range (S : Finset ℕ) (N : ℕ) :
    ∑ n ∈ Finset.range N, finsetIndicator S n =
      ((S.filter fun n ↦ n < N).card : ℝ) := by
  have hsets : Finset.range N ∩ S = S.filter fun n ↦ n < N := by
    ext n
    simp [and_comm]
  simp [finsetIndicator, hsets]

/-- Generic discrete Abel identity for reciprocal weights on a finite interval.-/
theorem finset_reciprocal_sum_eq_boundary_add_prefix {S : Finset ℕ} {L U : ℕ}
    (hLU : L < U) (hS : S ⊆ Finset.Ioc L U) :
    (∑ n ∈ S, (n : ℝ)⁻¹) =
      (S.card : ℝ) * (U : ℝ)⁻¹ +
        ∑ m ∈ Finset.Ioc L (U - 1),
          ((S.filter fun n ↦ n ≤ m).card : ℝ) /
            ((m : ℝ) * (m + 1)) := by
  classical
  have hfilter : (Finset.Ioc L U).filter (· ∈ S) = S := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_Ioc]
    constructor
    · exact fun hn ↦ hn.2
    · intro hn
      exact ⟨Finset.mem_Ioc.mp (hS hn), hn⟩
  have hleft :
      ∑ n ∈ Finset.Ioc L U, (n : ℝ)⁻¹ * finsetIndicator S n =
        ∑ n ∈ S, (n : ℝ)⁻¹ := by
    calc
      (∑ n ∈ Finset.Ioc L U, (n : ℝ)⁻¹ * finsetIndicator S n) =
          ∑ n ∈ Finset.Ioc L U, if n ∈ S then (n : ℝ)⁻¹ else 0 := by
        apply Finset.sum_congr rfl
        intro n _hn
        simp [finsetIndicator]
      _ = ∑ n ∈ (Finset.Ioc L U).filter (· ∈ S), (n : ℝ)⁻¹ := by
        rw [Finset.sum_filter]
      _ = ∑ n ∈ S, (n : ℝ)⁻¹ := by rw [hfilter]
  have hfilterUpper : S.filter (fun n ↦ n < U + 1) = S := by
    apply Finset.filter_eq_self.mpr
    intro n hn
    exact Nat.lt_succ_of_le (Finset.mem_Ioc.mp (hS hn)).2
  have hfilterLower : S.filter (fun n ↦ n < L + 1) = ∅ := by
    apply Finset.eq_empty_of_forall_notMem
    intro n hn
    rw [Finset.mem_filter] at hn
    have hnLower := (Finset.mem_Ioc.mp (hS hn.1)).1
    omega
  have hprefix (m : ℕ) :
      S.filter (fun n ↦ n < m + 1) = S.filter fun n ↦ n ≤ m := by
    ext n
    simp
  have habel := Finset.sum_Ioc_by_parts
    (fun n : ℕ ↦ (n : ℝ)⁻¹) (finsetIndicator S) hLU
  simp only [smul_eq_mul] at habel
  simp_rw [sum_finsetIndicator_range] at habel
  rw [hfilterUpper, hfilterLower] at habel
  simp only [Finset.card_empty, Nat.cast_zero, mul_zero, sub_zero] at habel
  simp_rw [hprefix] at habel
  rw [hleft] at habel
  calc
    (∑ n ∈ S, (n : ℝ)⁻¹) =
        (U : ℝ)⁻¹ * (S.card : ℝ) -
          ∑ m ∈ Finset.Ioc L (U - 1),
            (((m + 1 : ℕ) : ℝ)⁻¹ - (m : ℝ)⁻¹) *
              ((S.filter fun n ↦ n ≤ m).card : ℝ) := habel
    _ = (S.card : ℝ) * (U : ℝ)⁻¹ +
        ∑ m ∈ Finset.Ioc L (U - 1),
          ((S.filter fun n ↦ n ≤ m).card : ℝ) /
            ((m : ℝ) * (m + 1)) := by
      rw [sub_eq_add_neg, ← Finset.sum_neg_distrib]
      rw [mul_comm (U : ℝ)⁻¹ (S.card : ℝ)]
      apply congrArg (fun z : ℝ ↦ (S.card : ℝ) * (U : ℝ)⁻¹ + z)
      apply Finset.sum_congr rfl
      intro m hm
      have hmPos : 0 < m := lt_of_le_of_lt (Nat.zero_le L)
        (Finset.mem_Ioc.mp hm).1
      have hmReal : (m : ℝ) ≠ 0 := by positivity
      have hmSuccReal : ((m + 1 : ℕ) : ℝ) ≠ 0 := by positivity
      norm_num only [Nat.cast_add, Nat.cast_one]
      field_simp
      ring

/-- Abel summation specialized to residue-class prime intervals.-/
theorem residuePrimeIntervalReciprocalSum_eq_boundary_add_prefix {D a L U : ℕ}
    (hLU : L < U) :
    residuePrimeIntervalReciprocalSum D a L U =
      (residuePrimeIntervalCount D a L U : ℝ) * (U : ℝ)⁻¹ +
        ∑ m ∈ Finset.Ioc L (U - 1),
          (residuePrimeIntervalCount D a L m : ℝ) /
            ((m : ℝ) * (m + 1)) := by
  rw [residuePrimeIntervalReciprocalSum,
    finset_reciprocal_sum_eq_boundary_add_prefix
      (S := residuePrimeIntervalSet D a L U) hLU (Finset.filter_subset _ _)]
  simp only [residuePrimeIntervalCount]
  apply congrArg (fun z : ℝ ↦
    ((residuePrimeIntervalSet D a L U).card : ℝ) * (U : ℝ)⁻¹ + z)
  apply Finset.sum_congr rfl
  intro m hm
  have hmU : m ≤ U := by
    have hmTop := (Finset.mem_Ioc.mp hm).2
    omega
  have hfilter :
      (residuePrimeIntervalSet D a L U).filter (fun n ↦ n ≤ m) =
        residuePrimeIntervalSet D a L m := by
    ext q
    simp only [Finset.mem_filter, mem_residuePrimeIntervalSet]
    constructor
    · rintro ⟨hq, hqm⟩
      exact ⟨hq.1, hqm, hq.2.2⟩
    · intro hq
      exact ⟨⟨hq.1, hq.2.1.trans hmU, hq.2.2⟩, hq.2.1⟩
  rw [hfilter]

/-- A supplied pointwise prefix-count envelope gives the corresponding exact reciprocal bound.-/
theorem residuePrimeIntervalReciprocalSum_le_of_prefix_bound {D a L U : ℕ}
    (hLU : L < U) (B : ℕ → ℝ)
    (hB : ∀ m ∈ Finset.Icc (L + 1) U,
      (residuePrimeIntervalCount D a L m : ℝ) ≤ B m) :
    residuePrimeIntervalReciprocalSum D a L U ≤
      B U * (U : ℝ)⁻¹ +
        ∑ m ∈ Finset.Ioc L (U - 1), B m / ((m : ℝ) * (m + 1)) := by
  rw [residuePrimeIntervalReciprocalSum_eq_boundary_add_prefix hLU]
  apply add_le_add
  · apply mul_le_mul_of_nonneg_right
      (hB U (by simp [Nat.succ_le_iff.mpr hLU]))
    positivity
  · apply Finset.sum_le_sum
    intro m hm
    have hmRange : m ∈ Finset.Icc (L + 1) U := by
      rw [Finset.mem_Icc]
      have hmData := Finset.mem_Ioc.mp hm
      omega
    rw [div_eq_mul_inv, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right (hB m hmRange) (by positivity)

/-! ## Dyadic Brun–Titchmarsh reduction -/

/-- The dyadic interval `(2^j D,2^(j+1)D]`.-/
def dyadicResiduePrimeReciprocalSum (D a j : ℕ) : ℝ :=
  residuePrimeIntervalReciprocalSum D a (2 ^ j * D) (2 ^ (j + 1) * D)

/-- An explicitly parameterized dyadic interval-counting premise.-/
def DyadicBrunTitchmarshHypothesis (C : ℝ) (D a J : ℕ) : Prop :=
  ∀ j ∈ Finset.Icc 2 J,
    (residuePrimeIntervalCount D a (2 ^ j * D) (2 ^ (j + 1) * D) : ℝ) ≤
      C * (2 ^ j * D : ℝ) / ((D.totient : ℝ) * j)

/-- A single dyadic interval-counting estimate implies the matching reciprocal-mass estimate.-/
theorem dyadicResiduePrimeReciprocalSum_le {C : ℝ} {D a J j : ℕ}
    (hD : 0 < D) (hBT : DyadicBrunTitchmarshHypothesis C D a J)
    (hj : j ∈ Finset.Icc 2 J) :
    dyadicResiduePrimeReciprocalSum D a j ≤
      C / ((D.totient : ℝ) * (j : ℝ)) := by
  have hjPos : 0 < j := lt_of_lt_of_le (by norm_num) (Finset.mem_Icc.mp hj).1
  have hscale : 0 < 2 ^ j * D := mul_pos (pow_pos (by norm_num) _) hD
  have hcount := hBT j hj
  calc
    dyadicResiduePrimeReciprocalSum D a j ≤
        (residuePrimeIntervalCount D a (2 ^ j * D) (2 ^ (j + 1) * D) : ℝ) *
          (2 ^ j * D : ℝ)⁻¹ :=
      by simpa only [dyadicResiduePrimeReciprocalSum, Nat.cast_mul, Nat.cast_pow,
          Nat.cast_ofNat] using
        (residuePrimeIntervalReciprocalSum_le_card_mul_inv
          (D := D) (a := a) (U := 2 ^ (j + 1) * D) hscale)
    _ ≤ (C * (2 ^ j * D : ℝ) / ((D.totient : ℝ) * j)) *
          (2 ^ j * D : ℝ)⁻¹ := by
      exact mul_le_mul_of_nonneg_right hcount (by positivity)
    _ = C / ((D.totient : ℝ) * (j : ℝ)) := by
      have hscaleReal : (2 ^ j * D : ℝ) ≠ 0 := by exact_mod_cast hscale.ne'
      field_simp

/-- Exact dyadic decomposition from the initial interval `(0,4D]` through block `J`.-/
theorem residuePrimeIntervalReciprocalSum_dyadic_decomposition {D a J : ℕ}
    (hJ : 2 ≤ J) :
    residuePrimeIntervalReciprocalSum D a 0 (2 ^ (J + 1) * D) =
      residuePrimeIntervalReciprocalSum D a 0 (4 * D) +
        ∑ j ∈ Finset.Icc 2 J, dyadicResiduePrimeReciprocalSum D a j := by
  induction J, hJ using Nat.le_induction with
  | base =>
      have hconcat := residuePrimeIntervalReciprocalSum_consecutive
        (D := D) (a := a) (L := 0) (M := 4 * D) (U := 8 * D)
        (by omega) (by omega)
      simpa [dyadicResiduePrimeReciprocalSum] using hconcat
  | succ J hJ ih =>
      have hcutoff : 2 ^ (J + 1) * D ≤ 2 ^ (J + 2) * D := by
        calc
          2 ^ (J + 1) * D ≤ (2 ^ (J + 1) * 2) * D :=
            Nat.mul_le_mul_right D (Nat.le_mul_of_pos_right _ (by norm_num))
          _ = 2 ^ (J + 2) * D := by
            conv_rhs => rw [show J + 2 = (J + 1) + 1 by omega, pow_succ]
      calc
        residuePrimeIntervalReciprocalSum D a 0 (2 ^ (J + 1 + 1) * D) =
            residuePrimeIntervalReciprocalSum D a 0 (2 ^ (J + 1) * D) +
              residuePrimeIntervalReciprocalSum D a (2 ^ (J + 1) * D)
                (2 ^ (J + 2) * D) := by
          simpa only [show J + 1 + 1 = J + 2 by omega] using
            residuePrimeIntervalReciprocalSum_consecutive
              (D := D) (a := a) (L := 0) (M := 2 ^ (J + 1) * D)
              (U := 2 ^ (J + 2) * D) (by omega) hcutoff
        _ = residuePrimeIntervalReciprocalSum D a 0 (4 * D) +
              (∑ j ∈ Finset.Icc 2 J, dyadicResiduePrimeReciprocalSum D a j) +
              dyadicResiduePrimeReciprocalSum D a (J + 1) := by
          rw [ih]
          simp only [dyadicResiduePrimeReciprocalSum]
        _ = residuePrimeIntervalReciprocalSum D a 0 (4 * D) +
              ∑ j ∈ Finset.Icc 2 (J + 1), dyadicResiduePrimeReciprocalSum D a j := by
          rw [Finset.sum_Icc_succ_top (by omega)]
          ring

/-- A prime congruent to `1` modulo a positive `D` is strictly larger than `D`.-/
theorem modulus_lt_prime_of_modEq_one {D q : ℕ} (_hD : 0 < D) (hq : q.Prime)
    (hmod : q ≡ 1 [MOD D]) : D < q := by
  have hdiv : D ∣ q - 1 :=
    (Nat.modEq_iff_dvd' hq.one_le).mp hmod.symm
  have hqSubPos : 0 < q - 1 := by
    have hqTwo := hq.two_le
    omega
  have hDle : D ≤ q - 1 := Nat.le_of_dvd hqSubPos hdiv
  omega

/-- Initial reciprocal mass is controlled using only its cardinality and congruence.-/
theorem initialResiduePrimeReciprocalSum_le_card_mul_inv {D U : ℕ} (hD : 0 < D) :
    residuePrimeIntervalReciprocalSum D 1 0 U ≤
      (residuePrimeIntervalCount D 1 0 U : ℝ) * (D : ℝ)⁻¹ := by
  rw [residuePrimeIntervalReciprocalSum, residuePrimeIntervalCount]
  calc
    (∑ q ∈ residuePrimeIntervalSet D 1 0 U, (q : ℝ)⁻¹) ≤
        ∑ _q ∈ residuePrimeIntervalSet D 1 0 U, (D : ℝ)⁻¹ := by
      apply Finset.sum_le_sum
      intro q hq
      have hqData := mem_residuePrimeIntervalSet.mp hq
      have hDq : D ≤ q :=
        (modulus_lt_prime_of_modEq_one hD hqData.2.2.1 hqData.2.2.2).le
      have hDReal : (0 : ℝ) < D := by exact_mod_cast hD
      have hqReal : (0 : ℝ) < q := hDReal.trans_le (by exact_mod_cast hDq)
      exact (inv_le_inv₀ hqReal hDReal).2 (by exact_mod_cast hDq)
    _ = ((residuePrimeIntervalSet D 1 0 U).card : ℝ) * (D : ℝ)⁻¹ := by simp

/-- The elementary initial range contains at most five candidates in the residue class.-/
theorem initialResiduePrimeCount_le_five {D : ℕ} (hD : 0 < D) :
    residuePrimeIntervalCount D 1 0 (4 * D) ≤ 5 := by
  calc
    residuePrimeIntervalCount D 1 0 (4 * D) ≤ (4 * D) / D + 1 :=
      residuePrimeIntervalCount_le_div_add_one hD
    _ = 5 := by simp [hD.ne']

/-- Fully elementary bound for the short initial range in terms of Euler's totient.-/
theorem initialResiduePrimeReciprocalSum_le_five_mul_totient_inv {D : ℕ}
    (hD : 0 < D) :
    residuePrimeIntervalReciprocalSum D 1 0 (4 * D) ≤
      5 * (D.totient : ℝ)⁻¹ := by
  have hcard : (residuePrimeIntervalCount D 1 0 (4 * D) : ℝ) ≤ 5 := by
    exact_mod_cast initialResiduePrimeCount_le_five hD
  have hphiPos : (0 : ℝ) < D.totient := by
    exact_mod_cast Nat.totient_pos.mpr hD
  have hDPos : (0 : ℝ) < D := by exact_mod_cast hD
  have hphiD : (D.totient : ℝ) ≤ D := by exact_mod_cast Nat.totient_le D
  calc
    residuePrimeIntervalReciprocalSum D 1 0 (4 * D) ≤
        (residuePrimeIntervalCount D 1 0 (4 * D) : ℝ) * (D : ℝ)⁻¹ :=
      initialResiduePrimeReciprocalSum_le_card_mul_inv hD
    _ ≤ 5 * (D : ℝ)⁻¹ :=
      mul_le_mul_of_nonneg_right hcard (by positivity)
    _ ≤ 5 * (D.totient : ℝ)⁻¹ := by
      exact mul_le_mul_of_nonneg_left ((inv_le_inv₀ hDPos hphiPos).2 hphiD) (by norm_num)

/-- The dyadic harmonic loss is at most `1 + log J`.-/
theorem sum_Icc_two_natCast_inv_le_one_add_log (J : ℕ) :
    (∑ j ∈ Finset.Icc 2 J, (j : ℝ)⁻¹) ≤ 1 + Real.log J := by
  calc
    (∑ j ∈ Finset.Icc 2 J, (j : ℝ)⁻¹) ≤
        ∑ j ∈ Finset.Icc 1 J, (j : ℝ)⁻¹ := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro j hj
        simp only [Finset.mem_Icc] at hj ⊢
        omega
      · intro j _hj _hjNot
        positivity
    _ = (harmonic J : ℝ) := by
      simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
    _ ≤ 1 + Real.log J := harmonic_le_one_add_log J

/-- Finite reciprocal Brun–Titchmarsh reduction at a dyadic endpoint.-/
theorem residuePrimeReciprocalSum_le_of_dyadicBT_endpoint {C : ℝ} {D J : ℕ}
    (hC : 0 ≤ C) (hD : 0 < D) (hJ : 2 ≤ J)
    (hBT : DyadicBrunTitchmarshHypothesis C D 1 J) :
    residuePrimeIntervalReciprocalSum D 1 0 (2 ^ (J + 1) * D) ≤
      (5 + C * (1 + Real.log J)) * (D.totient : ℝ)⁻¹ := by
  rw [residuePrimeIntervalReciprocalSum_dyadic_decomposition hJ]
  calc
    residuePrimeIntervalReciprocalSum D 1 0 (4 * D) +
        ∑ j ∈ Finset.Icc 2 J, dyadicResiduePrimeReciprocalSum D 1 j ≤
        5 * (D.totient : ℝ)⁻¹ +
          ∑ j ∈ Finset.Icc 2 J,
            C / ((D.totient : ℝ) * (j : ℝ)) := by
      apply add_le_add (initialResiduePrimeReciprocalSum_le_five_mul_totient_inv hD)
      apply Finset.sum_le_sum
      intro j hj
      exact dyadicResiduePrimeReciprocalSum_le hD hBT hj
    _ = (5 + C * (∑ j ∈ Finset.Icc 2 J, (j : ℝ)⁻¹)) *
        (D.totient : ℝ)⁻¹ := by
      have hphi : (D.totient : ℝ) ≠ 0 := by
        exact_mod_cast (Nat.totient_pos.mpr hD).ne'
      have hsum :
          (∑ j ∈ Finset.Icc 2 J, C / ((D.totient : ℝ) * (j : ℝ))) =
            C * (D.totient : ℝ)⁻¹ *
              ∑ j ∈ Finset.Icc 2 J, (j : ℝ)⁻¹ := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        have hj0 : (j : ℝ) ≠ 0 := by
          have : 0 < j := lt_of_lt_of_le (by norm_num) (Finset.mem_Icc.mp hj).1
          exact_mod_cast this.ne'
        field_simp
      rw [hsum]
      ring
    _ ≤ (5 + C * (1 + Real.log J)) * (D.totient : ℝ)⁻¹ := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact add_le_add le_rfl
        (mul_le_mul_of_nonneg_left (sum_Icc_two_natCast_inv_le_one_add_log J) hC)

/-- Monotonicity in the upper endpoint.-/
theorem residuePrimeIntervalReciprocalSum_mono_upper {D a L U V : ℕ} (hUV : U ≤ V) :
    residuePrimeIntervalReciprocalSum D a L U ≤
      residuePrimeIntervalReciprocalSum D a L V := by
  rw [residuePrimeIntervalReciprocalSum, residuePrimeIntervalReciprocalSum]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro q hq
    have hqData := mem_residuePrimeIntervalSet.mp hq
    exact mem_residuePrimeIntervalSet.mpr
      ⟨hqData.1, hqData.2.1.trans hUV, hqData.2.2⟩
  · intro q _hq _hqNot
    positivity

/-- The endpoint reduction for an arbitrary cutoff covered by the dyadic range.-/
theorem residuePrimeReciprocalSum_le_of_dyadicBT {C : ℝ} {D J X : ℕ}
    (hC : 0 ≤ C) (hD : 0 < D) (hJ : 2 ≤ J)
    (hX : X ≤ 2 ^ (J + 1) * D)
    (hBT : DyadicBrunTitchmarshHypothesis C D 1 J) :
    residuePrimeIntervalReciprocalSum D 1 0 X ≤
      (5 + C * (1 + Real.log J)) * (D.totient : ℝ)⁻¹ := by
  exact (residuePrimeIntervalReciprocalSum_mono_upper hX).trans
    (residuePrimeReciprocalSum_le_of_dyadicBT_endpoint hC hD hJ hBT)

/-- Canonical dyadic depth for a cutoff `X`.-/
def reciprocalBrunTitchmarshDepth (X : ℕ) : ℕ :=
  Nat.log 2 X + 1

theorem two_le_reciprocalBrunTitchmarshDepth {X : ℕ} (hX : 2 ≤ X) :
    2 ≤ reciprocalBrunTitchmarshDepth X := by
  rw [reciprocalBrunTitchmarshDepth]
  have hlog : 0 < Nat.log 2 X := Nat.log_pos (by norm_num) hX
  omega

/-- The canonical depth covers every integer up to `X`, for every positive modulus.-/
theorem le_dyadic_cutoff_reciprocalBrunTitchmarshDepth {D X : ℕ} (hD : 0 < D) :
    X ≤ 2 ^ (reciprocalBrunTitchmarshDepth X + 1) * D := by
  change X ≤ 2 ^ (Nat.log 2 X + 1 + 1) * D
  have hfirst : X ≤ 2 ^ (Nat.log 2 X + 1) :=
    (Nat.lt_pow_succ_log_self (by norm_num) X).le
  calc
    X ≤ 2 ^ (Nat.log 2 X + 1) := hfirst
    _ ≤ 2 ^ (Nat.log 2 X + 1 + 1) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    _ ≤ 2 ^ (Nat.log 2 X + 1 + 1) * D :=
      Nat.le_mul_of_pos_right _ hD

/-- The logarithm of the canonical dyadic depth is bounded by an explicit iterated logarithm.-/
theorem log_reciprocalBrunTitchmarshDepth_le_log_one_add_logb {X : ℕ} :
    Real.log (reciprocalBrunTitchmarshDepth X) ≤
      Real.log (1 + Real.logb 2 X) := by
  have hdepth : (reciprocalBrunTitchmarshDepth X : ℝ) ≤
      1 + Real.logb 2 X := by
    rw [reciprocalBrunTitchmarshDepth, Nat.cast_add, Nat.cast_one]
    have hlog : (Nat.log 2 X : ℝ) ≤ Real.logb 2 X :=
      Real.natLog_le_logb X 2
    simpa only [add_comm] using add_le_add_right hlog 1
  have hdepthPos : (0 : ℝ) < reciprocalBrunTitchmarshDepth X := by
    exact_mod_cast (show 0 < reciprocalBrunTitchmarshDepth X by
      simp [reciprocalBrunTitchmarshDepth])
  exact Real.log_le_log hdepthPos hdepth

/-- Canonical finite form of Lemma 2.3 from a supplied dyadic Brun–Titchmarsh premise.-/
theorem residuePrimeReciprocalSum_le_of_dyadicBT_canonical {C : ℝ} {D X : ℕ}
    (hC : 0 ≤ C) (hD : 0 < D) (hX : 2 ≤ X)
    (hBT : DyadicBrunTitchmarshHypothesis C D 1
      (reciprocalBrunTitchmarshDepth X)) :
    residuePrimeIntervalReciprocalSum D 1 0 X ≤
      (5 + C * (1 + Real.log (1 + Real.logb 2 X))) *
        (D.totient : ℝ)⁻¹ := by
  have hbase := residuePrimeReciprocalSum_le_of_dyadicBT
    hC hD (two_le_reciprocalBrunTitchmarshDepth hX)
    (le_dyadic_cutoff_reciprocalBrunTitchmarshDepth hD) hBT
  refine hbase.trans ?_
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  apply add_le_add le_rfl
  apply mul_le_mul_of_nonneg_left _ hC
  exact add_le_add le_rfl log_reciprocalBrunTitchmarshDepth_le_log_one_add_logb

/-- The residue class `1 (mod D)` contributes no prime at all below `D`.-/
theorem residuePrimeIntervalSet_one_eq_empty_of_upper_lt_modulus {D X : ℕ}
    (hXD : X < D) :
    residuePrimeIntervalSet D 1 0 X = ∅ := by
  apply Finset.eq_empty_of_forall_notMem
  intro q hq
  have hqData := mem_residuePrimeIntervalSet.mp hq
  have hD : 0 < D := lt_of_le_of_lt (Nat.zero_le X) hXD
  have hDq := modulus_lt_prime_of_modEq_one hD hqData.2.2.1 hqData.2.2.2
  omega

/-- The reciprocal sum is zero when `D > X`, as stated in Lemma 2.3.-/
@[simp]
theorem residuePrimeIntervalReciprocalSum_one_eq_zero_of_upper_lt_modulus {D X : ℕ}
    (hXD : X < D) :
    residuePrimeIntervalReciprocalSum D 1 0 X = 0 := by
  rw [residuePrimeIntervalReciprocalSum,
    residuePrimeIntervalSet_one_eq_empty_of_upper_lt_modulus hXD]
  simp

end

end RankAmplification
