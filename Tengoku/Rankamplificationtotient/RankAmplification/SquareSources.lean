import Tengoku.Rankamplificationtotient.RankAmplification.RankStrata
import Tengoku.Rankamplificationtotient.RankAmplification.ShiftedCoprime
import Tengoku.Seed.Analysis.PSeries

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # The square-source branch This file formalizes the unconditional finite counting argument for the square-source branch of Section 4. -/

namespace RankAmplification

/-- Positive integers `n ≤ x` for which `d` divides the shifted value `n+a`.-/
def shiftedMultipleSet (x a d : ℕ) : Finset ℕ :=
  (Finset.Icc 1 x).filter fun n ↦ d ∣ n + a

/--
@isnad1 id=iff.0h4v.s5.f63ce2da4d4f from=translated src=- shape=e1a1bf60 vocab=1b8ce837
-/
@[simp]
theorem mem_shiftedMultipleSet {x a d n : ℕ} :
    n ∈ shiftedMultipleSet x a d ↔ 1 ≤ n ∧ n ≤ x ∧ d ∣ n + a := by
  simp [shiftedMultipleSet, and_assoc]

/-- One shifted residue class modulo `d` contributes at most `x/d+1` positive integers up to `x`.
@isnad1 id=le.1h3v.s5.9a3bb9af22c4 from=translated src=- shape=30d50065 vocab=59c3db69
-/
theorem shiftedMultipleSet_card_le {x a d : ℕ} (hd : 0 < d) :
    (shiftedMultipleSet x a d).card ≤ x / d + 1 := by
  by_cases hempty : shiftedMultipleSet x a d = ∅
  · simp [hempty]
  · obtain ⟨b, hb⟩ := Finset.nonempty_iff_ne_empty.mpr hempty
    calc
      (shiftedMultipleSet x a d).card ≤
          ((Finset.range (x + 1)).filter fun n ↦ n ≡ b [MOD d]).card := by
        apply Finset.card_le_card
        intro n hn
        have hnData := mem_shiftedMultipleSet.mp hn
        rw [Finset.mem_filter, Finset.mem_range]
        refine ⟨Nat.lt_succ_of_le hnData.2.1, ?_⟩
        exact shifted_divisors_modEq hnData.2.2 (mem_shiftedMultipleSet.mp hb).2.2
      _ = Nat.count (· ≡ b [MOD d]) (x + 1) := by
        rw [Nat.count_eq_card_filter_range]
      _ ≤ x / d + 1 := count_modEq_le_div_add_one x b d hd

/-- The square-source set attached to one prospective provider prime.-/
def squareSourceAtPrimeSet (x h p : ℕ) : Finset ℕ :=
  (Finset.Icc 1 x).filter fun n ↦ p ^ 2 ∣ n * (n + h)

/--
@isnad1 id=iff.0h4v.s6.c6553386b8d6 from=translated src=- shape=c7c659c3 vocab=b746237c
-/
@[simp]
theorem mem_squareSourceAtPrimeSet {x h p n : ℕ} :
    n ∈ squareSourceAtPrimeSet x h p ↔
      1 ≤ n ∧ n ≤ x ∧ p ^ 2 ∣ n * (n + h) := by
  simp [squareSourceAtPrimeSet, and_assoc]

/-- If `0 < h < p`, a prime-square divisor of `n(n+h)` cannot split between the two factors.
@isnad1 id=iff.3h3v.s6.d02520e104e0 from=translated src=- shape=77e933cd vocab=bb4b68c7
-/
theorem prime_sq_dvd_mul_shifted_iff {p n h : ℕ} (hp : p.Prime) (hh : 0 < h)
    (hph : h < p) :
    p ^ 2 ∣ n * (n + h) ↔ p ^ 2 ∣ n ∨ p ^ 2 ∣ n + h := by
  constructor
  · intro hsquare
    have hpSquare : p ∣ p ^ 2 := by
      rw [pow_two]
      exact Nat.dvd_mul_right p p
    have hpProduct : p ∣ n * (n + h) := hpSquare.trans hsquare
    rcases hp.dvd_mul.mp hpProduct with hpn | hpnShift
    · have hpNotShift : ¬p ∣ n + h :=
        prime_not_dvd_both_shifted hp hh hph hpn
      have hcop : (p ^ 2).Coprime (n + h) :=
        (hp.coprime_iff_not_dvd.mpr hpNotShift).pow_left 2
      exact Or.inl (hcop.dvd_of_dvd_mul_right hsquare)
    · have hpNotN : ¬p ∣ n := by
        intro hpn
        exact (prime_not_dvd_both_shifted hp hh hph hpn) hpnShift
      have hcop : (p ^ 2).Coprime n :=
        (hp.coprime_iff_not_dvd.mpr hpNotN).pow_left 2
      exact Or.inr (hcop.dvd_of_dvd_mul_left hsquare)
  · rintro (hn | hnShift)
    · exact hn.trans (Nat.dvd_mul_right n (n + h))
    · exact hnShift.trans (Nat.dvd_mul_left (n + h) n)

/-- A per-prime square-source set is covered by the two possible shifted residue classes.
@isnad1 id=le.3h3v.s6.93a21faf0826 from=translated src=- shape=2edcfd3f vocab=2eb6ffd1
-/
theorem squareSourceAtPrimeSet_subset_two_classes {x h p : ℕ} (hp : p.Prime)
    (hh : 0 < h) (hph : h < p) :
    squareSourceAtPrimeSet x h p ⊆
      shiftedMultipleSet x 0 (p ^ 2) ∪ shiftedMultipleSet x h (p ^ 2) := by
  intro n hn
  have hnData := mem_squareSourceAtPrimeSet.mp hn
  rw [prime_sq_dvd_mul_shifted_iff hp hh hph] at hnData
  rcases hnData.2.2 with hnSquare | hnShiftSquare
  · apply Finset.mem_union_left
    exact mem_shiftedMultipleSet.mpr ⟨hnData.1, hnData.2.1, by simpa using hnSquare⟩
  · apply Finset.mem_union_right
    exact mem_shiftedMultipleSet.mpr ⟨hnData.1, hnData.2.1, hnShiftSquare⟩

/-- The exact two-residue-class bound for one prime.
@isnad1 id=le.3h3v.s6.a14b34bf0aee from=translated src=- shape=9865b12d vocab=3e4b77a6
-/
theorem squareSourceAtPrimeSet_card_le {x h p : ℕ} (hp : p.Prime)
    (hh : 0 < h) (hph : h < p) :
    (squareSourceAtPrimeSet x h p).card ≤ 2 * (x / p ^ 2 + 1) := by
  calc
    (squareSourceAtPrimeSet x h p).card ≤
        (shiftedMultipleSet x 0 (p ^ 2) ∪ shiftedMultipleSet x h (p ^ 2)).card :=
      Finset.card_le_card (squareSourceAtPrimeSet_subset_two_classes hp hh hph)
    _ ≤ (shiftedMultipleSet x 0 (p ^ 2)).card +
        (shiftedMultipleSet x h (p ^ 2)).card := Finset.card_union_le _ _
    _ ≤ (x / p ^ 2 + 1) + (x / p ^ 2 + 1) := by
      exact Nat.add_le_add
        (shiftedMultipleSet_card_le (pow_pos hp.pos 2))
        (shiftedMultipleSet_card_le (pow_pos hp.pos 2))
    _ = 2 * (x / p ^ 2 + 1) := by omega

/-- A square-source prime is automatically at most `√(2x)` when both shifted arguments are at most `2x`.
@isnad1 id=le.7h4v.s6.e5da4641ee47 from=translated src=- shape=f961c371 vocab=ed9c13c4
-/
theorem squareSource_prime_le_sqrt_two_mul {x h p n : ℕ} (hp : p.Prime)
    (hh : 0 < h) (hph : h < p) (hn : 1 ≤ n) (hnx : n ≤ x) (hhx : h ≤ x)
    (hsquare : p ^ 2 ∣ n * (n + h)) :
    p ≤ (2 * x).sqrt := by
  rw [prime_sq_dvd_mul_shifted_iff hp hh hph] at hsquare
  apply Nat.le_sqrt'.2
  rcases hsquare with hnSquare | hnShiftSquare
  · have hp2n : p ^ 2 ≤ n := Nat.le_of_dvd (by omega) hnSquare
    omega
  · have hp2Shift : p ^ 2 ≤ n + h := Nat.le_of_dvd (by omega) hnShiftSquare
    omega

/-- Primes in the bounded interval `(y,P]`.-/
def squareSourcePrimeRange (y P : ℕ) : Finset ℕ :=
  (Finset.Ioc y P).filter Nat.Prime

/--
@isnad1 id=iff.0h3v.s5.b96276899cb1 from=translated src=- shape=8323a705 vocab=353b79da
-/
@[simp]
theorem mem_squareSourcePrimeRange {y P p : ℕ} :
    p ∈ squareSourcePrimeRange y P ↔ y < p ∧ p ≤ P ∧ p.Prime := by
  simp [squareSourcePrimeRange, and_assoc]

/-- Aggregate square sources over the bounded prime interval `(y,P]`.-/
noncomputable def squareSourceSet (x h y P : ℕ) : Finset ℕ := by
  classical
  exact (squareSourcePrimeRange y P).biUnion fun p ↦ squareSourceAtPrimeSet x h p

/--
@isnad1 id=iff.0h5v.s6.e1ed20953110 from=translated src=- shape=be90dbb4 vocab=1fe538a3
-/
@[simp]
theorem mem_squareSourceSet {x h y P n : ℕ} :
    n ∈ squareSourceSet x h y P ↔
      ∃ p, y < p ∧ p ≤ P ∧ p.Prime ∧ p ^ 2 ∣ n * (n + h) ∧ 1 ≤ n ∧ n ≤ x := by
  classical
  constructor
  · intro hn
    obtain ⟨p, hpRange, hnp⟩ := Finset.mem_biUnion.mp hn
    have hpData := mem_squareSourcePrimeRange.mp hpRange
    have hnData := mem_squareSourceAtPrimeSet.mp hnp
    exact ⟨p, hpData.1, hpData.2.1, hpData.2.2, hnData.2.2, hnData.1, hnData.2.1⟩
  · rintro ⟨p, hyp, hpP, hp, hsquare, hn, hnx⟩
    apply Finset.mem_biUnion.mpr
    exact ⟨p, mem_squareSourcePrimeRange.mpr ⟨hyp, hpP, hp⟩,
      mem_squareSourceAtPrimeSet.mpr ⟨hn, hnx, hsquare⟩⟩

/-- At the canonical square-root cutoff, membership is equivalent to carrying any prime-square witness above `y`; no separate upper-bound hypothesis on the witness is needed.
@isnad1 id=iff.3h4v.s6.9b73a16b5163 from=translated src=- shape=fba81943 vocab=b96ebc2e
-/
theorem mem_squareSourceSet_sqrt_cutoff {x h y n : ℕ} (hh : 0 < h)
    (hhy : h ≤ y) (hhx : h ≤ x) :
    n ∈ squareSourceSet x h y (2 * x).sqrt ↔
      1 ≤ n ∧ n ≤ x ∧ ∃ p, y < p ∧ p.Prime ∧ p ^ 2 ∣ n * (n + h) := by
  constructor
  · intro hn
    obtain ⟨p, hyp, _hpUpper, hp, hsquare, hnPos, hnx⟩ := mem_squareSourceSet.mp hn
    exact ⟨hnPos, hnx, p, hyp, hp, hsquare⟩
  · rintro ⟨hnPos, hnx, p, hyp, hp, hsquare⟩
    have hph : h < p := hhy.trans_lt hyp
    have hpUpper : p ≤ (2 * x).sqrt :=
      squareSource_prime_le_sqrt_two_mul hp hh hph hnPos hnx hhx hsquare
    exact mem_squareSourceSet.mpr ⟨p, hyp, hpUpper, hp, hsquare, hnPos, hnx⟩

/-- Finite-union square-source bound over a bounded prime range.
@isnad1 id=le.2h4v.s6.87276e637090 from=translated src=- shape=e1b5dda9 vocab=2fadf15b
-/
theorem squareSourceSet_card_le_sum {x h y P : ℕ} (hh : 0 < h) (hhy : h ≤ y) :
    (squareSourceSet x h y P).card ≤
      ∑ p ∈ squareSourcePrimeRange y P, 2 * (x / p ^ 2 + 1) := by
  rw [squareSourceSet]
  refine Finset.card_biUnion_le.trans ?_
  apply Finset.sum_le_sum
  intro p hp
  have hpData := mem_squareSourcePrimeRange.mp hp
  exact squareSourceAtPrimeSet_card_le hpData.2.2 hh (hhy.trans_lt hpData.1)

/-! ## Explicit connection to nonsmooth solutions -/

/-- Nonsmooth shifted equal-totient solutions carrying an explicit square-source witness in `(y,P]`.-/
noncomputable def nonsmoothSquareSourceSet (x h y P : ℕ) : Finset ℕ :=
  nonsmoothShiftedSet x h y ∩ squareSourceSet x h y P

/--
@isnad1 id=iff.0h5v.s6.a2705a91de2a from=translated src=- shape=48060ded vocab=3dd3e43f
-/
@[simp]
theorem mem_nonsmoothSquareSourceSet {x h y P n : ℕ} :
    n ∈ nonsmoothSquareSourceSet x h y P ↔
      n ∈ nonsmoothShiftedSet x h y ∧
        ∃ p, y < p ∧ p ≤ P ∧ p.Prime ∧ p ^ 2 ∣ n * (n + h) := by
  rw [nonsmoothSquareSourceSet, Finset.mem_inter, mem_squareSourceSet]
  constructor
  · rintro ⟨hnonsmooth, p, hyp, hpP, hp, hsquare, _hn, _hnx⟩
    exact ⟨hnonsmooth, p, hyp, hpP, hp, hsquare⟩
  · rintro ⟨hnonsmooth, p, hyp, hpP, hp, hsquare⟩
    have hnData := mem_nonsmoothShiftedSet.mp hnonsmooth
    exact ⟨hnonsmooth, p, hyp, hpP, hp, hsquare, hnData.1, hnData.2.1⟩

/-- At the canonical cutoff, the nonsmooth square-source branch needs only an explicit above-`y` prime-square witness.
@isnad1 id=iff.3h4v.s6.850feed2e55c from=translated src=- shape=94afd52f vocab=eed00031
-/
theorem mem_nonsmoothSquareSourceSet_sqrt_cutoff {x h y n : ℕ} (hh : 0 < h)
    (hhy : h ≤ y) (hhx : h ≤ x) :
    n ∈ nonsmoothSquareSourceSet x h y (2 * x).sqrt ↔
      n ∈ nonsmoothShiftedSet x h y ∧
        ∃ p, y < p ∧ p.Prime ∧ p ^ 2 ∣ n * (n + h) := by
  rw [nonsmoothSquareSourceSet, Finset.mem_inter,
    mem_squareSourceSet_sqrt_cutoff hh hhy hhx]
  constructor
  · rintro ⟨hnonsmooth, _hnPos, _hnx, hp⟩
    exact ⟨hnonsmooth, hp⟩
  · rintro ⟨hnonsmooth, hp⟩
    have hnData := mem_nonsmoothShiftedSet.mp hnonsmooth
    exact ⟨hnonsmooth, hnData.1, hnData.2.1, hp⟩

/-- The witnessed nonsmooth square-source branch is bounded by the aggregate square-source set.
@isnad1 id=le.0h4v.s4.d3758e0412c0 from=translated src=- shape=4b5b69e1 vocab=73a36829
-/
theorem nonsmoothSquareSourceSet_subset_squareSourceSet (x h y P : ℕ) :
    nonsmoothSquareSourceSet x h y P ⊆ squareSourceSet x h y P := by
  exact Finset.inter_subset_right

/-- Cardinal bound for the explicitly witnessed nonsmooth square-source branch.
@isnad1 id=le.2h4v.s6.ea03d69e9a05 from=translated src=- shape=e1b5dda9 vocab=b97a3b86
-/
theorem nonsmoothSquareSourceSet_card_le_sum {x h y P : ℕ}
    (hh : 0 < h) (hhy : h ≤ y) :
    (nonsmoothSquareSourceSet x h y P).card ≤
      ∑ p ∈ squareSourcePrimeRange y P, 2 * (x / p ^ 2 + 1) := by
  exact (Finset.card_le_card (nonsmoothSquareSourceSet_subset_squareSourceSet x h y P)).trans
    (squareSourceSet_card_le_sum hh hhy)

/-! ## Reciprocal-square tail -/

/-- The bounded prime range is contained in the corresponding interval of all integers.
@isnad1 id=le.0h2v.s4.abb0c1665e6c from=translated src=- shape=dd68c58f vocab=46a2fa77
-/
theorem squareSourcePrimeRange_subset_Ioc (y P : ℕ) :
    squareSourcePrimeRange y P ⊆ Finset.Ioc y P := by
  intro p hp
  exact Finset.mem_of_mem_filter p hp

/-- There are at most `P` primes in `(y,P]`; this elementary bound supplies the `+P` term.
@isnad1 id=le.0h2v.s3.0cb0a53db158 from=translated src=- shape=9da2df65 vocab=a4d936ab
-/
theorem squareSourcePrimeRange_card_le (y P : ℕ) :
    (squareSourcePrimeRange y P).card ≤ P := by
  calc
    (squareSourcePrimeRange y P).card ≤ (Finset.Ioc y P).card :=
      Finset.card_le_card (squareSourcePrimeRange_subset_Ioc y P)
    _ = P - y := by simp
    _ ≤ P := Nat.sub_le P y

/-- Explicit reciprocal-square tail over the bounded prime interval.
@isnad1 id=le.2h2v.s5.9de367a04690 from=translated src=- shape=4614e813 vocab=c2b3f04a
-/
theorem sum_squareSourcePrimeRange_inv_sq_le_inv {y P : ℕ}
    (hy : 0 < y) (hyP : y ≤ P) :
    (∑ p ∈ squareSourcePrimeRange y P, (((p : ℝ) ^ 2)⁻¹)) ≤ (y : ℝ)⁻¹ := by
  calc
    (∑ p ∈ squareSourcePrimeRange y P, (((p : ℝ) ^ 2)⁻¹)) ≤
        ∑ p ∈ Finset.Ioc y P, (((p : ℝ) ^ 2)⁻¹) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (squareSourcePrimeRange_subset_Ioc y P)
      intro p _ _
      positivity
    _ ≤ (y : ℝ)⁻¹ - (P : ℝ)⁻¹ :=
      sum_Ioc_inv_sq_le_sub hy.ne' hyP
    _ ≤ (y : ℝ)⁻¹ := sub_le_self _ (by positivity)

/-- Cast the finite-union estimate to the natural real reciprocal-square majorant.
@isnad1 id=le.2h4v.s6.acfef9f963ba from=translated src=- shape=4d4ecd7d vocab=7ebb711c
-/
theorem squareSourceSet_card_cast_le_sum {x h y P : ℕ}
    (hh : 0 < h) (hhy : h ≤ y) :
    ((squareSourceSet x h y P).card : ℝ) ≤
      ∑ p ∈ squareSourcePrimeRange y P,
        2 * ((x : ℝ) * (((p : ℝ) ^ 2)⁻¹) + 1) := by
  have hfinite := squareSourceSet_card_le_sum (x := x) (P := P) hh hhy
  calc
    ((squareSourceSet x h y P).card : ℝ) ≤
        ((∑ p ∈ squareSourcePrimeRange y P, 2 * (x / p ^ 2 + 1) : ℕ) : ℝ) := by
      exact_mod_cast hfinite
    _ = ∑ p ∈ squareSourcePrimeRange y P,
        ((2 * (x / p ^ 2 + 1) : ℕ) : ℝ) := by rw [Nat.cast_sum]
    _ ≤ ∑ p ∈ squareSourcePrimeRange y P,
        2 * ((x : ℝ) * (((p : ℝ) ^ 2)⁻¹) + 1) := by
      apply Finset.sum_le_sum
      intro p _hp
      have hdiv : ((x / p ^ 2 : ℕ) : ℝ) ≤
          (x : ℝ) * (((p : ℝ) ^ 2)⁻¹) := by
        have hcast : ((p ^ 2 : ℕ) : ℝ) = (p : ℝ) ^ 2 := by norm_num
        have hdivNat := Nat.cast_div_le (α := ℝ) (m := x) (n := p ^ 2)
        rw [hcast] at hdivNat
        simpa only [div_eq_mul_inv] using hdivNat
      norm_num only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_add, Nat.cast_one]
      have hadd : ((x / p ^ 2 : ℕ) : ℝ) + 1 ≤
          (x : ℝ) * (((p : ℝ) ^ 2)⁻¹) + 1 := by linarith
      exact mul_le_mul_of_nonneg_left hadd (by norm_num)

/-- Explicit `x/y + P` square-source bound.
@isnad1 id=le.4h4v.s6.15ace84f4c10 from=translated src=- shape=6af03548 vocab=ec5ee379
-/
theorem squareSourceSet_card_cast_le {x h y P : ℕ} (hh : 0 < h) (hhy : h ≤ y)
    (hy : 0 < y) (hyP : y ≤ P) :
    ((squareSourceSet x h y P).card : ℝ) ≤
      2 * (x : ℝ) * (y : ℝ)⁻¹ + 2 * (P : ℝ) := by
  have hsum := sum_squareSourcePrimeRange_inv_sq_le_inv hy hyP
  have hcard : ((squareSourcePrimeRange y P).card : ℝ) ≤ P := by
    exact_mod_cast squareSourcePrimeRange_card_le y P
  calc
    ((squareSourceSet x h y P).card : ℝ) ≤
        ∑ p ∈ squareSourcePrimeRange y P,
          2 * ((x : ℝ) * (((p : ℝ) ^ 2)⁻¹) + 1) :=
      squareSourceSet_card_cast_le_sum hh hhy
    _ = 2 * (x : ℝ) *
          (∑ p ∈ squareSourcePrimeRange y P, (((p : ℝ) ^ 2)⁻¹)) +
        2 * (squareSourcePrimeRange y P).card := by
      calc
        (∑ p ∈ squareSourcePrimeRange y P,
            2 * ((x : ℝ) * (((p : ℝ) ^ 2)⁻¹) + 1)) =
            (∑ p ∈ squareSourcePrimeRange y P,
              ((2 * (x : ℝ)) * (((p : ℝ) ^ 2)⁻¹) + 2)) := by
                apply Finset.sum_congr rfl
                intro p _hp
                ring
        _ = (∑ p ∈ squareSourcePrimeRange y P,
              (2 * (x : ℝ)) * (((p : ℝ) ^ 2)⁻¹)) +
            ∑ _p ∈ squareSourcePrimeRange y P, (2 : ℝ) :=
              Finset.sum_add_distrib
        _ = 2 * (x : ℝ) *
              (∑ p ∈ squareSourcePrimeRange y P, (((p : ℝ) ^ 2)⁻¹)) +
            2 * (squareSourcePrimeRange y P).card := by
              rw [Finset.mul_sum]
              simp
              ring
    _ ≤ 2 * (x : ℝ) * (y : ℝ)⁻¹ + 2 * (P : ℝ) := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left hsum (by positivity))
        (mul_le_mul_of_nonneg_left hcard (by norm_num))

/-- The preceding estimate at a square-root-sized upper cutoff.
@isnad1 id=le.5h4v.s7.efd78e930795 from=translated src=- shape=47a0cd96 vocab=f10895b2
-/
theorem squareSourceSet_card_cast_le_at_sqrt_cutoff {x h y P : ℕ}
    (hh : 0 < h) (hhy : h ≤ y) (hy : 0 < y) (hyP : y ≤ P)
    (hP : P ≤ (2 * x).sqrt) :
    ((squareSourceSet x h y P).card : ℝ) ≤
      2 * (x : ℝ) * (y : ℝ)⁻¹ + 2 * ((2 * x).sqrt : ℝ) := by
  have hPReal : (P : ℝ) ≤ ((2 * x).sqrt : ℝ) := by exact_mod_cast hP
  have htwice : 2 * (P : ℝ) ≤ 2 * ((2 * x).sqrt : ℝ) :=
    mul_le_mul_of_nonneg_left hPReal (by norm_num)
  exact (squareSourceSet_card_cast_le hh hhy hy hyP).trans
    (add_le_add le_rfl htwice)

/-- The full square-source branch at its automatic cutoff satisfies an explicit `2x/y + 2√(2x)` bound.
@isnad1 id=le.3h3v.s7.a54096b64d1a from=translated src=- shape=2c20079d vocab=f10895b2
-/
theorem squareSourceSet_card_cast_le_sqrt_cutoff {x h y : ℕ}
    (hh : 0 < h) (hhy : h ≤ y) (hy : 0 < y) :
    ((squareSourceSet x h y (2 * x).sqrt).card : ℝ) ≤
      2 * (x : ℝ) * (y : ℝ)⁻¹ + 2 * ((2 * x).sqrt : ℝ) := by
  by_cases hyCutoff : y ≤ (2 * x).sqrt
  · exact squareSourceSet_card_cast_le_at_sqrt_cutoff
      hh hhy hy hyCutoff le_rfl
  · classical
    have hrange : squareSourcePrimeRange y (2 * x).sqrt = ∅ := by
      apply Finset.eq_empty_of_forall_notMem
      intro p hp
      have hpData := mem_squareSourcePrimeRange.mp hp
      omega
    have hset : squareSourceSet x h y (2 * x).sqrt = ∅ := by
      simp [squareSourceSet, hrange]
    rw [hset]
    simp only [Finset.card_empty, Nat.cast_zero]
    positivity

/-- The explicitly witnessed nonsmooth square-source branch inherits the same unconditional square-root-cutoff estimate.
@isnad1 id=le.3h3v.s7.5307965e3426 from=translated src=- shape=2c20079d vocab=7fe85654
-/
theorem nonsmoothSquareSourceSet_card_cast_le_sqrt_cutoff {x h y : ℕ}
    (hh : 0 < h) (hhy : h ≤ y) (hy : 0 < y) :
    ((nonsmoothSquareSourceSet x h y (2 * x).sqrt).card : ℝ) ≤
      2 * (x : ℝ) * (y : ℝ)⁻¹ + 2 * ((2 * x).sqrt : ℝ) := by
  have hsubset : (nonsmoothSquareSourceSet x h y (2 * x).sqrt).card ≤
      (squareSourceSet x h y (2 * x).sqrt).card :=
    Finset.card_le_card (nonsmoothSquareSourceSet_subset_squareSourceSet
      x h y (2 * x).sqrt)
  have hsubsetReal : ((nonsmoothSquareSourceSet x h y (2 * x).sqrt).card : ℝ) ≤
      ((squareSourceSet x h y (2 * x).sqrt).card : ℝ) := by
    exact_mod_cast hsubset
  exact hsubsetReal.trans (squareSourceSet_card_cast_le_sqrt_cutoff hh hhy hy)

end RankAmplification
