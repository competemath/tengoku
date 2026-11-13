import Tengoku.Rankamplificationtotient.RankAmplification.Section9Assembly

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # Same-support indices and the two-variable S-unit equation This module isolates the exact arithmetic reduction behind Lemma 9.1. -/

namespace RankAmplification

noncomputable section

/-! ## Support units and the affine equation -/

/-- A positive natural number all of whose prime factors belong to `S`.-/
def IsPrimeSupportUnit (S : Finset ℕ) (n : ℕ) : Prop :=
  0 < n ∧ primeSupport n ⊆ S

/-- The two-variable affine S-unit equation used in the qualitative proof of Lemma 9.1.-/
def IsSUnitAffineSolution (S : Finset ℕ) (h u v : ℕ) : Prop :=
  IsPrimeSupportUnit S u ∧ IsPrimeSupportUnit S v ∧ u + h = v

/-- An exact finite carrier for all positive natural solutions of the affine S-unit equation.-/
def IsSUnitAffineCarrier (S : Finset ℕ) (h : ℕ) (U : Finset (ℕ × ℕ)) : Prop :=
  ∀ u v, (u, v) ∈ U ↔ IsSUnitAffineSolution S h u v

@[simp, nolint simpNF]
theorem mem_sUnitAffineCarrier {S : Finset ℕ} {h : ℕ} {U : Finset (ℕ × ℕ)}
    (hU : IsSUnitAffineCarrier S h U) {u v : ℕ} :
    (u, v) ∈ U ↔ IsSUnitAffineSolution S h u v :=
  hU u v

theorem IsPrimeSupportUnit.pos {S : Finset ℕ} {n : ℕ}
    (hn : IsPrimeSupportUnit S n) : 0 < n :=
  hn.1

theorem IsPrimeSupportUnit.ne_zero {S : Finset ℕ} {n : ℕ}
    (hn : IsPrimeSupportUnit S n) : n ≠ 0 :=
  hn.1.ne'

theorem IsPrimeSupportUnit.mono {S T : Finset ℕ} {n : ℕ}
    (hn : IsPrimeSupportUnit S n) (hST : S ⊆ T) :
    IsPrimeSupportUnit T n :=
  ⟨hn.1, hn.2.trans hST⟩

/-! ## Equal support forces support over the primes of the shift -/

/-- Every common prime divisor of `j` and `j+h` divides the shift.-/
theorem primeSupport_subset_shift_of_sameSupport {h j : ℕ} (hh : 0 < h)
    (hsame : IsSameSupportIndex h j) :
    primeSupport j ⊆ primeSupport h := by
  intro p hpj
  have hpjh : p ∈ primeSupport (j + h) := by
    simpa only [hsame.2] using hpj
  have hpj_dvd : p ∣ j := Nat.dvd_of_mem_primeFactors hpj
  have hpjh_dvd : p ∣ j + h := Nat.dvd_of_mem_primeFactors hpjh
  have hph : p ∣ h := by
    simpa using Nat.dvd_sub hpjh_dvd hpj_dvd
  exact (Nat.prime_of_mem_primeFactors hpj).mem_primeFactors hph hh.ne'

theorem shiftedPrimeSupport_subset_shift_of_sameSupport {h j : ℕ} (hh : 0 < h)
    (hsame : IsSameSupportIndex h j) :
    primeSupport (j + h) ⊆ primeSupport h := by
  rw [← hsame.2]
  exact primeSupport_subset_shift_of_sameSupport hh hsame

theorem sameSupport_left_isPrimeSupportUnit {h j : ℕ} (hh : 0 < h)
    (hsame : IsSameSupportIndex h j) :
    IsPrimeSupportUnit (primeSupport h) j :=
  ⟨zero_lt_one.trans_le hsame.1,
    primeSupport_subset_shift_of_sameSupport hh hsame⟩

theorem sameSupport_right_isPrimeSupportUnit {h j : ℕ} (hh : 0 < h)
    (hsame : IsSameSupportIndex h j) :
    IsPrimeSupportUnit (primeSupport h) (j + h) :=
  ⟨by omega, shiftedPrimeSupport_subset_shift_of_sameSupport hh hsame⟩

/-- The exact two-variable S-unit reduction `j ↦ (j,j+h)`.-/
theorem sameSupport_isSUnitAffineSolution {h j : ℕ} (hh : 0 < h)
    (hsame : IsSameSupportIndex h j) :
    IsSUnitAffineSolution (primeSupport h) h j (j + h) :=
  ⟨sameSupport_left_isPrimeSupportUnit hh hsame,
    sameSupport_right_isPrimeSupportUnit hh hsame, rfl⟩

/-! ## Normalized `a,b,c` data -/

/-- `a = j / gcd(j,j+h)`.-/
def normalizedSUnitA (h j : ℕ) : ℕ := diagonalB h j

/-- `b = (j+h) / gcd(j,j+h)`.-/
def normalizedSUnitB (h j : ℕ) : ℕ := diagonalA h j

/-- `c = h / gcd(j,j+h)`, so that `a+c=b`.-/
def normalizedSUnitC (h j : ℕ) : ℕ := h / diagonalGCD h j

/-- The normalized triple records the integral `S`-unit equation and its primitive condition.-/
structure IsNormalizedSUnitTriple (S : Finset ℕ) (a b c : ℕ) : Prop where
  a_unit : IsPrimeSupportUnit S a
  b_unit : IsPrimeSupportUnit S b
  c_unit : IsPrimeSupportUnit S c
  affine : a + c = b
  coprime_ab : Nat.Coprime a b
  coprime_ac : Nat.Coprime a c
  coprime_bc : Nat.Coprime b c

theorem diagonalGCD_dvd_shift (h j : ℕ) : diagonalGCD h j ∣ h := by
  simpa using Nat.dvd_sub (diagonalGCD_dvd_right h j)
    (diagonalGCD_dvd_left h j)

theorem diagonalGCD_mul_normalizedSUnitA (h j : ℕ) :
    diagonalGCD h j * normalizedSUnitA h j = j := by
  exact diagonalGCD_mul_diagonalB h j

theorem diagonalGCD_mul_normalizedSUnitB (h j : ℕ) :
    diagonalGCD h j * normalizedSUnitB h j = j + h := by
  exact diagonalGCD_mul_diagonalA h j

theorem diagonalGCD_mul_normalizedSUnitC (h j : ℕ) :
    diagonalGCD h j * normalizedSUnitC h j = h := by
  rw [normalizedSUnitC, Nat.mul_div_cancel' (diagonalGCD_dvd_shift h j)]

theorem normalizedSUnitA_pos {h j : ℕ} (hj : 0 < j) :
    0 < normalizedSUnitA h j :=
  diagonalB_pos hj

theorem normalizedSUnitB_pos {h j : ℕ} (hj : 0 < j) :
    0 < normalizedSUnitB h j :=
  diagonalA_pos hj

theorem normalizedSUnitC_pos {h j : ℕ} (hh : 0 < h) (hj : 0 < j) :
    0 < normalizedSUnitC h j := by
  apply Nat.div_pos
  · exact Nat.le_of_dvd hh (diagonalGCD_dvd_shift h j)
  · exact Nat.gcd_pos_of_pos_left (j + h) hj

/-- Cancelling the positive common gcd gives the primitive affine equation `a+c=b`.-/
theorem normalizedSUnit_affine {h j : ℕ} (hj : 0 < j) :
    normalizedSUnitA h j + normalizedSUnitC h j = normalizedSUnitB h j := by
  apply Nat.eq_of_mul_eq_mul_left (Nat.gcd_pos_of_pos_left (j + h) hj)
  calc
    diagonalGCD h j * (normalizedSUnitA h j + normalizedSUnitC h j) =
        j + h := by
      rw [Nat.mul_add, diagonalGCD_mul_normalizedSUnitA,
        diagonalGCD_mul_normalizedSUnitC]
    _ = diagonalGCD h j * normalizedSUnitB h j :=
      (diagonalGCD_mul_normalizedSUnitB h j).symm

/-- Dividing both variables by their gcd makes the normalized pair coprime.-/
theorem normalizedSUnit_coprime {h j : ℕ} (hj : 0 < j) :
    Nat.Coprime (normalizedSUnitA h j) (normalizedSUnitB h j) := by
  exact Nat.coprime_div_gcd_div_gcd
    (Nat.gcd_pos_of_pos_left (j + h) hj)

theorem normalizedSUnit_coprime_a_c {h j : ℕ} (hj : 0 < j) :
    Nat.Coprime (normalizedSUnitA h j) (normalizedSUnitC h j) := by
  rw [← Nat.coprime_self_add_right]
  rw [normalizedSUnit_affine hj]
  exact normalizedSUnit_coprime hj

theorem normalizedSUnit_coprime_b_c {h j : ℕ} (hj : 0 < j) :
    Nat.Coprime (normalizedSUnitB h j) (normalizedSUnitC h j) := by
  rw [← normalizedSUnit_affine hj]
  rw [Nat.coprime_add_self_left]
  exact normalizedSUnit_coprime_a_c hj

theorem normalizedSUnitA_dvd_left (h j : ℕ) : normalizedSUnitA h j ∣ j := by
  exact ⟨diagonalGCD h j, (diagonalGCD_mul_normalizedSUnitA h j).symm.trans
    (Nat.mul_comm _ _)⟩

theorem normalizedSUnitB_dvd_right (h j : ℕ) : normalizedSUnitB h j ∣ j + h := by
  exact ⟨diagonalGCD h j, (diagonalGCD_mul_normalizedSUnitB h j).symm.trans
    (Nat.mul_comm _ _)⟩

theorem normalizedSUnitC_dvd_shift (h j : ℕ) : normalizedSUnitC h j ∣ h := by
  exact ⟨diagonalGCD h j, (diagonalGCD_mul_normalizedSUnitC h j).symm.trans
    (Nat.mul_comm _ _)⟩

theorem normalizedSUnitA_isPrimeSupportUnit {h j : ℕ} (hh : 0 < h)
    (hsame : IsSameSupportIndex h j) :
    IsPrimeSupportUnit (primeSupport h) (normalizedSUnitA h j) := by
  refine ⟨normalizedSUnitA_pos (zero_lt_one.trans_le hsame.1), ?_⟩
  exact (Nat.primeFactors_mono (normalizedSUnitA_dvd_left h j)
    (sameSupport_left_isPrimeSupportUnit hh hsame).ne_zero).trans
      (primeSupport_subset_shift_of_sameSupport hh hsame)

theorem normalizedSUnitB_isPrimeSupportUnit {h j : ℕ} (hh : 0 < h)
    (hsame : IsSameSupportIndex h j) :
    IsPrimeSupportUnit (primeSupport h) (normalizedSUnitB h j) := by
  refine ⟨normalizedSUnitB_pos (zero_lt_one.trans_le hsame.1), ?_⟩
  exact (Nat.primeFactors_mono (normalizedSUnitB_dvd_right h j)
    (sameSupport_right_isPrimeSupportUnit hh hsame).ne_zero).trans
      (shiftedPrimeSupport_subset_shift_of_sameSupport hh hsame)

theorem normalizedSUnitC_isPrimeSupportUnit {h j : ℕ} (hh : 0 < h)
    (hsame : IsSameSupportIndex h j) :
    IsPrimeSupportUnit (primeSupport h) (normalizedSUnitC h j) := by
  refine ⟨normalizedSUnitC_pos hh (zero_lt_one.trans_le hsame.1), ?_⟩
  exact Nat.primeFactors_mono (normalizedSUnitC_dvd_shift h j) hh.ne'

/-- Complete normalized `a,b,c` reduction of a same-support index.-/
theorem sameSupport_isNormalizedSUnitTriple {h j : ℕ} (hh : 0 < h)
    (hsame : IsSameSupportIndex h j) :
    IsNormalizedSUnitTriple (primeSupport h)
      (normalizedSUnitA h j) (normalizedSUnitB h j) (normalizedSUnitC h j) where
  a_unit := normalizedSUnitA_isPrimeSupportUnit hh hsame
  b_unit := normalizedSUnitB_isPrimeSupportUnit hh hsame
  c_unit := normalizedSUnitC_isPrimeSupportUnit hh hsame
  affine := normalizedSUnit_affine (zero_lt_one.trans_le hsame.1)
  coprime_ab := normalizedSUnit_coprime (zero_lt_one.trans_le hsame.1)
  coprime_ac := normalizedSUnit_coprime_a_c (zero_lt_one.trans_le hsame.1)
  coprime_bc := normalizedSUnit_coprime_b_c (zero_lt_one.trans_le hsame.1)

/-! ## Exact finite injection and cover -/

/-- The injective map taking an index to its two affine variables.-/
def sameSupportAffineEmbedding (h : ℕ) : ℕ ↪ ℕ × ℕ where
  toFun j := (j, j + h)
  inj' := by
    intro j k hjk
    exact congrArg Prod.fst hjk

/-- The exact pair image of a proposed finite same-support carrier.-/
def sameSupportAffineImage (h : ℕ) (J : Finset ℕ) : Finset (ℕ × ℕ) :=
  J.map (sameSupportAffineEmbedding h)

@[simp]
theorem mem_sameSupportAffineImage {h : ℕ} {J : Finset ℕ} {u v : ℕ} :
    (u, v) ∈ sameSupportAffineImage h J ↔ u ∈ J ∧ v = u + h := by
  constructor
  · intro huv
    obtain ⟨j, hj, hpair⟩ := Finset.mem_map.mp huv
    have hu : j = u := congrArg Prod.fst hpair
    subst u
    exact ⟨hj, (congrArg Prod.snd hpair).symm⟩
  · rintro ⟨hu, rfl⟩
    exact Finset.mem_map.mpr ⟨u, hu, rfl⟩

@[simp]
theorem card_sameSupportAffineImage (h : ℕ) (J : Finset ℕ) :
    (sameSupportAffineImage h J).card = J.card :=
  Finset.card_map _

/-- A true finite carrier injects into every exact carrier of the larger affine S-unit equation.-/
theorem sameSupportAffineImage_subset_sUnitCarrier
    {h : ℕ} (hh : 0 < h) {J : Finset ℕ} {U : Finset (ℕ × ℕ)}
    (hJ : IsSameSupportCarrier h J)
    (hU : IsSUnitAffineCarrier (primeSupport h) h U) :
    sameSupportAffineImage h J ⊆ U := by
  intro z hz
  obtain ⟨u, v⟩ := z
  have hzData := mem_sameSupportAffineImage.mp hz
  rw [hzData.2]
  exact (hU u (u + h)).mpr
    (sameSupport_isSUnitAffineSolution hh ((hJ u).mp hzData.1))

theorem card_sameSupportCarrier_le_sUnitCarrier
    {h : ℕ} (hh : 0 < h) {J : Finset ℕ} {U : Finset (ℕ × ℕ)}
    (hJ : IsSameSupportCarrier h J)
    (hU : IsSUnitAffineCarrier (primeSupport h) h U) :
    J.card ≤ U.card := by
  rw [← card_sameSupportAffineImage h J]
  exact Finset.card_le_card
    (sameSupportAffineImage_subset_sUnitCarrier hh hJ hU)

/-- Filter the first-coordinate projection of an affine carrier by the original equal-support predicate.-/
def sameSupportCarrierFromSUnit (h : ℕ) (U : Finset (ℕ × ℕ)) : Finset ℕ :=
  by
    classical
    exact (U.image Prod.fst).filter (IsSameSupportIndex h)

theorem isSameSupportCarrier_sameSupportCarrierFromSUnit
    {h : ℕ} (hh : 0 < h) {U : Finset (ℕ × ℕ)}
    (hU : IsSUnitAffineCarrier (primeSupport h) h U) :
    IsSameSupportCarrier h (sameSupportCarrierFromSUnit h U) := by
  classical
  intro j
  constructor
  · intro hj
    rw [sameSupportCarrierFromSUnit, Finset.mem_filter] at hj
    exact hj.2
  · intro hj
    rw [sameSupportCarrierFromSUnit, Finset.mem_filter]
    refine ⟨?_, hj⟩
    apply Finset.mem_image.mpr
    refine ⟨(j, j + h), ?_, rfl⟩
    exact (hU j (j + h)).mpr (sameSupport_isSUnitAffineSolution hh hj)

/-- The portion of an affine carrier whose first coordinate really is a same-support index.-/
def sameSupportPartOfSUnitCarrier (h : ℕ) (U : Finset (ℕ × ℕ)) : Finset (ℕ × ℕ) :=
  by
    classical
    exact U.filter fun z ↦ IsSameSupportIndex h z.1

/-- The filtered projection loses no representation: the affine equation determines the second coordinate, so mapping the recovered indices back gives exactly the same-support part of `U`.-/
theorem sameSupportAffineImage_fromSUnit_eq_part
    {h : ℕ} (hh : 0 < h) {U : Finset (ℕ × ℕ)}
    (hU : IsSUnitAffineCarrier (primeSupport h) h U) :
    sameSupportAffineImage h (sameSupportCarrierFromSUnit h U) =
      sameSupportPartOfSUnitCarrier h U := by
  classical
  ext z
  obtain ⟨u, v⟩ := z
  constructor
  · intro hz
    have hzData := mem_sameSupportAffineImage.mp hz
    have huCarrier : u ∈ U.image Prod.fst ∧ IsSameSupportIndex h u := by
      simpa only [sameSupportCarrierFromSUnit, Finset.mem_filter] using hzData.1
    have hsame := huCarrier.2
    have hv : v = u + h := hzData.2
    rw [sameSupportPartOfSUnitCarrier, Finset.mem_filter]
    refine ⟨?_, hsame⟩
    rw [hv]
    exact (hU u (u + h)).mpr (sameSupport_isSUnitAffineSolution hh hsame)
  · intro hz
    have hzData : (u, v) ∈ U ∧ IsSameSupportIndex h u := by
      simpa only [sameSupportPartOfSUnitCarrier, Finset.mem_filter] using hz
    have hsolution := (hU u v).mp hzData.1
    apply mem_sameSupportAffineImage.mpr
    refine ⟨?_, hsolution.2.2.symm⟩
    rw [sameSupportCarrierFromSUnit, Finset.mem_filter]
    refine ⟨?_, hzData.2⟩
    exact Finset.mem_image.mpr ⟨(u, v), hzData.1, rfl⟩

theorem card_sameSupportCarrierFromSUnit_eq_part
    {h : ℕ} (hh : 0 < h) {U : Finset (ℕ × ℕ)}
    (hU : IsSUnitAffineCarrier (primeSupport h) h U) :
    (sameSupportCarrierFromSUnit h U).card =
      (sameSupportPartOfSUnitCarrier h U).card := by
  rw [← card_sameSupportAffineImage h (sameSupportCarrierFromSUnit h U),
    sameSupportAffineImage_fromSUnit_eq_part hh hU]

theorem card_sameSupportCarrierFromSUnit_le
    (h : ℕ) (U : Finset (ℕ × ℕ)) :
    (sameSupportCarrierFromSUnit h U).card ≤ U.card := by
  classical
  unfold sameSupportCarrierFromSUnit
  calc
    ((U.image Prod.fst).filter (IsSameSupportIndex h)).card ≤ (U.image Prod.fst).card :=
      Finset.card_filter_le _ _
    _ ≤ U.card := Finset.card_image_le

/-! ## Honest terminal finiteness inputs -/

/-- The exact qualitative terminal input supplied by the standard Evertse `S`-unit theorem.-/
def TerminalEvertseSUnitFiniteness (h : ℕ) : Prop :=
  ∃ U : Finset (ℕ × ℕ), IsSUnitAffineCarrier (primeSupport h) h U

/-- A selected finite affine carrier, conditional on the terminal Evertse input.-/
def terminalEvertseSUnitCarrier (h : ℕ) (hE : TerminalEvertseSUnitFiniteness h) :
    Finset (ℕ × ℕ) :=
  Classical.choose hE

theorem terminalEvertseSUnitCarrier_spec (h : ℕ)
    (hE : TerminalEvertseSUnitFiniteness h) :
    IsSUnitAffineCarrier (primeSupport h) h (terminalEvertseSUnitCarrier h hE) :=
  Classical.choose_spec hE

/-- The reusable `Section9Assembly.IsSameSupportCarrier` recovered from Evertse's terminal input.-/
def sameSupportCarrierOfEvertse (h : ℕ) (hE : TerminalEvertseSUnitFiniteness h) : Finset ℕ :=
  sameSupportCarrierFromSUnit h (terminalEvertseSUnitCarrier h hE)

theorem isSameSupportCarrier_sameSupportCarrierOfEvertse
    {h : ℕ} (hh : 0 < h) (hE : TerminalEvertseSUnitFiniteness h) :
    IsSameSupportCarrier h (sameSupportCarrierOfEvertse h hE) :=
  isSameSupportCarrier_sameSupportCarrierFromSUnit hh
    (terminalEvertseSUnitCarrier_spec h hE)

theorem exists_isSameSupportCarrier_of_terminalEvertse
    {h : ℕ} (hh : 0 < h) (hE : TerminalEvertseSUnitFiniteness h) :
    ∃ J : Finset ℕ, IsSameSupportCarrier h J :=
  ⟨sameSupportCarrierOfEvertse h hE,
    isSameSupportCarrier_sameSupportCarrierOfEvertse hh hE⟩

/-- The explicit Pollack--Pomerance--Treviño cardinality appearing in Lemma 9.1.-/
def pptSameSupportBound (h : ℕ) : ℕ :=
  3 * 7 ^ (3 + 2 * (primeSupport h).card)

/-- The quantitative PPT endpoint, again recorded only as an external proposition to be supplied.-/
def TerminalPPTSameSupportBound (h : ℕ) : Prop :=
  ∃ J : Finset ℕ,
    IsSameSupportCarrier h J ∧ J.card ≤ pptSameSupportBound h

/-- Finite same-support carrier selected from the quantitative PPT endpoint.-/
def sameSupportCarrierOfPPT (h : ℕ) (hPPT : TerminalPPTSameSupportBound h) : Finset ℕ :=
  Classical.choose hPPT

theorem isSameSupportCarrier_sameSupportCarrierOfPPT
    (h : ℕ) (hPPT : TerminalPPTSameSupportBound h) :
    IsSameSupportCarrier h (sameSupportCarrierOfPPT h hPPT) :=
  (Classical.choose_spec hPPT).1

theorem card_sameSupportCarrierOfPPT_le
    (h : ℕ) (hPPT : TerminalPPTSameSupportBound h) :
    (sameSupportCarrierOfPPT h hPPT).card ≤ pptSameSupportBound h :=
  (Classical.choose_spec hPPT).2

/-! ## Odd shifts: unconditional empty and stronger S-unit branches -/

/-- A positive number supported only on primes dividing an odd shift is itself odd.-/
theorem IsPrimeSupportUnit.odd_of_shift_odd {h n : ℕ} (hodd : Odd h)
    (hn : IsPrimeSupportUnit (primeSupport h) n) : Odd n := by
  apply Nat.not_even_iff_odd.mp
  intro hneven
  have htwo_dvd_n : 2 ∣ n := even_iff_two_dvd.mp hneven
  have htwo_mem_n : 2 ∈ primeSupport n :=
    Nat.mem_primeFactors.mpr ⟨Nat.prime_two, htwo_dvd_n, hn.ne_zero⟩
  have htwo_mem_h : 2 ∈ primeSupport h := hn.2 htwo_mem_n
  have htwo_dvd_h : 2 ∣ h := Nat.dvd_of_mem_primeFactors htwo_mem_h
  exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr htwo_dvd_h)

/-- Stronger than merely `J_h = ∅`: the ambient positive natural S-unit equation has no solution at all when the shift is odd.-/
theorem not_isSUnitAffineSolution_of_odd {h u v : ℕ} (hodd : Odd h) :
    ¬IsSUnitAffineSolution (primeSupport h) h u v := by
  rintro ⟨hu, hv, huv⟩
  have huodd : Odd u := hu.odd_of_shift_odd hodd
  have hvodd : Odd v := hv.odd_of_shift_odd hodd
  have heven : Even (u + h) :=
    Nat.even_add'.mpr ⟨fun _ ↦ hodd, fun _ ↦ huodd⟩
  rw [huv] at heven
  exact (Nat.not_even_iff_odd.mpr hvodd) heven

theorem sUnitAffineCarrier_eq_empty_of_odd
    {h : ℕ} (hodd : Odd h) {U : Finset (ℕ × ℕ)}
    (hU : IsSUnitAffineCarrier (primeSupport h) h U) :
    U = ∅ := by
  apply Finset.eq_empty_of_forall_notMem
  rintro ⟨u, v⟩ huv
  exact not_isSUnitAffineSolution_of_odd hodd ((hU u v).mp huv)

/-- For an odd shift, the empty affine carrier proves the would-be Evertse endpoint directly.-/
theorem isSUnitAffineCarrier_empty_of_odd {h : ℕ} (hodd : Odd h) :
    IsSUnitAffineCarrier (primeSupport h) h ∅ := by
  intro u v
  simp only [Finset.notMem_empty, false_iff]
  exact not_isSUnitAffineSolution_of_odd hodd

theorem terminalEvertseSUnitFiniteness_of_odd {h : ℕ} (hodd : Odd h) :
    TerminalEvertseSUnitFiniteness h :=
  ⟨∅, isSUnitAffineCarrier_empty_of_odd hodd⟩

theorem sameSupportCarrier_eq_empty_of_odd
    {h : ℕ} (hodd : Odd h) {J : Finset ℕ}
    (hJ : IsSameSupportCarrier h J) :
    J = ∅ := by
  ext j
  rw [hJ j]
  simp only [Finset.notMem_empty, iff_false]
  exact not_isSameSupportIndex_of_odd hodd

theorem sameSupportAffineImage_eq_empty_of_odd
    {h : ℕ} (hodd : Odd h) {J : Finset ℕ}
    (hJ : IsSameSupportCarrier h J) :
    sameSupportAffineImage h J = ∅ := by
  rw [sameSupportCarrier_eq_empty_of_odd hodd hJ]
  rfl

theorem terminalPPTSameSupportBound_of_odd {h : ℕ} (hodd : Odd h) :
    TerminalPPTSameSupportBound h := by
  refine ⟨∅, isSameSupportCarrier_empty_of_odd hodd, ?_⟩
  simp only [Finset.card_empty, Nat.zero_le]

theorem sameSupportCarrierOfEvertse_eq_empty_of_odd
    {h : ℕ} (hodd : Odd h) (hE : TerminalEvertseSUnitFiniteness h) :
    sameSupportCarrierOfEvertse h hE = ∅ :=
  sameSupportCarrier_eq_empty_of_odd hodd
    (isSameSupportCarrier_sameSupportCarrierOfEvertse hodd.pos hE)

end

end RankAmplification
