import Tengoku.PaperCLean.PaperC.Arithmetic.ChannelCount
import Tengoku.PaperCLean.PaperC.Arithmetic.ChannelEnumeration

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Natural-number multiplicity bounds for primitive channels

The rational estimate in `ChannelCount` is convenient for analytic
expressions.  Proposition 5.4 and Lemma 5.5 also need its sharp integral
form: if `q = max a b`, then a primitive channel in the offset box has at
most `1 + L / q` cells.  Equivalently,

`q * (card - 1) ≤ L`.

This module records that form and its immediate consequences for
`channelSigma`.
-/

namespace PaperC

open Finset

/--
A residue class in the `L+1` consecutive offsets `{-1, ..., L-1}` contains
at most `1 + L / q` elements.
@isnad1 id=le.1h3v.s6.eefc9e9a809c from=translated src=- shape=a5870778 vocab=c6f94e52
-/
theorem card_offsetInterval_modClass_le_one_add_div
    (L : ℕ) (v : ℤ) (q : ℕ) (hq : 0 < q) :
    {i ∈ Ico (-1 : ℤ) (L : ℤ) |
      i ≡ v [ZMOD (q : ℤ)]}.card ≤ 1 + L / q := by
  have hcount :=
    card_Ico_modEq_le_ceil_length
      (-1 : ℤ) (L : ℤ) v (q : ℤ)
      (by exact_mod_cast hq) (by omega)
  have hdivision :
      L + 1 ≤ (L / q + 1) * q := by
    have hstrict := Nat.lt_div_mul_add (a := L) hq
    have hsucc :
        L + 1 ≤ L / q * q + q :=
      Nat.succ_le_iff.mpr hstrict
    simpa [Nat.add_mul] using hsucc
  have hquotient :
      (((((L : ℤ) - (-1 : ℤ)) : ℤ) : ℚ) / (q : ℚ)) ≤
        (((L / q + 1 : ℕ) : ℤ) : ℚ) := by
    apply (div_le_iff₀ (by exact_mod_cast hq)).2
    norm_num only [Int.cast_sub, Int.cast_natCast, Int.cast_neg,
      Int.cast_one, neg_neg, Nat.cast_add, Nat.cast_one]
    have hdivisionInt :
        (L : ℤ) - (-1 : ℤ) ≤
          (((L / q + 1) * q : ℕ) : ℤ) := by
      rw [sub_neg_eq_add]
      exact_mod_cast hdivision
    exact_mod_cast hdivisionInt
  have hceil :
      ⌈(((((L : ℤ) - (-1 : ℤ)) : ℤ) : ℚ) / (q : ℚ))⌉ ≤
        ((L / q + 1 : ℕ) : ℤ) :=
    Int.ceil_le.mpr hquotient
  have hcardInt :
      ({i ∈ Ico (-1 : ℤ) (L : ℤ) |
        i ≡ v [ZMOD (q : ℤ)]}.card : ℤ) ≤
        ((L / q + 1 : ℕ) : ℤ) :=
    hcount.trans hceil
  have hcardNat :
      {i ∈ Ico (-1 : ℤ) (L : ℤ) |
        i ≡ v [ZMOD (q : ℤ)]}.card ≤ L / q + 1 := by
    exact_mod_cast hcardInt
  simpa [Nat.add_comm] using hcardNat

/-- Sharp natural count obtained by projecting to the first coordinate.
@isnad1 id=le.3h4v.s6.02ca2ef96823 from=translated src=- shape=88362041 vocab=7961ebf7
-/
theorem channelCells_card_le_one_add_div_firstStep
    (L a b : ℕ) (ha : 0 < a) (hb : 0 < b) (hab : a.Coprime b)
    (h : ℤ) :
    (channelCells L a b h).card ≤ 1 + L / b := by
  classical
  by_cases hempty : channelCells L a b h = ∅
  · simp [hempty]
  · obtain ⟨cell₀, hcell₀⟩ :=
      Finset.nonempty_iff_ne_empty.mpr hempty
    have hcard :
        (channelFirstCoordinates L a b h).card =
          (channelCells L a b h).card :=
      card_image_of_injOn (fst_injOn_channelCells hb)
    calc
      (channelCells L a b h).card =
          (channelFirstCoordinates L a b h).card := hcard.symm
      _ ≤ {i ∈ Ico (-1 : ℤ) (L : ℤ) |
            i ≡ cell₀.1 [ZMOD (b : ℤ)]}.card :=
        card_mono
          (channelFirstCoordinates_subset_modClass
            ha hb hab hcell₀)
      _ ≤ 1 + L / b :=
        card_offsetInterval_modClass_le_one_add_div
          L cell₀.1 b hb

/-- Sharp natural count obtained by projecting to the second coordinate.
@isnad1 id=le.3h4v.s6.c16fa240cad9 from=translated src=- shape=b04ea1bd vocab=7961ebf7
-/
theorem channelCells_card_le_one_add_div_secondStep
    (L a b : ℕ) (ha : 0 < a) (hb : 0 < b) (hab : a.Coprime b)
    (h : ℤ) :
    (channelCells L a b h).card ≤ 1 + L / a := by
  classical
  by_cases hempty : channelCells L a b h = ∅
  · simp [hempty]
  · obtain ⟨cell₀, hcell₀⟩ :=
      Finset.nonempty_iff_ne_empty.mpr hempty
    have hcard :
        (channelSecondCoordinates L a b h).card =
          (channelCells L a b h).card :=
      card_image_of_injOn (snd_injOn_channelCells ha)
    calc
      (channelCells L a b h).card =
          (channelSecondCoordinates L a b h).card := hcard.symm
      _ ≤ {j ∈ Ico (-1 : ℤ) (L : ℤ) |
            j ≡ cell₀.2 [ZMOD (a : ℤ)]}.card :=
        card_mono
          (channelSecondCoordinates_subset_modClass
            ha hb hab hcell₀)
      _ ≤ 1 + L / a :=
        card_offsetInterval_modClass_le_one_add_div
          L cell₀.2 a ha

/--
Sharp natural-number form of the primitive-channel lattice-point estimate,
with `q = max a b`.
@isnad1 id=le.3h4v.s6.96e7d77f99db from=translated src=- shape=cf789701 vocab=c8a77f78
-/
theorem channelCells_card_le_one_add_div_maxStep
    (L a b : ℕ) (ha : 0 < a) (hb : 0 < b) (hab : a.Coprime b)
    (h : ℤ) :
    (channelCells L a b h).card ≤ 1 + L / Nat.max a b := by
  by_cases habOrder : a ≤ b
  · simpa [Nat.max_eq_right habOrder] using
      channelCells_card_le_one_add_div_firstStep
        L a b ha hb hab h
  · have hba : b ≤ a := le_of_not_ge habOrder
    simpa [Nat.max_eq_left hba] using
      channelCells_card_le_one_add_div_secondStep
        L a b ha hb hab h

/--
Subtraction-free packing form: successive cells consume at least one step
`q = max a b` across an interval of diameter `L`.
@isnad1 id=le.3h4v.s6.a31d56650c94 from=translated src=- shape=e578e0fd vocab=37e46331
-/
theorem maxStep_mul_channelCells_card_sub_one_le
    (L a b : ℕ) (ha : 0 < a) (hb : 0 < b) (hab : a.Coprime b)
    (h : ℤ) :
    Nat.max a b * ((channelCells L a b h).card - 1) ≤ L := by
  let q := Nat.max a b
  have hcard :=
    channelCells_card_le_one_add_div_maxStep
      L a b ha hb hab h
  have hpred :
      (channelCells L a b h).card - 1 ≤ L / q := by
    rw [Nat.sub_le_iff_le_add]
    simpa [q, Nat.add_comm] using hcard
  calc
    q * ((channelCells L a b h).card - 1) ≤
        q * (L / q) :=
      Nat.mul_le_mul_left q hpred
    _ ≤ L := Nat.mul_div_le L q

/-- The preceding estimate in the named `channelSigma` notation.
@isnad1 id=le.3h4v.s5.fb62f1a4ccca from=translated src=- shape=87f1edc5 vocab=bd82854f
-/
theorem maxStep_mul_channelSigma_le
    (L a b : ℕ) (ha : 0 < a) (hb : 0 < b) (hab : a.Coprime b)
    (h : ℤ) :
    Nat.max a b * channelSigma L a b h ≤ L := by
  simpa [channelSigma] using
    maxStep_mul_channelCells_card_sub_one_le
      L a b ha hb hab h

/-- Quotient form of the channel-dimension estimate.
@isnad1 id=le.3h4v.s5.8a088f4de776 from=translated src=- shape=4c166a11 vocab=04fe96da
-/
theorem channelSigma_le_div_maxStep
    (L a b : ℕ) (ha : 0 < a) (hb : 0 < b) (hab : a.Coprime b)
    (h : ℤ) :
    channelSigma L a b h ≤ L / Nat.max a b := by
  have hq : 0 < Nat.max a b :=
    ha.trans_le (Nat.le_max_left a b)
  apply (Nat.le_div_iff_mul_le hq).2
  simpa [Nat.mul_comm] using
    maxStep_mul_channelSigma_le L a b ha hb hab h

/-- Monotone consequence for binary choices on a channel.
@isnad1 id=le.3h4v.s6.b27145ba878c from=translated src=- shape=1b8a6bfc vocab=58fb3c71
-/
theorem two_pow_channelSigma_le_div_maxStep
    (L a b : ℕ) (ha : 0 < a) (hb : 0 < b) (hab : a.Coprime b)
    (h : ℤ) :
    2 ^ channelSigma L a b h ≤
      2 ^ (L / Nat.max a b) :=
  Nat.pow_le_pow_right (by norm_num)
    (channelSigma_le_div_maxStep L a b ha hb hab h)

/-- Monotone consequence for the squared binary weight.
@isnad1 id=le.3h4v.s6.fb022895d338 from=translated src=- shape=1b8a6bfc vocab=58fb3c71
-/
theorem four_pow_channelSigma_le_div_maxStep
    (L a b : ℕ) (ha : 0 < a) (hb : 0 < b) (hab : a.Coprime b)
    (h : ℤ) :
    4 ^ channelSigma L a b h ≤
      4 ^ (L / Nat.max a b) :=
  Nat.pow_le_pow_right (by norm_num)
    (channelSigma_le_div_maxStep L a b ha hb hab h)

end PaperC
