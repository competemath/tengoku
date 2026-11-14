import Tengoku.Piirrationalitymeasure.Formalization.PiIrrationality

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option maxRecDepth 100000

/-!
Discrete certificates for the five index families in Section 3.1.
-/

namespace PiIrrationality

def familyI : Finset ℕ :=
  (Finset.Icc 1 371).filter (fun j => j % 2 = 1)

def familyII : Finset ℕ :=
  (Finset.Icc 2 1114).filter (fun j => j % 2 = 0)

def familyIII : Finset ℕ :=
  (Finset.Icc 373 1855).filter (fun j => j % 2 = 1)

def familyIV : Finset ℕ :=
  (Finset.Icc 1116 1856).filter (fun j => j % 2 = 0)

def familyV : Finset ℕ :=
  (Finset.Icc 1859 3713).filter (fun j => j % 2 = 1)

def indexSum (s : Finset ℕ) : ℕ := s.sum id

/--
@isnad1 id=eq.0h1v.s4.39e97bfe9cdf from=translated src=- shape=1cbbfbe7 vocab=7fe1c8ab
-/
theorem cast_indexSum (s : Finset ℕ) :
    (indexSum s : ℚ) = s.sum (fun j => (j : ℚ)) := by
  unfold indexSum
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      simp [ha, Nat.cast_add]

def familyILength : ℚ :=
  (2 * (indexSum familyI : ℚ) + (familyI.card : ℚ) * 3714) / (2 * 5570 * 3714)

def familyIILength : ℚ :=
  (indexSum familyII : ℚ) / (5570 * 3714)

def familyIIILength : ℚ :=
  ((familyIII.card : ℚ) * 3714 - 2 * (indexSum familyIII : ℚ)) / (2 * 3715 * 3714)

def familyIVLength : ℚ :=
  ((familyIV.card : ℚ) * 3714 - 2 * (indexSum familyIV : ℚ)) / (2 * 3715 * 3714)

def familyVLength : ℚ :=
  (2 * (indexSum familyV : ℚ) - (familyV.card : ℚ) * 3714) / (2 * 5570 * 3714)

def firstLeftEndpoint : ℚ := 1 / 3714

def periodicSummand (ell r q : ℚ) : ℚ :=
  (r - ell) / ((q + ell) * (q + r))

/--
@isnad1 id=eq.2h3v.s6.36ce95d26dbc from=translated src=- shape=ae1591ab vocab=5b420fd6
-/
theorem periodicSummand_eq_sub_inv {ell r q : ℚ}
    (hℓ : q + ell ≠ 0) (hr : q + r ≠ 0) :
    periodicSummand ell r q = 1 / (q + ell) - 1 / (q + r) := by
  unfold periodicSummand
  field_simp [hℓ, hr]
  ring

/--
@isnad1 id=lt.3h3v.s5.eb4527005027 from=translated src=- shape=ad19e1e2 vocab=32ed9c61
-/
theorem periodicSummand_pos {ell r q : ℚ}
    (hℓ : 0 < q + ell) (hr : 0 < q + r) (hord : ell < r) :
    0 < periodicSummand ell r q := by
  unfold periodicSummand
  have hden : 0 < (q + ell) * (q + r) := mul_pos hℓ hr
  apply div_pos
  · linarith
  · exact hden

/--
@isnad1 id=le.4h3v.s6.0e326dfa9fe2 from=translated src=- shape=ba90c9ef vocab=8dce521c
-/
theorem periodicSummand_le_inv_sq {ell r q : ℚ}
    (hℓ : 0 < ell) (hord : ell < r) (hr : r ≤ 1) (hq : 1 ≤ q) :
    periodicSummand ell r q ≤ 1 / q ^ 2 := by
  have hqpos : 0 < q := lt_of_lt_of_le (by norm_num) hq
  have hden : 0 < (q + ell) * (q + r) := by
    exact mul_pos (by linarith) (by linarith)
  have hq2 : 0 < q ^ 2 := sq_pos_of_pos hqpos
  apply (div_le_div_iff₀ hden hq2).2
  have hnum : r - ell ≤ 1 := by linarith
  have hprod : q ^ 2 ≤ (q + ell) * (q + r) := by
    nlinarith [mul_pos hℓ (by linarith : 0 < r)]
  calc
    (r - ell) * q ^ 2 ≤ 1 * q ^ 2 := by
      exact mul_le_mul_of_nonneg_right hnum (sq_nonneg q)
    _ ≤ 1 * ((q + ell) * (q + r)) := by
      exact mul_le_mul_of_nonneg_left hprod (by norm_num)

/--
@isnad1 id=iff.8h6v.s7.b5b94b274050 from=translated src=- shape=dfee417c vocab=a36accce
-/
theorem interval_endpoint_equiv
    {n p q ell r u : ℝ}
    (hn : 0 < n) (hp : 0 < p) (hq : 0 ≤ q) (hu0 : 0 ≤ u) (hu1 : u < 1)
    (heq : n / p = q + u) (hell : 0 < ell) (hord : ell < r) :
    (ell ≤ u ∧ u < r) ↔
      (n / (q + r) < p ∧ p ≤ n / (q + ell)) := by
  have hqell : 0 < q + ell := by linarith
  have hqr : 0 < q + r := by linarith
  constructor
  · rintro ⟨hℓu, hur⟩
    have hleft : q + ell ≤ n / p := by linarith [heq]
    have hright : n / p < q + r := by linarith [heq]
    constructor
    · apply (div_lt_iff₀ hqr).2
      simpa [mul_comm] using (div_lt_iff₀ hp).mp hright
    · apply (le_div_iff₀ hqell).2
      simpa [mul_comm] using (le_div_iff₀ hp).mp hleft
  · rintro ⟨hleft, hright⟩
    have hright' : n / p < q + r := by
      apply (div_lt_iff₀ hp).2
      simpa [mul_comm] using (div_lt_iff₀ hqr).mp hleft
    have hleft' : q + ell ≤ n / p := by
      apply (le_div_iff₀ hp).2
      simpa [mul_comm] using (le_div_iff₀ hqell).mp hright
    constructor <;> linarith [heq]

/--
@isnad1 id=eq.0h0v.s3.e0fa66df6605 from=translated src=- shape=3701a056 vocab=e3abbc54
-/
theorem familyI_card : familyI.card = 186 := by
  decide

/--
@isnad1 id=eq.0h0v.s3.5f75b74ecc5f from=translated src=- shape=3701a056 vocab=f558e0b4
-/
theorem familyII_card : familyII.card = 557 := by
  decide

/--
@isnad1 id=eq.0h0v.s3.5aea09a5a2d0 from=translated src=- shape=3701a056 vocab=71b9351b
-/
theorem familyIII_card : familyIII.card = 742 := by
  decide

/--
@isnad1 id=eq.0h0v.s3.bf714d582aa9 from=translated src=- shape=3701a056 vocab=c52a6670
-/
theorem familyIV_card : familyIV.card = 371 := by
  decide

/--
@isnad1 id=eq.0h0v.s3.2bf113622319 from=translated src=- shape=3701a056 vocab=711aa937
-/
theorem familyV_card : familyV.card = 928 := by
  decide

/--
@isnad1 id=eq.0h0v.s3.4b8246835579 from=translated src=- shape=b0ae1d2b vocab=7c091b47
-/
theorem familyI_sum : indexSum familyI = 34596 := by
  decide

/--
@isnad1 id=eq.0h0v.s3.3b9a1122a752 from=translated src=- shape=b0ae1d2b vocab=f29fbf91
-/
theorem familyII_sum : indexSum familyII = 310806 := by
  decide

/--
@isnad1 id=eq.0h0v.s3.bc24c37687d3 from=translated src=- shape=b0ae1d2b vocab=c6a02b71
-/
theorem familyIII_sum : indexSum familyIII = 826588 := by
  decide

/--
@isnad1 id=eq.0h0v.s3.e56338bd9e6d from=translated src=- shape=b0ae1d2b vocab=24497830
-/
theorem familyIV_sum : indexSum familyIV = 551306 := by
  decide

/--
@isnad1 id=eq.0h0v.s3.da6a7f7c9e9e from=translated src=- shape=b0ae1d2b vocab=d2146057
-/
theorem familyV_sum : indexSum familyV = 2585408 := by
  decide

/--
@isnad1 id=eq.0h0v.s4.e1066960c152 from=translated src=- shape=0efb1284 vocab=e2472953
-/
theorem familyILength_value : familyILength = 63333 / 3447830 := by
  norm_num [familyILength, familyI_sum, familyI_card]

/--
@isnad1 id=eq.0h0v.s4.f79e8fa83c6f from=translated src=- shape=0efb1284 vocab=62354686
-/
theorem familyIILength_value : familyIILength = 93 / 6190 := by
  norm_num [familyIILength, familyII_sum]

/--
@isnad1 id=eq.0h0v.s4.673c8de0116a from=translated src=- shape=0efb1284 vocab=b03177e1
-/
theorem familyIIILength_value : familyIIILength = 371 / 9285 := by
  norm_num [familyIIILength, familyIII_sum, familyIII_card]

/--
@isnad1 id=eq.0h0v.s4.0f38a072e519 from=translated src=- shape=0efb1284 vocab=b41563d7
-/
theorem familyIVLength_value : familyIVLength = 137641 / 13797510 := by
  norm_num [familyIVLength, familyIV_sum, familyIV_card]

/--
@isnad1 id=eq.0h0v.s4.82da5ffba5fd from=translated src=- shape=0efb1284 vocab=2ff7b289
-/
theorem familyVLength_value : familyVLength = 215528 / 5171745 := by
  norm_num [familyVLength, familyV_sum, familyV_card]

/--
@isnad1 id=eq.0h0v.s5.19068466efcc from=translated src=- shape=8137b75d vocab=32856deb
-/
theorem all_family_lengths_value :
    familyILength + familyIILength + familyIIILength + familyIVLength + familyVLength =
      1724689 / 13797510 := by
  rw [familyILength_value, familyIILength_value, familyIIILength_value,
    familyIVLength_value, familyVLength_value]
  norm_num

/--
@isnad1 id=lt.0h0v.s4.4a9c9491c571 from=translated src=- shape=f464b020 vocab=77f79d51
-/
theorem firstLeftEndpoint_gt_inv_d0 : firstLeftEndpoint > (1 : ℚ) / d0 := by
  rw [d0_eq]
  norm_num [firstLeftEndpoint]

/--
@isnad1 id=and.0h0v.s5.99484b0eaf7e from=translated src=- shape=ee3a5870 vocab=4809c16d
-/
theorem family_lengths_pos :
    0 < familyILength ∧ 0 < familyIILength ∧ 0 < familyIIILength ∧
      0 < familyIVLength ∧ 0 < familyVLength := by
  rw [familyILength_value, familyIILength_value, familyIIILength_value,
    familyIVLength_value, familyVLength_value]
  norm_num

/--
@isnad1 id=lt.0h0v.s5.8b585ac2bcb6 from=translated src=- shape=4c764b63 vocab=3a2d533e
-/
theorem all_family_lengths_pos : 0 <
    familyILength + familyIILength + familyIIILength + familyIVLength + familyVLength := by
  rw [all_family_lengths_value]
  norm_num

/--
@isnad1 id=eq.0h0v.s5.416a30bd6a57 from=translated src=- shape=72e67e3c vocab=2dc58c7d
-/
theorem five_family_component_count :
    familyI.card + familyII.card + familyIII.card + familyIV.card + familyV.card = 2784 := by
  norm_num [familyI_card, familyII_card, familyIII_card, familyIV_card, familyV_card]

/--
@isnad1 id=eq.0h0v.s3.e579009bea42 from=translated src=- shape=31ef3b0d vocab=444857a9
-/
theorem familyI_first : familyI.min' (by decide) = 1 := by
  decide

end PiIrrationality
