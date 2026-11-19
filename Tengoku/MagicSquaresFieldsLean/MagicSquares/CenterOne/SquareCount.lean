import Tengoku.MagicSquaresFieldsLean.MagicSquares.Weil.SharpQuadratic
import Tengoku.MagicSquaresFieldsLean.MagicSquares.Weil.AffineQuadratic
import Tengoku.MagicSquaresFieldsLean.MagicSquares.CenterOne.SquareExistence
import Tengoku.MagicSquaresFieldsLean.MagicSquares.CenterZero.Squares
import Tengoku.Seed.Data.Nat.Choose.Sum

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace MagicSquares

open scoped BigOperators

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- Unnormalized indicator for eight affine square conditions. At zeros
this can be fractional after division by `256`, so it is bounded by the
true indicator rather than identified with it.-/
noncomputable def affineSquareWeight (coeff : Fin 8 → F) (t : F) : ℝ :=
  ∏ i, (1 + (quadraticChar F (1 + coeff i * t) : ℝ))

private noncomputable def squareMinorLower (q : ℝ) (error : ℕ → ℝ) (r : ℕ) : ℝ :=
  if r = 0 then q else if r = 1 then 0 else if r = 2 then -1
  else -error r

private theorem square_minor_lower (hodd : ringChar F ≠ 2)
    (error : ℕ → ℝ)
    (coeff : Fin 8 → F) (hinj : Function.Injective coeff)
    (hnonzero : ∀ i, coeff i ≠ 0)
    (hlarge : ∀ s : Finset (Fin 8), 3 ≤ s.card →
      |((∑ t : F, quadraticChar F (∏ i ∈ s, (1 + coeff i * t)) : ℤ) : ℝ)| ≤ error s.card)
    (s : Finset (Fin 8)) :
    squareMinorLower (Fintype.card F) error s.card ≤
      ((∑ t : F, quadraticChar F (∏ i ∈ s, (1 + coeff i * t)) : ℤ) : ℝ) := by
  classical
  by_cases h0 : s.card = 0
  · have hs : s = ∅ := Finset.card_eq_zero.mp h0
    simp [hs, squareMinorLower]
  by_cases h1 : s.card = 1
  · obtain ⟨i, rfl⟩ := Finset.card_eq_one.mp h1
    simp only [Finset.card_singleton, squareMinorLower, Finset.prod_singleton]
    rw [quadraticChar_affine_sum hodd (hnonzero i)]
    norm_num
  by_cases h2 : s.card = 2
  · obtain ⟨i, j, hij, rfl⟩ := Finset.card_eq_two.mp h2
    have hc : coeff i ≠ coeff j := fun h => hij (hinj h)
    simp only [Finset.prod_pair hij, quadraticChar_affine_pair_sum hodd
      (hnonzero i) (hnonzero j) hc, Int.cast_neg]
    rw [show ({i, j} : Finset (Fin 8)).card = 2 by simp [hij]]
    simp only [squareMinorLower, show (2 : ℕ) ≠ 0 by decide,
      show (2 : ℕ) ≠ 1 by decide, ite_false, ite_true]
    have h := (abs_le.mp (quadraticChar_abs_le_one (coeff i * coeff j))).2
    linarith
  · simpa only [squareMinorLower, h0, h1, h2, ite_false] using
      (abs_le.mp (hlarge s (by omega))).1

/-- The subset expansion with an arbitrary bound for the character sums
on three or more factors. Linear sums vanish and pair sums cost at most one.
@isnad1 id=le.4h3v.s8.fd378568c5b6 from=translated src=- shape=62d5adba vocab=c0a52113
-/
theorem affineSquareWeight_sum_lower_with_error
    (hodd : ringChar F ≠ 2) (error : ℕ → ℝ)
    (coeff : Fin 8 → F) (hinj : Function.Injective coeff)
    (hnonzero : ∀ i, coeff i ≠ 0)
    (hlarge : ∀ s : Finset (Fin 8), 3 ≤ s.card →
      |((∑ t : F, quadraticChar F (∏ i ∈ s, (1 + coeff i * t)) : ℤ) : ℝ)| ≤ error s.card) :
    (Fintype.card F : ℝ) - 28 -
      (∑ r ∈ Finset.range 9, if 3 ≤ r then (Nat.choose 8 r : ℝ) * error r else 0) ≤
        ∑ t : F, affineSquareWeight coeff t := by
  classical
  have hexpand : (∑ t : F, affineSquareWeight coeff t) =
      ∑ s ∈ (Finset.univ : Finset (Fin 8)).powerset,
        ((∑ t : F, quadraticChar F (∏ i ∈ s, (1 + coeff i * t)) : ℤ) : ℝ) := by
    conv_lhs => simp only [affineSquareWeight, Finset.prod_one_add]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro s _
    simp only [Int.cast_sum, map_prod, Int.cast_prod]
  rw [hexpand]
  calc
    _ = ∑ s ∈ (Finset.univ : Finset (Fin 8)).powerset,
        squareMinorLower (Fintype.card F) error s.card := by
      rw [Finset.sum_powerset_apply_card]
      norm_num [squareMinorLower, Finset.sum_range_succ, Nat.choose]
      ring
    _ ≤ _ := Finset.sum_le_sum fun s _ =>
      square_minor_lower hodd error coeff hinj hnonzero hlarge s

/-- Expansion of all 256 subsets gives the paper's exact constants:
28 quadratic contributions and 741 in the higher-degree Weil terms.
@isnad1 id=le.4h2v.s7.57547810246b from=translated src=- shape=62b99816 vocab=fc8412c9
-/
theorem affineSquareWeight_sum_lower
    (hodd : ringChar F ≠ 2) (hWeil : HasSplitQuadraticWeilBound F)
    (coeff : Fin 8 → F) (hinj : Function.Injective coeff)
    (hnonzero : ∀ i, coeff i ≠ 0) :
    (Fintype.card F : ℝ) - 28 - 741 * Real.sqrt (Fintype.card F : ℝ) ≤
      ∑ t : F, affineSquareWeight coeff t := by
  have h := affineSquareWeight_sum_lower_with_error hodd
    (fun r => (r - 1 : ℕ) * Real.sqrt (Fintype.card F : ℝ)) coeff hinj hnonzero ?_
  · convert h using 1
    norm_num [Finset.sum_range_succ, Nat.choose]
    ring
  · intro s hs
    have h := hWeil.affine (fun i : s => coeff i)
      (by simpa using (show 0 < s.card by omega))
      (fun i j hij => Subtype.ext (hinj hij)) (fun i => hnonzero i)
    have hprod (t : F) : (∏ i : s, (1 + coeff i * t)) =
        ∏ i ∈ s, (1 + coeff i * t) :=
      Finset.prod_coe_sort s (fun i => 1 + coeff i * t)
    simpa only [Fintype.card_coe, hprod] using h

/-- The product indicator is dominated by the actual square indicator,
including parameters where one or more affine forms vanish.
@isnad1 id=le.0h3v.s8.366de57cac7f from=translated src=- shape=b4119c04 vocab=529baa49
-/
theorem affineSquareWeight_le_indicator (coeff : Fin 8 → F) (t : F) :
    affineSquareWeight coeff t ≤
      if ∀ i, IsSquare (1 + coeff i * t) then (256 : ℝ) else 0 := by
  classical
  by_cases h : ∀ i, IsSquare (1 + coeff i * t)
  · rw [ite_eq_left h]
    calc
      _ ≤ ∏ _i : Fin 8, (2 : ℝ) := by
        apply Finset.prod_le_prod
        · intro i _
          have hl := (abs_le.mp (quadraticChar_abs_le_one (1 + coeff i * t))).1
          linarith
        · intro i _
          have hu := (abs_le.mp (quadraticChar_abs_le_one (1 + coeff i * t))).2
          linarith
      _ = _ := by norm_num
  · rw [ite_eq_right h]
    push Not at h
    obtain ⟨i, hi⟩ := h
    have hchi := quadraticChar_neg_one_iff_not_isSquare.mpr hi
    have hz : affineSquareWeight coeff t = 0 := by
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      simp [hchi]
    exact hz.le

namespace Square3

/-- The eight coefficients obtained by deleting the central position.-/
def centerOneNoncenterCoeff (b : F) (i : Fin 8) : F :=
  centerOneCoeff b ((4 : Fin 9).succAbove i)

omit [DecidableEq F] in
/--
@isnad1 id=iff.0h3v.s6.bab4c6cea325 from=translated src=- shape=0d786b98 vocab=b33ab31f
-/
theorem noncenter_squares_iff_mem (b t : F) :
    (∀ i, IsSquare (1 + centerOneNoncenterCoeff b i * t)) ↔
      t ∈ centerOnePowerParameters 2 b := by
  rw [mem_centerOnePowerParameters]
  constructor
  · intro h k
    rw [isNthPower_two_iff_isSquare]
    by_cases hk : k = 4
    · subst k
      simp [centerOneCoeff]
    · obtain ⟨i, rfl⟩ := Fin.exists_succAbove_eq hk
      exact h i
  · intro h i
    exact (isNthPower_two_iff_isSquare _).mp (h ((4 : Fin 9).succAbove i))

/-- **Section 7 counting estimate from the sharp quadratic Weil bound.**
This proves the previously separate counting interface, including the
optimized constants 28 and 741 and all zero-parameter corrections.
@isnad1 id=hascente.2h1v.s5.bfb2ac911bc6 from=translated src=- shape=79da5d5f vocab=a9c1b8c1
-/
theorem hasCenterOneSquareCountBound_of_weil
    (hodd : ringChar F ≠ 2) (hWeil : HasSplitQuadraticWeilBound F) :
    HasCenterOneSquareCountBound F := by
  classical
  intro b hb
  have hinj : Function.Injective (centerOneNoncenterCoeff b) :=
    hb.comp Fin.succAbove_right_injective
  have hnz (i : Fin 8) : centerOneNoncenterCoeff b i ≠ 0 :=
    centerOneCoeff_ne_zero_of_good hb (Fin.succAbove_ne _ _)
  calc
    _ ≤ ∑ t : F, affineSquareWeight (centerOneNoncenterCoeff b) t :=
      affineSquareWeight_sum_lower hodd hWeil _ hinj hnz
    _ ≤ ∑ t : F, if t ∈ centerOnePowerParameters 2 b then (256 : ℝ) else 0 := by
      apply Finset.sum_le_sum
      intro t _
      simpa only [noncenter_squares_iff_mem] using
        affineSquareWeight_le_indicator (centerOneNoncenterCoeff b) t
    _ = _ := by
      rw [Finset.sum_ite_mem]
      simp [mul_comm]

/-- The square existence theorem now takes only the sharp Weil theorem
as its analytic input; no independent counting assumption is needed.
@isnad1 id=ex.3h1v.s6.664262107213 from=translated src=- shape=cb8d36e0 vocab=66bba117
-/
theorem exists_centerOne_magic_of_squares_of_weil
    (hodd : ringChar F ≠ 2) (hWeil : HasSplitQuadraticWeilBound F)
    (hq : 553736 ≤ Fintype.card F) :
    ∃ M : Square3 F, IsMagicOfPowers 2 M :=
  exists_centerOne_magic_of_squares_of_count_bound hodd
    (hasCenterOneSquareCountBound_of_weil hodd hWeil) hq

end Square3
end MagicSquares

/-!
## Square existence (paper, Section 7)

The counting estimate above now supplies the existence criterion.
-/

namespace MagicSquares.Square3

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

end MagicSquares.Square3
