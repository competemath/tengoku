import Tengoku.MagicSquaresFieldsLean.MagicSquares.NormalizedSearch

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace MagicSquares

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- If the exponent is coprime to `q-1`, every field element is a power.
@isnad1 id=isnthpow.2h3v.s5.8e92d78ee954 from=translated src=- shape=e3c8ed0d vocab=ff1932b8
-/
theorem isNthPower_of_powerIndex_eq_one {n : ℕ} (hn : 0 < n)
    (hd : powerIndex n (Fintype.card F) = 1) (x : F) : IsNthPower n x := by
  rw [isNthPower_iff_zero_or_pow_eq_one hn, hd, Nat.div_one]
  by_cases hx : x = 0
  · exact Or.inl hx
  · exact Or.inr (FiniteField.pow_card_sub_one_eq_one x hx)

/-- With trivial power index, avoiding seven collision parameters suffices.
@isnad1 id=ex.4h2v.s6.606ef607af2a from=translated src=- shape=6c0b142c vocab=638ecd92
-/
theorem exists_magic_of_powers_of_powerIndex_eq_one {n : ℕ} (hn : 0 < n)
    (hodd : ringChar F ≠ 2) (hq : 7 < Fintype.card F)
    (hd : powerIndex n (Fintype.card F) = 1) :
    ∃ M : Square3 F, IsMagicOfPowers n M := by
  have hcard : (centerZeroBadValues : Finset F).card < Fintype.card F :=
    lt_of_le_of_lt centerZeroBadValues_card_le hq
  have hex : ∃ x : F, x ∉ (centerZeroBadValues : Finset F) := by
    by_contra h
    have heq : (centerZeroBadValues : Finset F) = Finset.univ := by
      ext x
      simp only [Finset.mem_univ, iff_true]
      exact Classical.not_not.mp (fun hx => h ⟨x, hx⟩)
    simp [heq] at hcard
  obtain ⟨x, hx⟩ := hex
  refine ⟨Square3.centerZero x, Square3.centerZero_isMagic x,
    centerZero_pairwiseDistinct_of_not_mem_bad hodd hx, ?_⟩
  intro k
  exact isNthPower_of_powerIndex_eq_one hn hd _

end MagicSquares
