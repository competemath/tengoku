import Tengoku.Seed.RingTheory.Henselian
import Tengoku.Seed.RingTheory.LocalRing.ResidueField.Basic
import Tengoku.Seed.SetTheory.Cardinal.Finite
import Tengoku.FltAnthropic.P2M.Sol.S_HenselianLocalRing_exists_pow_card_residueField_sub_one_eq_one_sub_mem_maximalIdeal

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_HenselianLocalRing_exists_pow_card_residueField_sub_one_eq_one_sub_mem_maximalIdeal.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

/--
@isnad1 id=ex.1h2v.s7.863685b64ffb from=translated src=- shape=0dc13783 vocab=55c6d427
-/
theorem HenselianLocalRing.exists_pow_card_residueField_sub_one_eq_one_sub_mem_maximalIdeal
    {A : Type*} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
    [Finite (IsLocalRing.ResidueField A)] {u : A} (hu : IsUnit u) :
    ∃ ω : A, ω ^ (Nat.card (IsLocalRing.ResidueField A) - 1) = 1 ∧
      ω - u ∈ IsLocalRing.maximalIdeal A := by exact @_root_.P2MW.S_HenselianLocalRing_exists_pow_card_residueField_sub_one_eq_one_sub_mem_maximalIdeal.solution A _ _ _ _ u hu
