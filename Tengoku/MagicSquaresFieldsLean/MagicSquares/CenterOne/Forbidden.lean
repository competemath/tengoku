import Tengoku.MagicSquaresFieldsLean.MagicSquares.CenterOne.Geometry
import Tengoku.Seed.Tactic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace MagicSquares
namespace Square3

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-!
# Forbidden values of the line parameter b

The paper shows that, in odd characteristic, a zero or collision among

    ±1, ±b, ±(1+b), ±(1-b)

can occur only for

    b ∈ {0, ±1, ±2, ±1/2}.

This file records that seven-element exceptional set.  The converse
(`b` outside it implies `CenterOneGoodB b`) is the next algebraic lemma.
-/

/-- The exceptional `b`-values from Sections 7 and 14.-/
def centerOneForbiddenB : Finset F :=
  {0, 1, -1, 2, -2, (1 : F) / 2, -(1 : F) / 2}

omit [Fintype F] in
/--
@isnad1 id=iff.0h2v.s8.76476b8a38bc from=translated src=- shape=ac7798e5 vocab=44df0eb4
-/
@[simp]
theorem mem_centerOneForbiddenB (b : F) :
    b ∈ (centerOneForbiddenB : Finset F) ↔
      b = 0 ∨ b = 1 ∨ b = -1 ∨ b = 2 ∨ b = -2 ∨
      b = (1 : F) / 2 ∨ b = -(1 : F) / 2 := by
  simp [centerOneForbiddenB, or_assoc, or_comm]

omit [Fintype F] in
/-- There are at most seven forbidden values.
@isnad1 id=le.0h1v.s4.885d4bc074f3 from=translated src=- shape=1e8b59d0 vocab=be164fc9
-/
theorem centerOneForbiddenB_card_le :
    (centerOneForbiddenB : Finset F).card ≤ 7 := by
  classical
  unfold centerOneForbiddenB
  calc
    ({0, 1, -1, 2, -2, (1 : F) / 2, -(1 : F) / 2} : Finset F).card
        ≤ ({1, -1, 2, -2, (1 : F) / 2, -(1 : F) / 2} : Finset F).card + 1 :=
      Finset.card_insert_le _ _
    _ ≤ (({-1, 2, -2, (1 : F) / 2, -(1 : F) / 2} : Finset F).card + 1) + 1 := by
      exact Nat.add_le_add_right (Finset.card_insert_le _ _) 1
    _ ≤ ((({2, -2, (1 : F) / 2, -(1 : F) / 2} : Finset F).card + 1) + 1) + 1 := by
      gcongr
      exact Finset.card_insert_le _ _
    _ ≤ (((({-2, (1 : F) / 2, -(1 : F) / 2} : Finset F).card + 1) + 1) + 1) + 1 := by
      gcongr
      exact Finset.card_insert_le _ _
    _ ≤ ((((({(1 : F) / 2, -(1 : F) / 2} : Finset F).card + 1) + 1) + 1) + 1) + 1 := by
      gcongr
      exact Finset.card_insert_le _ _
    _ ≤ (((((({-(1 : F) / 2} : Finset F).card + 1) + 1) + 1) + 1) + 1) + 1 := by
      gcongr
      exact Finset.card_insert_le _ _
    _ = 7 := by simp

/-- If the field has more than seven elements, some `b` lies outside the
explicit forbidden set.
@isnad1 id=ex.1h1v.s5.a5034fa6427a from=translated src=- shape=ad9587ca vocab=b0fbba19
-/
theorem exists_not_mem_centerOneForbiddenB
    (hq : 7 < Fintype.card F) :
    ∃ b : F, b ∉ (centerOneForbiddenB : Finset F) := by
  by_contra h
  push Not at h
  have hall : (Finset.univ : Finset F) ⊆ centerOneForbiddenB := by
    intro b hb
    exact h b
  have hcard :
      Fintype.card F ≤ (centerOneForbiddenB : Finset F).card := by
    simpa using Finset.card_le_card hall
  have hseven := centerOneForbiddenB_card_le (F := F)
  omega

end Square3
end MagicSquares
