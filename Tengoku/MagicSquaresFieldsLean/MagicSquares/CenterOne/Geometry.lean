import Tengoku.MagicSquaresFieldsLean.MagicSquares.CenterForms
import Tengoku.Seed.Tactic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace MagicSquares
namespace Square3

variable {R : Type*} [CommRing R]

/-!
# Center-one line: coefficient geometry

For the flexible line `M(1,t,bt)`, every entry has the form

    1 + λ t.

We include the center by assigning it coefficient `0`.  Thus the nine
coefficients are

    1, -(1+b), b, b-1, 0, 1-b, -b, 1+b, -1.

This turns the distinctness part of Sections 7 and 14 into the injectivity
of one nine-element coefficient map.
-/

/-- Coefficient of `t` in each entry of `M(1,t,bt)`, in row-major order.-/
def centerOneCoeff (b : R) : Fin 9 → R :=
  ![1, -(1 + b), b, b - 1, 0, 1 - b, -b, 1 + b, -1]

/-- The nine line coefficients, including the center coefficient `0`,
are pairwise distinct.  Equivalently, the eight non-center coefficients
are nonzero and pairwise distinct.-/
def CenterOneGoodB (b : R) : Prop :=
  Function.Injective (centerOneCoeff b)

/-- Every entry of the center-one line is `1 + λ t` for the corresponding
coefficient `λ`.
@isnad1 id=eq.0h4v.s6.f0835b0581a0 from=translated src=- shape=6f84ec97 vocab=01ed6ede
-/
theorem centerOneLine_entry_formula (t b : R) (k : Fin 9) :
    (centerOneLine t b).entries k = 1 + centerOneCoeff b k * t := by
  fin_cases k <;>
    simp [centerOneCoeff, entries, centerOneLine, centerOne, parametrized] <;>
    ring

/-- The center-one line is automatically magic.
@isnad1 id=ismagic.0h3v.s4.6d236fda5dd0 from=translated src=- shape=ce8ffaa7 vocab=b35a0137
-/
theorem centerOneLine_isMagic (t b : R) :
    (centerOneLine t b).IsMagic := by
  simpa [centerOneLine] using centerOne_isMagic t (b * t)

/-- Once the coefficient map is injective, every nonzero parameter `t`
gives nine distinct entries.
@isnad1 id=pairwise.2h3v.s5.c7a514a76135 from=translated src=- shape=8ac05c46 vocab=86a10c77
-/
theorem centerOneLine_pairwiseDistinct
    [IsDomain R]
    {t b : R}
    (hb : CenterOneGoodB b)
    (ht : t ≠ 0) :
    (centerOneLine t b).PairwiseDistinct := by
  intro i j hij
  rw [centerOneLine_entry_formula, centerOneLine_entry_formula] at hij
  have hmul :
      centerOneCoeff b i * t = centerOneCoeff b j * t := by
    exact add_left_cancel hij
  have hcoeff :
      centerOneCoeff b i = centerOneCoeff b j := by
    exact mul_right_cancel₀ ht hmul
  exact hb hcoeff

/-- A good coefficient parameter has nonzero coefficient at every
non-center position.
@isnad1 id=ne.2h3v.s6.1826b0913eef from=translated src=- shape=6a0c16d0 vocab=726a7035
-/
theorem centerOneCoeff_ne_zero_of_good
    {b : R}
    (hb : CenterOneGoodB b)
    {k : Fin 9}
    (hk : k ≠ 4) :
    centerOneCoeff b k ≠ 0 := by
  intro hz
  have h4 : centerOneCoeff b (4 : Fin 9) = 0 := by
    simp [centerOneCoeff]
  have heq :
      centerOneCoeff b k = centerOneCoeff b (4 : Fin 9) := by
    simpa [h4] using hz
  exact hk (hb heq)

end Square3
end MagicSquares
