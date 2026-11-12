import Tengoku.AbelFormalization.AbelFormalization.RestrictedExpressionTower

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# One denominator for a finite family of rational coordinates

If finitely many values have individual denominator identities, their product
is a common denominator.  The corresponding common numerators are written
without division, by multiplying each individual numerator by all the other
denominators.  This is the algebraic row used when a multivariate polynomial
in exceptional pair-merge jets is cleared at once.
-/

noncomputable section

open scoped BigOperators

namespace AbelFormalization

set_option autoImplicit false

/-- Product of all denominators in a finite indexed family.-/
def finiteCommonDenominator
    {S κ : Type*} [CommMonoid S] [Fintype κ]
    (denominator : κ → S) : S :=
  ∏ i, denominator i

/-- The numerator for coordinate `i` after passing to the product common
denominator.  This definition involves multiplication only.-/
def finiteCommonClearedNumerator
    {S κ : Type*} [CommMonoid S] [Fintype κ] [DecidableEq κ]
    (denominator numerator : κ → S) (i : κ) : S :=
  numerator i * ∏ j ∈ (Finset.univ.erase i), denominator j

/-- The full product factors as one chosen denominator times the product of
all the remaining denominators.
@isnad1 id=eq.0h4v.s5.0aec15cdd5bf from=translated src=- shape=a8514fdb vocab=067a95be
-/
theorem finiteCommonDenominator_eq_mul_prod_erase
    {S κ : Type*} [CommMonoid S] [Fintype κ] [DecidableEq κ]
    (denominator : κ → S) (i : κ) :
    finiteCommonDenominator denominator =
      denominator i * ∏ j ∈ (Finset.univ.erase i), denominator j := by
  classical
  exact (Finset.mul_prod_erase Finset.univ denominator
    (Finset.mem_univ i)).symm

/-- Individual identities `denᵢ * oldᵢ = numᵢ` yield simultaneous identities
for the common product denominator.
@isnad1 id=eq.1h6v.s6.c80ddbceaec3 from=translated src=- shape=5cf8a2e6 vocab=60adce4a
-/
theorem finiteCommonDenominator_mul_eq_clearedNumerator
    {S κ : Type*} [CommMonoid S] [Fintype κ] [DecidableEq κ]
    (denominator numerator old : κ → S)
    (hcoordinate : ∀ i, denominator i * old i = numerator i)
    (i : κ) :
    finiteCommonDenominator denominator * old i =
      finiteCommonClearedNumerator denominator numerator i := by
  classical
  rw [finiteCommonDenominator_eq_mul_prod_erase denominator i,
    finiteCommonClearedNumerator]
  calc
    (denominator i * ∏ j ∈ Finset.univ.erase i, denominator j) * old i =
        (denominator i * old i) *
          ∏ j ∈ Finset.univ.erase i, denominator j := by
            ac_rfl
    _ = numerator i *
          ∏ j ∈ Finset.univ.erase i, denominator j := by
            rw [hcoordinate i]

/-- A finite product of functions in a function subalgebra remains in it.
@isnad1 id=mem.1h4v.s7.c81fe457cea8 from=translated src=- shape=ccea0b08 vocab=6b18d177
-/
theorem finiteCommonDenominator_mem_subalgebra
    {X κ : Type*} [Fintype κ]
    (B : Subalgebra ℝ (X → ℝ)) (denominator : κ → X → ℝ)
    (hdenominator : ∀ i, denominator i ∈ B) :
    finiteCommonDenominator denominator ∈ B := by
  classical
  exact B.prod_mem fun i _ ↦ hdenominator i

/-- Every common cleared numerator remains in the same function subalgebra.
@isnad1 id=mem.2h6v.s8.3eb8552a5ad9 from=translated src=- shape=01f81a64 vocab=10daf40a
-/
theorem finiteCommonClearedNumerator_mem_subalgebra
    {X κ : Type*} [Fintype κ] [DecidableEq κ]
    (B : Subalgebra ℝ (X → ℝ))
    (denominator numerator : κ → X → ℝ)
    (hdenominator : ∀ i, denominator i ∈ B)
    (hnumerator : ∀ i, numerator i ∈ B) (i : κ) :
    finiteCommonClearedNumerator denominator numerator i ∈ B := by
  classical
  exact B.mul_mem (hnumerator i)
    (B.prod_mem fun j _ ↦ hdenominator j)

/-- Positivity of every individual denominator implies positivity of their
common product.
@isnad1 id=lt.1h2v.s5.aace0b0c28a8 from=translated src=- shape=85338bc4 vocab=7a67c107
-/
theorem finiteCommonDenominator_pos
    {κ : Type*} [Fintype κ]
    (denominator : κ → ℝ) (hdenominator : ∀ i, 0 < denominator i) :
    0 < finiteCommonDenominator denominator := by
  classical
  exact Finset.prod_pos fun i _ ↦ hdenominator i

end AbelFormalization
