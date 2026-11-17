import Tengoku.Seed.Algebra.BigOperators.Group.Finset.Basic
import Tengoku.Seed.Algebra.BigOperators.Ring.Finset
import Tengoku.Seed.Data.Int.Order.Lemmas
import Tengoku.Seed.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Translating a short interval to Runge shifts

This file formalizes the elementary change of variables used between the
coding argument in Proposition 3.2 and Lemma 3.1 of Paper C.

Given distinct natural numbers `n i` in `[U, U + R]`, the shifts

`γ i = n i - U`

are distinct integers with `|γ i| ≤ R`, and evaluating the split product
`∏ i, (T + γ i)` at `T = U` recovers `∏ i, n i`.  In particular, a square
product before translation remains a square after translation.
-/

namespace PaperC
namespace RungeTranslation

open scoped BigOperators

variable {ι : Type*}

/-- The integer shift obtained by translating the value `n i` by the base `U`.-/
def translatedShift (U : ℕ) (n : ι → ℕ) (i : ι) : ℤ :=
  (n i : ℤ) - (U : ℤ)

/--
@isnad1 id=eq.0h4v.s5.80cb24feff7f from=translated src=- shape=557c3fdb vocab=192cf879
-/
@[simp]
theorem base_add_translatedShift (U : ℕ) (n : ι → ℕ) (i : ι) :
    (U : ℤ) + translatedShift U n i = n i := by
  simp [translatedShift]

/--
@isnad1 id=le.1h4v.s4.a13a6ebb3d92 from=translated src=- shape=cf0858ce vocab=5c2c864e
-/
theorem translatedShift_nonneg
    {U : ℕ} {n : ι → ℕ} {i : ι} (hU : U ≤ n i) :
    0 ≤ translatedShift U n i := by
  dsimp [translatedShift]
  omega

/--
@isnad1 id=le.1h5v.s5.207429cd6daf from=translated src=- shape=76a63526 vocab=cf66bfdd
-/
theorem translatedShift_le
    {U R : ℕ} {n : ι → ℕ} {i : ι} (hn : n i ≤ U + R) :
    translatedShift U n i ≤ R := by
  dsimp [translatedShift]
  omega

/--
@isnad1 id=le.2h5v.s5.e6eca1707ab7 from=translated src=- shape=3805a123 vocab=a6b9302f
-/
theorem abs_translatedShift_le
    {U R : ℕ} {n : ι → ℕ} {i : ι}
    (hU : U ≤ n i) (hn : n i ≤ U + R) :
    |translatedShift U n i| ≤ R := by
  rw [abs_of_nonneg (translatedShift_nonneg hU)]
  exact translatedShift_le hn

/--
@isnad1 id=injectiv.1h3v.s4.f7dbfde0cd36 from=translated src=- shape=c37d0940 vocab=65ed25e5
-/
theorem translatedShift_injective
    (U : ℕ) {n : ι → ℕ} (hn : Function.Injective n) :
    Function.Injective (translatedShift U n) := by
  intro i j hij
  apply hn
  have hcast : (n i : ℤ) = n j := by
    dsimp [translatedShift] at hij
    omega
  exact_mod_cast hcast

/-- Evaluation of the translated split product at the base point.
@isnad1 id=eq.0h3v.s5.f46a0f4f47f9 from=translated src=- shape=c07ec1a7 vocab=b83710b7
-/
theorem prod_base_add_translatedShift [Fintype ι] (U : ℕ) (n : ι → ℕ) :
    (∏ i, ((U : ℤ) + translatedShift U n i)) =
      ∏ i, (n i : ℤ) := by
  simp [translatedShift]

/-- Casting a finite product of natural numbers to the integers.
@isnad1 id=eq.0h2v.s5.2d81803b7486 from=translated src=- shape=3f297ea1 vocab=ab643504
-/
theorem prod_natCast [Fintype ι] (n : ι → ℕ) :
    ((∏ i, n i : ℕ) : ℤ) = ∏ i, (n i : ℤ) := by
  simp

/--
If the original product is a square in `ℕ`, evaluation of the translated
split product at `U` is a square in `ℤ`.
@isnad1 id=ex.1h3v.s6.ae6ae7fd0808 from=translated src=- shape=2577428d vocab=c815a129
-/
theorem translatedProduct_isSquare
    [Fintype ι]
    (U : ℕ) (n : ι → ℕ)
    (hsquare : ∃ a : ℕ, ∏ i, n i = a ^ 2) :
    ∃ a : ℤ,
      (∏ i, ((U : ℤ) + translatedShift U n i)) = a ^ 2 := by
  obtain ⟨a, ha⟩ := hsquare
  refine ⟨a, ?_⟩
  rw [prod_base_add_translatedShift, ← prod_natCast, ha]
  norm_num

/--
Packaged input conditions for the split-product form of Runge: the shifts are
distinct, bounded by `R`, and their product at `U` is an integer square.
@isnad1 id=and.4h4v.s7.9e9ac077632a from=translated src=- shape=14547548 vocab=d23d5dee
-/
theorem translatedRungeInput
    [Fintype ι]
    {U R : ℕ} {n : ι → ℕ}
    (hinjective : Function.Injective n)
    (hlower : ∀ i, U ≤ n i)
    (hupper : ∀ i, n i ≤ U + R)
    (hsquare : ∃ a : ℕ, ∏ i, n i = a ^ 2) :
    Function.Injective (translatedShift U n) ∧
      (∀ i, |translatedShift U n i| ≤ R) ∧
      ∃ a : ℤ,
        (∏ i, ((U : ℤ) + translatedShift U n i)) = a ^ 2 := by
  refine ⟨translatedShift_injective U hinjective, ?_, translatedProduct_isSquare U n hsquare⟩
  intro i
  exact abs_translatedShift_le (hlower i) (hupper i)

end RungeTranslation
end PaperC
