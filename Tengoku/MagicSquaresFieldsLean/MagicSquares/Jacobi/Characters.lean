import Tengoku.MagicSquaresFieldsLean.MagicSquares.QuadraticCharacter
import Tengoku.Seed.NumberTheory.JacobiSum.Basic
import Tengoku.Seed.RingTheory.RootsOfUnity.Complex
import Tengoku.Seed.GroupTheory.SpecificGroups.Cyclic
import Tengoku.Seed.GroupTheory.OrderOfElement
import Tengoku.Seed.Tactic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace MagicSquares

open scoped BigOperators

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-!
# Quartic characters for the center-zero cubic character sum

For `#F ≡ 1 (mod 4)` we choose a complex multiplicative character `chi4`
of order four.  Its square is the complexification of the quadratic
character.  This is the character-theoretic input for reducing the cubic
sum in Section 6 to two Jacobi sums.
-/

/-- The quadratic character, embedded from `ℤ` into `ℂ`.-/
noncomputable def quadraticCharC
    (F : Type*) [Field F] [Fintype F] [DecidableEq F] :
    MulChar F ℂ :=
  (quadraticChar F).ringHomComp (Int.castRingHom ℂ)

@[simp]
theorem quadraticCharC_apply (x : F) :
    quadraticCharC F x = (quadraticChar F x : ℂ) := by
  simp [quadraticCharC]

theorem quadraticCharC_isQuadratic :
    (quadraticCharC F).IsQuadratic := by
  exact (quadraticChar_isQuadratic F).comp (Int.castRingHom ℂ)

theorem quadraticCharC_sq_eq_one :
    quadraticCharC F ^ 2 = 1 := by
  exact (quadraticCharC_isQuadratic (F := F)).sq_eq_one

theorem quadraticCharC_ne_one
    (hodd : ringChar F ≠ 2) :
    quadraticCharC F ≠ 1 := by
  intro h
  obtain ⟨a, ha⟩ := quadraticChar_exists_neg_one' (F := F) hodd
  have heval :=
    congrArg (fun χ : MulChar F ℂ => χ (a : F)) h
  have hbad : ((-1 : ℤ) : ℂ) = 1 := by
    simpa [quadraticCharC, ha] using heval
  norm_num at hbad

omit [Fintype F] [DecidableEq F] in
/-- A nontrivial complex character whose square is trivial takes value `-1`
on a generator of the unit group.-/
private theorem mulChar_value_eq_neg_one_of_sq_eq_one
    (g : Fˣ)
    (hg : ∀ x : Fˣ, x ∈ Subgroup.zpowers g)
    (θ : MulChar F ℂ)
    (hsq : θ ^ 2 = 1)
    (hne : θ ≠ 1) :
    θ (g : F) = -1 := by
  have hval2 : θ (g : F) ^ 2 = 1 := by
    have h :=
      congrArg (fun ξ : MulChar F ℂ => ξ (g : F)) hsq
    simpa [pow_two] using h
  have hvalne : θ (g : F) ≠ 1 := by
    intro hval
    apply hne
    apply (MulChar.eq_iff hg θ 1).2
    simpa using hval
  have hfac :
      (θ (g : F) - 1) * (θ (g : F) + 1) = 0 := by
    calc
      (θ (g : F) - 1) * (θ (g : F) + 1)
          = θ (g : F) ^ 2 - 1 := by ring
      _ = 0 := by rw [hval2]; ring
  rcases mul_eq_zero.mp hfac with h | h
  · exact False.elim (hvalne (sub_eq_zero.mp h))
  · linear_combination h

omit [DecidableEq F] in
/-- Over a finite field there is at most one nontrivial complex quadratic
multiplicative character.-/
theorem mulChar_eq_of_sq_eq_one_of_ne_one
    (χ ψ : MulChar F ℂ)
    (hχsq : χ ^ 2 = 1)
    (hψsq : ψ ^ 2 = 1)
    (hχne : χ ≠ 1)
    (hψne : ψ ≠ 1) :
    χ = ψ := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Fˣ)
  apply (MulChar.eq_iff hg χ ψ).2
  rw [mulChar_value_eq_neg_one_of_sq_eq_one
        (F := F) g hg χ hχsq hχne,
      mulChar_value_eq_neg_one_of_sq_eq_one
        (F := F) g hg ψ hψsq hψne]

omit [DecidableEq F] in
/-- If `#F ≡ 1 (mod 4)`, there is a complex multiplicative character
of exact order four.-/
theorem exists_quartic_mulChar
    (hqmod : Fintype.card F % 4 = 1) :
    ∃ chi4 : MulChar F ℂ, orderOf chi4 = 4 := by
  have hdiv : 4 ∣ Fintype.card F - 1 := by
    omega
  exact MulChar.exists_mulChar_orderOf
    F hdiv (Complex.isPrimitiveRoot_exp 4 (by norm_num))

omit [Fintype F] [DecidableEq F] in
theorem quartic_ne_one
    {chi4 : MulChar F ℂ}
    (hchi4 : orderOf chi4 = 4) :
    chi4 ≠ 1 := by
  intro h
  have hone : orderOf chi4 = 1 := by
    rw [h]
    simp
  omega

omit [Fintype F] [DecidableEq F] in
theorem quartic_sq_ne_one
    {chi4 : MulChar F ℂ}
    (hchi4 : orderOf chi4 = 4) :
    chi4 ^ 2 ≠ 1 := by
  intro h
  have hdvd : orderOf chi4 ∣ 2 :=
    orderOf_dvd_of_pow_eq_one h
  rw [hchi4] at hdvd
  norm_num at hdvd

omit [Fintype F] [DecidableEq F] in
theorem quartic_cube_ne_one
    {chi4 : MulChar F ℂ}
    (hchi4 : orderOf chi4 = 4) :
    chi4 ^ 3 ≠ 1 := by
  intro h
  have hdvd : orderOf chi4 ∣ 3 :=
    orderOf_dvd_of_pow_eq_one h
  rw [hchi4] at hdvd
  norm_num at hdvd

omit [Fintype F] [DecidableEq F] in
theorem quartic_fourth_eq_one
    {chi4 : MulChar F ℂ}
    (hchi4 : orderOf chi4 = 4) :
    chi4 ^ 4 = 1 := by
  have h := pow_orderOf_eq_one chi4
  simpa [hchi4] using h

/-- The square of any quartic character is the complex quadratic character.-/
theorem quartic_sq_eq_quadraticCharC
    (hodd : ringChar F ≠ 2)
    {chi4 : MulChar F ℂ}
    (hchi4 : orderOf chi4 = 4) :
    chi4 ^ 2 = quadraticCharC F := by
  apply mulChar_eq_of_sq_eq_one_of_ne_one
      (F := F) (chi4 ^ 2) (quadraticCharC F)
  · have h4 := quartic_fourth_eq_one (F := F) hchi4
    calc
      (chi4 ^ 2) ^ 2 = chi4 ^ (2 * 2) := by rw [pow_mul]
      _ = chi4 ^ 4 := by norm_num
      _ = 1 := h4
  · exact quadraticCharC_sq_eq_one (F := F)
  · exact quartic_sq_ne_one (F := F) hchi4
  · exact quadraticCharC_ne_one (F := F) hodd

/-- In the `q ≡ 1 (mod 4)` case the complex quadratic character takes
the value `1` at `-1`.-/
theorem quadraticCharC_neg_one_eq_one_of_card_mod_four_one
    (_hodd : ringChar F ≠ 2)
    (hqmod : Fintype.card F % 4 = 1) :
    quadraticCharC F (-1) = 1 := by
  have hs : IsSquare (-1 : F) := by
    apply (FiniteField.isSquare_neg_one_iff (F := F)).2
    omega
  have hne : (-1 : F) ≠ 0 := neg_ne_zero.mpr one_ne_zero
  have hχ : quadraticChar F (-1) = 1 :=
    (quadraticChar_one_iff_isSquare hne).2 hs
  simp [quadraticCharC, hχ]

end MagicSquares
