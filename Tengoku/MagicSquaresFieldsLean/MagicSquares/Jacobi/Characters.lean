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

/--
@isnad1 id=eq.0h2v.s6.fad22afbc0d5 from=translated src=- shape=1d1a5f71 vocab=9b9e5e5c
-/
@[simp]
theorem quadraticCharC_apply (x : F) :
    quadraticCharC F x = (quadraticChar F x : ℂ) := by
  simp [quadraticCharC]

/--
@isnad1 id=isquadra.0h1v.s4.cc82e45c7b33 from=translated src=- shape=76f3b442 vocab=f9961993
-/
theorem quadraticCharC_isQuadratic :
    (quadraticCharC F).IsQuadratic := by
  exact (quadraticChar_isQuadratic F).comp (Int.castRingHom ℂ)

/--
@isnad1 id=eq.0h1v.s7.1d97e31ed707 from=translated src=- shape=68b86322 vocab=ecc9f440
-/
theorem quadraticCharC_sq_eq_one :
    quadraticCharC F ^ 2 = 1 := by
  exact (quadraticCharC_isQuadratic (F := F)).sq_eq_one

/--
@isnad1 id=ne.1h1v.s6.d8ab75e63f64 from=translated src=- shape=38e6bc32 vocab=422ccf49
-/
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
multiplicative character.
@isnad1 id=eq.4h3v.s9.27f8b20e2dd6 from=translated src=- shape=679154a3 vocab=ca285d4e
-/
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
of exact order four.
@isnad1 id=ex.1h1v.s7.624eeea85e10 from=translated src=- shape=ef1b18be vocab=1685b6d8
-/
theorem exists_quartic_mulChar
    (hqmod : Fintype.card F % 4 = 1) :
    ∃ chi4 : MulChar F ℂ, orderOf chi4 = 4 := by
  have hdiv : 4 ∣ Fintype.card F - 1 := by
    omega
  exact MulChar.exists_mulChar_orderOf
    F hdiv (Complex.isPrimitiveRoot_exp 4 (by norm_num))

omit [Fintype F] [DecidableEq F] in
/--
@isnad1 id=ne.1h2v.s7.c485a9f24913 from=translated src=- shape=05196bb8 vocab=89d41e0a
-/
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
/--
@isnad1 id=ne.1h2v.s8.bb1d500e86d7 from=translated src=- shape=89a30e83 vocab=e59860ae
-/
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
/--
@isnad1 id=ne.1h2v.s8.085a11bce14d from=translated src=- shape=89a30e83 vocab=e59860ae
-/
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
/--
@isnad1 id=eq.1h2v.s8.e72d361515a3 from=translated src=- shape=06c102d4 vocab=e59860ae
-/
theorem quartic_fourth_eq_one
    {chi4 : MulChar F ℂ}
    (hchi4 : orderOf chi4 = 4) :
    chi4 ^ 4 = 1 := by
  have h := pow_orderOf_eq_one chi4
  simpa [hchi4] using h

/-- The square of any quartic character is the complex quadratic character.
@isnad1 id=eq.2h2v.s8.1117e3229ab1 from=translated src=- shape=530221fc vocab=8de0cc08
-/
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
the value `1` at `-1`.
@isnad1 id=eq.2h1v.s7.49ffae6c0c83 from=translated src=- shape=d80d7912 vocab=7670c971
-/
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
