module

public import Tengoku.Seed.Analysis.SpecialFunctions.Complex.CircleAddChar
public import Tengoku.Seed.NumberTheory.DirichletCharacter.Basic
public import Tengoku.Seed.NumberTheory.GaussSum
public import Tengoku.Seed.NumberTheory.LegendreSymbol.QuadraticChar.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Gauss sums for Dirichlet characters modulo a prime

Thin wrapper around mathlib's `gaussSum` specialised to Dirichlet characters
modulo a prime `p`, using the standard additive character
`ZMod.stdAddChar`.

## Main results

* `KummerCriterion.gaussSum_one_stdAddChar`: the Gauss sum of the trivial
 Dirichlet character modulo a prime `p` with the standard additive character
 equals `-1`.
* `KummerCriterion.gaussSum_mul_gaussSum_inv_stdAddChar`: for a non-trivial
 Dirichlet character `χ` modulo a prime `p`,
 `τ(χ) · τ(χ̄) = χ(-1) · p`.
* `KummerCriterion.DirichletCharacter.isPrimitive_of_prime_of_ne_one`:
 `p` prime, every non-trivial Dirichlet character mod `p` is primitive.
* `KummerCriterion.gaussSum_stdAddChar_mulShift`: the key Galois-equivariance
 identity for the Gauss sum: for nontrivial `χ` mod prime `p` and `a: ZMod p`,
 `gaussSum χ (stdAddChar.mulShift a) = χ⁻¹ a · gaussSum χ stdAddChar`.
* `KummerCriterion.isIntegral_gaussSum_stdAddChar`: the Gauss sum
 `τ(χ) = gaussSum χ ZMod.stdAddChar` is an algebraic integer — integral over `ℤ`
 as an element of `ℂ`.
-/

@[expose] public section

noncomputable section

namespace KummerCriterion

open scoped BigOperators ComplexConjugate

section GaussSum

variable (p : ℕ) [hp : Fact p.Prime]

/-- For a non-trivial Dirichlet character `χ` modulo a prime `p`,
`τ(χ) · τ(χ̄) = χ(-1) · p`, where `τ(χ) = gaussSum χ ZMod.stdAddChar` is
the classical Gauss sum.-/
theorem gaussSum_mul_gaussSum_inv_stdAddChar
    {χ : DirichletCharacter ℂ p} (hχ : χ ≠ 1) :
    gaussSum χ (ZMod.stdAddChar (N := p)) *
        gaussSum χ⁻¹ (ZMod.stdAddChar (N := p)) =
      χ (-1) * p := by
  have hpow : χ ^ (orderOf χ - 1) = χ⁻¹ := by
    refine (inv_eq_of_mul_eq_one_right ?_).symm
    rw [← pow_succ', Nat.sub_one_add_one_eq_of_pos χ.orderOf_pos, pow_orderOf_eq_one]
  rw [← hpow]
  simpa [ZMod.card] using
    gaussSum_mul_gaussSum_pow_orderOf_sub_one hχ (ZMod.isPrimitive_stdAddChar p)

/-- For a prime modulus `p`, any non-trivial Dirichlet character
is primitive. Follows from `χ.conductor ∣ p` and the fact that the only
character factoring through `1` is the trivial character.-/
theorem DirichletCharacter.isPrimitive_of_ne_one
    {χ : DirichletCharacter ℂ p} (hχ : χ ≠ 1) : χ.IsPrimitive := by
  rw [DirichletCharacter.isPrimitive_def]
  rcases (Nat.dvd_prime hp.out).mp χ.conductor_dvd_level with h | h
  · exact absurd ((DirichletCharacter.factorsThrough_one_iff χ).mp
      (h ▸ χ.factorsThrough_conductor)) hχ
  · exact h

/-- The quadratic Dirichlet character modulo `p`, viewed as
`ℂ`-valued so it can be paired with `ZMod.stdAddChar` in Gauss sums.-/
noncomputable def quadraticCharComplex : DirichletCharacter ℂ p :=
  (quadraticChar (ZMod p)).ringHomComp (Int.castRingHom ℂ)

/-- The quadratic character modulo `p`, after base change to
`ℂ`, is still quadratic.-/
theorem quadraticCharComplex_isQuadratic :
    (quadraticCharComplex p).IsQuadratic := by
  simpa [quadraticCharComplex] using
    (quadraticChar_isQuadratic (F := ZMod p)).comp (Int.castRingHom ℂ)

/-- For odd prime `p`, the quadratic character modulo `p` is
nontrivial after base change to `ℂ`.-/
theorem quadraticCharComplex_ne_one (hp₂ : p ≠ 2) :
    quadraticCharComplex p ≠ 1 := by
  simpa [quadraticCharComplex] using
    (MulChar.ringHomComp_ne_one_iff
      (f := Int.castRingHom ℂ) (hf := Int.cast_injective)).2
      (quadraticChar_ne_one (F := ZMod p) ((ZMod.ringChar_zmod_n p).substr hp₂))

/-- The quadratic character modulo `p` is self-inverse after
base change to `ℂ`.-/
theorem quadraticCharComplex_inv :
    (quadraticCharComplex p)⁻¹ = quadraticCharComplex p := by
  simpa using
    (quadraticCharComplex_isQuadratic (p := p)).inv

/-- The quadratic character at `-1` is given by `χ₄(p)`.-/
theorem quadraticCharComplex_eval_neg_one_eq_chi4 (hp₂ : p ≠ 2) :
    quadraticCharComplex p (-1) = ZMod.χ₄ p := by
  rw [quadraticCharComplex, MulChar.ringHomComp_apply,
    quadraticChar_neg_one (F := ZMod p) ((ZMod.ringChar_zmod_n p).substr hp₂), ZMod.card]
  rfl

/-- The value of the quadratic character at `-1` is determined
by `p % 4`.-/
theorem quadraticCharComplex_eval_neg_one (hp₂ : p ≠ 2) :
    quadraticCharComplex p (-1) = if p % 4 = 1 then 1 else -1 := by
  have hp_odd : p % 2 = 1 := by
    rcases hp.out.odd_of_ne_two hp₂ with ⟨k, hk⟩
    omega
  rw [quadraticCharComplex_eval_neg_one_eq_chi4 (p := p) hp₂, ZMod.χ₄_nat_eq_if_mod_four]
  simp [hp_odd]

/-- If `p ≡ 1 (mod 4)`, the quadratic character takes the value
`1` at `-1`.-/
theorem quadraticCharComplex_eval_neg_one_of_mod_four_eq_one (hp₂ : p ≠ 2)
    (hp₄ : p % 4 = 1) :
    quadraticCharComplex p (-1) = 1 := by
  simp [quadraticCharComplex_eval_neg_one (p := p) hp₂, hp₄]

/-- If `p ≡ 3 (mod 4)`, the quadratic character takes the value
`-1` at `-1`.-/
theorem quadraticCharComplex_eval_neg_one_of_mod_four_eq_three (hp₂ : p ≠ 2)
    (hp₄ : p % 4 = 3) :
    quadraticCharComplex p (-1) = -1 := by
  simp [quadraticCharComplex_eval_neg_one (p := p) hp₂, hp₄]

end GaussSum

end KummerCriterion
