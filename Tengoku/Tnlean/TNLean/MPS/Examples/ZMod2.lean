/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Tengoku.Seed.Data.ZMod.Basic
import Tengoku.Seed.Algebra.Group.TypeTags.Basic
import Tengoku.Seed.Algebra.Group.TypeTags.Finite
import Tengoku.Seed.Data.Matrix.Mul
import Tengoku.Seed.Data.Complex.Basic
import Tengoku.Seed.LinearAlgebra.Matrix.ConjTranspose

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Z₂ and Z₂ × Z₂ group lemmas for MPS examples

Shared lemmas for MPS examples with `Z₂ = Multiplicative (ZMod 2)` or
`Z₂ × Z₂ = Multiplicative (ZMod 2 × ZMod 2)` symmetry.  These are reused by the
concrete cluster-state and AKLT examples, which both realise a `Z₂ × Z₂`
on-site symmetry by a pair of commuting involutions on the physical space.

## Main definitions

* `ofCommutingInvolutions` : the `Z₂ × Z₂` representation built from two
  commuting involutions `P₁`, `P₂` on a finite-dimensional space.
-/

open scoped Matrix

namespace MPSTensor

/-- Every element of `Multiplicative (ZMod 2)` is either `1` or `ofAdd 1`.
@isnad1 id=or.0h1v.s7.7d19ac92cb2e from=translated src=- shape=503cf106 vocab=646d2c74
-/
lemma zmod2_cases (g : Multiplicative (ZMod 2)) :
    g = 1 ∨ g = Multiplicative.ofAdd 1 := by
  revert g
  decide

/--
@isnad1 id=eq.0h0v.s7.e069b865ea2a from=translated src=- shape=21086a1f vocab=014cf724
-/
lemma zmod2_one_add_one : (1 : ZMod 2) + 1 = 0 := by decide

/-- Every element of `Multiplicative (ZMod 2 × ZMod 2)` is one of the four group
elements `1`, `ofAdd (1, 0)`, `ofAdd (0, 1)`, `ofAdd (1, 1)`.
@isnad1 id=or.0h1v.s10.d700fc9f73fb from=translated src=- shape=af8a545a vocab=3c9ff6c9
-/
lemma zmod2sq_cases (g : Multiplicative (ZMod 2 × ZMod 2)) :
    g = 1 ∨ g = Multiplicative.ofAdd (1, 0) ∨ g = Multiplicative.ofAdd (0, 1) ∨
      g = Multiplicative.ofAdd (1, 1) := by
  revert g
  decide

/-! ### A `Z₂ × Z₂` representation from two commuting involutions

Given two commuting involutions `P₁`, `P₂` on a finite-dimensional space, the
two `ZMod 2` factors act by `P₁` and `P₂`.  Because `P₁² = P₂² = 1` and
`P₁P₂ = P₂P₁`, this assignment is a group homomorphism. -/

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The `Z₂ × Z₂` representation built from two commuting involutions `P₁`, `P₂`:
the first factor acts by `P₁`, the second by `P₂`.  The involution and
commutation hypotheses `h₁ : P₁ * P₁ = 1`, `h₂ : P₂ * P₂ = 1`,
`hc : P₁ * P₂ = P₂ * P₁` make the assignment a group homomorphism.-/
def ofCommutingInvolutions (P₁ P₂ : Matrix n n ℂ) (h₁ : P₁ * P₁ = 1)
    (h₂ : P₂ * P₂ = 1) (hc : P₁ * P₂ = P₂ * P₁) :
    Multiplicative (ZMod 2 × ZMod 2) →* Matrix n n ℂ where
  toFun g :=
    (if (Multiplicative.toAdd g).1 = 0 then 1 else P₁) *
      (if (Multiplicative.toAdd g).2 = 0 then 1 else P₂)
  map_one' := by simp [toAdd_one]
  map_mul' a b := by
    have key : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide
    simp only [toAdd_mul, Prod.fst_add, Prod.snd_add]
    obtain (e1 | e1) := key (Multiplicative.toAdd a).1 <;>
      obtain (e2 | e2) := key (Multiplicative.toAdd a).2 <;>
        obtain (e3 | e3) := key (Multiplicative.toAdd b).1 <;>
          obtain (e4 | e4) := key (Multiplicative.toAdd b).2 <;>
            simp only [e1, e2, e3, e4, show (1 : ZMod 2) + 1 = 0 from by decide, add_zero,
              zero_add, one_ne_zero, ↓reduceIte, mul_one, one_mul]
    -- The eight remaining goals are equations among products of `1`, `P₁`, `P₂`,
    -- each closed using the involution facts `h₁`, `h₂` and commutation `hc`.
    · exact h₂.symm
    · exact hc
    · rw [hc, ← mul_assoc, h₂, one_mul]
    · exact h₁.symm
    · rw [← mul_assoc, h₁, one_mul]
    · rw [mul_assoc, h₂, mul_one]
    · rw [hc, mul_assoc, h₁, mul_one]
    · rw [mul_assoc, ← mul_assoc P₂ P₁ P₂, ← hc, mul_assoc P₁ P₂ P₂, h₂, mul_one, h₁]

/-- `ofCommutingInvolutions` evaluated on a group element is the corresponding
product of factors.
@isnad1 id=eq.3h4v.s10.95fd6465f2ff from=translated src=- shape=a417f63e vocab=98186d46
-/
@[simp]
lemma ofCommutingInvolutions_apply (P₁ P₂ : Matrix n n ℂ) (h₁ : P₁ * P₁ = 1)
    (h₂ : P₂ * P₂ = 1) (hc : P₁ * P₂ = P₂ * P₁) (g : Multiplicative (ZMod 2 × ZMod 2)) :
    ofCommutingInvolutions P₁ P₂ h₁ h₂ hc g =
      (if (Multiplicative.toAdd g).1 = 0 then 1 else P₁) *
        (if (Multiplicative.toAdd g).2 = 0 then 1 else P₂) := rfl

/--
@isnad1 id=eq.3h3v.s9.09eddc9b570b from=translated src=- shape=1b68431f vocab=e457ba50
-/
@[simp]
lemma ofCommutingInvolutions_ofAdd_10 (P₁ P₂ : Matrix n n ℂ) (h₁ : P₁ * P₁ = 1)
    (h₂ : P₂ * P₂ = 1) (hc : P₁ * P₂ = P₂ * P₁) :
    ofCommutingInvolutions P₁ P₂ h₁ h₂ hc (Multiplicative.ofAdd ((1, 0) : ZMod 2 × ZMod 2)) =
      P₁ := by
  simp only [ofCommutingInvolutions_apply, toAdd_ofAdd, show (1 : ZMod 2) ≠ 0 from by decide,
    ↓reduceIte, mul_one]

/--
@isnad1 id=eq.3h3v.s9.4348a8a0f2ae from=translated src=- shape=9b401ca2 vocab=e457ba50
-/
@[simp]
lemma ofCommutingInvolutions_ofAdd_01 (P₁ P₂ : Matrix n n ℂ) (h₁ : P₁ * P₁ = 1)
    (h₂ : P₂ * P₂ = 1) (hc : P₁ * P₂ = P₂ * P₁) :
    ofCommutingInvolutions P₁ P₂ h₁ h₂ hc (Multiplicative.ofAdd ((0, 1) : ZMod 2 × ZMod 2)) =
      P₂ := by
  simp only [ofCommutingInvolutions_apply, toAdd_ofAdd, show (1 : ZMod 2) ≠ 0 from by decide,
    ↓reduceIte, one_mul]

/--
@isnad1 id=eq.3h3v.s9.c6b38bb86cba from=translated src=- shape=a2c5f1c6 vocab=e457ba50
-/
@[simp]
lemma ofCommutingInvolutions_ofAdd_11 (P₁ P₂ : Matrix n n ℂ) (h₁ : P₁ * P₁ = 1)
    (h₂ : P₂ * P₂ = 1) (hc : P₁ * P₂ = P₂ * P₁) :
    ofCommutingInvolutions P₁ P₂ h₁ h₂ hc (Multiplicative.ofAdd ((1, 1) : ZMod 2 × ZMod 2)) =
      P₁ * P₂ := by
  simp only [ofCommutingInvolutions_apply, toAdd_ofAdd, show (1 : ZMod 2) ≠ 0 from by decide,
    ↓reduceIte]

/-- A representation built from two commuting involutions is unitary when both
generators are unitary.
@isnad1 id=eq.5h4v.s10.03dfc61ac6e4 from=translated src=- shape=c66c3c41 vocab=071c02e4
-/
lemma ofCommutingInvolutions_mul_conjTranspose (P₁ P₂ : Matrix n n ℂ)
    (h₁ : P₁ * P₁ = 1) (h₂ : P₂ * P₂ = 1) (hc : P₁ * P₂ = P₂ * P₁)
    (h₁U : P₁ * (P₁)ᴴ = 1) (h₂U : P₂ * (P₂)ᴴ = 1)
    (g : Multiplicative (ZMod 2 × ZMod 2)) :
    ofCommutingInvolutions P₁ P₂ h₁ h₂ hc g *
        (ofCommutingInvolutions P₁ P₂ h₁ h₂ hc g)ᴴ = 1 := by
  rcases zmod2sq_cases g with rfl | rfl | rfl | rfl
  · simp
  · simpa only [ofCommutingInvolutions_ofAdd_10] using h₁U
  · simpa only [ofCommutingInvolutions_ofAdd_01] using h₂U
  · rw [ofCommutingInvolutions_ofAdd_11, Matrix.conjTranspose_mul,
      mul_assoc P₁ P₂ ((P₂)ᴴ * (P₁)ᴴ), ← mul_assoc P₂ (P₂)ᴴ (P₁)ᴴ,
      h₂U, one_mul, h₁U]

/-- Two anticommuting involutions obey the standard `Z₂ × Z₂` projective
multiplication law with factor `(-1)^(g₂ h₁)`.
@isnad1 id=eq.3h5v.s12.408daa02532b from=translated src=- shape=33b271e7 vocab=2ec8d364
-/
lemma mul_of_anticommuting_involutions (P₁ P₂ : Matrix n n ℂ)
    (h₁ : P₁ * P₁ = 1) (h₂ : P₂ * P₂ = 1) (hc : P₂ * P₁ = -(P₁ * P₂))
    (g h : Multiplicative (ZMod 2 × ZMod 2)) :
    ((if (Multiplicative.toAdd g).1 = 0 then 1 else P₁) *
          (if (Multiplicative.toAdd g).2 = 0 then 1 else P₂)) *
        ((if (Multiplicative.toAdd h).1 = 0 then 1 else P₁) *
          (if (Multiplicative.toAdd h).2 = 0 then 1 else P₂)) =
      (if (Multiplicative.toAdd g).2 = 1 ∧ (Multiplicative.toAdd h).1 = 1
        then (-1 : ℂ) else 1) •
        ((if (Multiplicative.toAdd (g * h)).1 = 0 then 1 else P₁) *
          (if (Multiplicative.toAdd (g * h)).2 = 0 then 1 else P₂)) := by
  rcases zmod2sq_cases g with rfl | rfl | rfl | rfl <;>
    rcases zmod2sq_cases h with rfl | rfl | rfl | rfl <;>
    simp only [← ofAdd_add, Prod.mk_add_mk, toAdd_ofAdd, toAdd_one,
      Prod.fst_zero, Prod.snd_zero,
      show (1 : ZMod 2) + 1 = 0 from by decide,
      show (0 : ZMod 2) + 1 = 1 from by decide,
      show (1 : ZMod 2) + 0 = 1 from by decide,
      show (0 : ZMod 2) + 0 = 0 from by decide,
      one_ne_zero, zero_ne_one, ↓reduceIte, and_self, and_true, true_and,
      mul_one, one_mul, one_smul, neg_one_smul] <;>
    first
    | exact h₁
    | exact h₂
    | exact hc
    | rw [← mul_assoc, h₁, one_mul]
    | rw [mul_assoc, h₂, mul_one]
    | rw [hc, ← mul_assoc, h₁, one_mul]
    | rw [← mul_assoc, hc, neg_mul, mul_assoc, h₂, mul_one]
    | rw [mul_assoc, hc, mul_neg, ← mul_assoc, h₁, one_mul]
    | rw [mul_neg, h₁]
    | rw [← mul_assoc, hc, neg_mul, mul_assoc, h₂, mul_one]
    | rw [mul_assoc, hc, mul_neg, ← mul_assoc, h₁, one_mul]
    | rw [mul_assoc, hc, mul_neg, ← mul_assoc, h₁, one_mul]
    | rw [mul_assoc, ← mul_assoc P₂ P₁ P₂, hc, neg_mul, mul_assoc P₁ P₂ P₂,
        h₂, mul_one, mul_neg, h₁]

/-- An anticommuting negative involution and involution obey the
`Z₂ × Z₂` projective multiplication law with factor
`(-1)^((g₁ + g₂) h₁)`.
@isnad1 id=eq.3h5v.s12.2dee4b8945c0 from=translated src=- shape=ece884c1 vocab=d7a2057e
-/
lemma mul_of_anticommuting_neg_involution (P₁ P₂ : Matrix n n ℂ)
    (h₁ : P₁ * P₁ = -1) (h₂ : P₂ * P₂ = 1) (hc : P₂ * P₁ = -(P₁ * P₂))
    (g h : Multiplicative (ZMod 2 × ZMod 2)) :
    ((if (Multiplicative.toAdd g).1 = 0 then 1 else P₁) *
          (if (Multiplicative.toAdd g).2 = 0 then 1 else P₂)) *
        ((if (Multiplicative.toAdd h).1 = 0 then 1 else P₁) *
          (if (Multiplicative.toAdd h).2 = 0 then 1 else P₂)) =
      (if (Multiplicative.toAdd g).1 + (Multiplicative.toAdd g).2 = 1 ∧
          (Multiplicative.toAdd h).1 = 1 then (-1 : ℂ) else 1) •
        ((if (Multiplicative.toAdd (g * h)).1 = 0 then 1 else P₁) *
          (if (Multiplicative.toAdd (g * h)).2 = 0 then 1 else P₂)) := by
  rcases zmod2sq_cases g with rfl | rfl | rfl | rfl <;>
    rcases zmod2sq_cases h with rfl | rfl | rfl | rfl <;>
    simp only [← ofAdd_add, Prod.mk_add_mk, toAdd_ofAdd, toAdd_one,
      Prod.fst_zero, Prod.snd_zero,
      show (1 : ZMod 2) + 1 = 0 from by decide,
      show (0 : ZMod 2) + 1 = 1 from by decide,
      show (1 : ZMod 2) + 0 = 1 from by decide,
      show (0 : ZMod 2) + 0 = 0 from by decide,
      one_ne_zero, zero_ne_one, ↓reduceIte, and_self, and_true, true_and,
      mul_one, one_mul, one_smul, neg_one_smul] <;>
    first
    | exact h₁
    | exact h₂
    | exact hc
    | rw [← mul_assoc, h₁, one_mul]
    | rw [mul_assoc, h₂, mul_one]
    | rw [hc, ← mul_assoc, h₁, one_mul]
    | rw [← mul_assoc, hc, neg_mul, mul_assoc, h₂, mul_one]
    | rw [mul_assoc, hc, mul_neg, ← mul_assoc, h₁, one_mul]
    | rw [mul_neg, h₁, neg_neg]
    | rw [← mul_assoc, hc, neg_mul, mul_assoc, h₂, mul_one]
    | rw [mul_assoc, hc, mul_neg, ← mul_assoc, h₁, one_mul]
    | rw [mul_assoc, hc, mul_neg, ← mul_assoc, h₁, one_mul]
    | rw [← mul_assoc, h₁, neg_mul, one_mul]
    | rw [hc, mul_neg, ← mul_assoc, h₁, neg_mul, one_mul, neg_neg]
    | rw [mul_assoc, hc, mul_neg, ← mul_assoc, h₁, neg_mul, one_mul, neg_neg]
    | rw [mul_assoc, ← mul_assoc P₂ P₁ P₂, hc, neg_mul, mul_assoc P₁ P₂ P₂,
        h₂, mul_one, mul_neg, h₁]
  all_goals simp

end MPSTensor
