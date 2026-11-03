/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Tengoku.Seed.LinearAlgebra.BilinearForm.Basic
import Tengoku.Seed.Tactic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Rank-two Gram determinants of a bilinear form

For a module `M` over a commutative ring `R` with a bilinear form `B`, the Gram
determinant of a pair is `B v v * B w w - (B v w)^2`, and the pair is
**hyperbolic** when that determinant is negative -- signature `(1, 1)` for a
rank-two lattice.

## This is stated over an arbitrary ambient form, not over one extension

`Lattice/Mukai/RankTwo.lean` used to own these identities on the single carrier
`ℤ × N × ℤ`, but every one of them is arithmetic of two vectors under a
bilinear form. They are restated here on `(R, M, B)` and the Mukai file
specialises them at `B := Mukai.pairingBilin b`.

The file splits at the point where order is needed, which is also where the
hypotheses stop being purely algebraic:

* `gram`, the change-of-basis identity and `orthWitness` need only a commutative
  ring, and `apply_orthWitness` needs no symmetry either;
* `IsHyperbolicPair` and everything reading a sign need a linear order and a
  strict ordered ring structure.

## What is deliberately not here

`HasSphericalClass` and `HasIsotropicClass` stay with the Mukai lane. They are
phrased in terms of `IsSpherical` and `IsIsotropic`, which are application
vocabulary for `-2` and `0`, and the ledger keeps that vocabulary with the
application.

No geometry is asserted. The correspondence between rank-two data and actual
walls in a space of stability conditions is Bayer--Macrì Theorem 5.7; it needs
moduli of stable objects and is **not** formalised anywhere below.
-/

namespace BilinearForm

section Algebraic
variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
variable (B : M →ₗ[R] M →ₗ[R] R)

/-- The Gram determinant of the pair `(v, w)`: `B v v * B w w - (B v w)^2`.-/
def gram (v w : M) : R := B v v * B w w - B v w ^ 2

/--
@isnad1 id=eq.1h5v.s10.0f3b6190f009 from=translated src=- shape=db456486 vocab=3e32add3
-/
theorem gram_comm (hb : ∀ x y : M, B x y = B y x) (v w : M) :
    gram B v w = gram B w v := by
  simp only [gram, hb w v]; ring

/--
@isnad1 id=eq.0h4v.s7.3de310a635f4 from=translated src=- shape=bc30f642 vocab=f941801d
-/
@[simp] theorem gram_zero_left (w : M) : gram B 0 w = 0 := by simp [gram]
/--
@isnad1 id=eq.0h4v.s7.26bd0508bf46 from=translated src=- shape=71d01814 vocab=f941801d
-/
@[simp] theorem gram_zero_right (v : M) : gram B v 0 = 0 := by simp [gram]

/--
@isnad1 id=eq.1h9v.s11.3cfe3164d2cf from=translated src=- shape=2d64de76 vocab=14552ec7
-/
theorem apply_lincomb (hb : ∀ x y : M, B x y = B y x) (a₁ a₂ a₃ a₄ : R) (v w : M) :
    B (a₁ • v + a₂ • w) (a₃ • v + a₄ • w)
      = a₁ * a₃ * B v v + (a₁ * a₄ + a₂ * a₃) * B v w + a₂ * a₄ * B w w := by
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
    smul_eq_mul, hb w v]
  ring

/--
@isnad1 id=eq.1h7v.s11.5a453e0168ef from=translated src=- shape=28724f35 vocab=5d1e32b3
-/
theorem self_lincomb (hb : ∀ x y : M, B x y = B y x) (a₁ a₂ : R) (v w : M) :
    B (a₁ • v + a₂ • w) (a₁ • v + a₂ • w)
      = a₁ ^ 2 * B v v + 2 * (a₁ * a₂) * B v w + a₂ ^ 2 * B w w := by
  rw [apply_lincomb B hb a₁ a₂ a₁ a₂ v w]; ring

/--
@isnad1 id=eq.1h9v.s10.5bd92bd4c098 from=translated src=- shape=f9fec9ec vocab=32b959bb
-/
theorem gram_lincomb (hb : ∀ x y : M, B x y = B y x) (a₁ a₂ a₃ a₄ : R) (v w : M) :
    gram B (a₁ • v + a₂ • w) (a₃ • v + a₄ • w)
      = (a₁ * a₄ - a₂ * a₃) ^ 2 * gram B v w := by
  simp only [gram, self_lincomb B hb, apply_lincomb B hb]; ring

/-- `B v w • v - B v v • w`, the projection of `w` off `v` cleared of
denominators. Orthogonal to `v` with no symmetry hypothesis.-/
def orthWitness (v w : M) : M := B v w • v - B v v • w

/--
@isnad1 id=eq.0h5v.s9.78b135a29a51 from=translated src=- shape=b3d17fbc vocab=c93fd351
-/
theorem apply_orthWitness (v w : M) : B v (orthWitness B v w) = 0 := by
  simp only [orthWitness, map_sub, map_smul, smul_eq_mul]; ring

/--
@isnad1 id=eq.1h5v.s11.8c3f07f2b31e from=translated src=- shape=7e4803ff vocab=02cc775b
-/
theorem self_orthWitness (hb : ∀ x y : M, B x y = B y x) (v w : M) :
    B (orthWitness B v w) (orthWitness B v w) = B v v * gram B v w := by
  simp only [orthWitness, gram, map_sub, map_smul, LinearMap.sub_apply,
    LinearMap.smul_apply, smul_eq_mul, hb w v]
  ring

/-- The set of `R`-combinations of `v` and `w`.-/
def pairSpan (v w : M) : Set M := {x | ∃ a₁ a₂ : R, x = a₁ • v + a₂ • w}

/--
@isnad1 id=mem.0h4v.s5.b881bb736f84 from=translated src=- shape=1203b004 vocab=25d0e771
-/
theorem mem_pairSpan_left (v w : M) : v ∈ pairSpan (R := R) v w := ⟨1, 0, by simp⟩
/--
@isnad1 id=mem.0h4v.s5.fc9b117df68d from=translated src=- shape=660bc263 vocab=25d0e771
-/
theorem mem_pairSpan_right (v w : M) : w ∈ pairSpan (R := R) v w := ⟨0, 1, by simp⟩

/--
@isnad1 id=mem.0h5v.s7.f03d7f830f45 from=translated src=- shape=81bde37e vocab=3f042950
-/
theorem orthWitness_mem_pairSpan (v w : M) :
    orthWitness B v w ∈ pairSpan (R := R) v w :=
  ⟨B v w, -B v v, by simp [orthWitness, sub_eq_add_neg]⟩

end Algebraic

section Ordered
variable {R M : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]
variable [AddCommGroup M] [Module R M] (B : M →ₗ[R] M →ₗ[R] R)

/-- Negative Gram determinant: the rank-two form spanned by `v` and `w` is
indefinite. For a rank-two lattice this is signature `(1, 1)`.

A numerical condition on two vectors, and **not** a claim that a wall exists in
any space of stability conditions.-/
def IsHyperbolicPair (v w : M) : Prop := gram B v w < 0

/--
@isnad1 id=iff.0h5v.s10.3572e232423c from=translated src=- shape=a4c6e925 vocab=eabb2ffc
-/
theorem isHyperbolicPair_iff (v w : M) :
    IsHyperbolicPair B v w ↔ B v v * B w w < B v w ^ 2 := by
  rw [IsHyperbolicPair, gram]; constructor <;> intro h <;> linarith

/--
@isnad1 id=lt.1h5v.s10.066a4e976618 from=translated src=- shape=2e5e6022 vocab=9d2f33e2
-/
theorem discr_pos_of_isHyperbolicPair {v w : M} (h : IsHyperbolicPair B v w) :
    0 < 4 * (B v w ^ 2 - B v v * B w w) := by
  rw [IsHyperbolicPair, gram] at h; linarith

omit [IsStrictOrderedRing R] in
/--
@isnad1 id=ne.1h5v.s7.29598f0ad756 from=translated src=- shape=42b2f59e vocab=5b47d924
-/
theorem gram_ne_zero_of_isHyperbolicPair {v w : M} (h : IsHyperbolicPair B v w) :
    gram B v w ≠ 0 := ne_of_lt h

omit [IsStrictOrderedRing R] in
/--
@isnad1 id=ne.1h5v.s7.6f603490de74 from=translated src=- shape=68865645 vocab=cc2dd072
-/
theorem ne_zero_left_of_isHyperbolicPair {v w : M} (h : IsHyperbolicPair B v w) :
    v ≠ 0 := by
  rintro rfl; rw [IsHyperbolicPair, gram_zero_left] at h; exact absurd h (lt_irrefl 0)

omit [IsStrictOrderedRing R] in
/--
@isnad1 id=ne.1h5v.s7.85201f8b15c9 from=translated src=- shape=578aeed3 vocab=cc2dd072
-/
theorem ne_zero_right_of_isHyperbolicPair {v w : M} (h : IsHyperbolicPair B v w) :
    w ≠ 0 := by
  rintro rfl; rw [IsHyperbolicPair, gram_zero_right] at h; exact absurd h (lt_irrefl 0)

omit [IsStrictOrderedRing R] in
/--
@isnad1 id=iff.1h5v.s10.f63c06fc0f73 from=translated src=- shape=3e785e57 vocab=6bbe4296
-/
theorem isHyperbolicPair_comm (hb : ∀ x y : M, B x y = B y x) (v w : M) :
    IsHyperbolicPair B v w ↔ IsHyperbolicPair B w v := by
  rw [IsHyperbolicPair, IsHyperbolicPair, gram_comm B hb]

omit [IsStrictOrderedRing R] in
/--
@isnad1 id=ishyperb.3h9v.s10.7a87b142159a from=translated src=- shape=0f0cdaf9 vocab=d2b416a0
-/
theorem isHyperbolicPair_lincomb (hb : ∀ x y : M, B x y = B y x) {a₁ a₂ a₃ a₄ : R}
    (hd : (a₁ * a₄ - a₂ * a₃) ^ 2 = 1) {v w : M} (h : IsHyperbolicPair B v w) :
    IsHyperbolicPair B (a₁ • v + a₂ • w) (a₃ • v + a₄ • w) := by
  rw [IsHyperbolicPair, gram_lincomb B hb, hd, one_mul]; exact h

/--
@isnad1 id=lt.3h5v.s11.294e09b9e6a9 from=translated src=- shape=328453a1 vocab=f3243972
-/
theorem self_orthWitness_neg (hb : ∀ x y : M, B x y = B y x) {v w : M}
    (hv : 0 < B v v) (h : IsHyperbolicPair B v w) :
    B (orthWitness B v w) (orthWitness B v w) < 0 := by
  rw [self_orthWitness B hb]; exact mul_neg_of_pos_of_neg hv h

/--
@isnad1 id=ne.3h5v.s10.da37ee8ba523 from=translated src=- shape=92f8419b vocab=f3243972
-/
theorem orthWitness_ne_zero (hb : ∀ x y : M, B x y = B y x) {v w : M}
    (hv : 0 < B v v) (h : IsHyperbolicPair B v w) : orthWitness B v w ≠ 0 := by
  intro hzero
  have := self_orthWitness_neg B hb hv h
  rw [hzero, map_zero] at this
  simp at this

/--
@isnad1 id=ex.3h5v.s11.5ac6f281b796 from=translated src=- shape=a28cc92b vocab=71b6f3b6
-/
theorem exists_neg_self_of_isHyperbolicPair (hb : ∀ x y : M, B x y = B y x)
    {v w : M} (hv : 0 < B v v) (h : IsHyperbolicPair B v w) :
    ∃ x ∈ pairSpan (R := R) v w, x ≠ 0 ∧ B x x < 0 :=
  ⟨orthWitness B v w, orthWitness_mem_pairSpan B v w,
    orthWitness_ne_zero B hb hv h, self_orthWitness_neg B hb hv h⟩

end Ordered
end BilinearForm
