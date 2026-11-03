/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import Tengoku.QuadraticNumberFields.BinaryQuadraticForms.Core.Basic
import Tengoku.Seed.GroupTheory.GroupAction.Defs
import Tengoku.Seed.LinearAlgebra.Matrix.SpecialLinearGroup
import Tengoku.Seed.Tactic.NormNum
import Tengoku.Seed.Tactic.Ring

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Proper Equivalence of Binary Quadratic Forms

This file defines the explicit right `SL₂(ℤ)` coordinate action on binary
quadratic forms, registers it as a left action of `SL₂(ℤ)ᵐᵒᵖ`, and proves the
elementary invariants needed by proper equivalence.
-/

namespace QuadraticNumberFields
namespace BinaryQuadraticForm

open Matrix

/-- The integral special linear group in dimension two.-/
abbrev SL2Z := Matrix.SpecialLinearGroup (Fin 2) ℤ

private abbrev m00 (g : SL2Z) : ℤ := (g : Matrix (Fin 2) (Fin 2) ℤ) 0 0
private abbrev m01 (g : SL2Z) : ℤ := (g : Matrix (Fin 2) (Fin 2) ℤ) 0 1
private abbrev m10 (g : SL2Z) : ℤ := (g : Matrix (Fin 2) (Fin 2) ℤ) 1 0
private abbrev m11 (g : SL2Z) : ℤ := (g : Matrix (Fin 2) (Fin 2) ℤ) 1 1

/-- Coordinate transform of a form by an `SL₂(ℤ)` matrix.-/
def transform (Q : BinaryQuadraticForm) (g : SL2Z) : BinaryQuadraticForm where
  a := Q.a * m00 g ^ 2 + Q.b * m00 g * m10 g + Q.c * m10 g ^ 2
  b := 2 * Q.a * m00 g * m01 g +
    Q.b * (m00 g * m11 g + m01 g * m10 g) +
    2 * Q.c * m10 g * m11 g
  c := Q.a * m01 g ^ 2 + Q.b * m01 g * m11 g + Q.c * m11 g ^ 2

/--
@isnad1 id=eq.0h1v.s5.87e66774037f from=translated src=- shape=bb0110a5 vocab=4314cd75
-/
@[simp] theorem transform_one (Q : BinaryQuadraticForm) :
    transform Q (1 : SL2Z) = Q := by
  cases Q
  ext <;> norm_num [transform, m00, m01, m10, m11]

/-- The coordinate transform is compatible with multiplication in `SL₂(ℤ)`.
@isnad1 id=eq.0h3v.s5.09b7a6137976 from=translated src=- shape=69b0a24e vocab=cb5fb276
-/
theorem transform_mul (Q : BinaryQuadraticForm) (g h : SL2Z) :
    transform (transform Q g) h = transform Q (g * h) := by
  rcases Q with ⟨A, B, C⟩
  ext <;>
    simp [transform, m00, m01, m10, m11, Matrix.mul_apply, Fin.sum_univ_two] <;>
    ring_nf

/-- The right coordinate action as a left action of the opposite group.-/
instance instMulAction : MulAction SL2Zᵐᵒᵖ BinaryQuadraticForm where
  smul g Q := transform Q g.unop
  one_smul Q := by
    change transform Q (MulOpposite.unop 1) = Q
    simp
  mul_smul g h Q := by
    change transform Q ((g * h).unop) = transform (transform Q h.unop) g.unop
    rw [MulOpposite.unop_mul]
    exact (transform_mul Q h.unop g.unop).symm

/--
@isnad1 id=eq.0h2v.s6.998407fa8456 from=translated src=- shape=2c975f13 vocab=385d3ced
-/
@[simp] theorem smul_eq_transform (g : SL2Zᵐᵒᵖ) (Q : BinaryQuadraticForm) :
    g • Q = transform Q g.unop :=
  rfl

/--
@isnad1 id=eq.0h2v.s6.3338072a49d5 from=translated src=- shape=b3f51772 vocab=f82106fd
-/
@[simp] theorem op_smul_eq_transform (g : SL2Z) (Q : BinaryQuadraticForm) :
    (MulOpposite.op g : SL2Zᵐᵒᵖ) • Q = transform Q g :=
  rfl

/-- Proper equivalence: forms lie in the same `SL₂(ℤ)` orbit.-/
def ProperEquivalent (Q R : BinaryQuadraticForm) : Prop :=
  ∃ g : SL2Z, (MulOpposite.op g : SL2Zᵐᵒᵖ) • Q = R

/-- Proper equivalence is the orbit relation for the opposite-group action.
@isnad1 id=iff.0h2v.s5.c79bf9a861f3 from=translated src=- shape=217919de vocab=9e7bd826
-/
theorem properEquivalent_iff_orbitRel {Q R : BinaryQuadraticForm} :
    ProperEquivalent Q R ↔
      (MulAction.orbitRel SL2Zᵐᵒᵖ BinaryQuadraticForm).r R Q := by
  rw [MulAction.orbitRel_apply]
  constructor
  · rintro ⟨g, hg⟩
    exact ⟨MulOpposite.op g, hg⟩
  · rintro ⟨g, hg⟩
    exact ⟨g.unop, hg⟩

/-- Proper equivalence is reflexive.
@isnad1 id=propereq.0h1v.s2.dcccee20551e from=translated src=- shape=b3bac8d8 vocab=470b733f
-/
theorem ProperEquivalent.refl (Q : BinaryQuadraticForm) : ProperEquivalent Q Q := by
  rw [properEquivalent_iff_orbitRel]

/-- Proper equivalence is symmetric.
@isnad1 id=propereq.1h2v.s3.d21bb7790bbc from=translated src=- shape=7e524d71 vocab=470b733f
-/
theorem ProperEquivalent.symm {Q R : BinaryQuadraticForm}
    (hQR : ProperEquivalent Q R) : ProperEquivalent R Q := by
  rw [properEquivalent_iff_orbitRel] at hQR ⊢
  exact (MulAction.orbitRel SL2Zᵐᵒᵖ BinaryQuadraticForm).symm hQR

/-- Proper equivalence is transitive.
@isnad1 id=propereq.2h3v.s4.14b22b9deb43 from=translated src=- shape=0bc0c4a6 vocab=470b733f
-/
theorem ProperEquivalent.trans {Q R S : BinaryQuadraticForm}
    (hQR : ProperEquivalent Q R) (hRS : ProperEquivalent R S) :
    ProperEquivalent Q S := by
  rw [properEquivalent_iff_orbitRel] at hQR hRS ⊢
  exact (MulAction.orbitRel SL2Zᵐᵒᵖ BinaryQuadraticForm).trans hRS hQR

/-- A positive definite form evaluates positively on every nonzero vector.
@isnad1 id=lt.2h3v.s5.35a46002b6ce from=translated src=- shape=411a02c7 vocab=29be22ce
-/
theorem eval_pos_of_isPositiveDefinite (Q : BinaryQuadraticForm)
    (hQ : Q.IsPositiveDefinite) {x y : ℤ} (hxy : x ≠ 0 ∨ y ≠ 0) :
    0 < Q.eval x y := by
  rcases Q with ⟨a, b, c⟩
  rcases hQ with ⟨ha, hdisc⟩
  simp only [disc_mk] at hdisc
  simp only [eval_mk]
  have hcoef : 0 < 4 * a * c - b ^ 2 := by nlinarith
  have hmain : 0 < (2 * a * x + b * y) ^ 2 + (4 * a * c - b ^ 2) * y ^ 2 := by
    by_cases hy : y = 0
    · rcases hxy with hx | hy'
      · have hnonzero : 2 * a * x ≠ 0 :=
          mul_ne_zero (mul_ne_zero (by norm_num) (ne_of_gt ha)) hx
        have hs : 0 < (2 * a * x + b * y) ^ 2 := by
          rw [hy, mul_zero, add_zero]
          exact sq_pos_of_ne_zero hnonzero
        nlinarith
      · contradiction
    · have hy2 : 0 < y ^ 2 := sq_pos_of_ne_zero hy
      nlinarith [sq_nonneg (2 * a * x + b * y)]
  have hident :
      (2 * a * x + b * y) ^ 2 + (4 * a * c - b ^ 2) * y ^ 2 =
        4 * a * (a * x ^ 2 + b * x * y + c * y ^ 2) := by
    ring
  have hprod : 0 < 4 * a * (a * x ^ 2 + b * x * y + c * y ^ 2) := by
    rwa [hident] at hmain
  nlinarith

private theorem disc_transform_aux (a b c p q r s : ℤ) (hdet : p * s - q * r = 1) :
    (2 * a * p * q + b * (p * s + q * r) + 2 * c * r * s) ^ 2 -
        4 * (a * p ^ 2 + b * p * r + c * r ^ 2) *
          (a * q ^ 2 + b * q * s + c * s ^ 2) =
      b ^ 2 - 4 * a * c := by
  calc
    (2 * a * p * q + b * (p * s + q * r) + 2 * c * r * s) ^ 2 -
        4 * (a * p ^ 2 + b * p * r + c * r ^ 2) *
          (a * q ^ 2 + b * q * s + c * s ^ 2)
        = (b ^ 2 - 4 * a * c) * (p * s - q * r) ^ 2 := by ring
    _ = b ^ 2 - 4 * a * c := by
      rw [hdet]
      ring

/-- The `SL₂(ℤ)` coordinate transform preserves discriminants.
@isnad1 id=eq.0h2v.s3.1731104b59f5 from=translated src=- shape=bc45798f vocab=55618362
-/
theorem disc_transform (Q : BinaryQuadraticForm) (g : SL2Z) :
    (transform Q g).disc = Q.disc := by
  let p : ℤ := m00 g
  let q : ℤ := m01 g
  let r : ℤ := m10 g
  let s : ℤ := m11 g
  have hdet : p * s - q * r = 1 := by
    have h := g.2
    rw [Matrix.det_fin_two] at h
    simpa [p, q, r, s, m00, m01, m10, m11] using h
  rcases Q with ⟨A, B, C⟩
  simpa [transform, disc, p, q, r, s] using disc_transform_aux A B C p q r s hdet

/-- Properly equivalent forms have equal discriminants.
@isnad1 id=eq.1h2v.s3.66c0b213d25f from=translated src=- shape=52d409ee vocab=43b5d230
-/
theorem disc_eq_of_properEquivalent {Q R : BinaryQuadraticForm}
    (hQR : ProperEquivalent Q R) : Q.disc = R.disc := by
  rcases hQR with ⟨g, rfl⟩
  exact (disc_transform Q g).symm

/-- The `SL₂(ℤ)` coordinate transform preserves positive definiteness.
@isnad1 id=ispositi.1h2v.s3.ea71d8e43b31 from=translated src=- shape=1b0527e2 vocab=98ea95f8
-/
theorem isPositiveDefinite_transform (Q : BinaryQuadraticForm)
    (hQ : Q.IsPositiveDefinite) (g : SL2Z) : (transform Q g).IsPositiveDefinite := by
  constructor
  · rw [show (transform Q g).a = Q.eval (m00 g) (m10 g) by rfl]
    apply eval_pos_of_isPositiveDefinite Q hQ
    by_contra hzero
    push Not at hzero
    have hdet := g.2
    rw [Matrix.det_fin_two] at hdet
    simp [hzero.1, hzero.2] at hdet
  · simpa [disc_transform] using hQ.2

/-- Proper equivalence preserves positive definiteness.
@isnad1 id=ispositi.2h2v.s3.8dcdff2f2c2e from=translated src=- shape=db379f93 vocab=d6c5d9d3
-/
theorem isPositiveDefinite_of_properEquivalent {Q R : BinaryQuadraticForm}
    (hQ : Q.IsPositiveDefinite) (hQR : ProperEquivalent Q R) : R.IsPositiveDefinite := by
  rcases hQR with ⟨g, rfl⟩
  exact isPositiveDefinite_transform Q hQ g

private theorem dvd_coefficients_of_dvd_transform_coefficients
    (Q : BinaryQuadraticForm) (g : SL2Z) {n : ℕ}
    (ha : (n : ℤ) ∣ (transform Q g).a) (hb : (n : ℤ) ∣ (transform Q g).b)
    (hc : (n : ℤ) ∣ (transform Q g).c) :
    (n : ℤ) ∣ Q.a ∧ (n : ℤ) ∣ Q.b ∧ (n : ℤ) ∣ Q.c := by
  have hback : transform (transform Q g) g⁻¹ = Q := by
    rw [transform_mul, mul_inv_cancel, transform_one]
  constructor
  · rw [← congrArg BinaryQuadraticForm.a hback]
    convert
      dvd_add (dvd_add (dvd_mul_of_dvd_left ha (m00 g⁻¹ ^ 2))
        (dvd_mul_of_dvd_left hb (m00 g⁻¹ * m10 g⁻¹)))
        (dvd_mul_of_dvd_left hc (m10 g⁻¹ ^ 2)) using 1 <;>
      first | rfl | (simp [transform]; ring)
  · constructor
    · rw [← congrArg BinaryQuadraticForm.b hback]
      convert
        dvd_add (dvd_add (dvd_mul_of_dvd_left ha (2 * m00 g⁻¹ * m01 g⁻¹))
          (dvd_mul_of_dvd_left hb (m00 g⁻¹ * m11 g⁻¹ + m01 g⁻¹ * m10 g⁻¹)))
          (dvd_mul_of_dvd_left hc (2 * m10 g⁻¹ * m11 g⁻¹)) using 1 <;>
        first | rfl | (simp [transform]; ring)
    · rw [← congrArg BinaryQuadraticForm.c hback]
      convert
        dvd_add (dvd_add (dvd_mul_of_dvd_left ha (m01 g⁻¹ ^ 2))
          (dvd_mul_of_dvd_left hb (m01 g⁻¹ * m11 g⁻¹)))
          (dvd_mul_of_dvd_left hc (m11 g⁻¹ ^ 2)) using 1 <;>
        first | rfl | (simp [transform]; ring)

/-- The `SL₂(ℤ)` coordinate transform preserves primitivity.
@isnad1 id=isprimit.1h2v.s3.2a4124d366c6 from=translated src=- shape=1b0527e2 vocab=5ee53327
-/
theorem isPrimitive_transform (Q : BinaryQuadraticForm)
    (hQ : Q.IsPrimitive) (g : SL2Z) : (transform Q g).IsPrimitive := by
  unfold IsPrimitive at hQ ⊢
  let P := transform Q g
  let n : ℕ := Int.gcd P.a (Int.gcd P.b P.c)
  have haP : (n : ℤ) ∣ P.a := Int.gcd_dvd_left _ _
  have hbcP : (n : ℤ) ∣ Int.gcd P.b P.c := Int.gcd_dvd_right _ _
  have hbP : (n : ℤ) ∣ P.b := dvd_trans hbcP (Int.gcd_dvd_left _ _)
  have hcP : (n : ℤ) ∣ P.c := dvd_trans hbcP (Int.gcd_dvd_right _ _)
  have hQdvd := dvd_coefficients_of_dvd_transform_coefficients Q g haP hbP hcP
  have hngcd_bc : n ∣ Int.gcd Q.b Q.c := Int.dvd_gcd hQdvd.2.1 hQdvd.2.2
  have hngcd : n ∣ Int.gcd Q.a (Int.gcd Q.b Q.c) :=
    Int.dvd_gcd hQdvd.1 (by exact_mod_cast hngcd_bc)
  rw [hQ] at hngcd
  exact Nat.dvd_one.mp hngcd

/-- Proper equivalence preserves primitivity.
@isnad1 id=isprimit.2h2v.s3.dafb93058513 from=translated src=- shape=db379f93 vocab=16524b5c
-/
theorem isPrimitive_of_properEquivalent {Q R : BinaryQuadraticForm}
    (hQ : Q.IsPrimitive) (hQR : ProperEquivalent Q R) : R.IsPrimitive := by
  rcases hQR with ⟨g, rfl⟩
  exact isPrimitive_transform Q hQ g

end BinaryQuadraticForm
end QuadraticNumberFields
