/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.SandronesLibrary.SandronesLibrary.AbstractAlgebra.RingDivisibility

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Euclidean 环与扩展 Euclidean 算法

本模块以普通数据结构给出度量、商、余数和严格下降公理，并证明递归 gcd、gcd 泛性质与
Bézout 恒等式；公开教材接口不要求 Mathlib 的 `EuclideanDomain` 类型类。

> **Entry**: abstract-algebra.ring.euclidean
-/

namespace SandronesLibrary.AbstractAlgebra.Ring

/-- 一次带余除法的教材陈述。-/
def DivisionWithRemainder {R : Type*} [Zero R] [Add R] [Mul R]
    (measure : R → ℕ) (a b q r : R) : Prop :=
  a = b * q + r ∧ measure r < measure b

/-- Euclidean 环的教材数据与公理，不注册 Mathlib 类型类。-/
structure EuclideanDomainAxioms (R : Type*) [CommRing R] where
  domain : IntegralDomainAxioms R
  measure : R → ℕ
  quotient : R → R → R
  remainder : R → R → R
  divisionWithRemainder : ∀ a b : R, b ≠ 0 →
    DivisionWithRemainder measure a b (quotient a b) (remainder a b)

theorem EuclideanDomainAxioms.division {R : Type*} [CommRing R]
    (E : EuclideanDomainAxioms R) (a b : R) (hb : b ≠ 0) :
    a = b * E.quotient a b + E.remainder a b :=
  (E.divisionWithRemainder a b hb).1

theorem EuclideanDomainAxioms.remainder_lt {R : Type*} [CommRing R]
    (E : EuclideanDomainAxioms R) (a b : R) (hb : b ≠ 0) :
    E.measure (E.remainder a b) < E.measure b :=
  (E.divisionWithRemainder a b hb).2

/-- Euclidean 算法给出的 gcd 候选。-/
noncomputable def euclideanGCD {R : Type*} [CommRing R]
    (E : EuclideanDomainAxioms R) (a b : R) : R := by
  classical
  exact if hb : b = 0 then a else euclideanGCD E b (E.remainder a b)
termination_by E.measure b
decreasing_by exact E.remainder_lt a b hb

@[simp] theorem euclideanGCD_zero {R : Type*} [CommRing R]
    (E : EuclideanDomainAxioms R) (a : R) : euclideanGCD E a 0 = a := by
  rw [euclideanGCD]
  simp

theorem euclideanGCD_nonzero {R : Type*} [CommRing R]
    (E : EuclideanDomainAxioms R) (a b : R) (hb : b ≠ 0) :
    euclideanGCD E a b = euclideanGCD E b (E.remainder a b) := by
  rw [euclideanGCD]
  simp [hb]

/-- 扩展 Euclidean 算法返回 `(g,s,t)`，目标是 `g=s*a+t*b`。-/
noncomputable def extendedEuclidean {R : Type*} [CommRing R]
    (E : EuclideanDomainAxioms R) (a b : R) : R × R × R := by
  classical
  exact if hb : b = 0 then (a, 1, 0)
    else
      let z := extendedEuclidean E b (E.remainder a b)
      (z.1, z.2.2, z.2.1 - E.quotient a b * z.2.2)
termination_by E.measure b
decreasing_by exact E.remainder_lt a b hb

theorem extendedEuclidean_gcd {R : Type*} [CommRing R]
    (E : EuclideanDomainAxioms R) (a b : R) :
    (extendedEuclidean E a b).1 = euclideanGCD E a b := by
  rw [extendedEuclidean, euclideanGCD]
  split
  · rfl
  · dsimp only
    exact extendedEuclidean_gcd E b (E.remainder a b)
termination_by E.measure b
decreasing_by exact E.remainder_lt a b ‹b ≠ 0›

theorem extendedEuclidean_bezout {R : Type*} [CommRing R]
    (E : EuclideanDomainAxioms R) (a b : R) :
    (extendedEuclidean E a b).1 =
      (extendedEuclidean E a b).2.1 * a +
      (extendedEuclidean E a b).2.2 * b := by
  rw [extendedEuclidean]
  split
  · simp
  · dsimp only
    rw [extendedEuclidean_bezout E b (E.remainder a b)]
    have hr : E.remainder a b = a - b * E.quotient a b := by
      have hd := E.division a b ‹b ≠ 0›
      calc
        E.remainder a b =
            (b * E.quotient a b + E.remainder a b) - b * E.quotient a b := by ring
        _ = a - b * E.quotient a b := by rw [← hd]
    rw [hr]
    ring
termination_by E.measure b
decreasing_by exact E.remainder_lt a b ‹b ≠ 0›

theorem euclideanGCD_isGreatestCommonDivisor {R : Type*} [CommRing R]
    (E : EuclideanDomainAxioms R) (a b : R) :
    GreatestCommonDivisor (euclideanGCD E a b) a b := by
  by_cases hb : b = 0
  · subst b
    rw [euclideanGCD_zero]
    refine ⟨dividesElement_refl a, ⟨0, by rw [mul_zero]⟩, ?_⟩
    intro c hca _hc0
    exact hca
  · rw [euclideanGCD_nonzero E a b hb]
    let r := E.remainder a b
    let q := E.quotient a b
    have ih := euclideanGCD_isGreatestCommonDivisor E b r
    refine ⟨?_, ih.1, ?_⟩
    · obtain ⟨x, hbx⟩ := ih.1
      obtain ⟨y, hry⟩ := ih.2.1
      refine ⟨x * q + y, ?_⟩
      have hd := E.division a b hb
      calc
        a = b * q + r := hd
        _ = (euclideanGCD E b r * x) * q +
            euclideanGCD E b r * y := by rw [← hbx, ← hry]
        _ = euclideanGCD E b r * (x * q + y) := by ring
    · intro c hca hcb
      apply ih.2.2 c hcb
      obtain ⟨x, hax⟩ := hca
      obtain ⟨y, hby⟩ := hcb
      refine ⟨x - y * q, ?_⟩
      have hd := E.division a b hb
      calc
        r = a - b * q := by
          calc
            r = (b * q + r) - b * q := by ring
            _ = a - b * q := by rw [← hd]
        _ = c * x - (c * y) * q := by rw [← hax, ← hby]
        _ = c * (x - y * q) := by ring
termination_by E.measure b
decreasing_by exact E.remainder_lt a b ‹b ≠ 0›

theorem euclideanDomain_bezout_for_gcd {R : Type*} [CommRing R]
    (E : EuclideanDomainAxioms R) (a b : R) :
    ∃ s t : R, euclideanGCD E a b = s * a + t * b := by
  refine ⟨(extendedEuclidean E a b).2.1, (extendedEuclidean E a b).2.2, ?_⟩
  rw [← extendedEuclidean_gcd E a b]
  exact extendedEuclidean_bezout E a b

end SandronesLibrary.AbstractAlgebra.Ring
