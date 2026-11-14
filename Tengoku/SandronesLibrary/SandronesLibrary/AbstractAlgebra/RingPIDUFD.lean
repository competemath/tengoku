/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.SandronesLibrary.SandronesLibrary.AbstractAlgebra.RingEuclidean
import Tengoku.Seed.RingTheory.PrincipalIdealDomain

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/FurinaManifold/sandrones-library@6bce6404b264, `SandronesLibrary/AbstractAlgebra/RingPIDUFD.lean`: removed 1 `#adaptation_note` / `set_option linter` line(s) (notes and linter settings: no declaration depends on them). What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

/-!
# 主理想整环与唯一分解整环

本模块自建主理想和原子分解教材公理，证明 Euclidean 环推出 PID、PID 推出 UFD。
Mathlib 主理想环与唯一分解结构只在后一个证明体中作为局部实现后端。

> **Entry**: abstract-algebra.ring.pid-ufd
-/

namespace SandronesLibrary.AbstractAlgebra.Ring


/-- 集合理想由单个元素生成：成员恰为该元素的倍数。-/
def PrincipalIdealSet {R : Type*} [Mul R] (I : Set R) : Prop :=
  ∃ a : R, ∀ x : R, x ∈ I ↔ DividesElement a x

/-- 主理想整环的教材公理。-/
structure PrincipalIdealDomainAxioms (R : Type*) [CommRing R] : Prop where
  domain : IntegralDomainAxioms R
  principal : ∀ I : Set R, TwoSidedIdealSet I → PrincipalIdealSet I

/-- 原子分解存在性：每个非零非单位元都是有限个不可约元乘积再乘一个单位。-/
def AtomicFactorizationAxiom (R : Type*) [CommRing R] : Prop :=
  ∀ a : R, a ≠ 0 → ¬ UnitElement a →
    ∃ u : R, UnitElement u ∧ ∃ factors : Multiset R,
      (∀ p ∈ factors, IrreducibleElement p) ∧ a = u * factors.prod

/-- UFD 的教材公理：整环、原子分解存在，且不可约元均为素元。-/
structure UniqueFactorizationDomainAxioms (R : Type*) [CommRing R] : Prop where
  domain : IntegralDomainAxioms R
  atomic : AtomicFactorizationAxiom R
  irreducible_prime : ∀ p : R, IrreducibleElement p → PrimeElement p

theorem zeroIdeal_principal {R : Type*} [CommRing R] :
    PrincipalIdealSet ({0} : Set R) := by
  refine ⟨0, ?_⟩
  intro x
  constructor
  · intro hx
    change x = 0 at hx
    subst x
    exact ⟨0, (mul_zero 0).symm⟩
  · rintro ⟨c, hc⟩
    change x = 0
    rw [hc, zero_mul]

theorem euclideanDomain_implies_principalIdealDomain
    {R : Type*} [CommRing R] (E : EuclideanDomainAxioms R) :
    PrincipalIdealDomainAxioms R := by
  refine ⟨E.domain, ?_⟩
  intro I hI
  by_cases hzero : ∀ x : R, x ∈ I → x = 0
  · have hEq : I = ({0} : Set R) := by
      ext x
      constructor
      · intro hx; exact hzero x hx
      · intro hx
        change x = 0 at hx
        subst x
        exact hI.1.1
    rw [hEq]
    exact zeroIdeal_principal
  · push Not at hzero
    obtain ⟨a, haI, ha0⟩ := hzero
    let measures : Set ℕ := {n | ∃ x : R, x ∈ I ∧ x ≠ 0 ∧ E.measure x = n}
    have hmeasures : measures.Nonempty := ⟨E.measure a, a, haI, ha0, rfl⟩
    let n := sInf measures
    have hnmem : n ∈ measures := Nat.sInf_mem hmeasures
    obtain ⟨d, hdI, hd0, hdmeasure⟩ := hnmem
    refine ⟨d, ?_⟩
    intro x
    constructor
    · intro hxI
      let q := E.quotient x d
      let r := E.remainder x d
      have hrI : r ∈ I := by
        have hxsub : x - d * q ∈ I := by
          have hdq : d * q ∈ I := by
            simpa [mul_comm] using hI.1.2.2.2 q hdI
          simpa [sub_eq_add_neg] using hI.1.2.1 hxI (hI.1.2.2.1 hdq)
        have hdiv := E.division x d hd0
        have hr : r = x - d * q := by
          calc
            r = (d * q + r) - d * q := by ring
            _ = x - d * q := by rw [← hdiv]
        rw [hr]
        exact hxsub
      have hr0 : r = 0 := by
        by_contra hr0
        have hrmem : E.measure r ∈ measures := ⟨r, hrI, hr0, rfl⟩
        have hmin : n ≤ E.measure r := Nat.sInf_le hrmem
        have hlt : E.measure r < n := by simpa [n, hdmeasure] using E.remainder_lt x d hd0
        exact (Nat.not_lt_of_ge hmin) hlt
      exact ⟨q, by
        have hdiv := E.division x d hd0
        simpa [q, r, hr0] using hdiv⟩
    · rintro ⟨q, rfl⟩
      simpa [mul_comm] using hI.1.2.2.2 q hdI

theorem principalIdealDomain_implies_uniqueFactorizationDomain
    {R : Type*} [CommRing R] (P : PrincipalIdealDomainAxioms R) :
    UniqueFactorizationDomainAxioms R := by
  letI : IsDomain R := (integralDomainAxioms_iff_isDomain (R := R)).mp P.domain
  letI : IsPrincipalIdealRing R := by
    constructor
    intro I
    have hI : TwoSidedIdealSet (I : Set R) := by
      constructor
      · refine ⟨I.zero_mem, ?_, ?_, ?_⟩
        · intro x y hx hy; exact I.add_mem hx hy
        · intro x hx; exact I.neg_mem hx
        · intro r x hx; exact I.mul_mem_left r hx
      · refine ⟨I.zero_mem, ?_, ?_, ?_⟩
        · intro x y hx hy; exact I.add_mem hx hy
        · intro x hx; exact I.neg_mem hx
        · intro r x hx; exact I.mul_mem_right r hx
    obtain ⟨a, ha⟩ := P.principal I hI
    constructor
    refine ⟨a, ?_⟩
    ext x
    change x ∈ (I : Set R) ↔ _
    rw [ha x]
    change DividesElement a x ↔ x ∈ Ideal.span ({a} : Set R)
    rw [dividesElement_iff_dvd, Ideal.mem_span_singleton]
  letI : UniqueFactorizationMonoid R :=
    PrincipalIdealRing.to_uniqueFactorizationMonoid
  refine ⟨P.domain, ?_, ?_⟩
  · intro a ha0 _haunit
    obtain ⟨f, hfIrr, hfAssoc⟩ := WfDvdMonoid.exists_factors a ha0
    obtain ⟨u, hu⟩ := hfAssoc
    refine ⟨(u : R), (unitElement_iff_isUnit (u : R)).mpr u.isUnit, f, ?_, ?_⟩
    · intro p hp
      exact (irreducibleElement_iff_irreducible P.domain).mpr (hfIrr p hp)
    · simpa [mul_comm] using hu.symm
  · intro p hp
    exact (primeElement_iff_prime).mpr
      ((irreducibleElement_iff_irreducible P.domain).mp hp).prime

theorem euclideanDomain_implies_uniqueFactorizationDomain
    {R : Type*} [CommRing R] (E : EuclideanDomainAxioms R) :
    UniqueFactorizationDomainAxioms R := by
  exact principalIdealDomain_implies_uniqueFactorizationDomain
    (euclideanDomain_implies_principalIdealDomain E)

end SandronesLibrary.AbstractAlgebra.Ring
