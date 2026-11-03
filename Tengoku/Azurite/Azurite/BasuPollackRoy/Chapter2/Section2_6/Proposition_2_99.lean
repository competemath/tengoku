/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Tengoku.Azurite.Azurite.BasuPollackRoy.Chapter2.Section2_6.AlgebraicPuiseux
import Tengoku.Azurite.Azurite.BasuPollackRoy.Chapter2.Section2_6.Infinitesimal
import Tengoku.Azurite.Azurite.BasuPollackRoy.Chapter2.Section2_6.ConstPuiseux
import Tengoku.Azurite.Azurite.BasuPollackRoy.Chapter2.Section2_6.ValuationRing
import Tengoku.Seed.RingTheory.Valuation.ValuationSubring

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # BPR §2.6 Proposition 2.99 — the valuation ring `K⟨ε⟩_b`

* **Part 1.** The elements of `K⟨ε⟩` (algebraic Puiseux series) with non-negative order constitute a
  valuation ring `K⟨ε⟩_b` (`puiseuxBounded`). The order `o` is an additive valuation, so the
  non-negative-order elements form a subring; and for nonzero `x`, `o(x) + o(x⁻¹) = 0`, so one of
  `o(x)`, `o(x⁻¹)` is non-negative — the valuation-ring condition.

* **Part 2.** For `R` real closed, the elements of `R⟨ε⟩_b` are exactly the elements of `R⟨ε⟩`
  *bounded over `R`* (absolute value less than a positive element of `R`): this is the analytic core
  `bounded_iff_puiseuxOrder_nonneg`, comparing `|x|` with `ι(a)` through their leading terms. A
  negative-order series dominates every `ι(a)` (unbounded); a positive-order one is infinitesimal;
  and an order-`0` series differs from its constant leading term by an infinitesimal.

Part 3 (the complex modulus version, for `C = R[i]`) is in `Proposition_2_99_Complex`. -/

namespace Azurite.BPR

open Polynomial

/-! ## Order arithmetic helpers (any field of coefficients) -/

variable {K : Type*} [Field K]

theorem puiseuxOrder_one : puiseuxOrder K (1 : PuiseuxSeries K) = 0 := by
  show HahnSeries.orderTop ((1 : PuiseuxSeries K) : HahnSeries ℚ K) = 0
  rw [OneMemClass.coe_one]; exact HahnSeries.orderTop_one

theorem puiseuxOrder_neg (a : PuiseuxSeries K) : puiseuxOrder K (-a) = puiseuxOrder K a := by
  show HahnSeries.orderTop ((-a : PuiseuxSeries K) : HahnSeries ℚ K) = HahnSeries.orderTop _
  rw [NegMemClass.coe_neg, HahnSeries.orderTop_neg]

theorem puiseuxOrder_ne_top {x : PuiseuxSeries K} (hx : x ≠ 0) : puiseuxOrder K x ≠ ⊤ := by
  rw [puiseuxOrder, Ne, HahnSeries.orderTop_eq_top]; simpa using hx

/-! ## Part 1 — the valuation ring `K⟨ε⟩_b` -/

/-- **Proposition 2.99 (part 1).** `K⟨ε⟩_b`: the elements of `K⟨ε⟩ = algebraicPuiseux K` with
non-negative order form a valuation subring of `K⟨ε⟩`.-/
noncomputable def puiseuxBounded (K : Type*) [Field K] : ValuationSubring (algebraicPuiseux K) where
  carrier := {y | 0 ≤ puiseuxOrder K (y : PuiseuxSeries K)}
  one_mem' := by
    show 0 ≤ puiseuxOrder K ((1 : algebraicPuiseux K) : PuiseuxSeries K)
    rw [OneMemClass.coe_one, puiseuxOrder_one]
  mul_mem' := by
    intro a b ha hb
    show 0 ≤ puiseuxOrder K ((a * b : algebraicPuiseux K) : PuiseuxSeries K)
    rw [Subfield.coe_mul, puiseuxOrder_mul]; exact add_nonneg ha hb
  zero_mem' := by
    show 0 ≤ puiseuxOrder K ((0 : algebraicPuiseux K) : PuiseuxSeries K)
    rw [ZeroMemClass.coe_zero, puiseuxOrder_zero]; exact le_top
  add_mem' := by
    intro a b ha hb
    show 0 ≤ puiseuxOrder K ((a + b : algebraicPuiseux K) : PuiseuxSeries K)
    rw [Subfield.coe_add]; exact le_trans (le_min ha hb) (min_le_puiseuxOrder_add _ _)
  neg_mem' := by
    intro a ha
    show 0 ≤ puiseuxOrder K ((-a : algebraicPuiseux K) : PuiseuxSeries K)
    rw [NegMemClass.coe_neg, puiseuxOrder_neg]; exact ha
  mem_or_inv_mem' := by
    intro y
    simp only [Set.mem_ofPred_eq]
    rcases eq_or_ne y 0 with rfl | hy
    · left
      rw [ZeroMemClass.coe_zero, puiseuxOrder_zero]; exact le_top
    · have hcoe : (y : PuiseuxSeries K) ≠ 0 := by simpa using hy
      have hcoeinv : ((y⁻¹ : algebraicPuiseux K) : PuiseuxSeries K) ≠ 0 := by
        simpa using inv_ne_zero hy
      have hsum : puiseuxOrder K (y : PuiseuxSeries K)
          + puiseuxOrder K ((y⁻¹ : algebraicPuiseux K) : PuiseuxSeries K) = 0 := by
        rw [← puiseuxOrder_mul, ← Subfield.coe_mul, mul_inv_cancel₀ hy, OneMemClass.coe_one,
          puiseuxOrder_one]
      lift puiseuxOrder K (y : PuiseuxSeries K) to ℚ using puiseuxOrder_ne_top hcoe with p
      lift puiseuxOrder K ((y⁻¹ : algebraicPuiseux K) : PuiseuxSeries K) to ℚ using
        puiseuxOrder_ne_top hcoeinv with q
      rw [← WithTop.coe_add, ← WithTop.coe_zero, WithTop.coe_eq_coe] at hsum
      rw [WithTop.coe_nonneg, WithTop.coe_nonneg]
      by_cases hp : 0 ≤ p
      · exact Or.inl hp
      · right; linarith

/-- Membership in `K⟨ε⟩_b` is exactly non-negative order.-/
@[simp] theorem mem_puiseuxBounded {y : algebraicPuiseux K} :
    y ∈ puiseuxBounded K ↔ 0 ≤ puiseuxOrder K (y : PuiseuxSeries K) := Iff.rfl

/-! ## Part 2 — `R⟨ε⟩_b` is the ring of elements bounded over `R` -/

section Ordered

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]

end Ordered

end Azurite.BPR
