/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Tengoku.Azurite.Azurite.BasuPollackRoy.Chapter2.Section2_6.PuiseuxMonomial

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # BPR §2.6 — the constant embedding `R → R⟨⟨ε⟩⟩`

An element `c ∈ R` embeds into the field of Puiseux series as the constant series `single 0 c`
(order `0` when `c ≠ 0`). This is the ring homomorphism `constPuiseux : R →+* R⟨⟨ε⟩⟩` used to
regard the root `x ∈ R` of a characteristic polynomial, and the coefficients of the
characteristic polynomial, as Puiseux series in the substitution `X = ε^ξ(x + Y)` of Lemma 2.95.

We also record the order facts needed there: orders of constants are `≥ 0`, the order of a finite
sum is at least the minimum of the orders (`puiseuxOrder_sum_lt` gives the strict version we use),
and removing the leading term of an order-`0` series strictly raises the order
(`puiseuxOrder_sub_constPuiseux_leadingCoeff_pos`).
-/

namespace Azurite.BPR

open Polynomial HahnSeries

variable {R : Type*} [Field R]

/-- The constant series `single 0 c` is a Puiseux series (a Laurent series in `ε^{1/1}`).
@isnad1 id=mem.0h2v.s8.6f1bfa6fb775 from=translated src=- shape=be02048c vocab=4f35aa97
-/
theorem single_zero_mem (c : R) : (HahnSeries.single (0 : ℚ) c) ∈ PuiseuxSeries R := by
  rw [mem_puiseuxSeries_iff]
  refine ⟨1, ?_⟩
  rw [puiseuxSubfield, RingHom.mem_fieldRange]
  refine ⟨HahnSeries.single (0 : ℤ) c, ?_⟩
  rw [puiseuxEmb_single, show puiseuxExpHom (1 : ℕ+) (0 : ℤ) = (0 : ℚ) from by simp]

/-- **The constant embedding `R → R⟨⟨ε⟩⟩`**, `c ↦ single 0 c`.-/
noncomputable def constPuiseux : R →+* PuiseuxSeries R :=
  (HahnSeries.C).codRestrict (PuiseuxSeries R)
    (fun c => by rw [HahnSeries.C_apply]; exact single_zero_mem c)

/--
@isnad1 id=eq.0h2v.s11.e79ddbe29ed6 from=translated src=- shape=c003bf3d vocab=5eee26ce
-/
@[simp] theorem coe_constPuiseux (c : R) :
    ((constPuiseux c : PuiseuxSeries R) : HahnSeries ℚ R) = HahnSeries.single 0 c :=
  HahnSeries.C_apply c

/-- The initial coefficient of a constant `c` is `c` itself.
@isnad1 id=eq.0h2v.s11.026597d70b51 from=translated src=- shape=8abc04cb vocab=80ea4f3b
-/
@[simp] theorem puiseuxInitCoeff_constPuiseux (c : R) :
    puiseuxInitCoeff R (constPuiseux c) = c := by
  rw [puiseuxInitCoeff, coe_constPuiseux, HahnSeries.leadingCoeff_of_single]

/-- The order of a nonzero constant `c` is `0`.
@isnad1 id=eq.1h2v.s11.b044666a2433 from=translated src=- shape=d35cd2fb vocab=7e651f4d
-/
theorem puiseuxOrder_constPuiseux_of_ne {c : R} (hc : c ≠ 0) :
    puiseuxOrder R (constPuiseux c) = (0 : WithTop ℚ) := by
  rw [puiseuxOrder, coe_constPuiseux, HahnSeries.orderTop_single hc]
  exact WithTop.coe_zero

/-- The order of any constant is `≥ 0`.
@isnad1 id=le.0h2v.s11.133af78ae844 from=translated src=- shape=6e17a503 vocab=0fa83376
-/
theorem puiseuxOrder_constPuiseux_nonneg (c : R) :
    (0 : WithTop ℚ) ≤ puiseuxOrder R (constPuiseux c) := by
  rcases eq_or_ne c 0 with rfl | hc
  · rw [map_zero, puiseuxOrder_zero]; exact le_top
  · rw [puiseuxOrder_constPuiseux_of_ne hc]

/-- The initial coefficient is multiplicative: `In(ā b̄) = In(ā) In(b̄)`.
@isnad1 id=eq.0h3v.s11.3307283da39f from=translated src=- shape=84ac4601 vocab=0ddff052
-/
theorem puiseuxInitCoeff_mul (a b : PuiseuxSeries R) :
    puiseuxInitCoeff R (a * b) = puiseuxInitCoeff R a * puiseuxInitCoeff R b := by
  rw [puiseuxInitCoeff, puiseuxInitCoeff, puiseuxInitCoeff, Subfield.coe_mul,
    HahnSeries.leadingCoeff_mul]

/-- **A finite sum of positive-order series has positive order.**
@isnad1 id=lt.1h4v.s10.509da4e71282 from=translated src=- shape=c0b1d9c1 vocab=1b49b1bd
-/
theorem puiseuxOrder_sum_pos {ι : Type*} (s : Finset ι) (f : ι → PuiseuxSeries R)
    (h : ∀ i ∈ s, 0 < puiseuxOrder R (f i)) :
    0 < puiseuxOrder R (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction with
  | empty => rw [Finset.sum_empty, puiseuxOrder_zero]; exact lt_top_iff_ne_top.mpr (by simp)
  | @insert a t ha ih =>
    rw [Finset.sum_insert ha]
    refine lt_of_lt_of_le ?_ (min_le_puiseuxOrder_add _ _)
    rw [lt_min_iff]
    exact ⟨h a (Finset.mem_insert_self a t),
      ih (fun i hi => h i (Finset.mem_insert_of_mem hi))⟩

/-- **Removing the leading term raises the order.** If `ā` has order `0`, then subtracting its
constant initial part `In(ā)` strictly raises the order: `o(ā − In(ā)) > 0`.
@isnad1 id=lt.1h2v.s11.fda39d07a368 from=translated src=- shape=a39bd675 vocab=52aebd5e
-/
theorem puiseuxOrder_sub_constPuiseux_leadingCoeff_pos {a : PuiseuxSeries R}
    (ha : puiseuxOrder R a = 0) :
    0 < puiseuxOrder R (a - constPuiseux (puiseuxInitCoeff R a)) := by
  have hane : a ≠ 0 := by rintro rfl; rw [puiseuxOrder_zero] at ha; exact absurd ha.symm (by simp)
  have hac : ((a : PuiseuxSeries R) : HahnSeries ℚ R) ≠ 0 := by
    rw [Ne, ZeroMemClass.coe_eq_zero]; exact hane
  have hlc : puiseuxInitCoeff R a ≠ 0 := HahnSeries.leadingCoeff_ne_zero.mpr hac
  have key := HahnSeries.le_orderTop_of_leadingCoeff_eq (g := (0 : ℚ))
    (x := (a : HahnSeries ℚ R)) (y := HahnSeries.single 0 (puiseuxInitCoeff R a))
    (by rw [WithTop.coe_zero]; exact ha)
    (by rw [HahnSeries.orderTop_single hlc])
    (by rw [HahnSeries.leadingCoeff_of_single]; rfl)
  rw [puiseuxOrder, show ((a - constPuiseux (puiseuxInitCoeff R a) : PuiseuxSeries R)
      : HahnSeries ℚ R) = (a : HahnSeries ℚ R) - HahnSeries.single 0 (puiseuxInitCoeff R a) from by
    rw [Subfield.coe_sub, coe_constPuiseux]]
  rwa [WithTop.coe_zero] at key

end Azurite.BPR
