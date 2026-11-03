/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Tengoku.Azurite.Azurite.BasuPollackRoy.Chapter2.Section2_1.Cones
import Tengoku.Seed.Tactic.FieldSimp
import Tengoku.Seed.Tactic.LinearCombination

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # BPR Section 2.1 — Lemma 2.9

> Let `C` be a proper cone of `F`. If `−a ∉ C`, then
> `C[a] = { x + a·y | x, y ∈ C}` is a proper cone of `F`.
-/

namespace Azurite.BPR

variable {F : Type*} [Field F]

/-- The extension `C[a]`: the set `{ x + a·y | x, y ∈ C}`.-/
def coneExt (C : Subsemiring F) (hCone : IsCone C) (a : F) : Subsemiring F where
  carrier := { z | ∃ x ∈ C, ∃ y ∈ C, z = x + a * y}
  zero_mem' := ⟨0, C.zero_mem, 0, C.zero_mem, by ring⟩
  one_mem' := ⟨1, C.one_mem, 0, C.zero_mem, by ring⟩
  add_mem' := by
    rintro _ _ ⟨x₁, hx₁, y₁, hy₁, rfl⟩ ⟨x₂, hx₂, y₂, hy₂, rfl⟩
    exact ⟨x₁ + x₂, C.add_mem hx₁ hx₂, y₁ + y₂, C.add_mem hy₁ hy₂, by ring⟩
  mul_mem' := by
    rintro _ _ ⟨x₁, hx₁, y₁, hy₁, rfl⟩ ⟨x₂, hx₂, y₂, hy₂, rfl⟩
    exact ⟨x₁ * x₂ + a ^ 2 * (y₁ * y₂),
           C.add_mem (C.mul_mem hx₁ hx₂) (C.mul_mem (hCone a) (C.mul_mem hy₁ hy₂)),
           x₁ * y₂ + x₂ * y₁, C.add_mem (C.mul_mem hx₁ hy₂) (C.mul_mem hx₂ hy₁), by ring⟩

/-- `C[a]` is a cone (contains all squares).
@isnad1 id=iscone.1h3v.s5.aeb1686a4793 from=translated src=- shape=dacb98ec vocab=d5527395
-/
lemma coneExt_isCone {C : Subsemiring F} (hCone : IsCone C) (a : F) :
    IsCone (coneExt C hCone a) :=
  fun x => ⟨x ^ 2, hCone x, 0, C.zero_mem, by ring⟩

/-- **BPR Lemma 2.9.** If `C` is a proper cone and `−a ∉ C`, then `C[a]` is proper.
@isnad1 id=isproper.2h3v.s6.0c5ac4bd20f5 from=translated src=- shape=bb59a5e9 vocab=b8e9ca50
-/
theorem lemma_2_9 {C : Subsemiring F} (hC : IsProperCone C) (hna : -a ∉ C) :
    IsProperCone (coneExt C hC.1 a) := by
  refine ⟨coneExt_isCone hC.1 a, ?_⟩
  -- Need: -1 ∉ coneExt C a, i.e., ¬∃ x ∈ C, ∃ y ∈ C, -1 = x + a*y
  rintro ⟨x, hx, y, hy, heq⟩
  by_cases hy0 : y = 0
  · rw [hy0, mul_zero, add_zero] at heq; exact hC.2 (heq ▸ hx)
  · apply hna
    have hay : a * y = -1 - x := by linear_combination -heq
    have ha : a = (-1 - x) * y⁻¹ := by rw [← hay]; field_simp
    have : -a = y⁻¹ ^ 2 * (y * (1 + x)) := by rw [ha]; field_simp; ring
    rw [this]
    exact C.mul_mem (hC.1 y⁻¹) (C.mul_mem hy (C.add_mem C.one_mem hx))

end Azurite.BPR
