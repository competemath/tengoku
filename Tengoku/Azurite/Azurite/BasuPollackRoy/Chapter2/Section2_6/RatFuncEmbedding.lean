/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Tengoku.Azurite.Azurite.BasuPollackRoy.Chapter2.Section2_6.PuiseuxSeries
import Tengoku.Azurite.Azurite.BasuPollackRoy.Chapter2.Section2_1.OrderZeroPlus

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # BPR §2.6 — `K(ε)` with the `0₊` order embeds in `K⟨⟨ε⟩⟩`

The field of rational functions `K(ε) = RatFunc K`, equipped with the `0₊` order
(`Azurite.BPR.ZeroPlus`, BPR Notation 2.5), is an ordered subfield of the field of Puiseux
series `K⟨⟨ε⟩⟩`, via the Laurent expansion about `0`.

The key fact is that the `0₊` order matches the Laurent/Puiseux order: a rational function is
positive in `0₊` exactly when the initial (lowest-order) coefficient of its Laurent expansion
is positive. We establish this by computing the leading coefficient of the Laurent series of a
polynomial: it is the polynomial's *trailing* coefficient (the lowest-degree nonzero one),
which is exactly what `0₊`-positivity is about.
-/

open Polynomial HahnSeries

namespace Azurite.BPR

variable {F : Type*} [Field F]

/-! ## Embedding `K(ε)` into the Puiseux series `K⟨⟨ε⟩⟩`

The Laurent expansion `K(ε) → K((ε)) = LaurentSeries F`, followed by the exponent-preserving
inclusion `puiseuxEmb F 1 : K((ε)) → K⟨⟨ε⟩⟩` (`ε^{1/1} = ε`), realizes `K(ε)` as a subfield of
`K⟨⟨ε⟩⟩`.
-/

/-- The Laurent expansion of a rational function, viewed in `K⟨⟨ε⟩⟩` (it is a Laurent series in
`ε^{1/1} = ε`).-/
theorem coe_mem_puiseuxSeries (r : RatFunc F) :
    puiseuxEmb F 1 (r : LaurentSeries F) ∈ PuiseuxSeries F := by
  rw [mem_puiseuxSeries_iff]
  exact ⟨1, RingHom.mem_fieldRange.mpr ⟨(r : LaurentSeries F), rfl⟩⟩

/-- **The embedding of `K(ε)` into `K⟨⟨ε⟩⟩`** via Laurent expansion about `0`.-/
noncomputable def ratFuncToPuiseux (r : RatFunc F) : PuiseuxSeries F :=
  ⟨puiseuxEmb F 1 (r : LaurentSeries F), coe_mem_puiseuxSeries r⟩

@[simp] theorem ratFuncToPuiseux_coe (r : RatFunc F) :
    (ratFuncToPuiseux r : HahnSeries ℚ F) = puiseuxEmb F 1 (r : LaurentSeries F) := rfl

theorem ratFuncToPuiseux_zero : ratFuncToPuiseux (0 : RatFunc F) = 0 := by
  apply Subtype.ext; simp

theorem ratFuncToPuiseux_one : ratFuncToPuiseux (1 : RatFunc F) = 1 := by
  apply Subtype.ext; simp [map_one]

theorem ratFuncToPuiseux_add (r s : RatFunc F) :
    ratFuncToPuiseux (r + s) = ratFuncToPuiseux r + ratFuncToPuiseux s := by
  apply Subtype.ext; simp [Subfield.coe_add, map_add]

theorem ratFuncToPuiseux_mul (r s : RatFunc F) :
    ratFuncToPuiseux (r * s) = ratFuncToPuiseux r * ratFuncToPuiseux s := by
  apply Subtype.ext; simp [Subfield.coe_mul, map_mul]

/-- The embedding `K(ε) ↪ K⟨⟨ε⟩⟩` as a ring homomorphism.-/
noncomputable def ratFuncToPuiseuxHom (F : Type*) [Field F] : RatFunc F →+* PuiseuxSeries F where
  toFun := ratFuncToPuiseux
  map_one' := ratFuncToPuiseux_one
  map_mul' := ratFuncToPuiseux_mul
  map_zero' := ratFuncToPuiseux_zero
  map_add' := ratFuncToPuiseux_add

@[simp] theorem ratFuncToPuiseuxHom_apply (r : RatFunc F) :
    ratFuncToPuiseuxHom F r = ratFuncToPuiseux r := rfl

/-! ## The `0₊` order matches the Laurent leading coefficient

When `F` is an ordered field, the `0₊` order on `K(ε) = RatFunc F` (BPR Notation 2.5,
`Azurite.BPR.ZeroPlus`) agrees with the sign of the leading coefficient of the Laurent
expansion. This is the order-compatibility that makes `K(ε)` an *ordered* subfield of the
Puiseux series `K⟨⟨ε⟩⟩`.
-/

section Ordered

variable [LinearOrder F] [IsStrictOrderedRing F]

open ZeroPlus

end Ordered

end Azurite.BPR
