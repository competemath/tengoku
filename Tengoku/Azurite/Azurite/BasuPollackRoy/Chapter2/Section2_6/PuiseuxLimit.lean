/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Tengoku.Azurite.Azurite.BasuPollackRoy.Chapter2.Section2_6.Notation_2_100
import Tengoku.Azurite.Azurite.BasuPollackRoy.Chapter2.Section2_6.Corollary_2_98

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # BPR §2.6 — the base-field embedding `R ↪ R⟨ε⟩` and `lim_ε` foundations

Foundations for Proposition 3.5: the embedding `R ↪ R⟨ε⟩ = algebraicPuiseux R` (constants are
algebraic over `R(ε)`), that `lim_ε` fixes the base field, and the infinitesimal characterization
`lim_ε y = x ↔ y − x` is infinitesimal. -/

namespace Azurite.BPR

open Polynomial

variable {R : Type*} [Field R]

/-- `R(ε) = RatFunc R` acts on `R⟨ε⟩ = algebraicPuiseux R` (its relative algebraic closure).-/
noncomputable instance ratFuncAlgebraicPuiseuxAlgebra :
    Algebra (RatFunc R) (algebraicPuiseux R) :=
  inferInstanceAs (Algebra (RatFunc R) (algebraicClosure (RatFunc R) (PuiseuxSeries R)))

/-- **The base-field embedding `R ↪ R⟨ε⟩`**, as the composite `R → R(ε) → R⟨ε⟩`.-/
noncomputable instance algebraRAlgebraicPuiseux : Algebra R (algebraicPuiseux R) :=
  ((algebraMap (RatFunc R) (algebraicPuiseux R)).comp (algebraMap R (RatFunc R))).toAlgebra

/-- `ε = single 1 1` is algebraic over `R(ε)` (it is `R(ε)`'s indeterminate `X`), hence in `R⟨ε⟩`.
@isnad1 id=mem.0h1v.s10.673b7634a8a8 from=translated src=- shape=e0f03090 vocab=82c90ae3
-/
theorem puiseuxEps_mem_algebraicPuiseux :
    (puiseuxEps : PuiseuxSeries R) ∈ algebraicPuiseux R := by
  rw [mem_algebraicPuiseux]
  have h : (puiseuxEps : PuiseuxSeries R) = algebraMap (RatFunc R) (PuiseuxSeries R) RatFunc.X := by
    rw [RingHom.algebraMap_toAlgebra]
    apply Subtype.ext
    rw [ratFuncToPuiseuxHom_apply, ratFuncToPuiseux_coe, RatFunc.coe_X, puiseuxEmb_single,
      show puiseuxExpHom (1 : ℕ+) (1 : ℤ) = (1 : ℚ) from by simp]
    rfl
  rw [h]; exact isAlgebraic_algebraMap _

/-- **`ε` as an element of `R⟨ε⟩`.**-/
noncomputable def epsAP (R : Type*) [Field R] : algebraicPuiseux R :=
  ⟨puiseuxEps, puiseuxEps_mem_algebraicPuiseux⟩

/--
@isnad1 id=eq.0h1v.s10.c22aef936179 from=translated src=- shape=7e15e105 vocab=7b664ae9
-/
@[simp] theorem coe_epsAP : ((epsAP R : algebraicPuiseux R) : PuiseuxSeries R) = puiseuxEps := rfl

section Ordered

variable [LinearOrder R] [IsStrictOrderedRing R]

end Ordered

end Azurite.BPR
