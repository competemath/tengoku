/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Tengoku.Azurite.Azurite.BasuPollackRoy.Chapter2.Section2_6.PuiseuxSeries
import Tengoku.Azurite.Azurite.BasuPollackRoy.Chapter2.Section2_1.InfinitesimalUnbounded
import Tengoku.Seed.Algebra.Order.Archimedean.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # BPR §2.6 — `ε` is infinitesimal; `K⟨⟨ε⟩⟩` is non-archimedean

In the ordered field of Puiseux series `K⟨⟨ε⟩⟩`, the element `ε` (the Puiseux series
`ε^1 = single 1 1`) is **infinitesimal over `K`** (`Azurite.BPR.IsInfinitesimalOver`): it is
positive and smaller than every positive constant `a ∈ K`, since `a - ε > 0` (its initial,
lowest-order coefficient is `a > 0`). Consequently `K⟨⟨ε⟩⟩` is **non-archimedean**: no natural
multiple `n • ε` reaches `1`.

To phrase "infinitesimal over `K`" we equip `K⟨⟨ε⟩⟩` with the `K`-algebra structure given by
the constant embedding `k ↦ k` (`puiseuxC`, `HahnSeries.C` corestricted to the Puiseux
subfield).
-/

namespace Azurite.BPR

open HahnSeries

variable {K : Type*} [Field K]

/-- The constant `HahnSeries.C k` is a Puiseux series (a Laurent series in `ε^{1/1} = ε`).
@isnad1 id=mem.0h2v.s8.f420a9096e01 from=translated src=- shape=b46aaef6 vocab=37d12ddc
-/
theorem C_mem_puiseuxSeries (k : K) : (HahnSeries.C k : HahnSeries ℚ K) ∈ PuiseuxSeries K := by
  rw [mem_puiseuxSeries_iff]
  exact ⟨1, RingHom.mem_fieldRange.mpr ⟨HahnSeries.C k, by
    simp [puiseuxEmb, HahnSeries.embDomainRingHom_apply]⟩⟩

/-- **The constant embedding `K → K⟨⟨ε⟩⟩`**, sending `k` to the constant Puiseux series `k`.-/
noncomputable def puiseuxC : K →+* PuiseuxSeries K where
  toFun k := ⟨HahnSeries.C k, C_mem_puiseuxSeries k⟩
  map_one' := by apply Subtype.ext; simp
  map_mul' a b := by apply Subtype.ext; simp [map_mul]
  map_zero' := by apply Subtype.ext; simp
  map_add' a b := by apply Subtype.ext; simp [map_add]

/--
@isnad1 id=eq.0h2v.s11.52dfa91efa0c from=translated src=- shape=4e2b9957 vocab=716a9879
-/
@[simp] theorem puiseuxC_coe (k : K) : (puiseuxC k : HahnSeries ℚ K) = HahnSeries.C k := rfl

/-- `K⟨⟨ε⟩⟩` is a `K`-algebra via the constant embedding.-/
noncomputable instance : Algebra K (PuiseuxSeries K) := puiseuxC.toAlgebra

/-- **The infinitesimal `ε ∈ K⟨⟨ε⟩⟩`**: the Puiseux series `ε^1`.-/
noncomputable def puiseuxEps : PuiseuxSeries K :=
  ⟨HahnSeries.single 1 1, by
    rw [mem_puiseuxSeries_iff]
    exact ⟨1, RingHom.mem_fieldRange.mpr ⟨HahnSeries.single 1 1, by
      rw [puiseuxEmb, HahnSeries.embDomainRingHom_apply, HahnSeries.embDomain_single]
      norm_num⟩⟩⟩

/--
@isnad1 id=eq.0h1v.s8.487731a645be from=translated src=- shape=e75f8057 vocab=43295364
-/
@[simp] theorem puiseuxEps_coe :
    ((puiseuxEps : PuiseuxSeries K) : HahnSeries ℚ K) = HahnSeries.single 1 1 := rfl

section Ordered

variable [LinearOrder K] [IsStrictOrderedRing K]

end Ordered

end Azurite.BPR
