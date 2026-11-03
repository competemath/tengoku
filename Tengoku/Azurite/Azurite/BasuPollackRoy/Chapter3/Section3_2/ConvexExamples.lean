/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Tengoku.Azurite.Azurite.BasuPollackRoy.Chapter3.Section3_2.Convex
import Tengoku.Seed.Tactic.Linarith
import Tengoku.Seed.Tactic.Ring

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # BPR §3.2 — examples of convex sets

The whole space `R^k`, the empty set, and singletons are convex; on the line, every order-connected
subset of `R` (in particular every open or closed interval) is convex. The last statement is the
"a connected subset of `R` is convex" fact — connected subsets of a linearly ordered field are
exactly the order-connected ones. -/

namespace Azurite.BPR

variable {k : ℕ} {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]

/-- **`R^k` is convex.**
@isnad1 id=isconvex.0h2v.s5.963ed6efea3c from=translated src=- shape=327e23e9 vocab=4e353ca1
-/
theorem isConvex_univ : IsConvex (Set.univ : Set (Fin k → R)) :=
  isConvex_iff_convex.mpr convex_univ

/-- **The empty set is convex.**
@isnad1 id=isconvex.0h2v.s5.a68bb7ca948c from=translated src=- shape=1947b7e8 vocab=1b1c382c
-/
theorem isConvex_empty : IsConvex (∅ : Set (Fin k → R)) :=
  isConvex_iff_convex.mpr convex_empty

/-- **A single point is convex.**
@isnad1 id=isconvex.0h3v.s5.8058b7ed8180 from=translated src=- shape=aa340a37 vocab=0faf5e02
-/
theorem isConvex_singleton (p : Fin k → R) : IsConvex ({p} : Set (Fin k → R)) :=
  isConvex_iff_convex.mpr (convex_singleton p)

/-- **A connected (order-connected) subset of `R` is convex.** For a subset `I ⊆ R` that is
order-connected — equivalently, an interval — the corresponding line-set `{v | v₀ ∈ I}` is convex.
The convex combination `(1 − λ) x₀ + λ y₀` of two points of `I` lies in `I` by order-connectedness.
@isnad1 id=isconvex.1h2v.s6.1ac5d309e35a from=translated src=- shape=f470b85b vocab=7cce5712
-/
theorem isConvex_of_ordConnected_sect {I : Set R} (hI : I.OrdConnected) :
    IsConvex {v : Fin 1 → R | v 0 ∈ I} := by
  have hIconv : Convex R I := convex_iff_ordConnected.mpr hI
  intro x hx y hy l hl
  simp only [Set.mem_ofPred_eq] at hx hy ⊢
  rw [Pi.add_apply, Pi.smul_apply, Pi.smul_apply]
  exact hIconv hx hy (by linarith [hl.2]) hl.1 (by ring)

/-- **A closed interval of `R` is convex.**
@isnad1 id=isconvex.0h3v.s6.7db3f63934de from=translated src=- shape=3ecb8534 vocab=89f60c8e
-/
theorem isConvex_Icc (a b : R) : IsConvex {v : Fin 1 → R | v 0 ∈ Set.Icc a b} :=
  isConvex_of_ordConnected_sect Set.ordConnected_Icc

/-- **An open interval of `R` is convex.**
@isnad1 id=isconvex.0h3v.s6.4c113ce18968 from=translated src=- shape=3ecb8534 vocab=4c214e10
-/
theorem isConvex_Ioo (a b : R) : IsConvex {v : Fin 1 → R | v 0 ∈ Set.Ioo a b} :=
  isConvex_of_ordConnected_sect Set.ordConnected_Ioo

end Azurite.BPR
