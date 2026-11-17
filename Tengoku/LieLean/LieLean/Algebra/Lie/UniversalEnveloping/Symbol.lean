/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import Tengoku.LieLean.LieLean.Algebra.Lie.UniversalEnveloping.Domain
import Tengoku.LieLean.LieLean.Algebra.Lie.UniversalEnveloping.PBW

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Symbols in the universal enveloping algebra

`UniversalEnvelopingAlgebra.HasSymbol k s u` says that `u ∈ Fₖ U(L)` (the PBW filtration) and that
the class of `u` in `Fₖ / Fₖ₋₁ ⊆ gr U(L)` is `s`. Symbols are multiplicative
(`HasSymbol.mul`, `HasSymbol.pow`), two elements with the same symbol in degree `k + 1` differ by
an element of `Fₖ` (`HasSymbol.sub_mem`), and for `L` free over a domain, right multiplication by
an element with a nonzero symbol of degree one lowers no filtration degree
(`mem_filtration_of_mul_pow_mem`).

These are the degree arguments in the proof of Shapovalov's theorem ([HumO] §4.13): there
"degree" is the degree of a PBW monomial, i.e. the PBW filtration.

## References

* [HumO] J. E. Humphreys, *Representations of semisimple Lie algebras in the BGG category 𝒪*,
  GSM 94, AMS 2008, §4.12–4.13.
-/

noncomputable section

namespace UniversalEnvelopingAlgebra

attribute [local instance 100] LieRing.ofAssociativeRing

variable {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]

/-- `u ∈ Fₖ U(L)` and the class of `u` in `Fₖ / Fₖ₋₁ ⊆ gr U(L)` is `s`.-/
def HasSymbol (k : ℕ) (s : AssociatedGraded R L) (u : UniversalEnvelopingAlgebra R L) : Prop :=
  ∃ h : u ∈ filtration R L k, toGr R L k ⟨u, h⟩ = s

namespace HasSymbol

variable {k m n : ℕ} {s t : AssociatedGraded R L} {u w : UniversalEnvelopingAlgebra R L}

end HasSymbol

end UniversalEnvelopingAlgebra
