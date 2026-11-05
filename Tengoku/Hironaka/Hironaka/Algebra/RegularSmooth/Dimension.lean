/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Tengoku.Seed.FieldTheory.Perfect
public import Tengoku.Seed.RingTheory.AlgebraicIndependent.Basic
public import Tengoku.Seed.RingTheory.Kaehler.Basic
public import Tengoku.Seed.RingTheory.KrullDimension.Basic
public import Tengoku.Seed.RingTheory.LocalRing.ResidueField.Ideal
public import Tengoku.Seed.RingTheory.Smooth.StandardSmooth
import Tengoku.Hironaka.Hironaka.Algebra.RegularSmooth.Cotangent
import Tengoku.Hironaka.Hironaka.Algebra.RegularSmooth.SmoothImpliesRegular
import Tengoku.Hironaka.Hironaka.Algebra.RegularSmooth.Trdeg
import Tengoku.Seed.Algebra.Module.SpanRankOperations
import Tengoku.Seed.RingTheory.Smooth.Field
import Tengoku.Seed.RingTheory.Smooth.StandardSmoothCotangent

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The dimension of a smooth local ring

For `S` standard smooth of relative dimension `n` over a perfect field `k` and a prime `𝔮`, with
`R = S_𝔮` and `κ = κ(𝔮)`: `R` is regular
(`Hironaka/Algebra/RegularSmooth/SmoothImpliesRegular.lean`), so `dim R = dim_κ 𝔪/𝔪²`; the conormal
sequence is short exact (`Cotangent.lean`), so `dim_κ 𝔪/𝔪² + dim_κ Ω[κ⁄k] = dim_κ κ ⊗[R] Ω[R⁄k]`;
and `κ ⊗[R] Ω[R⁄k] = κ ⊗[S] Ω[S⁄k]` has dimension `n` (`Ω[S⁄k]` is free of rank `n`; `Ω[R⁄k] = R
⊗[S] Ω[S⁄k]` because a localization is formally étale). Hence `dim R + dim_κ Ω[κ⁄k] = n`. With
`dim_κ Ω[κ⁄k] = trdeg_k κ` (`Trdeg.lean`) this is the formula `dim S_𝔮 + trdeg_k κ(𝔮) = n` of [Sta,
Tag 0A21, (10)]; at a maximal ideal `κ` is finite over `k` (Zariski's lemma, Mathlib's
`finite_of_finite_type_of_isJacobsonRing`), hence separable algebraic over the perfect field `k`, so
`Ω[κ⁄k] = 0` and `dim S_𝔮 = n`. The dimension arithmetic is additive in `WithBot ℕ∞`, the
transcendence degree entering through `Cardinal.toENat`. The scheme forms are in
`Hironaka/Algebra/RegularSmooth/SchemeForms.lean`.
-/

public section

universe u

open IsLocalRing KaehlerDifferential
open scoped TensorProduct

namespace Algebra.IsStandardSmoothOfRelativeDimension

variable {k : Type u} [Field k] {S : Type u} [CommRing S] [Algebra k S]

end Algebra.IsStandardSmoothOfRelativeDimension
