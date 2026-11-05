/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Tengoku.Seed.RingTheory.RegularLocalRing.Defs
public import Tengoku.Seed.RingTheory.Smooth.Locus
public import Tengoku.Seed.RingTheory.Smooth.StandardSmooth
import Tengoku.Hironaka.Hironaka.Algebra.RegularSmooth.Cotangent
import Tengoku.Hironaka.Hironaka.Algebra.RegularSmooth.Polynomial
import Tengoku.Hironaka.Hironaka.Algebra.RegularSmooth.QuotientRegular
import Tengoku.Seed.RingTheory.Smooth.StandardSmoothOfFree

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Smooth at a prime implies regular

The last assertion of [Sta, Tag 00TT], "in this case the local ring `S_𝔮` is regular", for a
finite type algebra `S` over any field `k`. The argument is the Jacobian one, assembled from
[Sta, Tags 00T6, 00RX, 00RU, 00NQ]; the numbered steps below are followed by the Lean proof.

**The presentation.** By Mathlib's `Algebra.IsSmoothAt.exists_notMem_isStandardSmooth`,
smoothness at `𝔮` gives a `g ∉ 𝔮` with `S_g` standard smooth over `k` ([Sta, Tags 00TA, 00T7];
finite type over a field is finite presentation); since `S_𝔮 ≅ (S_g)_{𝔮 S_g}` and regularity is
invariant under ring isomorphism, we may assume `S` itself standard smooth: `S ≅ A/(f_1, …, f_c)`
with `A = k[x_1, …, x_N]` and the Jacobian minor `Δ = det(∂f_j/∂x_{m(i)})` a unit of `S`
(Mathlib's `SubmersivePresentation`, whose `map : σ → ι` picks the `c` distinguished variables).
For such `S`, `Ω[S⁄k]` is free of rank `N - c` ([Sta, Tag 00T7, (2)]; `rank_kaehlerDifferential`),
so `κ(𝔮) ⊗[S] Ω[S⁄k]` has dimension `N - c` at every prime.

**The Jacobian argument.** (1) Let `Q ⊆ A` be the preimage of `𝔮` and `P = A_Q`, a regular local
ring (`Hironaka/Algebra/RegularSmooth/Polynomial.lean`). (2) The localized surjection `φ : P → S_𝔮`
has kernel `(f_1, …, f_c)P`, so `S_𝔮 ≅ P/(f_1, …, f_c)`.
(3) In the basis `1 ⊗ d x_i` of `κ ⊗[P] Ω[P⁄k]` the vector `1 ⊗ d f_j` has coordinates
`∂f_j/∂x_i mod Q`, and the `c × c` minor on the distinguished variables is `Δ mod Q ≠ 0` (a unit of
`S` does not lie in `𝔮`), so the `1 ⊗ d f_j` are linearly independent over `κ`.
(4) The conormal map `𝔪_P/𝔪_P² → κ ⊗ Ω[P⁄k]` sends the class of `f_j` to `1 ⊗ d f_j`, so the
classes of the `f_j` are linearly independent in `𝔪_P/𝔪_P²` (no injectivity of the conormal map is
used, only that it is a well-defined linear map).
(5) By [Sta, Tag 00NQ] (`Hironaka/Algebra/RegularSmooth/QuotientRegular.lean`), `P/(f_1, …, f_c)` is
a regular local ring, and so is `S_𝔮`.
-/

public section

universe u

open IsLocalRing KaehlerDifferential
open scoped TensorProduct

namespace Algebra

variable {k : Type u} [Field k] {S : Type u} [CommRing S] [Algebra k S]

/-- If the finite type `k`-algebra `S` is smooth at `𝔮` over `k`, there is `g ∉ 𝔮` with `S_g`
standard smooth over `k` (the first sentence of the proof of (1) ⇒ (3) in [Sta, Tag 00TT];
[Sta, Tag 00TA]). Mathlib's statement for finitely presented algebras, with finite type over a
field giving finite presentation.
@isnad1 id=ex.0h3v.s7.f39997c84cf3 from=translated src=- shape=a609283d vocab=0edac30f
-/
theorem IsSmoothAt.exists_notMem_isStandardSmooth_of_finiteType [Algebra.FiniteType k S]
    (𝔮 : Ideal S) [𝔮.IsPrime] [Algebra.IsSmoothAt k 𝔮] :
    ∃ g ∉ 𝔮, Algebra.IsStandardSmooth k (Localization.Away g) := by
  have : Algebra.FinitePresentation k S :=
    Algebra.FinitePresentation.of_finiteType.mp inferInstance
  exact Algebra.IsSmoothAt.exists_notMem_isStandardSmooth (R := k) 𝔮

/-- For `S` standard smooth of relative dimension `d` over `k`, `Ω[S⁄k]` is free of rank `d`, so
`κ(𝔮) ⊗[S] Ω[S⁄k]` has dimension `d` at every prime `𝔮` ([Sta, Tag 00T7, (2)]; [Sta, Tag 02G1]).
@isnad1 id=eq.0h4v.s9.c50d870b4106 from=translated src=- shape=78fee096 vocab=0051c072
-/
theorem IsStandardSmoothOfRelativeDimension.finrank_residueField_tensor_kaehlerDifferential
    (d : ℕ) [Algebra.IsStandardSmoothOfRelativeDimension d k S] (𝔮 : Ideal S) [𝔮.IsPrime] :
    Module.finrank 𝔮.ResidueField (𝔮.ResidueField ⊗[S] Ω[S⁄k]) = d := by
  have : Nontrivial S := by
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    exact ‹𝔮.IsPrime›.ne_top (Subsingleton.elim _ _)
  obtain ⟨ι, σ, _, _, ⟨P, -⟩⟩ := ‹Algebra.IsStandardSmoothOfRelativeDimension d k S›
  have : Module.Free S Ω[S⁄k] := P.free_kaehlerDifferential
  rw [Module.finrank_baseChange]
  exact Module.finrank_eq_of_rank_eq
    (Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential (R := k) (S := S) d)

end Algebra
