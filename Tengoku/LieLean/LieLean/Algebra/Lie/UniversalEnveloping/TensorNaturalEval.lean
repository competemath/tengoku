/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import Tengoku.LieLean.LieLean.Algebra.Lie.UniversalEnveloping.TensorNatural
import Tengoku.Seed.LinearAlgebra.FiniteDimensional.Lemmas
import Tengoku.Seed.LinearAlgebra.TensorProduct.Basis

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Evaluating natural transformations at a faithful module

Let `I` be a two-sided ideal of `U = U(L)`, `A = U / I`, and `M` a module killed by `I`. A
morphism `g : V → A^{ad} ⊗ W` gives `φ_M = tensorNatMap g : M ⊗ V → M ⊗ W`. The map
`g ↦ φ_M` is linear (`tensorNatLinear`); it is injective when `I` is the annihilator of `M`
over a field (`tensorNatLinear_injective`), and hence bijective when the two Hom spaces have
the same finite dimension (`tensorNatLinear_bijective`).

In Humphreys' proof of Theorem 10.7 (Bernstein–Gelfand), `M = M(λ)` with `λ` dominant and
`I = Ann M(λ)`: Duflo's theorem identifies `I`, Kostant's theorem computes the dimension of
`Hom_𝔤(V, A^{ad} ⊗ W)`, and `finrank_hom_tensor_verma_tensor_of_isDominant` computes the
dimension of `Hom_𝔤(M(λ) ⊗ V, M(λ) ⊗ W)`.

## Main results

* `UniversalEnvelopingAlgebra.eq_zero_of_forall_rTensor_flip_eq_zero`: for an injective
  `φ : A → End(M)` over a field, `t ∈ A ⊗ W` with `(a ↦ φ(a) m) ⊗ 1 (t) = 0` for all `m` is `0`.
* `UniversalEnvelopingAlgebra.tensorNatLinear_injective`,
  `UniversalEnvelopingAlgebra.tensorNatLinear_bijective`.

## References

* J. E. Humphreys, *Representations of semisimple Lie algebras in the BGG category 𝒪*,
  GSM 94, AMS 2008, §10.8, proof of Thm. 10.7.
-/

noncomputable section

open TensorProduct LieModule

namespace UniversalEnvelopingAlgebra

section Faithful

variable {K A M W : Type*} [Field K] [AddCommGroup A] [Module K A] [AddCommGroup M] [Module K M]
  [AddCommGroup W] [Module K W]

end Faithful

variable {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
  {I : TwoSidedIdeal (UniversalEnvelopingAlgebra R L)}
  {M : Type*} [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]
  {V W : Type*} [AddCommGroup V] [Module R V] [LieRingModule L V] [LieModule R L V]
  [AddCommGroup W] [Module R W] [LieRingModule L W] [LieModule R L W]

variable {K : Type*} [Field K] [LieAlgebra K L]
  {I : TwoSidedIdeal (UniversalEnvelopingAlgebra K L)}
  {M V W : Type*} [AddCommGroup M] [Module K M] [LieRingModule L M] [LieModule K L M]
  [AddCommGroup V] [Module K V] [LieRingModule L V] [LieModule K L V]
  [AddCommGroup W] [Module K W] [LieRingModule L W] [LieModule K L W]

end UniversalEnvelopingAlgebra
