/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Tengoku.Hironaka.Hironaka.Algebra.RegularSmooth.Stalk
import Tengoku.Hironaka.Hironaka.Algebra.Local.RegularSystem
import Tengoku.Hironaka.Hironaka.Algebra.RegularSmooth.Cotangent
import Tengoku.Hironaka.Hironaka.Scheme.Smooth.AdaptedCoordinates
import Tengoku.Hironaka.Hironaka.Scheme.Smooth.DifferentialBasis
import Tengoku.Seed.Algebra.Module.SpanRankOperations

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The differential basis at an arbitrary point

Kollár's local coordinates at non-closed points: at any `x ∈ X` (smooth of relative dimension `n`
over the perfect field `k`), with `t = trdeg_k κ(x)`, a regular system of parameters
`y_0, …, y_{m-1}` of `𝒪_{X,x}` (`m = dim 𝒪_{X,x} = n − t`) together with lifts
`z_0, …, z_{t-1} ∈ 𝒪_{X,x}` of a separating transcendence basis of `κ(x)/k` has differentials
`1 ⊗ d y_i, 1 ⊗ d z_j` forming a basis of `κ(x) ⊗ Ω[𝒪_{X,x}⁄k]`
(`exists_basis_tensor_kaehlerDifferential_sum`). Not in the sources in this form.

The argument: the conormal sequence `0 → 𝔪/𝔪² → κ ⊗ Ω[𝒪⁄k] → Ω[κ⁄k] → 0` is exact
([Sta, Tag 00TV]; `κ` is formally smooth over the perfect `k`, see
`Hironaka/Algebra/RegularSmooth/Cotangent.lean`); the `d s_j` of a separating transcendence basis
`s` form a basis of `Ω[κ⁄k]`
(`exists_basis_kaehlerDifferential_of_isTranscendenceBasis`, the construction of
`Hironaka/Algebra/RegularSmooth/Trdeg.lean`: `Ω[k[s]⁄k]` is free on the `d s_j`, and `k(s)/k[s]` and
`κ/k(s)` are formally étale, [Sta, Tags 00RX, 030O]); the classes `ȳ_i` form a basis of `𝔪/𝔪²`
(Nakayama). Hence the family `1 ⊗ d y_i` (in the image of `𝔪/𝔪²`) and `1 ⊗ d z_j` (mapping to the
basis `d s_j`) is linearly independent of size `m + t`, and
`dim_κ κ ⊗ Ω = dim 𝔪/𝔪² + dim Ω[κ⁄k] = m + t`, so it is a basis. Used in
`Hironaka/Scheme/IdealSheaf/Derivative/StalkCoords.lean`.
-/

public section

namespace AlgebraicGeometry

open KaehlerDifferential TensorProduct IsLocalRing

open scoped IntermediateField.algebraAdjoinAdjoin

universe u v

section Field

variable (k K : Type u) [Field k] [Field K] [Algebra k K]

/-- For a separating transcendence basis `v` of `K/k`, the differentials `d (v i)` form a basis of
`Ω[K⁄k]` ([Sta, Tags 00RX, 030O]; the construction of `Hironaka/Algebra/RegularSmooth/Trdeg.lean`).-/
theorem exists_basis_kaehlerDifferential_of_isTranscendenceBasis {ι : Type v} (v : ι → K)
    (hv : IsTranscendenceBasis k v)
    [Algebra.IsSeparable (IntermediateField.adjoin k (Set.range v)) K] :
    ∃ b : Module.Basis ι K Ω[K⁄k], ∀ i, b i = D k K (v i) := by
  classical
  set A := Algebra.adjoin k (Set.range v) with hA
  set F := IntermediateField.adjoin k (Set.range v) with hF
  let e : MvPolynomial ι k ≃ₐ[k] A := hv.1.aevalEquiv
  let _ : Algebra (MvPolynomial ι k) A := e.toRingEquiv.toRingHom.toAlgebra
  have : IsScalarTower k (MvPolynomial ι k) A :=
    IsScalarTower.of_algebraMap_eq fun x => (e.commutes x).symm
  have : IsLocalization (⊥ : Submonoid (MvPolynomial ι k)) (MvPolynomial ι k) :=
    IsLocalization.of_le_isUnit bot_le
  have : IsLocalization (⊥ : Submonoid (MvPolynomial ι k)) A :=
    IsLocalization.isLocalization_of_algEquiv (⊥ : Submonoid (MvPolynomial ι k))
      (AlgEquiv.ofBijective (Algebra.ofId (MvPolynomial ι k) A) e.bijective)
  have : Algebra.FormallyEtale (MvPolynomial ι k) A :=
    Algebra.FormallyEtale.of_isLocalization (Rₘ := A) ⊥
  let bA : Module.Basis ι A Ω[A⁄k] :=
    ((mvPolynomialBasis k ι).baseChange A).map
      (tensorKaehlerEquivOfFormallyEtale k (MvPolynomial ι k) A)
  let bF : Module.Basis ι F Ω[F⁄k] :=
    bA.ofIsLocalizedModule F (nonZeroDivisors A) (map k k A F)
  have : Algebra.FormallyEtale F K := Algebra.FormallyEtale.of_isSeparable F K
  let bK : Module.Basis ι K Ω[K⁄k] :=
    (bF.baseChange K).map (tensorKaehlerEquivOfFormallyEtale k F K)
  refine ⟨bK, fun i => ?_⟩
  have he : algebraMap A K (e (MvPolynomial.X i)) = v i := by
    rw [AlgebraicIndependent.algebraMap_aevalEquiv, MvPolynomial.aeval_X]
  simp only [bK, bF, bA, Module.Basis.map_apply, Module.Basis.baseChange_apply,
    Module.Basis.ofIsLocalizedModule_apply, mvPolynomialBasis_apply,
    tensorKaehlerEquivOfFormallyEtale_apply, mapBaseChange_tmul, one_smul, map_D]
  rw [← he, IsScalarTower.algebraMap_apply A F K]
  rfl

end Field

section Stalk

open AlgebraicGeometry CategoryTheory

variable {k : Type u} [Field k] [PerfectField k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) (n : ℕ)
  [SmoothOfRelativeDimension n f] (x : X)
include f n

end Stalk

end AlgebraicGeometry
