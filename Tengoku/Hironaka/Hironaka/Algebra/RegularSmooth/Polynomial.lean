/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Tengoku.Seed.RingTheory.Kaehler.Polynomial
public import Tengoku.Seed.RingTheory.RegularLocalRing.Defs
public import Tengoku.Seed.RingTheory.Etale.Kaehler
import Tengoku.Seed.RingTheory.RegularLocalRing.Polynomial
import Tengoku.Seed.RingTheory.Localization.Module
import Tengoku.Seed.LinearAlgebra.TensorProduct.Basis
import Tengoku.Seed.RingTheory.LocalRing.ResidueField.Ideal

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Differentials and regularity of a localized polynomial ring

The ambient ring of the Jacobian arguments of this directory is `P = k[x_i]_Q`, the polynomial
ring over the field `k` localized at a prime `Q`. Two facts about it [Sta, Tags 00RX, 00RT]:
`Ω[P⁄k]` is free on the `d x_i`, because `Ω` of a polynomial ring is free on the `d x_i` and `Ω`
commutes with localization (Mathlib's `mvPolynomialBasis` and `isLocalizedModule_map`, combined by
`Basis.ofIsLocalizedModule`); and `κ(Q) ⊗[P] Ω[P⁄k]` has the basis `1 ⊗ d x_i` (base change of a
basis). Third, `P` is a regular local ring: a field is a regular ring (Mathlib, through its
instance chain for Dedekind domains), a polynomial ring over a regular ring is regular (Mathlib),
and a localization of a regular ring at a prime is regular local by definition of `IsRegularRing`.
-/

@[expose] public section

universe u v

open IsLocalRing KaehlerDifferential MvPolynomial
open scoped TensorProduct

namespace KaehlerDifferential

/-- The `i`-th coordinate of `d x` in the basis `d x_j` of `Ω[R[x_j] ⁄ R]` is `∂x/∂x_i`
([Sta, Tag 00RX], "`d f = ∑ (∂f/∂x_i) d x_i`").
@isnad1 id=eq.0h4v.s11.b062969579cf from=translated src=- shape=2f71020c vocab=dea267a1
-/
theorem mvPolynomialBasis_repr_D_apply {R : Type u} [CommRing R] {σ : Type v}
    (x : MvPolynomial σ R) (i : σ) :
    (mvPolynomialBasis R σ).repr (D R (MvPolynomial σ R) x) i = pderiv i x := by
  classical
  rw [mvPolynomialBasis_repr_D]
  have h : (Finsupp.lapply i : (σ →₀ MvPolynomial σ R) →ₗ[MvPolynomial σ R]
      MvPolynomial σ R).compDer
        (mkDerivation R fun j => Finsupp.single j (1 : MvPolynomial σ R)) = pderiv i := by
    refine derivation_ext fun j => ?_
    change (Finsupp.lapply i : (σ →₀ MvPolynomial σ R) →ₗ[MvPolynomial σ R] MvPolynomial σ R)
        (mkDerivation R (fun j => Finsupp.single j (1 : MvPolynomial σ R)) (X j)) =
      pderiv i (X j)
    rw [mkDerivation_X, Finsupp.lapply_apply, pderiv_X, Finsupp.single_apply, Pi.single_apply]
  exact Derivation.congr_fun h x

variable {k : Type u} [CommRing k] {ι : Type v} (Q : Ideal (MvPolynomial ι k)) [Q.IsPrime]

/-- The basis `d x_i` of `Ω[k[x_i]_Q ⁄ k]`, the localization of the basis `d x_i` of
`Ω[k[x_i] ⁄ k]` [Sta, Tags 00RX, 00RT].-/
noncomputable def mvPolynomialLocalizationBasis :
    Module.Basis ι (Localization.AtPrime Q) Ω[Localization.AtPrime Q⁄k] :=
  (mvPolynomialBasis k ι).ofIsLocalizedModule (Localization.AtPrime Q) Q.primeCompl
    (map k k (MvPolynomial ι k) (Localization.AtPrime Q))

/--
@isnad1 id=eq.0h4v.s13.ffbd7e610833 from=translated src=- shape=1a1f37d4 vocab=3803afa7
-/
@[simp]
theorem mvPolynomialLocalizationBasis_apply (i : ι) :
    mvPolynomialLocalizationBasis Q i =
      D k (Localization.AtPrime Q)
        (algebraMap (MvPolynomial ι k) (Localization.AtPrime Q) (X i)) := by
  rw [mvPolynomialLocalizationBasis, Module.Basis.ofIsLocalizedModule_apply,
    mvPolynomialBasis_apply, map_D]

/-- The coordinates of `d f` in the basis `d x_i` of `Ω[k[x]_Q ⁄ k]` are the partial derivatives
`∂f/∂x_i` [Sta, Tag 00RX].
@isnad1 id=eq.0h5v.s14.96ec25a8f14f from=translated src=- shape=ff60f4e7 vocab=8efd29ec
-/
theorem mvPolynomialLocalizationBasis_repr_D (x : MvPolynomial ι k) (i : ι) :
    (mvPolynomialLocalizationBasis Q).repr
        (D k (Localization.AtPrime Q)
          (algebraMap (MvPolynomial ι k) (Localization.AtPrime Q) x)) i =
      algebraMap (MvPolynomial ι k) (Localization.AtPrime Q) (pderiv i x) := by
  rw [← map_D k k, mvPolynomialLocalizationBasis, Module.Basis.ofIsLocalizedModule_repr_apply,
    mvPolynomialBasis_repr_D_apply]

/-- The basis `1 ⊗ d x_i` of `κ(Q) ⊗[P] Ω[P⁄k]`, `P = k[x_i]_Q` (base change of a basis).-/
noncomputable def residueFieldTensorMvPolynomialLocalizationBasis :
    Module.Basis ι Q.ResidueField
      (Q.ResidueField ⊗[Localization.AtPrime Q] Ω[Localization.AtPrime Q⁄k]) :=
  (mvPolynomialLocalizationBasis Q).baseChange Q.ResidueField

/--
@isnad1 id=eq.0h4v.s14.7373f81580f3 from=translated src=- shape=5b06d50a vocab=3400e363
-/
@[simp]
theorem residueFieldTensorMvPolynomialLocalizationBasis_apply (i : ι) :
    residueFieldTensorMvPolynomialLocalizationBasis Q i =
      1 ⊗ₜ D k (Localization.AtPrime Q)
        (algebraMap (MvPolynomial ι k) (Localization.AtPrime Q) (X i)) := by
  rw [residueFieldTensorMvPolynomialLocalizationBasis, Module.Basis.baseChange_apply,
    mvPolynomialLocalizationBasis_apply]

/-- The coordinates of `1 ⊗ d f` in the basis `1 ⊗ d x_i` of `κ(Q) ⊗[P] Ω[P⁄k]` are the residues
`∂f/∂x_i mod Q`; this is how the Jacobian minor enters the proof that smooth implies regular.
@isnad1 id=eq.0h5v.s15.09b1cca081e5 from=translated src=- shape=8dc792b7 vocab=030f2d16
-/
theorem residueFieldTensorMvPolynomialLocalizationBasis_repr_tmul_D (x : MvPolynomial ι k)
    (i : ι) :
    (residueFieldTensorMvPolynomialLocalizationBasis Q).repr
        (1 ⊗ₜ D k (Localization.AtPrime Q)
          (algebraMap (MvPolynomial ι k) (Localization.AtPrime Q) x)) i =
      algebraMap (MvPolynomial ι k) Q.ResidueField (pderiv i x) := by
  rw [residueFieldTensorMvPolynomialLocalizationBasis, Module.Basis.baseChange_repr_tmul,
    mvPolynomialLocalizationBasis_repr_D, Algebra.smul_def, mul_one,
    ← IsScalarTower.algebraMap_apply]

end KaehlerDifferential

/-- For a field `k` and a prime `Q` of `k[x_1, …, x_N]`, the localization `k[x]_Q` is a regular
local ring (the regularity of the ambient ring in the proof of [Sta, Tag 00TS]).
@isnad1 id=isregula.0h3v.s7.53aa8fc646e7 from=translated src=- shape=639423b1 vocab=48c0298e
-/
theorem MvPolynomial.isRegularLocalRing_localization_atPrime {k : Type u} [Field k] {ι : Type v}
    [Finite ι] (Q : Ideal (MvPolynomial ι k)) [Q.IsPrime] :
    IsRegularLocalRing (Localization.AtPrime Q) :=
  IsRegularRing.isRegularLocalRing_localization Q
