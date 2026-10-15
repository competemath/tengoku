/-
Copyright (c) 2026 BochaoKong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BochaoKong
-/
module

public import Tengoku.LeanPool.LeanPool.LocalComplexGeometry.Germs.Basic
public import Tengoku
public import Tengoku.LeanPool.LeanPool.LocalComplexGeometry.ClassicalComplexWPT.Basic

/-!
# Coordinates and pullback for holomorphic germs

This module relates the standard model `Fin (n + 1) → ℂ` to the product model
used by the pinned Weierstrass-preparation dependency.  It also constructs
contravariant pullback homomorphisms on holomorphic germs, the inclusion of
lower-dimensional base germs, and the resulting algebra structure.
-/

@[expose] public section

open Filter
open scoped Topology

namespace LocalComplexGeometry

noncomputable section

/-! ## The standard successor-coordinate splitting -/

/-- Split the last coordinate of `ℂⁿ⁺¹`, as a complex-linear equivalence. -/
def wptAmbientLinearEquiv (n : ℕ) :
    ComplexEuclidean (n + 1) ≃ₗ[ℂ] ClassicalComplexWPT.Ambient n where
  toFun x := (fun i ↦ x i.castSucc, x (Fin.last n))
  invFun x := Fin.lastCases x.2 x.1
  left_inv x := by
    funext i
    cases i using Fin.lastCases <;> simp
  right_inv x := by
    ext i <;> simp
  map_add' x y := by
    ext i <;> simp
  map_smul' c x := by
    ext i <;> simp

/-- The continuous complex-linear splitting of the last coordinate of `ℂⁿ⁺¹`.

The codomain is definitionally WPT's `(Fin n → ℂ) × ℂ` ambient space.
-/
def wptAmbientEquiv (n : ℕ) :
    ComplexEuclidean (n + 1) ≃L[ℂ] ClassicalComplexWPT.Ambient n :=
  (wptAmbientLinearEquiv n).toContinuousLinearEquiv

/--
@isnad1 id=eq.0h2v.s9.3a39688a76bd from=translated src=- shape=2b0fb116 vocab=f754f00b
-/
@[simp]
theorem wptAmbientEquiv_apply (n : ℕ) (x : ComplexEuclidean (n + 1)) :
    wptAmbientEquiv n x = (fun i ↦ x i.castSucc, x (Fin.last n)) :=
  rfl

/--
@isnad1 id=eq.0h2v.s10.c8a44a0e6444 from=translated src=- shape=167d6661 vocab=9fd5e76e
-/
@[simp]
theorem wptAmbientEquiv_symm_apply (n : ℕ)
    (x : ClassicalComplexWPT.Ambient n) :
    (wptAmbientEquiv n).symm x = Fin.lastCases x.2 x.1 :=
  rfl

/--
@isnad1 id=eq.0h1v.s9.5375ae267211 from=translated src=- shape=917c824d vocab=ac7ad809
-/
theorem wptAmbientEquiv_zero (n : ℕ) :
    wptAmbientEquiv n (0 : ComplexEuclidean (n + 1)) = 0 :=
  map_zero (wptAmbientEquiv n)

/--
@isnad1 id=eq.0h1v.s10.2e51cf817802 from=translated src=- shape=e660c348 vocab=da8ca540
-/
theorem wptAmbientEquiv_symm_zero (n : ℕ) :
    (wptAmbientEquiv n).symm (0 : ClassicalComplexWPT.Ambient n) = 0 :=
  map_zero (wptAmbientEquiv n).symm

/-- Analyticity at the origin is preserved and reflected by the standard/WPT
ambient-coordinate equivalence.
@isnad1 id=iff.0h2v.s10.9eb7ffc9968c from=translated src=- shape=848c7b38 vocab=4c76986a
-/
theorem analyticAt_comp_wptAmbientEquiv_iff (n : ℕ)
    (f : ClassicalComplexWPT.Ambient n → ℂ) :
    AnalyticAt ℂ (f ∘ wptAmbientEquiv n) 0 ↔ AnalyticAt ℂ f 0 := by
  constructor
  · intro hf
    have hf' : AnalyticAt ℂ (f ∘ wptAmbientEquiv n)
        ((wptAmbientEquiv n).symm 0) := by
      rw [map_zero]
      exact hf
    have hcomp := hf'.compContinuousLinearMap
      (u := (wptAmbientEquiv n).symm.toContinuousLinearMap) (x := 0)
    simpa [Function.comp_def] using hcomp
  · intro hf
    have hf' : AnalyticAt ℂ f (wptAmbientEquiv n 0) := by
      rw [map_zero]
      exact hf
    simpa using hf'.compContinuousLinearMap
      (u := (wptAmbientEquiv n).toContinuousLinearMap) (x := 0)

/-- Neighborhood equality at the origin is preserved and reflected by the
standard/WPT ambient-coordinate equivalence.
@isnad1 id=iff.0h3v.s10.a251fb3449a8 from=translated src=- shape=aebc3f1a vocab=4eec4537
-/
theorem eventuallyEq_comp_wptAmbientEquiv_iff (n : ℕ)
    (f g : ClassicalComplexWPT.Ambient n → ℂ) :
    (f ∘ wptAmbientEquiv n) =ᶠ[𝓝 0] (g ∘ wptAmbientEquiv n) ↔
      f =ᶠ[𝓝 0] g := by
  constructor
  · intro h
    have ht : Tendsto (wptAmbientEquiv n).symm (𝓝 0) (𝓝 0) := by
      have ht' : Tendsto (wptAmbientEquiv n).symm (𝓝 0)
          (𝓝 ((wptAmbientEquiv n).symm 0)) :=
        (wptAmbientEquiv n).symm.continuousAt
      rw [map_zero] at ht'
      exact ht'
    simpa [Function.comp_def] using h.comp_tendsto ht
  · intro h
    have ht : Tendsto (wptAmbientEquiv n) (𝓝 0) (𝓝 0) := by
      have ht' : Tendsto (wptAmbientEquiv n) (𝓝 0)
          (𝓝 (wptAmbientEquiv n 0)) :=
        (wptAmbientEquiv n).continuousAt
      rw [map_zero] at ht'
      exact ht'
    exact h.comp_tendsto ht

/-! ## Pullback of function germs and holomorphic germs -/

/-- Precomposition of function germs by a continuous linear map fixing the origin. -/
def functionGermPullbackHom {n m : ℕ}
    (L : ComplexEuclidean n →L[ℂ] ComplexEuclidean m) :
    FunctionGerm m →+* FunctionGerm n where
  toFun φ := φ.compTendsto L (by
    have hL : Tendsto L (𝓝 (0 : ComplexEuclidean n)) (𝓝 (L 0)) :=
      L.continuous.continuousAt
    rw [L.map_zero] at hL
    exact hL)
  map_zero' := rfl
  map_one' := rfl
  map_add' φ ψ := by
    refine Filter.Germ.inductionOn φ ?_
    intro f
    refine Filter.Germ.inductionOn ψ ?_
    intro g
    rfl
  map_mul' φ ψ := by
    refine Filter.Germ.inductionOn φ ?_
    intro f
    refine Filter.Germ.inductionOn ψ ?_
    intro g
    rfl

/--
@isnad1 id=eq.0h4v.s9.a38e5367aac7 from=translated src=- shape=8058a0f0 vocab=365a9b14
-/
@[simp]
theorem functionGermPullbackHom_coe {n m : ℕ}
    (L : ComplexEuclidean n →L[ℂ] ComplexEuclidean m)
    (f : ComplexEuclidean m → ℂ) :
    functionGermPullbackHom L (f : FunctionGerm m) =
      ((f ∘ L : ComplexEuclidean n → ℂ) : FunctionGerm n) :=
  rfl

/--
@isnad1 id=eq.0h4v.s8.9b84066c9282 from=translated src=- shape=eb0f011a vocab=4995df2d
-/
@[simp]
theorem functionGermPullbackHom_value {n m : ℕ}
    (L : ComplexEuclidean n →L[ℂ] ComplexEuclidean m)
    (φ : FunctionGerm m) :
    Filter.Germ.value (functionGermPullbackHom L φ) = Filter.Germ.value φ := by
  refine Filter.Germ.inductionOn φ ?_
  intro f
  change (f ∘ L) 0 = f 0
  simp only [Function.comp_apply, map_zero]

/--
@isnad1 id=eq.0h1v.s7.e0479f8d0984 from=translated src=- shape=5f9f27ce vocab=daafde70
-/
@[simp]
theorem functionGermPullbackHom_id (n : ℕ) :
    functionGermPullbackHom (ContinuousLinearMap.id ℂ (ComplexEuclidean n)) =
      RingHom.id (FunctionGerm n) := by
  ext φ
  refine Filter.Germ.inductionOn φ ?_
  intro f
  rfl

/--
@isnad1 id=eq.0h5v.s9.7149b9a66d97 from=translated src=- shape=8e70370b vocab=77380202
-/
theorem functionGermPullbackHom_comp {n m k : ℕ}
    (L : ComplexEuclidean n →L[ℂ] ComplexEuclidean m)
    (M : ComplexEuclidean m →L[ℂ] ComplexEuclidean k) :
    functionGermPullbackHom (M.comp L) =
      (functionGermPullbackHom L).comp (functionGermPullbackHom M) := by
  ext φ
  refine Filter.Germ.inductionOn φ ?_
  intro f
  rfl

/--
@isnad1 id=leftinve.0h3v.s9.716ef04b4e95 from=translated src=- shape=bad92158 vocab=96d9a9b5
-/
theorem functionGermPullbackHom_leftInverse {n m : ℕ}
    (L : ComplexEuclidean n ≃L[ℂ] ComplexEuclidean m) :
    Function.LeftInverse
      (functionGermPullbackHom
        (L.symm : ComplexEuclidean m →L[ℂ] ComplexEuclidean n))
      (functionGermPullbackHom
        (L : ComplexEuclidean n →L[ℂ] ComplexEuclidean m)) := by
  intro φ
  change ((functionGermPullbackHom
      (L.symm : ComplexEuclidean m →L[ℂ] ComplexEuclidean n)).comp
    (functionGermPullbackHom
      (L : ComplexEuclidean n →L[ℂ] ComplexEuclidean m))) φ = φ
  rw [← DFunLike.congr_fun (functionGermPullbackHom_comp
    (L.symm : ComplexEuclidean m →L[ℂ] ComplexEuclidean n)
    (L : ComplexEuclidean n →L[ℂ] ComplexEuclidean m)) φ]
  have hcomp :
      (L : ComplexEuclidean n →L[ℂ] ComplexEuclidean m).comp
          (L.symm : ComplexEuclidean m →L[ℂ] ComplexEuclidean n) =
        ContinuousLinearMap.id ℂ (ComplexEuclidean m) := by
    apply ContinuousLinearMap.ext
    intro x
    exact L.apply_symm_apply x
  rw [hcomp, DFunLike.congr_fun (functionGermPullbackHom_id m) φ]
  rfl

/--
@isnad1 id=rightinv.0h3v.s9.8d24a319a7d5 from=translated src=- shape=bad92158 vocab=047da358
-/
theorem functionGermPullbackHom_rightInverse {n m : ℕ}
    (L : ComplexEuclidean n ≃L[ℂ] ComplexEuclidean m) :
    Function.RightInverse
      (functionGermPullbackHom
        (L.symm : ComplexEuclidean m →L[ℂ] ComplexEuclidean n))
      (functionGermPullbackHom
        (L : ComplexEuclidean n →L[ℂ] ComplexEuclidean m)) := by
  intro φ
  change ((functionGermPullbackHom
      (L : ComplexEuclidean n →L[ℂ] ComplexEuclidean m)).comp
    (functionGermPullbackHom
      (L.symm : ComplexEuclidean m →L[ℂ] ComplexEuclidean n))) φ = φ
  rw [← DFunLike.congr_fun (functionGermPullbackHom_comp
    (L : ComplexEuclidean n →L[ℂ] ComplexEuclidean m)
    (L.symm : ComplexEuclidean m →L[ℂ] ComplexEuclidean n)) φ]
  have hcomp :
      (L.symm : ComplexEuclidean m →L[ℂ] ComplexEuclidean n).comp
          (L : ComplexEuclidean n →L[ℂ] ComplexEuclidean m) =
        ContinuousLinearMap.id ℂ (ComplexEuclidean n) := by
    apply ContinuousLinearMap.ext
    intro x
    exact L.symm_apply_apply x
  rw [hcomp, DFunLike.congr_fun (functionGermPullbackHom_id n) φ]
  rfl

/-- Pullback of holomorphic germs by a continuous complex-linear map. -/
def holomorphicGermPullbackHom {n m : ℕ}
    (L : ComplexEuclidean n →L[ℂ] ComplexEuclidean m) :
    HolomorphicGerm m →+* HolomorphicGerm n where
  toFun φ :=
    ⟨functionGermPullbackHom L φ.1, by
      obtain ⟨f, hf, hφ⟩ := φ.property
      refine ⟨f ∘ L, ?_, ?_⟩
      · have hf' : AnalyticAt ℂ f (L 0) := by simpa using hf
        simpa using hf'.compContinuousLinearMap (u := L) (x := 0)
      · rw [← hφ]
        rfl⟩
  map_zero' := by
    apply Subtype.ext
    exact map_zero (functionGermPullbackHom L)
  map_one' := by
    apply Subtype.ext
    exact map_one (functionGermPullbackHom L)
  map_add' φ ψ := by
    apply Subtype.ext
    exact map_add (functionGermPullbackHom L) φ.1 ψ.1
  map_mul' φ ψ := by
    apply Subtype.ext
    exact map_mul (functionGermPullbackHom L) φ.1 ψ.1

/--
@isnad1 id=eq.0h4v.s12.d4b3de98a9a3 from=translated src=- shape=ebe3d71d vocab=f23cf987
-/
@[simp]
theorem holomorphicGermPullbackHom_coe {n m : ℕ}
    (L : ComplexEuclidean n →L[ℂ] ComplexEuclidean m)
    (φ : HolomorphicGerm m) :
    ((holomorphicGermPullbackHom L φ : HolomorphicGerm n) : FunctionGerm n) =
      functionGermPullbackHom L (φ : FunctionGerm m) :=
  rfl

/--
@isnad1 id=eq.1h4v.s11.b486ee684433 from=translated src=- shape=dcf4360b vocab=23d9455d
-/
@[simp]
theorem holomorphicGermPullbackHom_ofFunction {n m : ℕ}
    (L : ComplexEuclidean n →L[ℂ] ComplexEuclidean m)
    (f : ComplexEuclidean m → ℂ) (hf : AnalyticAt ℂ f 0) :
    holomorphicGermPullbackHom L (HolomorphicGerm.ofFunction f hf) =
      HolomorphicGerm.ofFunction (f ∘ L)
        (by
          have hf' : AnalyticAt ℂ f (L 0) := by simpa using hf
          simpa using hf'.compContinuousLinearMap (u := L) (x := 0)) := by
  apply Subtype.ext
  rfl

/--
@isnad1 id=eq.0h4v.s11.4a679db8c303 from=translated src=- shape=524e4355 vocab=e2150826
-/
@[simp]
theorem evalAtOrigin_holomorphicGermPullbackHom {n m : ℕ}
    (L : ComplexEuclidean n →L[ℂ] ComplexEuclidean m)
    (φ : HolomorphicGerm m) :
    evalAtOrigin (holomorphicGermPullbackHom L φ) = evalAtOrigin φ := by
  exact functionGermPullbackHom_value L (φ : FunctionGerm m)

/--
@isnad1 id=eq.0h1v.s11.d14561846017 from=translated src=- shape=2222c3a9 vocab=6c2518e0
-/
@[simp]
theorem holomorphicGermPullbackHom_id (n : ℕ) :
    holomorphicGermPullbackHom (ContinuousLinearMap.id ℂ (ComplexEuclidean n)) =
      RingHom.id (HolomorphicGerm n) := by
  ext φ
  exact DFunLike.congr_fun (functionGermPullbackHom_id n) φ.1

/--
@isnad1 id=eq.0h5v.s11.d4d55387627d from=translated src=- shape=9db10015 vocab=81edd397
-/
theorem holomorphicGermPullbackHom_comp {n m k : ℕ}
    (L : ComplexEuclidean n →L[ℂ] ComplexEuclidean m)
    (M : ComplexEuclidean m →L[ℂ] ComplexEuclidean k) :
    holomorphicGermPullbackHom (M.comp L) =
      (holomorphicGermPullbackHom L).comp (holomorphicGermPullbackHom M) := by
  ext φ
  exact DFunLike.congr_fun (functionGermPullbackHom_comp L M) φ.1

/-- Pullback by a continuous complex-linear equivalence, as a ring equivalence.

The direction is contravariant: an equivalence `L : ℂⁿ ≃L[ℂ] ℂᵐ` induces an
equivalence from germs on `ℂᵐ` to germs on `ℂⁿ`.
-/
def coordinatePullback {n m : ℕ}
    (L : ComplexEuclidean n ≃L[ℂ] ComplexEuclidean m) :
    HolomorphicGerm m ≃+* HolomorphicGerm n where
  toFun := holomorphicGermPullbackHom
    (L : ComplexEuclidean n →L[ℂ] ComplexEuclidean m)
  invFun := holomorphicGermPullbackHom
    (L.symm : ComplexEuclidean m →L[ℂ] ComplexEuclidean n)
  left_inv φ := by
    apply Subtype.ext
    exact functionGermPullbackHom_leftInverse L (φ : FunctionGerm m)
  right_inv φ := by
    apply Subtype.ext
    exact functionGermPullbackHom_rightInverse L (φ : FunctionGerm n)
  map_add' φ ψ := (holomorphicGermPullbackHom
    (L : ComplexEuclidean n →L[ℂ] ComplexEuclidean m)).map_add φ ψ
  map_mul' φ ψ := (holomorphicGermPullbackHom
    (L : ComplexEuclidean n →L[ℂ] ComplexEuclidean m)).map_mul φ ψ

/--
@isnad1 id=eq.0h4v.s13.0c1bc6a19e6c from=translated src=- shape=26b3c432 vocab=fe779cd0
-/
@[simp]
theorem coordinatePullback_apply {n m : ℕ}
    (L : ComplexEuclidean n ≃L[ℂ] ComplexEuclidean m)
    (φ : HolomorphicGerm m) :
    coordinatePullback L φ = holomorphicGermPullbackHom
      (L : ComplexEuclidean n →L[ℂ] ComplexEuclidean m) φ :=
  rfl

/--
@isnad1 id=eq.0h4v.s14.4a7102d49113 from=translated src=- shape=1c6c7b29 vocab=6cf6cf80
-/
@[simp]
theorem coordinatePullback_symm_apply {n m : ℕ}
    (L : ComplexEuclidean n ≃L[ℂ] ComplexEuclidean m)
    (φ : HolomorphicGerm n) :
    (coordinatePullback L).symm φ = holomorphicGermPullbackHom
      (L.symm : ComplexEuclidean m →L[ℂ] ComplexEuclidean n) φ :=
  rfl

/--
@isnad1 id=eq.0h4v.s13.8a4e7c24bab0 from=translated src=- shape=4f91309b vocab=9430e91c
-/
theorem evalAtOrigin_coordinatePullback {n m : ℕ}
    (L : ComplexEuclidean n ≃L[ℂ] ComplexEuclidean m)
    (φ : HolomorphicGerm m) :
    evalAtOrigin (coordinatePullback L φ) = evalAtOrigin φ :=
  evalAtOrigin_holomorphicGermPullbackHom
    (L : ComplexEuclidean n →L[ℂ] ComplexEuclidean m) φ

/--
@isnad1 id=eq.0h1v.s12.f3a564272a80 from=translated src=- shape=2222c3a9 vocab=e69284dc
-/
@[simp]
theorem coordinatePullback_refl (n : ℕ) :
    coordinatePullback (ContinuousLinearEquiv.refl ℂ (ComplexEuclidean n)) =
      RingEquiv.refl (HolomorphicGerm n) := by
  ext φ
  exact DFunLike.congr_fun (functionGermPullbackHom_id n) φ.1

/--
@isnad1 id=eq.0h5v.s13.5e196e106a09 from=translated src=- shape=77655a85 vocab=d0cfff5e
-/
theorem coordinatePullback_trans {n m k : ℕ}
    (L : ComplexEuclidean n ≃L[ℂ] ComplexEuclidean m)
    (M : ComplexEuclidean m ≃L[ℂ] ComplexEuclidean k) :
    coordinatePullback (L.trans M) =
      (coordinatePullback M).trans (coordinatePullback L) := by
  ext φ
  exact DFunLike.congr_fun
    (functionGermPullbackHom_comp (L : ComplexEuclidean n →L[ℂ] ComplexEuclidean m)
      (M : ComplexEuclidean m →L[ℂ] ComplexEuclidean k)) φ.1

/--
@isnad1 id=eq.0h3v.s12.3f57250eb698 from=translated src=- shape=4f1d087b vocab=8a2b375d
-/
@[simp]
theorem coordinatePullback_symm {n m : ℕ}
    (L : ComplexEuclidean n ≃L[ℂ] ComplexEuclidean m) :
    coordinatePullback L.symm = (coordinatePullback L).symm := by
  ext φ
  rfl

/-! ## Base inclusion and the last coordinate -/

/-- Projection from `ℂⁿ⁺¹` to its first `n` coordinates. -/
def baseProjectionCLM (n : ℕ) :
    ComplexEuclidean (n + 1) →L[ℂ] ComplexEuclidean n :=
  (ContinuousLinearMap.fst ℂ (ComplexEuclidean n) ℂ).comp
    (wptAmbientEquiv n : ComplexEuclidean (n + 1) →L[ℂ]
      ClassicalComplexWPT.Ambient n)

/--
@isnad1 id=eq.0h2v.s8.b05befae70a0 from=translated src=- shape=1b84fdc0 vocab=cfd4d441
-/
@[simp]
theorem baseProjectionCLM_apply (n : ℕ) (x : ComplexEuclidean (n + 1)) :
    baseProjectionCLM n x = fun i ↦ x i.castSucc :=
  rfl

/-- The zero-last-coordinate section `z ↦ (z, 0)` in the standard model. -/
def baseSectionCLM (n : ℕ) :
    ComplexEuclidean n →L[ℂ] ComplexEuclidean (n + 1) :=
  (wptAmbientEquiv n).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.inl ℂ (ComplexEuclidean n) ℂ)

/--
@isnad1 id=eq.0h3v.s8.254a52195d2c from=translated src=- shape=a17e8ab7 vocab=011b4aa6
-/
@[simp]
theorem baseSectionCLM_castSucc (n : ℕ) (z : ComplexEuclidean n) (i : Fin n) :
    baseSectionCLM n z i.castSucc = z i := by
  simp [baseSectionCLM]

/--
@isnad1 id=eq.0h2v.s8.dcff22f1e5fa from=translated src=- shape=b2288724 vocab=aad5bc66
-/
@[simp]
theorem baseSectionCLM_last (n : ℕ) (z : ComplexEuclidean n) :
    baseSectionCLM n z (Fin.last n) = 0 := by
  simp [baseSectionCLM]

/-- Extraction of the last coordinate of `ℂⁿ⁺¹`. -/
def lastCoordinateCLM (n : ℕ) : ComplexEuclidean (n + 1) →L[ℂ] ℂ :=
  (ContinuousLinearMap.snd ℂ (ComplexEuclidean n) ℂ).comp
    (wptAmbientEquiv n : ComplexEuclidean (n + 1) →L[ℂ]
      ClassicalComplexWPT.Ambient n)

/--
@isnad1 id=eq.0h2v.s8.14cc6ef839ee from=translated src=- shape=1a7eaf67 vocab=ab63077a
-/
@[simp]
theorem lastCoordinateCLM_apply (n : ℕ) (x : ComplexEuclidean (n + 1)) :
    lastCoordinateCLM n x = x (Fin.last n) :=
  rfl

/--
@isnad1 id=eq.0h1v.s8.15c1c99e6461 from=translated src=- shape=4f331626 vocab=92ab173e
-/
@[simp]
theorem baseProjectionCLM_comp_baseSectionCLM (n : ℕ) :
    (baseProjectionCLM n).comp (baseSectionCLM n) =
      ContinuousLinearMap.id ℂ (ComplexEuclidean n) := by
  apply ContinuousLinearMap.ext
  intro z
  funext i
  simp

/-- Include a base germ as a germ independent of the last coordinate. -/
def lowerDimensionalInclusion (n : ℕ) :
    HolomorphicGerm n →+* HolomorphicGerm (n + 1) :=
  holomorphicGermPullbackHom (baseProjectionCLM n)

/-- Restrict an ambient germ to the zero-last-coordinate base section. -/
def lowerDimensionalRestriction (n : ℕ) :
    HolomorphicGerm (n + 1) →+* HolomorphicGerm n :=
  holomorphicGermPullbackHom (baseSectionCLM n)

/--
@isnad1 id=eq.1h2v.s13.1a7b858e26c3 from=translated src=- shape=601c6d41 vocab=2e0ff148
-/
@[simp]
theorem lowerDimensionalInclusion_ofFunction {n : ℕ}
    (f : ComplexEuclidean n → ℂ) (hf : AnalyticAt ℂ f 0) :
    lowerDimensionalInclusion n (HolomorphicGerm.ofFunction f hf) =
      HolomorphicGerm.ofFunction (f ∘ baseProjectionCLM n)
        (by
          have hf' : AnalyticAt ℂ f (baseProjectionCLM n 0) := by
            rw [map_zero]
            exact hf
          simpa using hf'.compContinuousLinearMap
            (u := baseProjectionCLM n) (x := 0)) :=
  holomorphicGermPullbackHom_ofFunction (baseProjectionCLM n) f hf

/--
@isnad1 id=eq.1h2v.s13.389a7ced4b0b from=translated src=- shape=3dd709a2 vocab=6a64260b
-/
@[simp]
theorem lowerDimensionalRestriction_ofFunction {n : ℕ}
    (f : ComplexEuclidean (n + 1) → ℂ) (hf : AnalyticAt ℂ f 0) :
    lowerDimensionalRestriction n (HolomorphicGerm.ofFunction f hf) =
      HolomorphicGerm.ofFunction (f ∘ baseSectionCLM n)
        (by
          have hf' : AnalyticAt ℂ f (baseSectionCLM n 0) := by
            rw [map_zero]
            exact hf
          simpa using hf'.compContinuousLinearMap
            (u := baseSectionCLM n) (x := 0)) :=
  holomorphicGermPullbackHom_ofFunction (baseSectionCLM n) f hf

/--
@isnad1 id=eq.0h2v.s12.ec1dd97bfd29 from=translated src=- shape=45677dd5 vocab=2ae6cf7c
-/
@[simp]
theorem evalAtOrigin_lowerDimensionalInclusion {n : ℕ}
    (φ : HolomorphicGerm n) :
    evalAtOrigin (lowerDimensionalInclusion n φ) = evalAtOrigin φ :=
  evalAtOrigin_holomorphicGermPullbackHom (baseProjectionCLM n) φ

/--
@isnad1 id=eq.0h2v.s13.fb2c8723459a from=translated src=- shape=dd7481ba vocab=720e76cd
-/
@[simp]
theorem evalAtOrigin_lowerDimensionalRestriction {n : ℕ}
    (φ : HolomorphicGerm (n + 1)) :
    evalAtOrigin (lowerDimensionalRestriction n φ) = evalAtOrigin φ :=
  evalAtOrigin_holomorphicGermPullbackHom (baseSectionCLM n) φ

/--
@isnad1 id=eq.0h1v.s12.3e2dd3dcd18e from=translated src=- shape=0ca63776 vocab=d2c99845
-/
@[simp]
theorem lowerDimensionalRestriction_comp_inclusion (n : ℕ) :
    (lowerDimensionalRestriction n).comp (lowerDimensionalInclusion n) =
      RingHom.id (HolomorphicGerm n) := by
  unfold lowerDimensionalRestriction lowerDimensionalInclusion
  rw [← holomorphicGermPullbackHom_comp,
    baseProjectionCLM_comp_baseSectionCLM, holomorphicGermPullbackHom_id]

/--
@isnad1 id=injectiv.0h1v.s13.f8672d53ed21 from=translated src=- shape=394f46cf vocab=70060ae4
-/
theorem lowerDimensionalInclusion_injective (n : ℕ) :
    Function.Injective (lowerDimensionalInclusion n) := by
  apply Function.LeftInverse.injective (g := lowerDimensionalRestriction n)
  intro φ
  change ((lowerDimensionalRestriction n).comp
    (lowerDimensionalInclusion n)) φ = φ
  rw [lowerDimensionalRestriction_comp_inclusion]
  rfl

/-- The germ of the last coordinate `w` on `ℂⁿ⁺¹`. -/
def lastCoordinateGerm (n : ℕ) : HolomorphicGerm (n + 1) :=
  HolomorphicGerm.ofFunction (lastCoordinateCLM n)
    ((lastCoordinateCLM n).analyticAt 0)

/--
@isnad1 id=eq.0h1v.s4.71ca6c2d9815 from=translated src=- shape=e018fdef vocab=f3b160dc
-/
@[simp]
theorem evalAtOrigin_lastCoordinateGerm (n : ℕ) :
    evalAtOrigin (lastCoordinateGerm n) = 0 := by
  simp [lastCoordinateGerm]

/--
@isnad1 id=eq.0h1v.s13.d357d06051d1 from=translated src=- shape=2676bed8 vocab=a1bdb70d
-/
@[simp]
theorem lowerDimensionalRestriction_lastCoordinateGerm (n : ℕ) :
    lowerDimensionalRestriction n (lastCoordinateGerm n) = 0 := by
  apply Subtype.ext
  apply Filter.Germ.coe_eq.mpr
  exact Filter.Eventually.of_forall fun z ↦ by
    simp

/-! ## The ambient germ ring as an algebra over the base germ ring -/

/-- The natural algebra structure induced by germs independent of the last coordinate. -/
instance holomorphicGermSuccAlgebra (n : ℕ) :
    Algebra (HolomorphicGerm n) (HolomorphicGerm (n + 1)) :=
  (lowerDimensionalInclusion n).toAlgebra

/--
@isnad1 id=eq.0h1v.s12.871f1edeb829 from=translated src=- shape=aa3af319 vocab=78fadd80
-/
@[simp]
theorem algebraMap_holomorphicGermSucc (n : ℕ) :
    algebraMap (HolomorphicGerm n) (HolomorphicGerm (n + 1)) =
      lowerDimensionalInclusion n :=
  rfl

/--
@isnad1 id=eq.0h2v.s14.098e801b5468 from=translated src=- shape=cf5d444e vocab=65ae507a
-/
@[simp]
theorem algebraMap_holomorphicGermSucc_apply (n : ℕ) (φ : HolomorphicGerm n) :
    algebraMap (HolomorphicGerm n) (HolomorphicGerm (n + 1)) φ =
      lowerDimensionalInclusion n φ :=
  rfl

/--
@isnad1 id=eq.0h3v.s14.10be418117bf from=translated src=- shape=83bf69dd vocab=127631fd
-/
theorem holomorphicGermSucc_smul_eq_mul (n : ℕ)
    (a : HolomorphicGerm n) (f : HolomorphicGerm (n + 1)) :
    a • f = lowerDimensionalInclusion n a * f :=
  rfl

end

end LocalComplexGeometry
