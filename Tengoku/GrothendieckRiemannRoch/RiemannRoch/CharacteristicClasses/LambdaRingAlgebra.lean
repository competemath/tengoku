/-
Copyright (c) 2026 Guanghao Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guanghao Li
-/

import Tengoku.Seed.LinearAlgebra.TensorProduct.Graded.Internal
import Tengoku.Seed.LinearAlgebra.ExteriorAlgebra.Grading
import Tengoku.Seed.LinearAlgebra.ExteriorPower.Basic
import Tengoku.Seed.LinearAlgebra.TensorProduct.RightExactness

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Linear algebra for the `λ`-filtration of `Λ^n F`

For modules `K F Q` over a commutative ring with maps `f : K → F`, `g : F → Q`, and a retraction
`r : F → K` of `f` with `g ∘ f = 0`, we build

* `psi r g : Λ F →ₐ Λ K ⊗̂ Λ Q`, the algebra map induced by `m ↦ r m ⊗ 1 + 1 ⊗ g m` into the
  graded (Koszul-signed) tensor product;
* `rho i j r g : Λ F → Λ^i K ⊗ Λ^j Q`, its `(i, j)` component.

`rho` kills `Λ^{i+1} f(K) ∧ Λ F` (`rho_eq_zero_of_mem`) and restricts to `1 ⊗ Λ^j g` on
`Λ^i f(K) ∧ Λ^j F` (`rho_wedgeLin`). Together with the submodule calculus in the exterior algebra
(`mem_mul_of_map_eq_zero`: `ker Λ^{m+1} g = f(K) ∧ Λ^m F` for a split sequence), this is exactly
what is needed to identify the graded pieces of the filtration of `Λ^n F` by the images of
`Λ^i K ⊗ Λ^{n-i} F` with `Λ^i K ⊗ Λ^{n-i} Q`, with no choice of bases.
-/

set_option autoImplicit false

noncomputable section

open TensorProduct DirectSum

universe u

namespace SchemeKTheory.LambdaFiltration

variable {R : Type u} [CommRing R] {K F Q : Type u}
  [AddCommGroup K] [Module R K] [AddCommGroup F] [Module R F] [AddCommGroup Q] [Module R Q]

variable (R K Q) in
/-- The graded tensor product `Λ K ⊗̂ Λ Q`.-/
abbrev GT := GradedTensorProduct R (fun i : ℕ ↦ ⋀[R]^i K) (fun i : ℕ ↦ ⋀[R]^i Q)

lemma ι_mem_one {M : Type u} [AddCommGroup M] [Module R M] (m : M) :
    ExteriorAlgebra.ι R m ∈ ⋀[R]^1 M := by
  simpa only [pow_one] using LinearMap.mem_range_self _ m

/-- The degree-one part of `Ψ`.-/
def psiOne (r : F →ₗ[R] K) (g : F →ₗ[R] Q) : F →ₗ[R] GT R K Q :=
  (GradedTensorProduct.includeLeft (fun i : ℕ ↦ ⋀[R]^i K) (fun i : ℕ ↦ ⋀[R]^i Q)).toLinearMap ∘ₗ
      ExteriorAlgebra.ι R ∘ₗ r +
    (GradedTensorProduct.includeRight (fun i : ℕ ↦ ⋀[R]^i K)
      (fun i : ℕ ↦ ⋀[R]^i Q)).toLinearMap ∘ₗ ExteriorAlgebra.ι R ∘ₗ g

lemma psiOne_sq (r : F →ₗ[R] K) (g : F →ₗ[R] Q) (m : F) :
    psiOne r g m * psiOne r g m = 0 := by
  set a := ExteriorAlgebra.ι R (r m)
  set b := ExteriorAlgebra.ι R (g m)
  have h1 : psiOne r g m = a ᵍ⊗ₜ[R] (1 : ExteriorAlgebra R Q) +
      (1 : ExteriorAlgebra R K) ᵍ⊗ₜ[R] b := rfl
  rw [h1, add_mul, mul_add, mul_add]
  have e1 : (a ᵍ⊗ₜ[R] (1 : ExteriorAlgebra R Q) * a ᵍ⊗ₜ[R] (1 : ExteriorAlgebra R Q) :
      GT R K Q) = 0 := by
    rw [← GradedTensorProduct.includeLeft_apply, ← map_mul, ExteriorAlgebra.ι_sq_zero, map_zero]
  have e2 : ((1 : ExteriorAlgebra R K) ᵍ⊗ₜ[R] b * (1 : ExteriorAlgebra R K) ᵍ⊗ₜ[R] b :
      GT R K Q) = 0 := by
    rw [← GradedTensorProduct.includeRight_apply, ← map_mul, ExteriorAlgebra.ι_sq_zero, map_zero]
  have e3 : (a ᵍ⊗ₜ[R] (1 : ExteriorAlgebra R Q) * (1 : ExteriorAlgebra R K) ᵍ⊗ₜ[R] b :
      GT R K Q) = a ᵍ⊗ₜ[R] b :=
    GradedTensorProduct.tmul_one_mul_one_tmul _ _ a b
  have e4 : ((1 : ExteriorAlgebra R K) ᵍ⊗ₜ[R] b * a ᵍ⊗ₜ[R] (1 : ExteriorAlgebra R Q) :
      GT R K Q) = -(a ᵍ⊗ₜ[R] b) := by
    have := GradedTensorProduct.tmul_coe_mul_coe_tmul (R := R) (fun i : ℕ ↦ ⋀[R]^i K)
      (fun i : ℕ ↦ ⋀[R]^i Q) (1 : ExteriorAlgebra R K) (⟨b, ι_mem_one _⟩ : ⋀[R]^1 Q)
      (⟨a, ι_mem_one _⟩ : ⋀[R]^1 K) (1 : ExteriorAlgebra R Q)
    simp only [one_mul, mul_one] at this
    rw [this]
    simp
  rw [e1, e2, e3, e4]
  abel

/-- `Ψ : Λ F → Λ K ⊗̂ Λ Q`, induced by `m ↦ r m ⊗ 1 + 1 ⊗ g m`.-/
def psi (r : F →ₗ[R] K) (g : F →ₗ[R] Q) : ExteriorAlgebra R F →ₐ[R] GT R K Q :=
  ExteriorAlgebra.lift R ⟨psiOne r g, psiOne_sq r g⟩

/-- The augmentation kills positive exterior degrees.-/
lemma algebraMapInv_eq_zero {M : Type u} [AddCommGroup M] [Module R M] {i : ℕ} (hi : i ≠ 0)
    (a : ExteriorAlgebra R M) (ha : a ∈ ⋀[R]^i M) :
    ExteriorAlgebra.algebraMapInv a = 0 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hi
  rw [← exteriorPower.ιMulti_span_fixedDegree] at ha
  induction ha using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨v, rfl⟩ := hx
      rw [ExteriorAlgebra.ιMulti_succ_apply, map_mul]
      simp [ExteriorAlgebra.algebraMapInv]
  | zero => exact map_zero _
  | add x y _ _ hx hy => rw [map_add, hx, hy, add_zero]
  | smul c x _ hx => rw [map_smul, hx, smul_zero]

variable (R K Q) in
/-- `Θ : Λ K ⊗̂ Λ Q → Λ Q`, augmentation on the left factor.-/
def theta : GT R K Q →ₐ[R] ExteriorAlgebra R Q :=
  GradedTensorProduct.lift (fun i : ℕ ↦ ⋀[R]^i K) (fun i : ℕ ↦ ⋀[R]^i Q)
    ((Algebra.ofId R (ExteriorAlgebra R Q)).comp ExteriorAlgebra.algebraMapInv)
    (AlgHom.id R (ExteriorAlgebra R Q)) (by
      intro i j a b
      by_cases hi : i = 0
      · subst hi
        simp only [AlgHom.comp_apply, Algebra.ofId_apply, AlgHom.id_apply]
        rw [mul_zero, uzpow_zero, one_smul]
        exact Algebra.commutes (ExteriorAlgebra.algebraMapInv (a : ExteriorAlgebra R K))
          (b : ExteriorAlgebra R Q)
      · have h0 := algebraMapInv_eq_zero hi (a : ExteriorAlgebra R K) a.2
        simp [h0])

variable (R) in
/-- Projection of the exterior algebra onto its degree-`i` part.-/
def proj (M : Type u) [AddCommGroup M] [Module R M] (i : ℕ) :
    ExteriorAlgebra R M →ₗ[R] ⋀[R]^i M :=
  DirectSum.component R ℕ (fun i : ℕ ↦ ⋀[R]^i M) i ∘ₗ
    (decomposeLinearEquiv (fun i : ℕ ↦ ⋀[R]^i M)).toLinearMap

/-- The component map `Λ F → Λ^i K ⊗ Λ^j Q`.-/
def rho (i j : ℕ) (r : F →ₗ[R] K) (g : F →ₗ[R] Q) :
    ExteriorAlgebra R F →ₗ[R] ⋀[R]^i K ⊗[R] ⋀[R]^j Q :=
  TensorProduct.map (proj R K i) (proj R Q j) ∘ₗ
    (GradedTensorProduct.of R (fun i : ℕ ↦ ⋀[R]^i K) (fun i : ℕ ↦ ⋀[R]^i Q)).symm.toLinearMap ∘ₗ
      (psi r g).toLinearMap

/-! ### Exterior-algebra submodule calculus -/

lemma coe_exteriorPower_map {M N : Type u} [AddCommGroup M] [Module R M] [AddCommGroup N]
    [Module R N] (n : ℕ) (g : M →ₗ[R] N) (x : ⋀[R]^n M) :
    ((exteriorPower.map n g x : ⋀[R]^n N) : ExteriorAlgebra R N) =
      ExteriorAlgebra.map g (x : ExteriorAlgebra R M) := by
  have h : (⋀[R]^n N).subtype ∘ₗ exteriorPower.map n g =
      (ExteriorAlgebra.map g).toLinearMap ∘ₗ (⋀[R]^n M).subtype := by
    apply exteriorPower.linearMap_ext
    ext v
    simp [exteriorPower.map_apply_ιMulti, ExteriorAlgebra.map_apply_ιMulti]
  exact LinearMap.congr_fun h x

/-! ### The wedge maps `Λ^i K ⊗ Λ^j F → Λ^n F` -/

lemma map_mem_exteriorPower (f : K →ₗ[R] F) (i : ℕ) (a : ⋀[R]^i K) :
    ExteriorAlgebra.map f (a : ExteriorAlgebra R K) ∈ ⋀[R]^i F := by
  rw [← coe_exteriorPower_map]
  exact (exteriorPower.map i f a).2

/-- `κ ⊗ ω ↦ Λ^i f (κ) ∧ ω`.-/
def wedgeLin (f : K →ₗ[R] F) (i j n : ℕ) (h : i + j = n) :
    ⋀[R]^i K ⊗[R] ⋀[R]^j F →ₗ[R] ⋀[R]^n F :=
  LinearMap.codRestrict (⋀[R]^n F)
    (LinearMap.mul' R (ExteriorAlgebra R F) ∘ₗ
      TensorProduct.map ((ExteriorAlgebra.map f).toLinearMap ∘ₗ (⋀[R]^i K).subtype)
        (⋀[R]^j F).subtype) (by
      intro x
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul a b =>
          simp only [LinearMap.coe_comp, Function.comp_apply, TensorProduct.map_tmul,
            LinearMap.mul'_apply, AlgHom.toLinearMap_apply, Submodule.coe_subtype]
          rw [← h]
          exact SetLike.GradedMul.mul_mem (map_mem_exteriorPower f i a) b.2
      | add x y hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy)

@[simp]
lemma coe_wedgeLin_tmul (f : K →ₗ[R] F) (i j n : ℕ) (h : i + j = n) (a : ⋀[R]^i K)
    (b : ⋀[R]^j F) :
    ((wedgeLin f i j n h (a ⊗ₜ b) : ⋀[R]^n F) : ExteriorAlgebra R F) =
      ExteriorAlgebra.map f (a : ExteriorAlgebra R K) * (b : ExteriorAlgebra R F) := rfl

lemma lTensor_bijective_of_bijective {M N P : Type u} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] [AddCommGroup P] [Module R P] (φ : N →ₗ[R] P)
    (hφ : Function.Bijective φ) : Function.Bijective (LinearMap.lTensor M φ) := by
  have h : LinearMap.lTensor M φ = ((LinearEquiv.ofBijective φ hφ).lTensor M).toLinearMap := by
    rw [LinearEquiv.coe_lTensor]
    rfl
  rw [h]
  exact LinearEquiv.bijective _

end SchemeKTheory.LambdaFiltration
