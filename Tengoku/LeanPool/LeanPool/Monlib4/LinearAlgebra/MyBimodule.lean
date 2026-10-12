/-
Copyright (c) 2023 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
module

public import Tengoku
public import Tengoku.LeanPool.LeanPool.Monlib4.LinearAlgebra.LmulRmul
import Tengoku.LeanPool.LeanPool.Monlib4.LinearAlgebra.End
import Tengoku.LeanPool.LeanPool.Monlib4.LinearAlgebra.TensorProduct.BasicLemmas
import Tengoku.LeanPool.LeanPool.Monlib4.Preq.Finset

/-!
# (A-A)-Bimodules

We define (A-A)-bimodules, where A is a commutative semiring, and show basic
properties of them.
-/

@[expose] public section

variable {R H₁ H₂ : Type _} [CommSemiring R] [Semiring H₁] [Semiring H₂] [Algebra R H₁]
  [Algebra R H₂]

open scoped TensorProduct

local notation x " ⊗ₘ " y => TensorProduct.map x y

/-- Left multiplication on the left tensor factor. -/
noncomputable def Bimodule.lsmul (x : H₁) (y : H₁ ⊗[R] H₂) : H₁ ⊗[R] H₂ :=
  (LinearMap.mulLeft R x ⊗ₘ 1) y

/-- Right multiplication on the right tensor factor. -/
noncomputable def Bimodule.rsmul (x : H₁ ⊗[R] H₂) (y : H₂) : H₁ ⊗[R] H₂ :=
  (1 ⊗ₘ LinearMap.mulRight R y) x

/-- Scoped notation for left multiplication on the left tensor factor. -/
scoped[Bimodule] infixl:72 " •ₗ " => Bimodule.lsmul

/-- Scoped notation for right multiplication on the right tensor factor. -/
scoped[Bimodule] infixl:72 " •ᵣ " => Bimodule.rsmul

open scoped Bimodule BigOperators

theorem Bimodule.lsmul_apply (x a : H₁) (b : H₂) : x •ₗ a ⊗ₜ b = (x * a) ⊗ₜ[R] b :=
  rfl

theorem Bimodule.rsmul_apply (a : H₁) (x b : H₂) : a ⊗ₜ b •ᵣ x = a ⊗ₜ[R] (b * x) :=
  rfl

theorem Bimodule.lsmul_rsmul_assoc (x : H₁) (y : H₂) (a : H₁ ⊗[R] H₂) :
    x •ₗ a •ᵣ y = x •ₗ (a •ᵣ y) := by
  simp_rw [Bimodule.lsmul, Bimodule.rsmul, ← LinearMap.comp_apply, ← TensorProduct.map_comp,
    LinearMap.one_comp, LinearMap.comp_one]

theorem Bimodule.lsmul_zero (x : H₁) : x •ₗ (0 : H₁ ⊗[R] H₂) = 0 :=
  rfl

theorem Bimodule.zero_lsmul (x : H₁ ⊗[R] H₂) : 0 •ₗ x = 0 := by
  rw [Bimodule.lsmul, LinearMap.mulLeft_zero_eq_zero, TensorProduct.map_zero_left,
    LinearMap.zero_apply]

theorem Bimodule.zero_rsmul (x : H₂) : (0 : H₁ ⊗[R] H₂) •ᵣ x = 0 :=
  rfl

theorem Bimodule.rsmul_zero (x : H₁ ⊗[R] H₂) : x •ᵣ 0 = 0 := by
  rw [Bimodule.rsmul, LinearMap.mulRight_zero_eq_zero, TensorProduct.map_zero_right,
    LinearMap.zero_apply]

theorem Bimodule.lsmul_add (x : H₁) (a b : H₁ ⊗[R] H₂) : x •ₗ (a + b) = x •ₗ a + x •ₗ b :=
  map_add _ _ _

theorem Bimodule.add_rsmul (x : H₂) (a b : H₁ ⊗[R] H₂) : (a + b) •ᵣ x = a •ᵣ x + b •ᵣ x :=
  map_add _ _ _

theorem Bimodule.lsmul_sum (x : H₁) {k : Type _} {s : Finset k} (a : k → H₁ ⊗[R] H₂) :
    x •ₗ ∑ i ∈ s, a i = ∑ i ∈ s, x •ₗ a i :=
  map_sum _ _ _

theorem Bimodule.sum_rsmul (x : H₂) {k : Type _} {s : Finset k} (a : k → H₁ ⊗[R] H₂) :
    (∑ i ∈ s, a i) •ᵣ x = ∑ i ∈ s, a i •ᵣ x :=
  map_sum _ _ _

theorem Bimodule.one_lsmul (x : H₁ ⊗[R] H₂) : 1 •ₗ x = x := by
  rw [Bimodule.lsmul, LinearMap.mulLeft_one, ← Module.End.one_eq_id, TensorProduct.map_one,
    Module.End.one_apply]

theorem Bimodule.rsmul_one (x : H₁ ⊗[R] H₂) : x •ᵣ 1 = x := by
  rw [Bimodule.rsmul, LinearMap.mulRight_one, ← Module.End.one_eq_id, TensorProduct.map_one,
    Module.End.one_apply]

theorem Bimodule.lsmul_one (x : H₁) : x •ₗ (1 : H₁ ⊗[R] H₂) = x ⊗ₜ 1 := by
  rw [Algebra.TensorProduct.one_def, Bimodule.lsmul_apply, mul_one]

theorem Bimodule.one_rsmul (x : H₂) : (1 : H₁ ⊗[R] H₂) •ᵣ x = 1 ⊗ₜ x := by
  rw [Algebra.TensorProduct.one_def, Bimodule.rsmul_apply, one_mul]

theorem Bimodule.lsmul_smul (α : R) (x : H₁) (a : H₁ ⊗[R] H₂) : x •ₗ α • a = α • (x •ₗ a) := by
  simp_rw [Bimodule.lsmul, _root_.map_smul]

theorem Bimodule.smul_rsmul (α : R) (x : H₂) (a : H₁ ⊗[R] H₂) : α • a •ᵣ x = α • (a •ᵣ x) := by
  simp_rw [Bimodule.rsmul, _root_.map_smul]

theorem Bimodule.lsmul_lsmul (x y : H₁) (a : H₁ ⊗[R] H₂) : x •ₗ (y •ₗ a) = (x * y) •ₗ a := by
  simp_rw [Bimodule.lsmul, ← LinearMap.comp_apply, ← TensorProduct.map_comp,
    ← LinearMap.mulLeft_mul]
  rfl

theorem Bimodule.rsmul_rsmul (x y : H₂) (a : H₁ ⊗[R] H₂) : a •ᵣ x •ᵣ y = a •ᵣ (x * y) := by
  simp_rw [Bimodule.rsmul, ← LinearMap.comp_apply, ← TensorProduct.map_comp,
    ← LinearMap.mulRight_mul]
  rfl

local notation "l(" x "," y ")" => y →ₗ[x] y

/-- A linear map commuting with the left and right tensor-factor actions. -/
def LinearMap.IsBimoduleMap (P : l(R,H₁ ⊗[R] H₂)) : Prop :=
  ∀ (x : H₁) (y : H₂) (a : H₁ ⊗[R] H₂), P (x •ₗ a •ᵣ y) = x •ₗ P a •ᵣ y

theorem LinearMap.IsBimoduleMap.lsmul {P : l(R,H₁ ⊗[R] H₂)} (hP : P.IsBimoduleMap) (x : H₁)
    (a : H₁ ⊗[R] H₂) : P (x •ₗ a) = x •ₗ P a := by
  nth_rw 1 [← Bimodule.rsmul_one a]
  rw [← Bimodule.lsmul_rsmul_assoc, hP, Bimodule.rsmul_one]

theorem LinearMap.IsBimoduleMap.rsmul {P : l(R,H₁ ⊗[R] H₂)} (hP : P.IsBimoduleMap) (x : H₂)
    (a : H₁ ⊗[R] H₂) : P (a •ᵣ x) = P a •ᵣ x := by
  nth_rw 1 [← Bimodule.one_lsmul a]
  rw [hP, Bimodule.one_lsmul]

theorem LinearMap.IsBimoduleMap.add {P Q : l(R,H₁ ⊗[R] H₂)} (hP : P.IsBimoduleMap)
    (hQ : Q.IsBimoduleMap) : (P + Q).IsBimoduleMap := by
  simp_rw [LinearMap.IsBimoduleMap, LinearMap.add_apply, Bimodule.lsmul_add, Bimodule.add_rsmul]
  intro x y a
  rw [hP, hQ]

theorem LinearMap.isBimoduleMap.zero : (0 : l(R,H₁ ⊗[R] H₂)).IsBimoduleMap := by
  intro x y a
  simp_rw [LinearMap.zero_apply, Bimodule.lsmul_zero, Bimodule.zero_rsmul]

theorem LinearMap.IsBimoduleMap.smul {x : l(R,H₁ ⊗[R] H₂)} (hx : x.IsBimoduleMap) (k : R) :
    (k • x).IsBimoduleMap := by
  intro x y a
  simp only [LinearMap.smul_apply, Bimodule.lsmul_smul, Bimodule.smul_rsmul]
  rw [hx]

theorem LinearMap.IsBimoduleMap.nsmul {x : l(R,H₁ ⊗[R] H₂)} (hx : x.IsBimoduleMap) (k : ℕ) :
    (k • x).IsBimoduleMap := by
  intro x y a
  simp only [LinearMap.smul_apply, ← Nat.cast_smul_eq_nsmul R k,
    Bimodule.lsmul_smul, Bimodule.smul_rsmul]
  rw [hx]

/-- The submodule of bimodule endomorphisms of a tensor product. -/
noncomputable def LinearMap.IsBimoduleMaps (R H₁ H₂ : Type _) [CommSemiring R]
  [Semiring H₁] [Semiring H₂] [Algebra R H₁] [Algebra R H₂] :
    Submodule R (l(R, H₁ ⊗[R] H₂)) where
  carrier x := x.IsBimoduleMap
  add_mem' x y := x.add y
  zero_mem' := LinearMap.isBimoduleMap.zero
  smul_mem' r _ x := x.smul r

-- { x : l(R,H₁ ⊗[R] H₂) // x.IsBimoduleMap }

@[simp] lemma LinearMap.IsBimoduleMaps.coe_add (x y : IsBimoduleMaps R H₁ H₂) :
   ((x + y : IsBimoduleMaps R H₁ H₂) : H₁ ⊗[R] H₂ →ₗ[R] H₁ ⊗[R] H₂) = ↑x + ↑y := rfl
@[simp] lemma LinearMap.IsBimoduleMaps.coe_smul (x : IsBimoduleMaps R H₁ H₂)
  (r : R) :
   ((r • x : IsBimoduleMaps R H₁ H₂) : H₁ ⊗[R] H₂ →ₗ[R] H₁ ⊗[R] H₂) = r • ↑x := rfl
@[simp] lemma LinearMap.IsBimoduleMaps.coe_nsmul (x : IsBimoduleMaps R H₁ H₂)
  (r : ℕ) :
   ((r • x : IsBimoduleMaps R H₁ H₂) : H₁ ⊗[R] H₂ →ₗ[R] H₁ ⊗[R] H₂) = r • ↑x := rfl
@[simp] lemma LinearMap.IsBimoduleMaps.coe_zero :
   ((0 : IsBimoduleMaps R H₁ H₂) : H₁ ⊗[R] H₂ →ₗ[R] H₁ ⊗[R] H₂) = 0 := rfl

theorem LinearMap.IsBimoduleMap.add_smul (a b : R) (x : (IsBimoduleMaps R H₁ H₂)) :
    (a + b) • x = a • x + b • x := by
  rw [← Subtype.coe_inj]
  simp_rw [IsBimoduleMaps.coe_smul, IsBimoduleMaps.coe_add, _root_.add_smul]
  rfl

theorem LinearMap.IsBimoduleMap.sum_coe {p : Type _} {s : Finset p}
  (x : p → (IsBimoduleMaps R H₁ H₂)) :
  (∑ i ∈ s, x i : IsBimoduleMaps R H₁ H₂).1 = ∑ i ∈ s, (x i).1 :=
Submodule.coe_sum _ _ _

@[simp]
theorem LinearMap.mem_isBimoduleMaps_iff {x : l(R,H₁ ⊗[R] H₂)} :
  x ∈ LinearMap.IsBimoduleMaps R H₁ H₂ ↔ x.IsBimoduleMap :=
by rfl
