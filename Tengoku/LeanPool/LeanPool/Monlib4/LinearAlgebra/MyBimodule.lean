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

/--
@isnad1 id=eq.0h6v.s7.f5c5412b3742 from=translated src=- shape=cd51afc1 vocab=13a504b3
-/
theorem Bimodule.lsmul_apply (x a : H₁) (b : H₂) : x •ₗ a ⊗ₜ b = (x * a) ⊗ₜ[R] b :=
  rfl

/--
@isnad1 id=eq.0h6v.s7.a083c2d002d8 from=translated src=- shape=e485f8d7 vocab=c0830ea4
-/
theorem Bimodule.rsmul_apply (a : H₁) (x b : H₂) : a ⊗ₜ b •ᵣ x = a ⊗ₜ[R] (b * x) :=
  rfl

/--
@isnad1 id=eq.0h6v.s6.44118c56b116 from=translated src=- shape=2ce23408 vocab=293717c6
-/
theorem Bimodule.lsmul_rsmul_assoc (x : H₁) (y : H₂) (a : H₁ ⊗[R] H₂) :
    x •ₗ a •ᵣ y = x •ₗ (a •ᵣ y) := by
  simp_rw [Bimodule.lsmul, Bimodule.rsmul, ← LinearMap.comp_apply, ← TensorProduct.map_comp,
    LinearMap.one_comp, LinearMap.comp_one]

/--
@isnad1 id=eq.0h4v.s7.2ad5d54f390a from=translated src=- shape=46c2f4a0 vocab=2a8d19f7
-/
theorem Bimodule.lsmul_zero (x : H₁) : x •ₗ (0 : H₁ ⊗[R] H₂) = 0 :=
  rfl

/--
@isnad1 id=eq.0h4v.s7.9621639846eb from=translated src=- shape=d92a1e9f vocab=2a8d19f7
-/
theorem Bimodule.zero_lsmul (x : H₁ ⊗[R] H₂) : 0 •ₗ x = 0 := by
  rw [Bimodule.lsmul, LinearMap.mulLeft_zero_eq_zero, TensorProduct.map_zero_left,
    LinearMap.zero_apply]

/--
@isnad1 id=eq.0h4v.s7.aee26fc04de0 from=translated src=- shape=1abe177d vocab=d30874a4
-/
theorem Bimodule.zero_rsmul (x : H₂) : (0 : H₁ ⊗[R] H₂) •ᵣ x = 0 :=
  rfl

/--
@isnad1 id=eq.0h4v.s7.5c89a7734e4d from=translated src=- shape=aca24248 vocab=d30874a4
-/
theorem Bimodule.rsmul_zero (x : H₁ ⊗[R] H₂) : x •ᵣ 0 = 0 := by
  rw [Bimodule.rsmul, LinearMap.mulRight_zero_eq_zero, TensorProduct.map_zero_right,
    LinearMap.zero_apply]

/--
@isnad1 id=eq.0h6v.s8.75473c66ae53 from=translated src=- shape=c8958cb6 vocab=85d4bfbd
-/
theorem Bimodule.lsmul_add (x : H₁) (a b : H₁ ⊗[R] H₂) : x •ₗ (a + b) = x •ₗ a + x •ₗ b :=
  map_add _ _ _

/--
@isnad1 id=eq.0h6v.s8.386052595b6a from=translated src=- shape=56501aae vocab=b02c9d17
-/
theorem Bimodule.add_rsmul (x : H₂) (a b : H₁ ⊗[R] H₂) : (a + b) •ᵣ x = a •ᵣ x + b •ᵣ x :=
  map_add _ _ _

/--
@isnad1 id=eq.0h7v.s7.ff67b165edcf from=translated src=- shape=8f1e1f63 vocab=ff1976e3
-/
theorem Bimodule.lsmul_sum (x : H₁) {k : Type _} {s : Finset k} (a : k → H₁ ⊗[R] H₂) :
    x •ₗ ∑ i ∈ s, a i = ∑ i ∈ s, x •ₗ a i :=
  map_sum _ _ _

/--
@isnad1 id=eq.0h7v.s7.e319a196dbdc from=translated src=- shape=9ab4477a vocab=c78e754b
-/
theorem Bimodule.sum_rsmul (x : H₂) {k : Type _} {s : Finset k} (a : k → H₁ ⊗[R] H₂) :
    (∑ i ∈ s, a i) •ᵣ x = ∑ i ∈ s, a i •ᵣ x :=
  map_sum _ _ _

/--
@isnad1 id=eq.0h4v.s6.68b0773e299f from=translated src=- shape=b805ef4f vocab=2a8d19f7
-/
theorem Bimodule.one_lsmul (x : H₁ ⊗[R] H₂) : 1 •ₗ x = x := by
  rw [Bimodule.lsmul, LinearMap.mulLeft_one, ← Module.End.one_eq_id, TensorProduct.map_one,
    Module.End.one_apply]

/--
@isnad1 id=eq.0h4v.s6.cc188681c225 from=translated src=- shape=1ecb259b vocab=d30874a4
-/
theorem Bimodule.rsmul_one (x : H₁ ⊗[R] H₂) : x •ᵣ 1 = x := by
  rw [Bimodule.rsmul, LinearMap.mulRight_one, ← Module.End.one_eq_id, TensorProduct.map_one,
    Module.End.one_apply]

/--
@isnad1 id=eq.0h4v.s7.1188cf240e63 from=translated src=- shape=13366233 vocab=d5a61330
-/
theorem Bimodule.lsmul_one (x : H₁) : x •ₗ (1 : H₁ ⊗[R] H₂) = x ⊗ₜ 1 := by
  rw [Algebra.TensorProduct.one_def, Bimodule.lsmul_apply, mul_one]

/--
@isnad1 id=eq.0h4v.s7.ad79d37e4731 from=translated src=- shape=481fdf47 vocab=48b899d2
-/
theorem Bimodule.one_rsmul (x : H₂) : (1 : H₁ ⊗[R] H₂) •ᵣ x = 1 ⊗ₜ x := by
  rw [Algebra.TensorProduct.one_def, Bimodule.rsmul_apply, one_mul]

/--
@isnad1 id=eq.0h6v.s8.2d7e09640bef from=translated src=- shape=095f4fd3 vocab=cee8127b
-/
theorem Bimodule.lsmul_smul (α : R) (x : H₁) (a : H₁ ⊗[R] H₂) : x •ₗ α • a = α • (x •ₗ a) := by
  simp_rw [Bimodule.lsmul, _root_.map_smul]

/--
@isnad1 id=eq.0h6v.s8.d7a0d7746447 from=translated src=- shape=e0d5dd48 vocab=a7c343ae
-/
theorem Bimodule.smul_rsmul (α : R) (x : H₂) (a : H₁ ⊗[R] H₂) : α • a •ᵣ x = α • (a •ᵣ x) := by
  simp_rw [Bimodule.rsmul, _root_.map_smul]

/--
@isnad1 id=eq.0h6v.s6.baa3e4dc9c50 from=translated src=- shape=1bbe3599 vocab=d4639688
-/
theorem Bimodule.lsmul_lsmul (x y : H₁) (a : H₁ ⊗[R] H₂) : x •ₗ (y •ₗ a) = (x * y) •ₗ a := by
  simp_rw [Bimodule.lsmul, ← LinearMap.comp_apply, ← TensorProduct.map_comp,
    ← LinearMap.mulLeft_mul]
  rfl

/--
@isnad1 id=eq.0h6v.s6.7e0b194a04d4 from=translated src=- shape=b67db332 vocab=4bc0e842
-/
theorem Bimodule.rsmul_rsmul (x y : H₂) (a : H₁ ⊗[R] H₂) : a •ᵣ x •ᵣ y = a •ᵣ (x * y) := by
  simp_rw [Bimodule.rsmul, ← LinearMap.comp_apply, ← TensorProduct.map_comp,
    ← LinearMap.mulRight_mul]
  rfl

local notation "l(" x "," y ")" => y →ₗ[x] y

/-- A linear map commuting with the left and right tensor-factor actions. -/
def LinearMap.IsBimoduleMap (P : l(R,H₁ ⊗[R] H₂)) : Prop :=
  ∀ (x : H₁) (y : H₂) (a : H₁ ⊗[R] H₂), P (x •ₗ a •ᵣ y) = x •ₗ P a •ᵣ y

/--
@isnad1 id=eq.1h6v.s10.1b90b4a4f01d from=translated src=- shape=1ef30bdc vocab=039691c0
-/
theorem LinearMap.IsBimoduleMap.lsmul {P : l(R,H₁ ⊗[R] H₂)} (hP : P.IsBimoduleMap) (x : H₁)
    (a : H₁ ⊗[R] H₂) : P (x •ₗ a) = x •ₗ P a := by
  nth_rw 1 [← Bimodule.rsmul_one a]
  rw [← Bimodule.lsmul_rsmul_assoc, hP, Bimodule.rsmul_one]

/--
@isnad1 id=eq.1h6v.s10.30c434d05c42 from=translated src=- shape=ec6a5947 vocab=668f0a80
-/
theorem LinearMap.IsBimoduleMap.rsmul {P : l(R,H₁ ⊗[R] H₂)} (hP : P.IsBimoduleMap) (x : H₂)
    (a : H₁ ⊗[R] H₂) : P (a •ᵣ x) = P a •ᵣ x := by
  nth_rw 1 [← Bimodule.one_lsmul a]
  rw [hP, Bimodule.one_lsmul]

/--
@isnad1 id=isbimodu.2h5v.s10.530bad293cf0 from=translated src=- shape=dc6206d1 vocab=3ad15450
-/
theorem LinearMap.IsBimoduleMap.add {P Q : l(R,H₁ ⊗[R] H₂)} (hP : P.IsBimoduleMap)
    (hQ : Q.IsBimoduleMap) : (P + Q).IsBimoduleMap := by
  simp_rw [LinearMap.IsBimoduleMap, LinearMap.add_apply, Bimodule.lsmul_add, Bimodule.add_rsmul]
  intro x y a
  rw [hP, hQ]

/--
@isnad1 id=isbimodu.0h3v.s8.9d3955699fc1 from=translated src=- shape=3cae65e1 vocab=3d912226
-/
theorem LinearMap.isBimoduleMap.zero : (0 : l(R,H₁ ⊗[R] H₂)).IsBimoduleMap := by
  intro x y a
  simp_rw [LinearMap.zero_apply, Bimodule.lsmul_zero, Bimodule.zero_rsmul]

/--
@isnad1 id=isbimodu.1h5v.s9.51ebaf059672 from=translated src=- shape=d8e2211c vocab=603863ef
-/
theorem LinearMap.IsBimoduleMap.smul {x : l(R,H₁ ⊗[R] H₂)} (hx : x.IsBimoduleMap) (k : R) :
    (k • x).IsBimoduleMap := by
  intro x y a
  simp only [LinearMap.smul_apply, Bimodule.lsmul_smul, Bimodule.smul_rsmul]
  rw [hx]

/--
@isnad1 id=isbimodu.1h5v.s10.3214427f5656 from=translated src=- shape=5a2a5540 vocab=901a89d8
-/
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

/--
@isnad1 id=eq.0h5v.s14.f2b4874bf75d from=translated src=- shape=88cf5193 vocab=fb781824
-/
@[simp] lemma LinearMap.IsBimoduleMaps.coe_add (x y : IsBimoduleMaps R H₁ H₂) :
   ((x + y : IsBimoduleMaps R H₁ H₂) : H₁ ⊗[R] H₂ →ₗ[R] H₁ ⊗[R] H₂) = ↑x + ↑y := rfl
/--
@isnad1 id=eq.0h5v.s13.ad91e5df76dc from=translated src=- shape=d50103f6 vocab=db779f2f
-/
@[simp] lemma LinearMap.IsBimoduleMaps.coe_smul (x : IsBimoduleMaps R H₁ H₂)
  (r : R) :
   ((r • x : IsBimoduleMaps R H₁ H₂) : H₁ ⊗[R] H₂ →ₗ[R] H₁ ⊗[R] H₂) = r • ↑x := rfl
/--
@isnad1 id=eq.0h5v.s13.ed4d821d06af from=translated src=- shape=97466f3a vocab=5304b580
-/
@[simp] lemma LinearMap.IsBimoduleMaps.coe_nsmul (x : IsBimoduleMaps R H₁ H₂)
  (r : ℕ) :
   ((r • x : IsBimoduleMaps R H₁ H₂) : H₁ ⊗[R] H₂ →ₗ[R] H₁ ⊗[R] H₂) = r • ↑x := rfl
/--
@isnad1 id=eq.0h3v.s12.9aabf310d18a from=translated src=- shape=6e7358ed vocab=d47a2955
-/
@[simp] lemma LinearMap.IsBimoduleMaps.coe_zero :
   ((0 : IsBimoduleMaps R H₁ H₂) : H₁ ⊗[R] H₂ →ₗ[R] H₁ ⊗[R] H₂) = 0 := rfl

/--
@isnad1 id=eq.0h6v.s15.e5867f77db72 from=translated src=- shape=5d8506ea vocab=554e81c7
-/
theorem LinearMap.IsBimoduleMap.add_smul (a b : R) (x : (IsBimoduleMaps R H₁ H₂)) :
    (a + b) • x = a • x + b • x := by
  rw [← Subtype.coe_inj]
  simp_rw [IsBimoduleMaps.coe_smul, IsBimoduleMaps.coe_add, _root_.add_smul]
  rfl

/--
@isnad1 id=eq.0h6v.s13.d3fd73f4540c from=translated src=- shape=78c7fb45 vocab=ce77e14f
-/
theorem LinearMap.IsBimoduleMap.sum_coe {p : Type _} {s : Finset p}
  (x : p → (IsBimoduleMaps R H₁ H₂)) :
  (∑ i ∈ s, x i : IsBimoduleMaps R H₁ H₂).1 = ∑ i ∈ s, (x i).1 :=
Submodule.coe_sum _ _ _

/--
@isnad1 id=iff.0h4v.s10.bea236704e6d from=translated src=- shape=f9be9f2a vocab=9fbe4957
-/
@[simp]
theorem LinearMap.mem_isBimoduleMaps_iff {x : l(R,H₁ ⊗[R] H₂)} :
  x ∈ LinearMap.IsBimoduleMaps R H₁ H₂ ↔ x.IsBimoduleMap :=
by rfl
