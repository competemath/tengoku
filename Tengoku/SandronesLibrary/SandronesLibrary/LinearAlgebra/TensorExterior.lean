/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.SandronesLibrary.SandronesLibrary.LinearAlgebra.VectorSpace
import Tengoku.Seed.LinearAlgebra.Dual.Lemmas
import Tengoku.Seed.LinearAlgebra.Dual.Basis
import Tengoku.Seed.LinearAlgebra.Contraction
import Tengoku.Seed.LinearAlgebra.ExteriorAlgebra.Basic
import Tengoku.Seed.LinearAlgebra.ExteriorPower.Basis
import Tengoku.Seed.LinearAlgebra.TensorProduct.Basis

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# 对偶空间、张量积与外代数

本模块建立经典微分几何和微分形式所需的线性代数前置。教材层接口依次包括：

* 对偶空间、自然配对、双对偶评价映射以及有限维情形的维数公式；
* 张量积中的纯张量、双线性关系、由双线性映射诱导的线性映射以及自然缩并；
* 外代数中的向量楔积、反交换律和交替多重线性形式。

张量积不是“所有元素都是纯张量”的集合，而是由纯张量的有限和生成并满足双线性
关系的向量空间。外代数进一步施加 `v ∧ v = 0`，由此得到楔积的反交换性。

> **Entry**: linear-algebra.tensor-exterior
-/

noncomputable section

namespace SandronesLibrary.LinearAlgebra.TensorExterior

open SandronesLibrary.LinearAlgebra.VectorSpace
open scoped TensorProduct

universe u v w x

variable (K : Type u) [Field K]

/-! ## 对偶空间 -/

/-- 向量空间 `V` 的对偶空间：所有从 `V` 到标量域 `K` 的线性泛函。-/
abbrev DualSpace (V : Type v) [AddCommGroup V] [LinearSpace K V] := V →ₗ[K] K

instance dualLinearSpace (V : Type v) [AddCommGroup V] [LinearSpace K V] :
    LinearSpace K (DualSpace K V) where
  toModule := inferInstance

/-- 对偶空间与原空间之间的自然配对 `(φ,v) ↦ φ(v)`。-/
def dualPairing {V : Type v} [AddCommGroup V] [LinearSpace K V] :
    DualSpace K V →ₗ[K] V →ₗ[K] K := LinearMap.id

/--
@isnad1 id=eq.0h4v.s9.fde854ce8f36 from=translated src=- shape=086280db vocab=2c773f88
-/
@[simp] theorem dualPairing_apply {V : Type v} [AddCommGroup V] [LinearSpace K V]
    (φ : DualSpace K V) (v : V) : dualPairing K φ v = φ v := rfl

/-- 对偶空间与原空间具有相同维数。
@isnad1 id=eq.0h2v.s6.ba55d5458b7b from=translated src=- shape=68107c96 vocab=428f66a9
-/
theorem dim_dual_eq_dim {V : Type v} [AddCommGroup V] [LinearSpace K V] :
    dim K (DualSpace K V) = dim K V := by
  exact Subspace.dual_finrank_eq

/-- 把向量 `v` 送到双对偶中的“在 `v` 处取值”泛函。-/
def doubleDualEvaluation {V : Type v} [AddCommGroup V] [LinearSpace K V] :
    V →ₗ[K] DualSpace K (DualSpace K V) := Module.Dual.eval K V

/--
@isnad1 id=eq.0h4v.s10.eeb14b80d3ce from=translated src=- shape=77f6b1c1 vocab=91837472
-/
@[simp] theorem doubleDualEvaluation_apply {V : Type v}
    [AddCommGroup V] [LinearSpace K V] (v : V) (φ : DualSpace K V) :
    doubleDualEvaluation K v φ = φ v := rfl

/-- 有限维向量空间自然同构于其双对偶；这里先记录自然评价映射的双射性。
@isnad1 id=bijectiv.0h2v.s10.a0bdebf3cf0a from=translated src=- shape=a9a10440 vocab=bae04e25
-/
theorem doubleDualEvaluation_bijective {V : Type v}
    [AddCommGroup V] [LinearSpace K V] [IsFiniteDimensional K V] :
    Function.Bijective (doubleDualEvaluation K (V := V)) := by
  exact Module.bijective_dual_eval K V

/-- 有限基存在唯一的对偶基；其配对矩阵为单位矩阵。
@isnad1 id=ex.1h4v.s8.52bd82328265 from=translated src=- shape=b2561b51 vocab=d90aea10
-/
theorem exists_dual_basis {V : Type v} [AddCommGroup V] [LinearSpace K V]
    {n : ℕ} (b : Fin n → V) (hb : IsBasis K b) :
    ∃ φ : Fin n → DualSpace K V,
      IsBasis K φ ∧ ∀ i j, φ i (b j) = if i = j then 1 else 0 := by
  let B : Module.Basis (Fin n) K V := Module.Basis.mk hb.1 (by simpa [hb.2])
  refine ⟨B.dualBasis, ?_, ?_⟩
  · exact ⟨B.dualBasis.linearIndependent, B.dualBasis.span_eq⟩
  · intro i j
    simpa [B, eq_comm] using B.dualBasis_apply_self i j

/-! ## 张量积 -/

/-- `V` 与 `W` 在 `K` 上的张量积。-/
abbrev TensorSpace (V : Type v) (W : Type w)
    [AddCommGroup V] [LinearSpace K V] [AddCommGroup W] [LinearSpace K W] :=
  TensorProduct K V W

instance tensorLinearSpace (V : Type v) (W : Type w)
    [AddCommGroup V] [LinearSpace K V] [AddCommGroup W] [LinearSpace K W] :
    LinearSpace K (TensorSpace K V W) where
  toModule := inferInstance

/-- 有限维张量积的维数是两个因子维数的乘积。
@isnad1 id=eq.0h3v.s6.d697f6fae597 from=translated src=- shape=688a1a80 vocab=2155fbf8
-/
theorem dim_tensor_eq_mul {V : Type v} {W : Type w}
    [AddCommGroup V] [LinearSpace K V] [AddCommGroup W] [LinearSpace K W] :
    dim K (TensorSpace K V W) = dim K V * dim K W := by
  exact Module.finrank_tensorProduct

/-- 向量 `v,w` 生成的纯张量 `v ⊗ w`。-/
def pureTensor {V : Type v} {W : Type w}
    [AddCommGroup V] [LinearSpace K V] [AddCommGroup W] [LinearSpace K W]
    (v : V) (w : W) : TensorSpace K V W := v ⊗ₜ[K] w

/-- 两组有限基的逐对纯张量构成张量积的一组基。
@isnad1 id=isbasis.2h7v.s7.e03aca4c90b9 from=translated src=- shape=b21ef85a vocab=ccb80916
-/
theorem tensor_product_basis {V : Type v} {W : Type w}
    [AddCommGroup V] [LinearSpace K V] [AddCommGroup W] [LinearSpace K W]
    {n m : ℕ} (b : Fin n → V) (c : Fin m → W)
    (hb : IsBasis K b) (hc : IsBasis K c) :
    IsBasis K (fun p : Fin n × Fin m => pureTensor K (b p.1) (c p.2)) := by
  let B : Module.Basis (Fin n) K V := Module.Basis.mk hb.1 (by simpa [hb.2])
  let C : Module.Basis (Fin m) K W := Module.Basis.mk hc.1 (by simpa [hc.2])
  let D := B.tensorProduct C
  have hB (i : Fin n) : B i = b i := by simp [B]
  have hC (j : Fin m) : C j = c j := by simp [C]
  have hD (p : Fin n × Fin m) :
      D p = pureTensor K (b p.1) (c p.2) := by
    rw [show D p = B p.1 ⊗ₜ[K] C p.2 by
      exact Module.Basis.tensorProduct_apply' B C p]
    rw [hB, hC]
    rfl
  rw [← funext hD]
  exact ⟨D.linearIndependent, D.span_eq⟩

/--
@isnad1 id=eq.0h6v.s7.2b4a11d0afaf from=translated src=- shape=69882ae4 vocab=1f00bc1b
-/
@[simp] theorem pureTensor_add_left {V : Type v} {W : Type w}
    [AddCommGroup V] [LinearSpace K V] [AddCommGroup W] [LinearSpace K W]
    (v₁ v₂ : V) (w : W) :
    pureTensor K (v₁ + v₂) w = pureTensor K v₁ w + pureTensor K v₂ w := by
  exact TensorProduct.add_tmul v₁ v₂ w

/--
@isnad1 id=eq.0h6v.s7.5417c669dca6 from=translated src=- shape=8a9f5076 vocab=1f00bc1b
-/
@[simp] theorem pureTensor_add_right {V : Type v} {W : Type w}
    [AddCommGroup V] [LinearSpace K V] [AddCommGroup W] [LinearSpace K W]
    (v : V) (w₁ w₂ : W) :
    pureTensor K v (w₁ + w₂) = pureTensor K v w₁ + pureTensor K v w₂ := by
  exact TensorProduct.tmul_add v w₁ w₂

/--
@isnad1 id=eq.0h6v.s7.f341c516236c from=translated src=- shape=fdd101cc vocab=58cec264
-/
@[simp] theorem pureTensor_smul_left {V : Type v} {W : Type w}
    [AddCommGroup V] [LinearSpace K V] [AddCommGroup W] [LinearSpace K W]
    (a : K) (v : V) (w : W) : pureTensor K (a • v) w = a • pureTensor K v w := by
  exact TensorProduct.smul_tmul' a v w

/--
@isnad1 id=eq.0h6v.s7.cb984bce4025 from=translated src=- shape=299693bb vocab=58cec264
-/
@[simp] theorem pureTensor_smul_right {V : Type v} {W : Type w}
    [AddCommGroup V] [LinearSpace K V] [AddCommGroup W] [LinearSpace K W]
    (a : K) (v : V) (w : W) : pureTensor K v (a • w) = a • pureTensor K v w := by
  exact TensorProduct.tmul_smul a v w

/-- 张量积的泛性质：双线性映射 `B : V × W → X` 唯一诱导出张量积上的线性映射。-/
def tensorLift {V : Type v} {W : Type w} {X : Type x}
    [AddCommGroup V] [LinearSpace K V] [AddCommGroup W] [LinearSpace K W]
    [AddCommGroup X] [LinearSpace K X] (B : V →ₗ[K] W →ₗ[K] X) :
    TensorSpace K V W →ₗ[K] X := TensorProduct.lift B

/--
@isnad1 id=eq.0h7v.s10.c725288d507d from=translated src=- shape=50a6883e vocab=1eb8ada8
-/
@[simp] theorem tensorLift_pureTensor {V : Type v} {W : Type w} {X : Type x}
    [AddCommGroup V] [LinearSpace K V] [AddCommGroup W] [LinearSpace K W]
    [AddCommGroup X] [LinearSpace K X] (B : V →ₗ[K] W →ₗ[K] X) (v : V) (w : W) :
    tensorLift K B (pureTensor K v w) = B v w := by
  exact TensorProduct.lift.tmul v w

/-- 对偶向量与向量张量的自然缩并 `φ ⊗ v ↦ φ(v)`。-/
def dualTensorContraction {V : Type v} [AddCommGroup V] [LinearSpace K V] :
    TensorSpace K (DualSpace K V) V →ₗ[K] K := contractLeft K V

/--
@isnad1 id=eq.0h4v.s10.7c976723a2aa from=translated src=- shape=0926ec03 vocab=5ce037e3
-/
@[simp] theorem dualTensorContraction_pureTensor {V : Type v}
    [AddCommGroup V] [LinearSpace K V] (φ : DualSpace K V) (v : V) :
    dualTensorContraction K (pureTensor K φ v) = φ v := by
  exact contractLeft_apply φ v

/-! ## 外代数与向量楔积 -/

/-- 向量空间的外代数；乘法就是楔积。-/
abbrev ExteriorSpace (V : Type v) [AddCommGroup V] [LinearSpace K V] :=
  ExteriorAlgebra K V

/-- `V` 的 `k` 次外幂，即外代数的 `k` 次齐次分量。-/
abbrev ExteriorPowerSpace (V : Type v) [AddCommGroup V] [LinearSpace K V]
    (k : ℕ) := ⋀[K]^k V

instance exteriorPowerLinearSpace (V : Type v)
    [AddCommGroup V] [LinearSpace K V] (k : ℕ) :
    LinearSpace K (ExteriorPowerSpace K V k) where
  toModule := inferInstance

/-- `n` 维空间的 `k` 次外幂维数为二项式系数 `C(n,k)`。
@isnad1 id=eq.0h3v.s10.5b7d0a75568a from=translated src=- shape=250feebf vocab=8a7da6e2
-/
theorem dim_exteriorPower_eq_choose {V : Type v}
    [AddCommGroup V] [LinearSpace K V] [IsFiniteDimensional K V] (k : ℕ) :
    dim K (ExteriorPowerSpace K V k) = Nat.choose (dim K V) k := by
  exact exteriorPower.finrank_eq K k

/-- 把一次向量嵌入外代数。-/
def exteriorVector {V : Type v} [AddCommGroup V] [LinearSpace K V] :
    V →ₗ[K] ExteriorSpace K V := ExteriorAlgebra.ι K

/-- 外代数中任意两个元素的楔积。与只接受两个一次向量的 `vectorWedge` 不同，
该运算可以继续接受已经形成的高次外代数元素。-/
def exteriorWedge {V : Type v} [AddCommGroup V] [LinearSpace K V]
    (a b : ExteriorSpace K V) : ExteriorSpace K V := a * b

/-- 楔积满足结合律，因此多重楔积无需依赖括号的选择。
@isnad1 id=eq.0h5v.s6.4bb2512a032e from=translated src=- shape=562698be vocab=2876b445
-/
@[simp] theorem exteriorWedge_assoc {V : Type v} [AddCommGroup V] [LinearSpace K V]
    (a b c : ExteriorSpace K V) :
    exteriorWedge K (exteriorWedge K a b) c =
      exteriorWedge K a (exteriorWedge K b c) := by
  exact mul_assoc a b c

/--
@isnad1 id=eq.0h5v.s8.4cf671af7d20 from=translated src=- shape=61afb97d vocab=07bdb964
-/
@[simp] theorem exteriorWedge_add_left {V : Type v} [AddCommGroup V] [LinearSpace K V]
    (a b c : ExteriorSpace K V) :
    exteriorWedge K (a + b) c = exteriorWedge K a c + exteriorWedge K b c := by
  exact add_mul a b c

/--
@isnad1 id=eq.0h5v.s8.52212b062ded from=translated src=- shape=781b7f8b vocab=07bdb964
-/
@[simp] theorem exteriorWedge_add_right {V : Type v} [AddCommGroup V] [LinearSpace K V]
    (a b c : ExteriorSpace K V) :
    exteriorWedge K a (b + c) = exteriorWedge K a b + exteriorWedge K a c := by
  exact mul_add a b c

/-- 两个向量的楔积。-/
def vectorWedge {V : Type v} [AddCommGroup V] [LinearSpace K V]
    (v w : V) : ExteriorSpace K V := exteriorVector K v * exteriorVector K w

/-- 两个向量的楔积就是它们嵌入外代数之后的普通楔积。
@isnad1 id=eq.0h4v.s10.6dbd88f4a75a from=translated src=- shape=8c5b6a7f vocab=4766e0b4
-/
theorem vectorWedge_eq_exteriorWedge {V : Type v} [AddCommGroup V] [LinearSpace K V]
    (v w : V) :
    vectorWedge K v w = exteriorWedge K (exteriorVector K v) (exteriorVector K w) :=
  rfl

/-- 三个向量的楔积结合律：`(u ∧ v) ∧ w = u ∧ (v ∧ w)`。
@isnad1 id=eq.0h5v.s10.5e35955731de from=translated src=- shape=32cc928b vocab=4766e0b4
-/
theorem vectorWedge_assoc {V : Type v} [AddCommGroup V] [LinearSpace K V]
    (u v w : V) :
    exteriorWedge K (vectorWedge K u v) (exteriorVector K w) =
      exteriorWedge K (exteriorVector K u) (vectorWedge K v w) := by
  exact exteriorWedge_assoc K _ _ _

/--
@isnad1 id=eq.0h3v.s7.4a1dfff0a27e from=translated src=- shape=f4561be9 vocab=ccbe7b6f
-/
@[simp] theorem vectorWedge_self {V : Type v} [AddCommGroup V] [LinearSpace K V]
    (v : V) : vectorWedge K v v = 0 := ExteriorAlgebra.ι_sq_zero v

/--
@isnad1 id=eq.0h4v.s7.2654a3b4c514 from=translated src=- shape=823b26d1 vocab=3259c0a7
-/
theorem vectorWedge_swap {V : Type v} [AddCommGroup V] [LinearSpace K V]
    (v w : V) : vectorWedge K v w = -vectorWedge K w v := by
  apply eq_neg_of_add_eq_zero_left
  exact ExteriorAlgebra.ι_add_mul_swap v w

/--
@isnad1 id=eq.0h5v.s7.2fce29312c4a from=translated src=- shape=b9854911 vocab=6ed901a5
-/
@[simp] theorem vectorWedge_add_left {V : Type v} [AddCommGroup V] [LinearSpace K V]
    (u v w : V) : vectorWedge K (u + v) w = vectorWedge K u w + vectorWedge K v w := by
  simp [vectorWedge, exteriorVector, add_mul]

/--
@isnad1 id=eq.0h5v.s7.08c443833edb from=translated src=- shape=75362ca4 vocab=6ed901a5
-/
@[simp] theorem vectorWedge_add_right {V : Type v} [AddCommGroup V] [LinearSpace K V]
    (u v w : V) : vectorWedge K u (v + w) = vectorWedge K u v + vectorWedge K u w := by
  simp [vectorWedge, exteriorVector, mul_add]

/--
@isnad1 id=eq.0h5v.s7.608737e7cef8 from=translated src=- shape=d3643d92 vocab=c9f0f464
-/
@[simp] theorem vectorWedge_smul_left {V : Type v} [AddCommGroup V] [LinearSpace K V]
    (a : K) (v w : V) : vectorWedge K (a • v) w = a • vectorWedge K v w := by
  simp [vectorWedge, exteriorVector]

/--
@isnad1 id=eq.0h5v.s7.80877eea40ea from=translated src=- shape=683328c5 vocab=c9f0f464
-/
@[simp] theorem vectorWedge_smul_right {V : Type v} [AddCommGroup V] [LinearSpace K V]
    (a : K) (v w : V) : vectorWedge K v (a • w) = a • vectorWedge K v w := by
  simp [vectorWedge, exteriorVector]

/-! ## 交替形式 -/

/-- `V` 上的 `k` 次交替形式，即取值于标量域的交替 `k` 重线性映射。-/
abbrev AlternatingForm (V : Type v) [AddCommGroup V] [LinearSpace K V] (k : ℕ) :=
  V [⋀^Fin k]→ₗ[K] K

/--
@isnad1 id=eq.2h7v.s7.cc9a45435c92 from=translated src=- shape=300b6bfb vocab=5c1ef2ad
-/
theorem alternatingForm_eq_zero_of_repeat {V : Type v} [AddCommGroup V] [LinearSpace K V]
    {k : ℕ} (ω : AlternatingForm K V k) (v : Fin k → V) {i j : Fin k}
    (hij : i ≠ j) (hrepeat : v i = v j) : ω v = 0 := by
  exact ω.map_eq_zero_of_eq v hrepeat hij

end SandronesLibrary.LinearAlgebra.TensorExterior
