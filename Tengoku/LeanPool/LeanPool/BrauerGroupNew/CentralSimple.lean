/-
Copyright (c) 2026 Yunzhou Xie and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yunzhou Xie, Yichen Feng, Jujian Zhang, Yael Dillies
-/
/-
Copyright (c) 2024 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yunzhou Xie, Jujian Zhang, Kevin Buzzard
-/
module

public import Tengoku.Seed.Algebra.Central.Defs
public import Tengoku.Seed.Data.Matrix.Basic
public import Tengoku.Seed.RingTheory.TensorProduct.Maps
public import Tengoku.Seed.RingTheory.TwoSidedIdeal.Operations
import Tengoku.LeanPool.LeanPool.BrauerGroupNew.Centralizer
import Tengoku.LeanPool.LeanPool.BrauerGroupNew.TwoSidedIdeal
import Tengoku.LeanPool.LeanPool.BrauerGroupNew.Wedderburn
import Tengoku.Seed.Algebra.Central.Basic
import Tengoku.Seed.Data.Rat.Floor
import Tengoku.Seed.RingTheory.Flat.Basic
import Tengoku.Seed.RingTheory.TwoSidedIdeal.BigOperators
import Tengoku.Seed.Tactic.Continuity.Init

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/
/-!
# Characteristic predicate for central simple algebras
In this file we define the predicate `IsCentralSimple K D` where `K` is a field
and `D` is a (noncommutative) `K`-algebra.
Note that the predicate makes sense just for `K` a `CommRing` but it doesn't give the
right definition; for a commutative ring base one should use the theory of Azumaya algebras.
This adds an extra layer of complication which we don't need. In fact ideals of `K`
immediately give rise to nontrivial quotients of `D` so there are no central simple
algebras in this case according to our definition.
-/

@[expose] public section
universe u v w
open Module
variable (K : Type u) [Field K]
open Matrix in
instance MatrixRing.isCentral (ι : Type) [Fintype ι] [DecidableEq ι] :
    Algebra.IsCentral K (Matrix ι ι K) where
  out _ h := mem_range_scalar_of_commute_single fun _ _ _ =>
    Subalgebra.mem_center_iff.mp h _
namespace IsCentralSimple
variable (D : Type v) [Ring D] [Algebra K D]
/-
\begin{lemma}
    \label{IsCentralSimple.baseChange}
    If DD is a central simple algebra over~KK and L/KL/K is a field extension, then L⊗KDL\otimes_KD
    is a central simple algebra over~LL.
\end{lemma}
\begin{proof}
    This is not too hard: it's lemma b of section 12.4 in Peirce's "Associative algebras".
    Will maybe write more on Saturday.
\end{proof}
-/
open scoped TensorProduct
instance instAlgebraSubtypeMemSubringCenterLeanPool (B : Type*) [Ring B] [Algebra K B] :
    Algebra K (Subring.center B) :=
  RingHom.toAlgebra <| (algebraMap K B).codRestrict _ fun x ↦ by
    rw [Subring.mem_center_iff]
    exact fun y ↦ Algebra.commutes x y |>.symm
lemma _root_.IsCentralSimple.TensorProduct.sum_tmul_basis_right_eq_zero'
    (B : Type*) [Ring B] [Algebra K B]
    (C : Type*) [Ring C] [Algebra K C]
    {ιC : Type*} (𝒞 : Basis ιC K C)
    (s : Finset ιC) (b : ιC → B)
    (h : ∑ i ∈ s, b i ⊗ₜ[K] 𝒞 i = 0) :
    ∀ i ∈ s, b i = 0 := by
  classical
  intro i
  have := TensorProduct.sum_tmul_basis_right_eq_zero (κ := ιC) 𝒞 (M := B)
    { support := s.filter fun i ↦ b i ≠ 0
      toFun x := if x ∈ s then b x else 0
      mem_support_toFun := by simp }
    (by
      simp only [Finsupp.sum, ne_eq, Finsupp.coe_mk, Finset.sum_filter, ite_not]
      convert h using 1
      congr!
      aesop)
  simpa using Finsupp.ext_iff.mp this i
lemma _root_.IsCentralSimple.TensorProduct.sum_tmul_basis_left_eq_zero'
    (B : Type*) [Ring B] [Algebra K B]
    (C : Type*) [Ring C] [Algebra K C]
    {ιB : Type*} (ℬ : Basis ιB K B)
    (s : Finset ιB) (c : ιB → C)
    (h : ∑ i ∈ s, ℬ i ⊗ₜ[K] c i = 0) :
    ∀ i ∈ s, c i = 0 := by
  apply TensorProduct.sum_tmul_basis_right_eq_zero' K C B ℬ s c
  apply_fun TensorProduct.comm K B C at h
  simpa using h
lemma _root_.IsCentralSimple.TensorProduct.submodule_tensor_inf_tensor_submodule
    (B C : Type u) [AddCommGroup B] [Module K B] [AddCommGroup C] [Module K C]
    (b : Submodule K B) (c : Submodule K C) :
    LinearMap.range (TensorProduct.map b.subtype .id) ⊓
    LinearMap.range (TensorProduct.map .id c.subtype) =
    LinearMap.range (TensorProduct.map b.subtype c.subtype) := by
  refine le_antisymm ?_ ?_
  · let : Module.Flat K (B ⧸ b) := Module.Flat.of_free
    let u : b ⊗[K] c →ₗ[K] B ⊗[K] c := TensorProduct.map b.subtype LinearMap.id
    let v : B ⊗[K] c →ₗ[K] (B ⧸ b) ⊗[K] c :=
      TensorProduct.map (Submodule.mkQ _) LinearMap.id
    have exactuv : Function.Exact u v := by
      apply rTensor_exact _ _ (Submodule.mkQ_surjective _)
      rw [LinearMap.exact_iff]
      simp only [Submodule.ker_mkQ, Submodule.range_subtype]
    let u' : b ⊗[K] C →ₗ[K] B ⊗[K] C := TensorProduct.map b.subtype LinearMap.id
    let v' : B ⊗[K] C →ₗ[K] (B ⧸ b) ⊗[K] C := TensorProduct.map (Submodule.mkQ _) LinearMap.id
    have exactu'v' : Function.Exact u' v' := by
      apply rTensor_exact _ _ (Submodule.mkQ_surjective _)
      rw [LinearMap.exact_iff]
      simp only [Submodule.ker_mkQ, Submodule.range_subtype]
    let α : b ⊗[K] c →ₗ[K] b ⊗[K] C := TensorProduct.map LinearMap.id c.subtype
    let β : B ⊗[K] c →ₗ[K] B ⊗[K] C := TensorProduct.map LinearMap.id c.subtype
    let γ : (B ⧸ b) ⊗[K] c →ₗ[K] (B ⧸ b) ⊗[K] C := TensorProduct.map LinearMap.id c.subtype
    have γ_inj : Function.Injective γ :=
      Module.Flat.iff_lTensor_preserves_injective_linearMap (R := K) (M := B ⧸ b)|>.1 inferInstance
        c.subtype c.injective_subtype
    rintro z (hz : z ∈ LinearMap.range u' ⊓ LinearMap.range β)
    obtain ⟨z, rfl⟩ := hz.2
    have comm0 : v' ∘ₗ β = γ ∘ₗ v := by
      ext
      simp [v', β, γ, v]
    have hz1 : v' (β z) = γ (v z) := congr($comm0 z)
    have hz2 : v' (β z) = 0 := by
      rw [← LinearMap.mem_ker]
      rw [LinearMap.exact_iff] at exactu'v'
      simp_all
    rw [hz2] at hz1
    have hz3 : v z ∈ LinearMap.ker γ := by rw [LinearMap.mem_ker]; exact hz1.symm
    replace hz3 : v z = 0 := by
      rw [← LinearMap.ker_eq_bot] at γ_inj; rw [γ_inj] at hz3; exact hz3
    replace hz3 : z ∈ LinearMap.ker v := hz3
    replace hz3 : z ∈ LinearMap.range u := by
      rw [LinearMap.exact_iff] at exactuv
      rwa [← exactuv]
    obtain ⟨z, rfl⟩ := hz3
    change (β ∘ₗ u) z ∈ _
    have comm1 : β ∘ₗ u = u' ∘ₗ α := by
      ext
      simp [β, u, u', α]
    rw [comm1, LinearMap.comp_apply]
    refine ⟨z, ?_⟩
    simp only [u', α]
    change _ = (TensorProduct.map b.subtype .id ∘ₗ TensorProduct.map .id c.subtype) z
    rw [← TensorProduct.map_comp, LinearMap.comp_id, LinearMap.id_comp]
  · rintro _ ⟨x, rfl⟩
    refine ⟨⟨TensorProduct.map LinearMap.id c.subtype x, ?_⟩,
      ⟨TensorProduct.map b.subtype LinearMap.id x, ?_⟩⟩
    · change (TensorProduct.map b.subtype LinearMap.id ∘ₗ
        TensorProduct.map LinearMap.id c.subtype) x = _
      rw [← TensorProduct.map_comp]
      rfl
    · change (TensorProduct.map LinearMap.id c.subtype ∘ₗ
        TensorProduct.map b.subtype LinearMap.id) x = _
      rw [← TensorProduct.map_comp]
      rfl
-- We need to restrict the universe, because we used properties of flatness.

/-- Linear map from the tensor product of centers into the tensor product algebra. -/
noncomputable def centerTensorCenter (B C : Type v) [Ring B] [Algebra K B] [Ring C] [Algebra K C] :
    (Subalgebra.center K B ⊗[K] Subalgebra.center K C) →ₗ[K] (B ⊗[K] C) :=
  TensorProduct.map (Subalgebra.val _).toLinearMap (Subalgebra.val _).toLinearMap
lemma centerTensorCenter_injective (B C : Type v) [Ring B] [Algebra K B] [Ring C] [Algebra K C] :
    Function.Injective (centerTensorCenter K B C) := by
  have : centerTensorCenter K B C =
    ((Subalgebra.center K B).val.toLinearMap.rTensor _) ∘ₗ
    ((Subalgebra.center K C).val.toLinearMap.lTensor _) := by
    ext; simp [centerTensorCenter]
  rw [this]
  apply Function.Injective.comp (g := (Subalgebra.center K B).val.toLinearMap.rTensor _)
  · apply Module.Flat.rTensor_preserves_injective_linearMap
    exact Subtype.val_injective
  · apply Module.Flat.lTensor_preserves_injective_linearMap
    exact Subtype.val_injective

variable {K} in
/--
a non-zero element in an ideal that can be represented as a sum of tensor products of `n`-terms.
-/
structure is_obtainable_by_sum_tmul
    {ιA A B : Type*} [Ring A] [Algebra K A] [Ring B] [Algebra K B]
    (x : A ⊗[K] B) (𝒜 : Basis ιA K A) (I : TwoSidedIdeal <| A ⊗[K] B) (n : ℕ) : Prop where
  mem : x ∈ I
  ne_zero : x ≠ 0
  rep : ∃ (s : Finset ιA) (_ : s.card = n) (f : ιA → B),
    x = ∑ i ∈ s, 𝒜 i ⊗ₜ[K] f i
end IsCentralSimple
section CSA_implies_CSA
variable (K : Type u) [Field K]
variable (B : Type*) [Ring B]
lemma top_eq_ring (R : Type*) [Ring R] : (⊤ : TwoSidedIdeal R) = (⊤ : Set R) := by
  aesop
lemma _root_.AlgEquiv.isCentral {K B C : Type*}
    [Field K] [Ring B] [Algebra K B]
    [hc : Algebra.IsCentral K B]
    [Ring C] [Algebra K C] (e : B ≃ₐ[K] C) :
    Algebra.IsCentral K C where
  out z hz := by
    obtain ⟨k, hk⟩ := hc.out (show e.symm z ∈ _ by
      simp only [Subalgebra.mem_center_iff] at hz ⊢
      exact fun x ↦ by simpa using congr(e.symm $(hz (e x))))
    exact ⟨k, by simpa [Algebra.ofId_apply] using congr(e $hk)⟩
theorem CSA_implies_CSA (K : Type*) (B : Type*) [Field K] [Ring B] [Algebra K B]
    (n : ℕ) (D : Type*) [NeZero n] (h : DivisionRing D) [Algebra K D]
    (Wdb : B ≃ₐ[K] (Matrix (Fin n) (Fin n) D)) [Algebra.IsCentral K B] :
    Algebra.IsCentral K D := by
  refine ⟨fun d hd => ?_⟩
  obtain ⟨k, hk⟩ := Wdb.isCentral.1
    (show (Matrix.diagonal fun _ ↦ d) ∈ _ by
      rw [Matrix.mem_center_iff']
      refine ⟨⟨d, hd⟩, ?_⟩
      ext i j
      simp only [Matrix.diagonal_apply, Matrix.smul_apply, Matrix.one_apply, smul_ite, smul_zero]
      split_ifs
      · change d = (⟨d, hd⟩ : Subalgebra.center K D).1 * (1 : D)
        simp
      · rfl)
  refine ⟨k, ?_⟩
  apply_fun (· 0 0) at hk
  simpa [Matrix.algebraMap_matrix_apply] using hk
end CSA_implies_CSA
