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

public import Tengoku
import Tengoku.LeanPool.LeanPool.BrauerGroupNew.Centralizer
import Tengoku.LeanPool.LeanPool.BrauerGroupNew.TwoSidedIdeal
import Tengoku.LeanPool.LeanPool.BrauerGroupNew.Wedderburn
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
lemma _root_.IsCentralSimple.TensorProduct.left_tensor_base_sup_base_tensor_right
    (K B C : Type*) [CommRing K] [Ring B] [Algebra K B] [Ring C] [Algebra K C] :
    (Algebra.TensorProduct.map (AlgHom.id K B) (Algebra.ofId K C)).range ⊔
    (Algebra.TensorProduct.map (Algebra.ofId K B) (AlgHom.id K C)).range = ⊤ := by
  rw [eq_top_iff]
  rintro x -
  induction x using TensorProduct.inductionOn with
  | tmul b c =>
    rw [show b ⊗ₜ[K] c = b ⊗ₜ[K] 1 * 1 ⊗ₜ[K] c by simp]
    exact Algebra.mul_mem_sup ⟨b ⊗ₜ 1, by simp⟩ ⟨1 ⊗ₜ c, by simp⟩
  | add x y hx hy =>
    exact Subalgebra.add_mem _ hx hy
-- We need to restrict the universe, because we used properties of flatness.
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
lemma center_tensorProduct
    (B C : Type u) [Ring B] [Algebra K B] [Ring C] [Algebra K C] :
    Subalgebra.center K (B ⊗[K] C) =
      (Algebra.TensorProduct.map (Subalgebra.center K B).val
        (Subalgebra.center K C).val).range := by
  rw [show Subalgebra.center K (B ⊗[K] C) = Subalgebra.centralizer K (⊤ : Subalgebra K (B ⊗[K] C))
    by simp, ← TensorProduct.left_tensor_base_sup_base_tensor_right K B C,
    Subalgebra.centralizer_sup, Subalgebra.centralizer_tensorProduct_eq_center_tensorProduct_left,
    Subalgebra.centralizer_tensorProduct_eq_center_tensorProduct_right]
  suffices eq :
    Subalgebra.toSubmodule (Algebra.TensorProduct.map (Subalgebra.center K B).val (.id K C)).range ⊓
    Subalgebra.toSubmodule (Algebra.TensorProduct.map (.id K B) (Subalgebra.center K C).val).range =
    Subalgebra.toSubmodule (Algebra.TensorProduct.map (Subalgebra.center K B).val
      (Subalgebra.center K C).val).range by
    apply_fun Subalgebra.toSubmodule using Subalgebra.toSubmodule_injective
    simp_all
  have eq1 :
      Subalgebra.toSubmodule (Algebra.TensorProduct.map (Subalgebra.center K B).val (.id K C)).range
        = LinearMap.range (TensorProduct.map (Subalgebra.center K B).val.toLinearMap .id) := rfl
  rw [eq1]
  have eq2 :
      Subalgebra.toSubmodule (Algebra.TensorProduct.map (.id K B) (Subalgebra.center K C).val).range
        = LinearMap.range (TensorProduct.map .id (Subalgebra.center K C).val.toLinearMap) := rfl
  rw [eq2]
  have eq3 :
      Subalgebra.toSubmodule (Algebra.TensorProduct.map (Subalgebra.center K B).val
        (Subalgebra.center K C).val).range =
      LinearMap.range (TensorProduct.map (Subalgebra.center K B).val.toLinearMap
        (Subalgebra.center K C).val.toLinearMap) := by
    rfl
  rw [eq3]
  have := TensorProduct.submodule_tensor_inf_tensor_submodule K B C
    (Subalgebra.toSubmodule <| .center K B)
    (Subalgebra.toSubmodule <| .center K C)
  have eq4 : (Subalgebra.toSubmodule (Subalgebra.center K B)).subtype =
    (Subalgebra.center K B).val.toLinearMap := by rfl
  rw [eq4] at this
  have eq5 : (Subalgebra.toSubmodule (Subalgebra.center K C)).subtype =
    (Subalgebra.center K C).val.toLinearMap := by rfl
  simp_all

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

instance _root_.IsCentralSimple.TensorProduct.isCentral
    (A B : Type u) [Ring A] [Algebra K A] [Ring B] [Algebra K B]
    [isCentral_A : Algebra.IsCentral K A] [isCentral_B : Algebra.IsCentral K B] :
    Algebra.IsCentral K (A ⊗[K] B) := by
  constructor
  intro _ H
  obtain ⟨x, rfl⟩ := le_of_eq (center_tensorProduct K A B) H; clear H
  induction x using TensorProduct.inductionOn with
  | tmul a b =>
    obtain ⟨a', ha⟩ := isCentral_A.1 a.2
    obtain ⟨b', hb⟩ := isCentral_B.1 b.2
    refine ⟨b' * a', ?_⟩
    simp only [AlgHom.toRingHom_eq_coe, map_mul, RingHom.coe_coe, Algebra.TensorProduct.map_tmul,
      Subalgebra.coe_val, ← ha, ← hb]
    rw [Algebra.ofId_apply, Algebra.ofId_apply, Algebra.TensorProduct.algebraMap_apply',
      Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.tmul_mul_tmul]
    simp_all
  | add x y hx hy =>
    obtain ⟨kx, hx⟩ := hx
    obtain ⟨ky, hy⟩ := hy
    refine ⟨kx + ky, ?_⟩
    rw [map_add, hx, hy, map_add]
instance _root_.IsCentralSimple.TensorProduct.nontrivial
    (A B : Type v) [Ring A] [Algebra K A] [Ring B] [Algebra K B]
    [Nontrivial A] [Nontrivial B] :
    Nontrivial (A ⊗[K] B) := by
  refine ⟨0, 1, fun r ↦ ?_⟩
  let f : K ⊗[K] B →ₐ[K] A ⊗[K] B :=
    Algebra.TensorProduct.map (Algebra.ofId _ _) (.id _ _)
  have hf : Function.Injective f := Module.Flat.rTensor_preserves_injective_linearMap _
    (algebraMap K A).injective
  have r' : f 0 = f 1 := by rw [map_zero, map_one]; exact r
  specialize hf r'
  apply_fun Algebra.TensorProduct.lid K B at hf
  simp_all
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
instance baseChange
    (D L : Type u) [Ring D] [Algebra K D]
    [Field L] [Algebra K L]
    [h : Algebra.IsCentral K D] :
    Algebra.IsCentral L (L ⊗[K] D) where
  out:= by
    intro _ H
    obtain ⟨x, rfl⟩ := le_of_eq (center_tensorProduct K L D) H; clear H
    induction x using TensorProduct.inductionOn with
    | tmul l d =>
      obtain ⟨k, hk⟩ := h.out d.2
      refine ⟨k • l, ?_⟩
      simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.map_tmul,
        Subalgebra.coe_val, ← hk]
      simp only [Algebra.ofId_apply, Algebra.TensorProduct.algebraMap_apply,
        Algebra.algebraMap_self, RingHom.id_apply]
      rw [TensorProduct.smul_tmul, Algebra.algebraMap_eq_smul_one]
    | add x y hx hy =>
      obtain ⟨kx, (hkx : kx ⊗ₜ 1 = _)⟩ := hx
      obtain ⟨ky, (hky : ky ⊗ₜ 1 = _)⟩ := hy
      exact ⟨kx + ky, by simp only [AlgHom.toRingHom_eq_coe, map_add, RingHom.coe_coe,
        Algebra.ofId_apply, Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self,
        RingHom.id_apply, hkx, hky]⟩
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
