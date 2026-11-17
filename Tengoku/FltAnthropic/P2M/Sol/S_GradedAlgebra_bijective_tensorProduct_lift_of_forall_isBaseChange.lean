import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_GradedAlgebra_bijective_tensorProduct_lift_of_forall_isBaseChange.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_reactivate`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_GradedAlgebra_bijective_tensorProduct_lift_of_forall_isBaseChange

set_option autoImplicit false

open TensorProduct DirectSum

universe u

namespace GradedBaseChange

variable {S : Type u} [CommRing S] (T : Type u) [CommRing T] [Algebra S T]
  (A : Type u) [CommRing A] [Algebra S A] (𝓐 : ℕ → Submodule S A) [GradedAlgebra 𝓐]
  (B : Type u) [CommRing B] [Algebra T B] [Algebra S B] [IsScalarTower S T B]
  (𝓑 : ℕ → Submodule T B) [GradedAlgebra 𝓑]
  (ϑ : A →ₐ[S] B) (hϑdeg : ∀ n, ∀ x ∈ 𝓐 n, ϑ x ∈ 𝓑 n)

abbrev piece (n : ℕ) : 𝓐 n →ₗ[S] (𝓑 n).restrictScalars S :=
  ϑ.toLinearMap.restrict (p := 𝓐 n) (q := (𝓑 n).restrictScalars S) (hϑdeg n)

abbrev φ : A ⊗[S] T →ₐ[S] B :=
  Algebra.TensorProduct.lift ϑ (IsScalarTower.toAlgHom S T B) (fun _ _ => Commute.all _ _)

/--
@isnad1 id=eq.0h7v.s9.d75301280302 from=translated src=- shape=68943376 vocab=1c7ebe69
-/
theorem φ_tmul (a : A) (t : T) : φ T A B ϑ (a ⊗ₜ[S] t) = t • ϑ a := by
  rw [Algebra.TensorProduct.lift_tmul, IsScalarTower.coe_toAlgHom', Algebra.smul_def, mul_comm]

noncomputable def incl (n : ℕ) : T ⊗[S] ↥(𝓐 n) →ₗ[S] A ⊗[S] T :=
  (TensorProduct.map (𝓐 n).subtype LinearMap.id) ∘ₗ (TensorProduct.comm S T ↥(𝓐 n)).toLinearMap

/--
@isnad1 id=eq.0h7v.s11.c8ef0c321ea8 from=translated src=- shape=0d8805e8 vocab=a9b96f2a
-/
@[scoped simp] theorem incl_tmul (n : ℕ) (t : T) (a : 𝓐 n) : incl T A 𝓐 n (t ⊗ₜ[S] a) = (a : A) ⊗ₜ[S] t := by
  simp [incl]

/--
@isnad1 id=eq.0h9v.s12.240dea1d59c0 from=translated src=- shape=1a97da10 vocab=9de06f65
-/
theorem φ_incl_smul (n : ℕ) (t : T) (z : T ⊗[S] ↥(𝓐 n)) :
    φ T A B ϑ (incl T A 𝓐 n (t • z)) = t • φ T A B ϑ (incl T A 𝓐 n z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul t' a =>
    rw [TensorProduct.smul_tmul', incl_tmul, incl_tmul, φ_tmul, φ_tmul, smul_eq_mul, mul_smul]
  | add x y hx hy => simp only [smul_add, map_add, hx, hy]

variable (hbc : ∀ n, IsBaseChange T (piece T A 𝓐 B 𝓑 ϑ hϑdeg n))

noncomputable def ψn (n : ℕ) : ↥(𝓑 n) →ₗ[S] A ⊗[S] T :=
  (incl T A 𝓐 n) ∘ₗ (((hbc n).equiv.symm.toLinearMap.restrictScalars S) ∘ₗ
    ({ toFun := fun x => ⟨x.1, x.2⟩, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl } :
      ↥(𝓑 n) →ₗ[S] ↥((𝓑 n).restrictScalars S)))

noncomputable def ψ : B →ₗ[S] A ⊗[S] T :=
  (DirectSum.toModule S ℕ (A ⊗[S] T) (ψn T A 𝓐 B 𝓑 ϑ hϑdeg hbc)) ∘ₗ
    ((DirectSum.decomposeLinearEquiv 𝓑).toLinearMap.restrictScalars S)

/--
@isnad1 id=eq.3h9v.s11.a1df836cf0b6 from=translated src=- shape=549ae1b5 vocab=f1decdc5
-/
theorem ψ_of_mem {b : B} {n : ℕ} (hb : b ∈ 𝓑 n) :
    ψ T A 𝓐 B 𝓑 ϑ hϑdeg hbc b = ψn T A 𝓐 B 𝓑 ϑ hϑdeg hbc n ⟨b, hb⟩ := by
  simp only [ψ, LinearMap.comp_apply, LinearMap.restrictScalars_apply, LinearEquiv.coe_toLinearMap,
    DirectSum.decomposeLinearEquiv_apply, DirectSum.decompose_of_mem 𝓑 hb]
  exact DirectSum.toModule_lof (M := fun n => ↥(𝓑 n)) S n (⟨b, hb⟩ : ↥(𝓑 n))

/--
@isnad1 id=eq.2h9v.s13.a42ec3396d5e from=translated src=- shape=2e7e3c04 vocab=9ba7e7f8
-/
theorem φ_ψn (n : ℕ) (x : ↥((𝓑 n).restrictScalars S)) :
    φ T A B ϑ (incl T A 𝓐 n ((hbc n).equiv.symm x)) = (x : B) := by
  induction x using (hbc n).inductionOn with
  | zero => simp
  | tmul m =>
    rw [IsBaseChange.equiv_symm_apply, incl_tmul, φ_tmul, one_smul]
    rfl
  | smul t y hy =>
    rw [LinearEquiv.map_smul, φ_incl_smul, hy]
    rfl
  | add y₁ y₂ h₁ h₂ =>
    rw [map_add, map_add, map_add, h₁, h₂]
    rfl

/--
@isnad1 id=eq.2h8v.s10.53dae9112183 from=translated src=- shape=8fe09499 vocab=177bd864
-/
theorem φ_ψ (b : B) : φ T A B ϑ (ψ T A 𝓐 B 𝓑 ϑ hϑdeg hbc b) = b := by
  classical
  conv_rhs => rw [← DirectSum.sum_support_decompose 𝓑 b]
  conv_lhs => rw [← DirectSum.sum_support_decompose 𝓑 b]
  rw [map_sum, map_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [ψ_of_mem T A 𝓐 B 𝓑 ϑ hϑdeg hbc (DirectSum.decompose 𝓑 b n).2]
  exact φ_ψn T A 𝓐 B 𝓑 ϑ hϑdeg hbc n ⟨_, (DirectSum.decompose 𝓑 b n).2⟩

/--
@isnad1 id=eq.3h10v.s10.17b18ad13409 from=translated src=- shape=a5d66bf5 vocab=b0910258
-/
theorem ψ_φ_tmul_of_mem {a : A} {n : ℕ} (ha : a ∈ 𝓐 n) (t : T) :
    ψ T A 𝓐 B 𝓑 ϑ hϑdeg hbc (φ T A B ϑ (a ⊗ₜ[S] t)) = a ⊗ₜ[S] t := by
  rw [φ_tmul]
  have hmem : t • ϑ a ∈ 𝓑 n := Submodule.smul_mem _ _ (hϑdeg n a ha)
  rw [ψ_of_mem T A 𝓐 B 𝓑 ϑ hϑdeg hbc hmem]
  have heq : (⟨t • ϑ a, hmem⟩ : ↥((𝓑 n).restrictScalars S)) = t • piece T A 𝓐 B 𝓑 ϑ hϑdeg n ⟨a, ha⟩ := rfl
  simp only [ψn, LinearMap.comp_apply, LinearMap.restrictScalars_apply, LinearEquiv.coe_toLinearMap]
  change incl T A 𝓐 n ((hbc n).equiv.symm (⟨t • ϑ a, hmem⟩ : ↥((𝓑 n).restrictScalars S))) = a ⊗ₜ[S] t
  rw [heq, LinearEquiv.map_smul, IsBaseChange.equiv_symm_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one,
    incl_tmul]

/--
@isnad1 id=eq.2h8v.s10.42adfa28c5dc from=translated src=- shape=46ce7cf1 vocab=177bd864
-/
theorem ψ_φ (z : A ⊗[S] T) : ψ T A 𝓐 B 𝓑 ϑ hϑdeg hbc (φ T A B ϑ z) = z := by
  classical
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a t =>
    conv_lhs => rw [← DirectSum.sum_support_decompose 𝓐 a]
    conv_rhs => rw [← DirectSum.sum_support_decompose 𝓐 a]
    rw [TensorProduct.sum_tmul, map_sum, map_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    exact ψ_φ_tmul_of_mem T A 𝓐 B 𝓑 ϑ hϑdeg hbc (DirectSum.decompose 𝓐 a n).2 t
  | add x y hx hy => rw [map_add, map_add, hx, hy]

end GradedBaseChange
open scoped _root_.P2MW.S_GradedAlgebra_bijective_tensorProduct_lift_of_forall_isBaseChange.GradedBaseChange

open GradedBaseChange in
/--
@isnad1 id=bijectiv.2h7v.s10.a4a90b8d7cec from=translated src=- shape=a855bc7f vocab=518db677
-/
theorem solution
    {S : Type u} [CommRing S] (T : Type u) [CommRing T] [Algebra S T]
    (A : Type u) [CommRing A] [Algebra S A] (𝓐 : ℕ → Submodule S A) [GradedAlgebra 𝓐]
    (B : Type u) [CommRing B] [Algebra T B] [Algebra S B] [IsScalarTower S T B]
    (𝓑 : ℕ → Submodule T B) [GradedAlgebra 𝓑]
    (ϑ : A →ₐ[S] B) (hϑdeg : ∀ n, ∀ x ∈ 𝓐 n, ϑ x ∈ 𝓑 n)
    (hbc : ∀ n, IsBaseChange T ((ϑ.toLinearMap.restrict (p := 𝓐 n) (q := (𝓑 n).restrictScalars S) (hϑdeg n))
      : 𝓐 n →ₗ[S] (𝓑 n).restrictScalars S)) :
    Function.Bijective
      (Algebra.TensorProduct.lift ϑ (IsScalarTower.toAlgHom S T B) (fun _ _ => Commute.all _ _) : A ⊗[S] T →ₐ[S] B) := by
  refine ⟨fun x y hxy => ?_, fun b => ⟨ψ T A 𝓐 B 𝓑 ϑ hϑdeg hbc b, φ_ψ T A 𝓐 B 𝓑 ϑ hϑdeg hbc b⟩⟩
  have := congrArg (ψ T A 𝓐 B 𝓑 ϑ hϑdeg hbc) hxy
  rwa [ψ_φ, ψ_φ] at this
