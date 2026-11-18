import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_Module_FaithfullyFlat_of_forall_isMaximal_exists_flat_algebra.lean`: wrote out 3 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 2 `p2m_export`, 1 `p2m_open`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_Module_FaithfullyFlat_of_forall_isMaximal_exists_flat_algebra

set_option maxHeartbeats 1600000

universe u v

namespace Module
export _root_.Module (Flat Injective mem_annihilator annihilator FaithfullyFlat Flat.lTensor_preserves_injective_linearMap FaithfullyFlat.iff_flat_and_proper_ideal Flat.rTensor_preserves_injective_linearMap Flat.iff_rTensor_injective')
namespace FaithfullyFlat
export _root_.Module.FaithfullyFlat (trans toFlat iff_flat_and_proper_ideal)
namespace LocalAlg
open _root_.Module.FaithfullyFlat open _root_.Module

open scoped TensorProduct

variable {B : Type u} [CommRing B]

/--
@isnad1 id=subsingl.1h2v.s8.ed3982bf010c from=translated src=- shape=45c41a08 vocab=2b8bd7a8
-/
theorem subsingleton_of_forall (Q : Type*) [AddCommGroup Q] [Module B Q]
    (h : ∀ (M : Ideal B), M.IsMaximal →
      ∃ (C : Type u) (_ : CommRing C) (_ : Algebra B C) (_ : Module.Flat B C),
        M.map (algebraMap B C) ≠ ⊤ ∧ Subsingleton (C ⊗[B] Q)) :
    Subsingleton Q := by
  refine ⟨fun q q' => ?_⟩
  rw [← sub_eq_zero]
  set x := q - q'
  by_contra hx
  let I : Ideal B := (Submodule.span B {x}).annihilator
  have hI : I ≠ ⊤ := by
    intro hI
    have h1 : (1 : B) ∈ I := by rw [hI]; trivial
    have := Submodule.mem_annihilator.1 h1 x (Submodule.mem_span_singleton_self x)
    rw [one_smul] at this
    exact hx this
  obtain ⟨M, hM, hIM⟩ := Ideal.exists_le_maximal I hI
  obtain ⟨C, _, _, _, hMC, hsub⟩ := h M hM
  let φ : (B ⧸ I) →ₗ[B] Q :=
    Submodule.liftQ I (LinearMap.toSpanSingleton B Q x) (by
      intro r hr
      rw [LinearMap.mem_ker, LinearMap.toSpanSingleton_apply]
      exact Submodule.mem_annihilator.1 hr x (Submodule.mem_span_singleton_self x))
  have hφ : Function.Injective φ := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro r hr
    induction r using Submodule.Quotient.induction_on with
    | H r =>
      rw [LinearMap.mem_ker, Submodule.liftQ_apply, LinearMap.toSpanSingleton_apply] at hr
      rw [Submodule.mem_bot, Submodule.Quotient.mk_eq_zero, Submodule.mem_annihilator]
      intro y hy
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hy
      rw [smul_comm, hr, smul_zero]
  have hφ1 : Function.Injective (LinearMap.lTensor C φ) := Module.Flat.lTensor_preserves_injective_linearMap φ hφ
  haveI : Subsingleton (C ⊗[B] (B ⧸ I)) := hφ1.subsingleton
  let ψ := Algebra.TensorProduct.quotIdealMapEquivTensorQuot C I
  haveI : Subsingleton (C ⧸ I.map (algebraMap B C)) := ψ.toEquiv.subsingleton
  have htop : I.map (algebraMap B C) = ⊤ := by
    rw [← Ideal.Quotient.subsingleton_iff]
    infer_instance
  exact hMC (top_le_iff.1 (htop ▸ Ideal.map_mono hIM))

/--
@isnad1 id=flat.1h2v.s8.002fc90a20fd from=translated src=- shape=00d537eb vocab=7fe9039f
-/
theorem flat_of_forall (H : Type*) [AddCommGroup H] [Module B H]
    (h : ∀ (M : Ideal B), M.IsMaximal →
      ∃ (C : Type u) (_ : CommRing C) (_ : Algebra B C) (_ : Module.Flat B C),
        M.map (algebraMap B C) ≠ ⊤ ∧ Module.Flat C (C ⊗[B] H)) :
    Module.Flat B H := by
  rw [Module.Flat.iff_rTensor_injective']
  intro I
  set f : ↥I ⊗[B] H →ₗ[B] B ⊗[B] H := LinearMap.rTensor H I.subtype
  rw [← LinearMap.ker_eq_bot]
  suffices hK : Subsingleton (LinearMap.ker f) by
    rw [eq_bot_iff]
    intro z hz
    have : (⟨z, hz⟩ : LinearMap.ker f) = 0 := Subsingleton.elim _ _
    exact congrArg Subtype.val this
  refine subsingleton_of_forall (B := B) (LinearMap.ker f) fun M hM => ?_
  obtain ⟨C, _, _, _, hMC, hflat⟩ := h M hM
  refine ⟨C, inferInstance, inferInstance, inferInstance, hMC, ?_⟩
  have hfp : Function.Injective (f.baseChange C) := by
    let θ₁ := TensorProduct.AlgebraTensorModule.distribBaseChange B C (↥I) H
    let θ₂ := TensorProduct.AlgebraTensorModule.distribBaseChange B C B H
    have hj : Function.Injective ((Submodule.subtype I).baseChange C) :=
      Module.Flat.lTensor_preserves_injective_linearMap _ I.injective_subtype
    have hg : Function.Injective (LinearMap.rTensor (C ⊗[B] H) ((Submodule.subtype I).baseChange C)) :=
      Module.Flat.rTensor_preserves_injective_linearMap _ hj
    have hsq : ∀ z, θ₂ (f.baseChange C z) = LinearMap.rTensor (C ⊗[B] H) ((Submodule.subtype I).baseChange C) (θ₁ z) := by
      intro z
      induction z using TensorProduct.induction_on with
      | zero => simp only [map_zero]
      | tmul b w =>
          induction w using TensorProduct.induction_on with
          | zero => simp only [TensorProduct.tmul_zero, map_zero]
          | tmul i x => rfl
          | add u v hu hv => simp only [TensorProduct.tmul_add, map_add, hu, hv]
      | add u v hu hv => simp only [map_add, hu, hv]
    intro z₁ z₂ hz
    apply θ₁.injective
    apply hg
    rw [← hsq, ← hsq, hz]
  have hinj : Function.Injective ((LinearMap.ker f).subtype.baseChange C) :=
    Module.Flat.lTensor_preserves_injective_linearMap _ (LinearMap.ker f).injective_subtype
  refine ⟨fun a b => hinj (hfp ?_)⟩
  have hz : ∀ t, f.baseChange C (((LinearMap.ker f).subtype.baseChange C) t) = 0 := by
    intro t
    rw [← LinearMap.comp_apply, ← LinearMap.baseChange_comp]
    have : f ∘ₗ (LinearMap.ker f).subtype = 0 := by ext ⟨z, hz⟩; exact hz
    rw [this, LinearMap.baseChange_zero, LinearMap.zero_apply]
  rw [hz, hz]

set_option maxHeartbeats 3200000 in
set_option synthInstance.maxHeartbeats 400000 in

/--
@isnad1 id=ne.2h4v.s8.f7a80a51a63b from=translated src=- shape=12750278 vocab=150b907d
-/
theorem smul_top_ne_top (H : Type*) [AddCommGroup H] [Module B H]
    (M : Ideal B) (C : Type u) [CommRing C] [Algebra B C]
    (hMC : M.map (algebraMap B C) ≠ ⊤) (hff : Module.FaithfullyFlat C (C ⊗[B] H)) :
    M • (⊤ : Submodule B H) ≠ ⊤ := by
  intro hMH
  apply ((Module.FaithfullyFlat.iff_flat_and_proper_ideal C (C ⊗[B] H)).1 hff).2 _ hMC
  rw [eq_top_iff]
  rintro z -
  induction z using TensorProduct.induction_on with
  | zero => exact Submodule.zero_mem _
  | tmul b x =>
      have hx : x ∈ M • (⊤ : Submodule B H) := by rw [hMH]; trivial
      induction hx using Submodule.smul_induction_on' with
      | smul a ha y _ =>
          rw [TensorProduct.tmul_smul, ← algebraMap_smul C a (b ⊗ₜ[B] y)]
          exact Submodule.smul_mem_smul (Ideal.mem_map_of_mem _ ha) Submodule.mem_top
      | add u _ v _ hu hv =>
          rw [TensorProduct.tmul_add]
          exact Submodule.add_mem _ hu hv
  | add u v hu hv => exact Submodule.add_mem _ hu hv

end Module.FaithfullyFlat.LocalAlg

/--
@isnad1 id=faithful.1h2v.s8.10b447e57e75 from=translated src=- shape=8205a1ba vocab=7ecfe2e5
-/
theorem solution
    (B : Type u) [CommRing B] (H : Type v) [AddCommGroup H] [Module B H]
    (h : ∀ (M : Ideal B), M.IsMaximal →
      ∃ (C : Type u) (_ : CommRing C) (_ : Algebra B C) (_ : Module.Flat B C),
        M.map (algebraMap B C) ≠ ⊤ ∧ Module.FaithfullyFlat C (TensorProduct B C H)) :
    Module.FaithfullyFlat B H := by
  have hflat : Module.Flat B H :=
    Module.FaithfullyFlat.LocalAlg.flat_of_forall (B := B) H (fun M hM => by
      obtain ⟨C, _, _, _, hMC, hff⟩ := h M hM
      exact ⟨C, inferInstance, inferInstance, inferInstance, hMC, hff.toFlat⟩)
  have key : ∀ (M : Ideal B), M.IsMaximal → M • (⊤ : Submodule B H) ≠ ⊤ := fun M hM => by
    obtain ⟨C, _, _, _, hMC, hff⟩ := h M hM
    exact Module.FaithfullyFlat.LocalAlg.smul_top_ne_top (B := B) H M C hMC hff
  exact (Module.FaithfullyFlat.iff_flat_and_proper_ideal B H).2
    ⟨hflat, fun I hI hIH => by
      obtain ⟨M, hM, hIM⟩ := Ideal.exists_le_maximal I hI
      exact key M hM (eq_top_iff.2 (hIH.symm.le.trans (Submodule.smul_mono_left hIM)))⟩
