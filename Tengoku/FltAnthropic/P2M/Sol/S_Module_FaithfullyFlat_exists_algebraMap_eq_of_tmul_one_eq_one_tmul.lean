import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_Module_FaithfullyFlat_exists_algebraMap_eq_of_tmul_one_eq_one_tmul.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_reactivate`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_Module_FaithfullyFlat_exists_algebraMap_eq_of_tmul_one_eq_one_tmul

set_option autoImplicit false

universe u v

open TensorProduct

namespace AmitsurDegreeZero

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]

noncomputable def amitsurDelta (A : Type u) (B : Type v) [CommRing A] [CommRing B]
    [Algebra A B] : B →ₗ[A] B ⊗[A] B :=
  (TensorProduct.mk A B B).flip 1 - TensorProduct.mk A B B 1

/--
@isnad1 id=eq.0h3v.s9.1d7c01ad0f27 from=translated src=- shape=895ddfee vocab=f8e24ec8
-/
@[scoped simp] theorem amitsurDelta_apply (b : B) :
    amitsurDelta A B b = b ⊗ₜ[A] (1 : B) - (1 : B) ⊗ₜ[A] b := rfl

/--
@isnad1 id=eq.0h2v.s9.77f71aafdd0f from=translated src=- shape=80099438 vocab=ca307290
-/
theorem amitsurDelta_comp_linearMap : amitsurDelta A B ∘ₗ Algebra.linearMap A B = 0 := by
  ext
  simp [Algebra.algebraMap_eq_smul_one]

noncomputable def amitsurContraction (A : Type u) (B : Type v) [CommRing A] [CommRing B]
    [Algebra A B] : B ⊗[A] (B ⊗[A] B) →ₗ[A] B ⊗[A] B :=
  (LinearMap.mul' A B).rTensor B ∘ₗ (TensorProduct.assoc A B B B).symm.toLinearMap

/--
@isnad1 id=eq.0h3v.s12.d45d2f6797d9 from=translated src=- shape=b4453c66 vocab=d708c94a
-/
theorem amitsurContraction_lTensor_amitsurDelta (x : B ⊗[A] B) :
    amitsurContraction A B ((amitsurDelta A B).lTensor B x) =
      (LinearMap.mul' A B x) ⊗ₜ[A] (1 : B) - x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul b c =>
      simp [amitsurContraction, LinearMap.lTensor_tmul, TensorProduct.tmul_sub,
        TensorProduct.assoc_symm_tmul, LinearMap.rTensor_tmul, LinearMap.mul'_apply]
  | add x y hx hy =>
      simp only [map_add, hx, hy, TensorProduct.add_tmul]
      abel

/--
@isnad1 id=exact.0h2v.s11.0794ca16adac from=translated src=- shape=569af0b9 vocab=2642690b
-/
theorem exact_lTensor_linearMap_lTensor_amitsurDelta :
    Function.Exact ((Algebra.linearMap A B).lTensor B) ((amitsurDelta A B).lTensor B) := by
  intro x
  constructor
  · intro hx
    refine ⟨(LinearMap.mul' A B x) ⊗ₜ[A] (1 : A), ?_⟩
    have h := amitsurContraction_lTensor_amitsurDelta x
    rw [hx, map_zero, eq_comm, sub_eq_zero] at h
    rw [LinearMap.lTensor_tmul, Algebra.linearMap_apply, map_one, h]
  · rintro ⟨y, rfl⟩
    rw [← LinearMap.comp_apply, ← LinearMap.lTensor_comp, amitsurDelta_comp_linearMap,
      LinearMap.lTensor_zero, LinearMap.zero_apply]

/--
@isnad1 id=exact.0h2v.s9.a234e1c3b54a from=translated src=- shape=272d0bd1 vocab=7bc78109
-/
theorem exact_linearMap_amitsurDelta [Module.FaithfullyFlat A B] :
    Function.Exact (Algebra.linearMap A B) (amitsurDelta A B) :=
  (Module.FaithfullyFlat.lTensor_exact_iff_exact A B _ _).mp
    exact_lTensor_linearMap_lTensor_amitsurDelta

end AmitsurDegreeZero
open scoped _root_.P2MW.S_Module_FaithfullyFlat_exists_algebraMap_eq_of_tmul_one_eq_one_tmul.AmitsurDegreeZero

/--
@isnad1 id=ex.1h3v.s8.9cb9d2b8d2af from=translated src=- shape=de0ccc05 vocab=4f5e8bb4
-/
theorem solution
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    [Module.FaithfullyFlat A B] {b : B} (hb : b ⊗ₜ[A] (1 : B) = (1 : B) ⊗ₜ[A] b) :
    ∃ a : A, algebraMap A B a = b := by
  obtain ⟨a, ha⟩ := ((AmitsurDegreeZero.exact_linearMap_amitsurDelta (A := A) (B := B)) b).mp
    (by rw [AmitsurDegreeZero.amitsurDelta_apply, hb, sub_self])
  exact ⟨a, ha⟩
