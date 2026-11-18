import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_AlgebraicGeometry_TwoChartCech

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_Module_exists_forall_isUnit_surjective_baseChange_of_surjective_baseChange_residueField.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_Module_exists_forall_isUnit_surjective_baseChange_of_surjective_baseChange_residueField

set_option autoImplicit false

universe u

open TensorProduct

namespace K4FSurjSpread

variable {R : Type u} [CommRing R] {M N : Type u} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

/--
@isnad1 id=surjecti.1h5v.s9.c64324d7f9df from=translated src=- shape=19baaf61 vocab=01f0c8aa
-/
theorem lTensor_surjective_of_subsingleton (f : M →ₗ[R] N) (A : Type u) [AddCommGroup A] [Module R A]
    (h : Subsingleton (A ⊗[R] (N ⧸ LinearMap.range f))) : Function.Surjective (f.lTensor A) := by
  have ex := lTensor_exact A (LinearMap.exact_map_mkQ_range f) (Submodule.mkQ_surjective _)
  rw [← LinearMap.range_eq_top, ← ex.linearMap_ker_eq, LinearMap.ker_eq_top]
  ext x
  exact Subsingleton.elim _ _

/--
@isnad1 id=subsingl.2h4v.s7.d9327c2665c9 from=translated src=- shape=d8bb8869 vocab=28a36cbc
-/
theorem subsingleton_tensor_of_smul_eq_zero (Q : Type u) [AddCommGroup Q] [Module R Q] (g : R)
    (hg : ∀ q : Q, g • q = 0) (A : Type u) [CommRing A] [Algebra R A] (hu : IsUnit (algebraMap R A g)) :
    Subsingleton (A ⊗[R] Q) := by
  refine ⟨fun x y => ?_⟩
  suffices h0 : ∀ z : A ⊗[R] Q, z = 0 by rw [h0 x, h0 y]
  intro z
  induction z using TensorProduct.induction_on with
  | zero => rfl
  | tmul a q =>
    obtain ⟨v, hv⟩ := hu
    have : a = g • ((v⁻¹ : Aˣ).1 * a) := by
      rw [Algebra.smul_def, ← mul_assoc, ← hv, Units.mul_inv, one_mul]
    rw [this, ← smul_tmul', ← tmul_smul, hg, tmul_zero]
  | add x y hx hy => rw [hx, hy, add_zero]

end K4FSurjSpread

open K4FSurjSpread in
/--
@isnad1 id=ex.1h5v.s12.6be489a3fadb from=translated src=- shape=bc177733 vocab=81c6968e
-/
theorem solution
    {R : Type u} [CommRing R]
    {M N : Type u} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] [Module.Finite R N]
    (f : M →ₗ[R] N) (𝔭 : PrimeSpectrum R)
    (hf : Function.Surjective (f.baseChange 𝔭.asIdeal.ResidueField)) :
    ∃ g : R, g ∉ 𝔭.asIdeal ∧
      ∀ (A : Type u) [CommRing A] [Algebra R A], IsUnit (algebraMap R A g) →
        Function.Surjective (f.baseChange A) := by
  classical
  set Q := N ⧸ LinearMap.range f with hQ

  have hsub : Subsingleton (𝔭.asIdeal.ResidueField ⊗[R] Q) := by
    have ex := lTensor_exact 𝔭.asIdeal.ResidueField (LinearMap.exact_map_mkQ_range f)
      (Submodule.mkQ_surjective _)
    have hsurj : Function.Surjective ((LinearMap.range f).mkQ.lTensor 𝔭.asIdeal.ResidueField) :=
      LinearMap.lTensor_surjective _ (Submodule.mkQ_surjective _)
    have hzero : (LinearMap.range f).mkQ.lTensor 𝔭.asIdeal.ResidueField = 0 := by
      rw [← LinearMap.ker_eq_top, ex.linearMap_ker_eq, LinearMap.range_eq_top]
      have : ⇑(f.baseChange 𝔭.asIdeal.ResidueField) = ⇑(f.lTensor 𝔭.asIdeal.ResidueField) :=
        LinearMap.baseChange_eq_ltensor f
      rw [← this]; exact hf
    refine ⟨fun x y => ?_⟩
    obtain ⟨x', rfl⟩ := hsurj x; obtain ⟨y', rfl⟩ := hsurj y
    rw [hzero]; rfl

  have hnot : 𝔭 ∉ Module.support R Q := by
    rw [Module.mem_support_iff_nontrivial_residueField_tensorProduct, not_nontrivial_iff_subsingleton]
    exact hsub
  rw [Module.mem_support_iff_of_finite, SetLike.not_le_iff_exists] at hnot
  obtain ⟨g, hgann, hg𝔭⟩ := hnot
  refine ⟨g, hg𝔭, fun A _ _ hu => ?_⟩
  have hsubA := subsingleton_tensor_of_smul_eq_zero Q g (fun q => Module.mem_annihilator.mp hgann q) A hu
  have := lTensor_surjective_of_subsingleton f A hsubA
  have hfun : ⇑(f.baseChange A) = ⇑(f.lTensor A) := LinearMap.baseChange_eq_ltensor f
  rw [hfun]; exact this
