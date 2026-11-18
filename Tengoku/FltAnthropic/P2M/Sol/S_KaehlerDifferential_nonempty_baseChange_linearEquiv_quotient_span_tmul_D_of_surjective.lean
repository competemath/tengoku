import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_KaehlerDifferential_nonempty_baseChange_linearEquiv_quotient_span_tmul_D_of_surjective.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_KaehlerDifferential_nonempty_baseChange_linearEquiv_quotient_span_tmul_D_of_surjective

set_option autoImplicit false

open TensorProduct KaehlerDifferential

universe u

namespace Conormal29

section

variable (R C A R' : Type u) [CommRing R] [CommRing C] [CommRing A] [CommRing R']
    [Algebra R C] [Algebra R A] [Algebra C A] [IsScalarTower R C A]
    [Algebra A R'] [Algebra C R'] [IsScalarTower C A R']

noncomputable def ψ : R' ⊗[C] Ω[C⁄R] →ₗ[R'] R' ⊗[A] Ω[A⁄R] :=
  ((KaehlerDifferential.mapBaseChange R C A).baseChange R') ∘ₗ
    (TensorProduct.AlgebraTensorModule.cancelBaseChange C A R' R' Ω[C⁄R]).symm.toLinearMap

noncomputable def N : Submodule R' (R' ⊗[C] Ω[C⁄R]) :=
  Submodule.span R' (Set.range fun f : RingHom.ker (algebraMap C A) => (1 : R') ⊗ₜ[C] D R C (f : C))

omit [Algebra R A] [IsScalarTower R C A] in
/--
@isnad1 id=eq.0h6v.s12.b2b283fa8679 from=translated src=- shape=6ce72c26 vocab=efd268b4
-/
theorem cancelBaseChange_symm_tmul (r : R') (ω : Ω[C⁄R]) :
    (TensorProduct.AlgebraTensorModule.cancelBaseChange C A R' R' Ω[C⁄R]).symm (r ⊗ₜ[C] ω) =
      r ⊗ₜ[A] ((1 : A) ⊗ₜ[C] ω) := rfl

/--
@isnad1 id=eq.0h6v.s10.66423ef5ab0d from=translated src=- shape=679d131b vocab=ae6d5e55
-/
theorem ψ_tmul (r : R') (ω : Ω[C⁄R]) :
    ψ R C A R' (r ⊗ₜ[C] ω) = r ⊗ₜ[A] KaehlerDifferential.map R R C A ω := by
  simp only [ψ, LinearMap.comp_apply, LinearEquiv.coe_coe, cancelBaseChange_symm_tmul,
    LinearMap.baseChange_tmul, mapBaseChange_tmul, one_smul]

variable {R C A R'}

/--
@isnad1 id=surjecti.1h4v.s10.00ff3c82980b from=translated src=- shape=b12ec6fe vocab=0d8c4a3f
-/
theorem ψ_surjective (hsurj : Function.Surjective (algebraMap C A)) :
    Function.Surjective (ψ R C A R') := by
  have h1 : Function.Surjective ((KaehlerDifferential.mapBaseChange R C A).baseChange R') := by
    rw [LinearMap.baseChange_eq_ltensor]
    exact LinearMap.lTensor_surjective R' (mapBaseChange_surjective R C A hsurj)
  exact h1.comp (TensorProduct.AlgebraTensorModule.cancelBaseChange C A R' R' Ω[C⁄R]).symm.surjective

variable (R C A R') in
/--
@isnad1 id=le.0h4v.s10.834501edc1d7 from=translated src=- shape=00b91a78 vocab=0af469e8
-/
theorem N_le_ker : N R C A R' ≤ LinearMap.ker (ψ R C A R') := by
  rw [N, Submodule.span_le]
  rintro _ ⟨f, rfl⟩
  rw [SetLike.mem_coe, LinearMap.mem_ker, ψ_tmul, map_D, RingHom.mem_ker.mp f.2, map_zero,
    TensorProduct.tmul_zero]

/--
@isnad1 id=le.1h4v.s10.48792dd1aaac from=translated src=- shape=f13a8639 vocab=ba3f9392
-/
theorem ker_le_N (hsurj : Function.Surjective (algebraMap C A)) :
    LinearMap.ker (ψ R C A R') ≤ N R C A R' := by
  intro x hx
  have hgs : Function.Surjective (KaehlerDifferential.mapBaseChange R C A) :=
    mapBaseChange_surjective R C A hsurj

  have hy : LinearMap.lTensor R' (KaehlerDifferential.mapBaseChange R C A)
      ((TensorProduct.AlgebraTensorModule.cancelBaseChange C A R' R' Ω[C⁄R]).symm x) = 0 := by
    rw [← LinearMap.baseChange_eq_ltensor]
    exact hx

  have hex : Function.Exact
      (LinearMap.lTensor R' (LinearMap.ker (KaehlerDifferential.mapBaseChange R C A)).subtype)
      (LinearMap.lTensor R' (KaehlerDifferential.mapBaseChange R C A)) :=
    lTensor_exact R' (LinearMap.exact_subtype_ker_map _) hgs
  obtain ⟨t, ht⟩ := (hex _).1 hy
  have hxE : x = TensorProduct.AlgebraTensorModule.cancelBaseChange C A R' R' Ω[C⁄R]
      (LinearMap.lTensor R' (LinearMap.ker (KaehlerDifferential.mapBaseChange R C A)).subtype t) := by
    rw [ht, LinearEquiv.apply_symm_apply]
  rw [hxE]
  clear hxE ht hy hx

  induction t using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]; exact (N R C A R').zero_mem
  | tmul r k =>
    obtain ⟨κ, hκ⟩ := ((exact_kerCotangentToTensor_mapBaseChange R C A hsurj) k.1).1 k.2
    obtain ⟨f, rfl⟩ := Ideal.toCotangent_surjective _ κ
    rw [kerCotangentToTensor_toCotangent] at hκ
    rw [LinearMap.lTensor_tmul, Submodule.subtype_apply, ← hκ]
    change TensorProduct.AlgebraTensorModule.cancelBaseChange C A R' R' Ω[C⁄R]
      (r ⊗ₜ[A] ((1 : A) ⊗ₜ[C] D R C (f : C))) ∈ N R C A R'
    rw [TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul, one_smul]
    have : r ⊗ₜ[C] D R C (f : C) = r • ((1 : R') ⊗ₜ[C] D R C (f : C)) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [this]
    exact Submodule.smul_mem _ r (Submodule.subset_span ⟨f, rfl⟩)
  | add a b ha hb => rw [map_add, map_add]; exact Submodule.add_mem _ ha hb

/--
@isnad1 id=eq.1h4v.s9.11f5a441a3d6 from=translated src=- shape=f13a8639 vocab=13df53ad
-/
theorem ker_eq_N (hsurj : Function.Surjective (algebraMap C A)) :
    LinearMap.ker (ψ R C A R') = N R C A R' :=
  le_antisymm (ker_le_N hsurj) (N_le_ker R C A R')

end

end Conormal29

open Conormal29

/--
@isnad1 id=nonempty.1h4v.s11.133775fcee00 from=translated src=- shape=63ce7fcc vocab=faf78627
-/
theorem solution
    {R C A R' : Type u} [CommRing R] [CommRing C] [CommRing A] [CommRing R']
    [Algebra R C] [Algebra R A] [Algebra C A] [IsScalarTower R C A]
    (hsurj : Function.Surjective (algebraMap C A))
    [Algebra A R'] [Algebra C R'] [IsScalarTower C A R'] :
    Nonempty ((R' ⊗[A] Ω[A⁄R]) ≃ₗ[R']
      ((R' ⊗[C] Ω[C⁄R]) ⧸ Submodule.span R'
        (Set.range fun f : RingHom.ker (algebraMap C A) => (1 : R') ⊗ₜ[C] D R C (f : C)))) := by
  have e0 := Submodule.quotEquivOfEq _ _ (ker_eq_N (R := R) (C := C) (A := A) (R' := R') hsurj).symm
  have e1 := LinearMap.quotKerEquivOfSurjective _ (ψ_surjective (R := R) (C := C) (A := A) (R' := R') hsurj)
  exact ⟨(e0.trans e1).symm⟩
