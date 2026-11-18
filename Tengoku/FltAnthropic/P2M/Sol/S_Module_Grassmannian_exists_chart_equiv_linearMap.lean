import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_Module_Grassmannian_exists_chart_equiv_linearMap.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_Module_Grassmannian_exists_chart_equiv_linearMap

open scoped TensorProduct
open TensorProduct

set_option autoImplicit false

namespace GrassChartS1a

variable (R : Type) [CommRing R] {M : Type} [AddCommGroup M] [Module R M] {k : ℕ} (x : Fin k → M)
variable (A : Type) [CommRing A] [Algebra R A]

abbrev Chart : Type :=
  {N : Module.Grassmannian A (A ⊗[R] M) k //
    Function.Bijective fun v : Fin k → A => ∑ i, v i • N.toSubmodule.mkQ ((1 : A) ⊗ₜ[R] x i)}

abbrev HomX : Type :=
  {ψ : M →ₗ[R] (Fin k → A) // ∀ j, ψ (x j) = Pi.single j 1}

variable {R A}

def cmap (N : Submodule A (A ⊗[R] M)) : (Fin k → A) →ₗ[A] (A ⊗[R] M) ⧸ N :=
  Fintype.linearCombination A (fun i => N.mkQ ((1 : A) ⊗ₜ[R] x i))

/--
@isnad1 id=eq.0h6v.s12.696f52ad6979 from=translated src=- shape=8a7b773a vocab=2700f7e9
-/
lemma coe_cmap (N : Submodule A (A ⊗[R] M)) :
    ⇑(cmap x N) = fun v : Fin k → A => ∑ i, v i • N.mkQ ((1 : A) ⊗ₜ[R] x i) := rfl

/--
@isnad1 id=eq.0h7v.s11.88f3fb73a761 from=translated src=- shape=cedffc2b vocab=373971c3
-/
lemma cmap_single (N : Submodule A (A ⊗[R] M)) (j : Fin k) :
    cmap x N (Pi.single j 1) = N.mkQ ((1 : A) ⊗ₜ[R] x j) := by
  classical
  simp [cmap]

noncomputable def coordEquiv (N : Chart R x A) : (Fin k → A) ≃ₗ[A] (A ⊗[R] M) ⧸ N.1.toSubmodule :=
  LinearEquiv.ofBijective (cmap x N.1.toSubmodule) N.2

/--
@isnad1 id=eq.0h7v.s16.82f4523f2de2 from=translated src=- shape=d18b6150 vocab=418abec8
-/
lemma coordEquiv_apply (N : Chart R x A) (v : Fin k → A) :
    coordEquiv x N v = cmap x N.1.toSubmodule v := rfl

/--
@isnad1 id=eq.0h7v.s16.42344a612ecf from=translated src=- shape=918db52d vocab=37918a29
-/
lemma coordEquiv_symm_mkQ_x (N : Chart R x A) (j : Fin k) :
    (coordEquiv x N).symm (N.1.toSubmodule.mkQ ((1 : A) ⊗ₜ[R] x j)) = Pi.single j 1 := by
  rw [LinearEquiv.symm_apply_eq, coordEquiv_apply, cmap_single]

noncomputable def toHomX (N : Chart R x A) : HomX R x A :=
  ⟨(((coordEquiv x N).symm.toLinearMap ∘ₗ N.1.toSubmodule.mkQ).restrictScalars R) ∘ₗ
      TensorProduct.mk R A M 1,
    fun j => by
      simp only [LinearMap.coe_comp, LinearMap.coe_restrictScalars, LinearEquiv.coe_coe,
        Function.comp_apply, TensorProduct.mk_apply]
      exact coordEquiv_symm_mkQ_x x N j⟩

/--
@isnad1 id=eq.0h7v.s16.ef1e083d848c from=translated src=- shape=d0384f02 vocab=a3ccf600
-/
lemma toHomX_apply (N : Chart R x A) (m : M) :
    (toHomX x N).1 m = (coordEquiv x N).symm (N.1.toSubmodule.mkQ ((1 : A) ⊗ₜ[R] m)) := rfl

noncomputable abbrev ext' (ψ : M →ₗ[R] (Fin k → A)) : A ⊗[R] M →ₗ[A] (Fin k → A) :=
  ψ.liftBaseChange A

/--
@isnad1 id=surjecti.0h6v.s9.1b53fe58804d from=translated src=- shape=31207bb7 vocab=2e6da0bf
-/
lemma ext'_surjective (ψ : HomX R x A) : Function.Surjective (ext' ψ.1) := by
  intro v
  refine ⟨∑ i, v i ⊗ₜ[R] x i, ?_⟩
  simp only [map_sum, LinearMap.liftBaseChange_tmul, ψ.2]
  ext i
  simp [Finset.sum_apply, Pi.single_apply]

noncomputable def quotEquiv (ψ : HomX R x A) :
    ((A ⊗[R] M) ⧸ LinearMap.ker (ext' ψ.1)) ≃ₗ[A] (Fin k → A) :=
  (ext' ψ.1).quotKerEquivOfSurjective (ext'_surjective x ψ)

/--
@isnad1 id=eq.0h7v.s13.6be089201ef0 from=translated src=- shape=f796d9f2 vocab=d481eda7
-/
lemma quotEquiv_mkQ (ψ : HomX R x A) (p : A ⊗[R] M) :
    quotEquiv x ψ ((LinearMap.ker (ext' ψ.1)).mkQ p) = ext' ψ.1 p :=
  LinearMap.quotKerEquivOfSurjective_apply_mk _ _ _

/--
@isnad1 id=eq.0h7v.s13.1b83f619b75f from=translated src=- shape=fd055e2f vocab=dd466694
-/
lemma quotEquiv_cmap (ψ : HomX R x A) (v : Fin k → A) :
    quotEquiv x ψ (cmap x (LinearMap.ker (ext' ψ.1)) v) = v := by
  simp only [coe_cmap, map_sum, map_smul, quotEquiv_mkQ, LinearMap.liftBaseChange_tmul, one_smul,
    ψ.2]
  ext i
  simp [Finset.sum_apply, Pi.single_apply]

/--
@isnad1 id=eq.0h6v.s14.b0971f76184b from=translated src=- shape=fba6d172 vocab=8099025c
-/
lemma cmap_ker_eq (ψ : HomX R x A) :
    ⇑(cmap x (LinearMap.ker (ext' ψ.1))) = (quotEquiv x ψ).symm := by
  funext v
  rw [eq_comm, LinearEquiv.symm_apply_eq, quotEquiv_cmap]

noncomputable def ofHomX (ψ : HomX R x A) : Chart R x A := by
  refine ⟨{ toSubmodule := LinearMap.ker (ext' ψ.1)
            finite_quotient := Module.Finite.equiv (quotEquiv x ψ).symm
            projective_quotient := Module.Projective.of_equiv (quotEquiv x ψ).symm
            rankAtStalk_eq := fun p => ?_ }, ?_⟩
  · haveI : Nontrivial A := by
      by_contra h
      haveI := not_nontrivial_iff_subsingleton.mp h
      exact IsEmpty.false p
    rw [Module.rankAtStalk_eq_of_equiv (quotEquiv x ψ), Module.rankAtStalk_eq_finrank_of_free,
      Module.finrank_fin_fun]
    rfl
  · change Function.Bijective (cmap x (LinearMap.ker (ext' ψ.1)))
    rw [cmap_ker_eq]
    exact (quotEquiv x ψ).symm.bijective

/--
@isnad1 id=eq.0h6v.s12.e023dd7869fb from=translated src=- shape=a7f8c4bf vocab=e3e341a1
-/
lemma ofHomX_toSubmodule (ψ : HomX R x A) :
    (ofHomX x ψ).1.toSubmodule = LinearMap.ker (ext' ψ.1) := rfl

/--
@isnad1 id=eq.0h6v.s15.6d242ab89dc5 from=translated src=- shape=45519ea4 vocab=48e1b7f7
-/
lemma ext'_toHomX (N : Chart R x A) :
    ext' (toHomX x N).1 = (coordEquiv x N).symm.toLinearMap ∘ₗ N.1.toSubmodule.mkQ := by
  refine TensorProduct.AlgebraTensorModule.ext fun a m => ?_
  simp only [LinearMap.liftBaseChange_tmul, toHomX_apply, LinearMap.coe_comp, LinearEquiv.coe_coe,
    Function.comp_apply]
  rw [← map_smul, ← map_smul, TensorProduct.smul_tmul', smul_eq_mul, mul_one]

/--
@isnad1 id=eq.0h6v.s6.a408d317fe73 from=translated src=- shape=7d3ce6a1 vocab=866e5ec4
-/
lemma ofHomX_toHomX (N : Chart R x A) : ofHomX x (toHomX x N) = N := by
  apply Subtype.ext
  apply Module.Grassmannian.ext
  rw [ofHomX_toSubmodule, ext'_toHomX, LinearEquiv.ker_comp, Submodule.ker_mkQ]

/--
@isnad1 id=eq.0h7v.s16.ce9d8843bb88 from=translated src=- shape=79108e87 vocab=ecb01e36
-/
lemma coordEquiv_ofHomX_symm (ψ : HomX R x A) (y) :
    (coordEquiv x (ofHomX x ψ)).symm y = quotEquiv x ψ y := by
  have h1 : (coordEquiv x (ofHomX x ψ)) ((coordEquiv x (ofHomX x ψ)).symm y) = y :=
    LinearEquiv.apply_symm_apply _ _
  rw [coordEquiv_apply] at h1
  have h2 := congrArg (quotEquiv x ψ) h1

  change quotEquiv x ψ (cmap x (LinearMap.ker (ext' ψ.1)) _) = _ at h2
  rwa [quotEquiv_cmap] at h2

/--
@isnad1 id=eq.0h6v.s6.2b3538a5a88d from=translated src=- shape=7d3ce6a1 vocab=266aa47c
-/
lemma toHomX_ofHomX (ψ : HomX R x A) : toHomX x (ofHomX x ψ) = ψ := by
  apply Subtype.ext
  apply LinearMap.ext
  intro m
  rw [toHomX_apply, coordEquiv_ofHomX_symm]
  change quotEquiv x ψ ((LinearMap.ker (ext' ψ.1)).mkQ ((1 : A) ⊗ₜ[R] m)) = _
  rw [quotEquiv_mkQ, LinearMap.liftBaseChange_tmul, one_smul]

noncomputable def chartEquiv : Chart R x A ≃ HomX R x A where
  toFun := toHomX x
  invFun := ofHomX x
  left_inv := ofHomX_toHomX x
  right_inv := toHomX_ofHomX x

variable {B : Type} [CommRing B] [Algebra R B] (φ : A →ₐ[R] B)

def pushHomX (ψ : HomX R x A) : HomX R x B :=
  ⟨(φ.toLinearMap.compLeft (Fin k)) ∘ₗ ψ.1, fun j => by
    ext i
    simp [LinearMap.compLeft, ψ.2, Pi.single_apply, apply_ite φ]⟩

/--
@isnad1 id=eq.0h10v.s10.0537e30b42bf from=translated src=- shape=1a1c0955 vocab=365afcee
-/
lemma pushHomX_apply (ψ : HomX R x A) (m : M) (i : Fin k) :
    (pushHomX x φ ψ).1 m i = φ (ψ.1 m i) := rfl

/--
@isnad1 id=eq.0h8v.s12.0fb132d8f4bc from=translated src=- shape=c209c44a vocab=53361ffc
-/
lemma map_ofHomX_toSubmodule (ψ : HomX R x A) :
    (Module.Grassmannian.map φ (ofHomX x ψ).1).toSubmodule =
      LinearMap.ker (ext' (pushHomX x φ ψ).1) := by
  classical
  rw [Module.Grassmannian.map_toSubmodule]
  letI : Algebra A B := φ.toAlgebra
  letI : IsScalarTower R A B := IsScalarTower.of_algebraMap_eq' <| IsScalarTower.algebraMap_eq R A B

  let T : B ⊗[A] ((A ⊗[R] M) ⧸ (ofHomX x ψ).1.toSubmodule) ≃ₗ[B] (Fin k → B) :=
    (quotEquiv x ψ).baseChange A B _ _ ≪≫ₗ TensorProduct.piScalarRight A B B (Fin k)
  have hT : (T.toLinearMap ∘ₗ Module.Grassmannian.baseChangeMkQ B (ofHomX x ψ).1.toSubmodule) =
      ext' (pushHomX x φ ψ).1 := by
    refine TensorProduct.AlgebraTensorModule.ext fun b m => ?_
    simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
      Module.Grassmannian.baseChangeMkQ, TensorProduct.AlgebraTensorModule.cancelBaseChange_symm_tmul,
      LinearMap.baseChange_tmul, LinearMap.liftBaseChange_tmul]
    simp only [T, LinearEquiv.trans_apply]
    change TensorProduct.piScalarRight A B B (Fin k) (b ⊗ₜ[A] quotEquiv x ψ ((LinearMap.ker (ext' ψ.1)).mkQ _)) = _
    rw [quotEquiv_mkQ, LinearMap.liftBaseChange_tmul, one_smul]
    ext i
    simp only [TensorProduct.piScalarRight_apply, TensorProduct.piScalarRightHom_tmul, Pi.smul_apply,
      pushHomX_apply, smul_eq_mul, Algebra.smul_def, RingHom.algebraMap_toAlgebra, mul_comm]
    rfl
  rw [← hT, LinearEquiv.ker_comp]

/--
@isnad1 id=eq.0h8v.s13.54152fd73da1 from=translated src=- shape=8f0beac5 vocab=4c5ddd00
-/
lemma map_ofHomX (ψ : HomX R x A) :
    Module.Grassmannian.map φ (ofHomX x ψ).1 = (ofHomX x (pushHomX x φ ψ)).1 :=
  Module.Grassmannian.ext (map_ofHomX_toSubmodule x φ ψ)

/--
@isnad1 id=bijectiv.0h8v.s16.29e64cc7936a from=translated src=- shape=9b381824 vocab=844cd36a
-/
lemma map_mem_chart (N : Chart R x A) :
    Function.Bijective fun v : Fin k → B =>
      ∑ i, v i • (Module.Grassmannian.map φ N.1).toSubmodule.mkQ ((1 : B) ⊗ₜ[R] x i) := by
  have hN : N = ofHomX x (toHomX x N) := (ofHomX_toHomX x N).symm
  rw [hN, map_ofHomX]
  exact (ofHomX x (pushHomX x φ (toHomX x N))).2

/--
@isnad1 id=eq.0h8v.s13.cc011ae48e43 from=translated src=- shape=062699b0 vocab=7e780d59
-/
lemma chartEquiv_map (N : Chart R x A) :
    chartEquiv x ⟨Module.Grassmannian.map φ N.1, map_mem_chart x φ N⟩ =
      pushHomX x φ (chartEquiv x N) := by
  have hN : N = ofHomX x (toHomX x N) := (ofHomX_toHomX x N).symm
  have : (⟨Module.Grassmannian.map φ N.1, map_mem_chart x φ N⟩ : Chart R x B) =
      ofHomX x (pushHomX x φ (toHomX x N)) := by
    apply Subtype.ext
    change Module.Grassmannian.map φ N.1 = _
    conv_lhs => rw [hN]
    exact map_ofHomX x φ (toHomX x N)
  rw [this]
  exact toHomX_ofHomX x _

end GrassChartS1a

open GrassChartS1a in
/--
@isnad1 id=ex.0h4v.s18.dec8a04674c2 from=translated src=- shape=9fb69c02 vocab=6948aa2b
-/
theorem solution
    (R : Type) [CommRing R] (M : Type) [AddCommGroup M] [Module R M] (k : ℕ) (x : Fin k → M) :
    ∃ pt : ∀ (A : Type) [CommRing A] [Algebra R A],
        {N : Module.Grassmannian A (A ⊗[R] M) k //
            Function.Bijective fun v : Fin k → A =>
              ∑ i, v i • N.toSubmodule.mkQ ((1 : A) ⊗ₜ[R] x i)} ≃
          {ψ : M →ₗ[R] (Fin k → A) // ∀ j, ψ (x j) = Pi.single j 1},
      (∀ (A : Type) [CommRing A] [Algebra R A]
          (N : {N : Module.Grassmannian A (A ⊗[R] M) k //
            Function.Bijective fun v : Fin k → A =>
              ∑ i, v i • N.toSubmodule.mkQ ((1 : A) ⊗ₜ[R] x i)})
          (m : M),
          ∑ i, (pt A N).1 m i • N.1.toSubmodule.mkQ ((1 : A) ⊗ₜ[R] x i) =
            N.1.toSubmodule.mkQ ((1 : A) ⊗ₜ[R] m)) ∧
      (∀ (A : Type) [CommRing A] [Algebra R A]
          (ψ : {ψ : M →ₗ[R] (Fin k → A) // ∀ j, ψ (x j) = Pi.single j 1}),
          ((pt A).symm ψ).1.toSubmodule = LinearMap.ker (ψ.1.liftBaseChange A)) ∧
      (∀ (A B : Type) [CommRing A] [CommRing B] [Algebra R A] [Algebra R B] (φ : A →ₐ[R] B)
          (N : {N : Module.Grassmannian A (A ⊗[R] M) k //
            Function.Bijective fun v : Fin k → A =>
              ∑ i, v i • N.toSubmodule.mkQ ((1 : A) ⊗ₜ[R] x i)}),
          ∃ h : Function.Bijective fun v : Fin k → B =>
              ∑ i, v i • (Module.Grassmannian.map φ N.1).toSubmodule.mkQ ((1 : B) ⊗ₜ[R] x i),
            ∀ (m : M) (i : Fin k),
              (pt B ⟨Module.Grassmannian.map φ N.1, h⟩).1 m i = φ ((pt A N).1 m i)) := by
  refine ⟨fun A _ _ => chartEquiv (R := R) (A := A) x, ?_, ?_, ?_⟩
  ·
    intro A _ _ N m
    change cmap x N.1.toSubmodule ((coordEquiv x N).symm (N.1.toSubmodule.mkQ ((1 : A) ⊗ₜ[R] m))) = _
    rw [← coordEquiv_apply, LinearEquiv.apply_symm_apply]
  · intro A _ _ ψ
    rfl
  · intro A B _ _ _ _ φ N
    exact ⟨map_mem_chart x φ N, fun m i => by
      have h := chartEquiv_map x φ N
      exact congrArg (fun ψ : HomX R x B => ψ.1 m i) h⟩
