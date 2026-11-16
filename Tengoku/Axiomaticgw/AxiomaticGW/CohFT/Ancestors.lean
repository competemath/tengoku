/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import Tengoku.Axiomaticgw.AxiomaticGW.CohFT.Constant
public import Tengoku.Axiomaticgw.AxiomaticGW.CohFT.Tautological

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Ancestor correlators

Ancestor correlators multiply a CohFT class by powers of stable-curve `psi`
classes and integrate the resulting class.
-/

@[expose] public section

namespace AxiomaticGW

universe u

namespace CohFT

variable {R V : Type u} [CommRing R] [Algebra ℚ R]
  [AddCommGroup V] [Module R V] [Module.Free R V] [Module.Finite R V]
  {C : StableCurveCohomology R}

/-- Multiplication by a fixed stable-curve `psi` monomial.-/
def multiplyPsi (P : PsiClasses C)
    (g : ℕ) (S : Type) [Fintype S] (h : StableArity g S)
    (k : S → ℕ) : C.H g S →ₗ[R] C.H g S where
  toFun x := x * P.monomial g S h k
  map_add' x y := add_mul x y _
  map_smul' r x := by
    simp only [Algebra.smul_def, mul_assoc, RingHom.id_apply]

/-- Numerical ancestor correlator with cotangent powers `k`.-/
def ancestor (Ω : CohFT R V C) (P : PsiClasses C)
    (I : StableCurveIntegration C) (g : ℕ) (S : Type) [Fintype S]
    (h : StableArity g S) (k : S → ℕ) :
    MultilinearMap R (fun _ : S ↦ V) R :=
  (I.integrate g S h).compMultilinearMap
    ((multiplyPsi P g S h k).compMultilinearMap (Ω.omega g S h))

/--
@isnad1 id=eq.1h10v.s9.f85f2cbaa5e0 from=translated src=- shape=c9875b79 vocab=2fa5ccdc
-/
@[simp]
theorem ancestor_apply (Ω : CohFT R V C) (P : PsiClasses C)
    (I : StableCurveIntegration C) (g : ℕ) (S : Type) [Fintype S]
    (h : StableArity g S) (k : S → ℕ) (a : S → V) :
    Ω.ancestor P I g S h k a =
      I.integrate g S h (Ω.omega g S h a * P.monomial g S h k) := rfl

/--
@isnad1 id=eq.1h9v.s9.ff78b38db978 from=translated src=- shape=035bf9d8 vocab=b682ed8f
-/
theorem ancestor_zero_apply (Ω : CohFT R V C) (P : PsiClasses C)
    (I : StableCurveIntegration C) (g : ℕ) (S : Type) [Fintype S]
    (h : StableArity g S) (a : S → V) :
    Ω.ancestor P I g S h (fun _ ↦ 0) a =
      I.integrate g S h (Ω.omega g S h a) := by
  simp only [ancestor_apply, PsiClasses.monomial_zero, mul_one]

/-- Ancestor correlators are invariant under simultaneous relabelling of
markings, insertion powers, and state-space inputs.
@isnad1 id=eq.2h11v.s7.aaa152362a27 from=translated src=- shape=7292ceed vocab=0b478943
-/
theorem ancestor_domDomCongr (Ω : CohFT R V C) (P : PsiClasses C)
    (I : StableCurveIntegration C) (g : ℕ) (S T : Type)
    [Fintype S] [Fintype T] (hS : StableArity g S) (hT : StableArity g T)
    (e : S ≃ T) (k : S → ℕ) :
    (Ω.ancestor P I g S hS k).domDomCongr e =
      Ω.ancestor P I g T hT (fun t ↦ k (e.symm t)) := by
  ext a
  rw [MultilinearMap.domDomCongr_apply]
  simp only [ancestor_apply]
  rw [← I.integrate_rename g S T hS hT e]
  rw [map_mul, P.rename_monomial]
  have homega := Ω.relabel g S T hS hT e
  exact congrArg (fun f ↦ f a) homega ▸ rfl

end CohFT

namespace constantStableCurveCohomology

variable (R : Type u) [CommRing R] [Algebra ℚ R]

/-- The constant target has zero cotangent-line classes.-/
def psiClasses : PsiClasses (constantStableCurveCohomology R) where
  psi := fun _ _ _ _ _ ↦ 0
  psi_degree := by intros; exact Submodule.zero_mem _
  rename_psi := by intros; simp only [AlgEquiv.coe_refl, id_eq]
  nonseparating_psi := by intros; simp only [AlgHom.coe_id, id_eq]
  separating_psi_left := by
    intros
    simp only [Algebra.TensorProduct.includeLeft_apply, TensorProduct.zero_tmul]
  separating_psi_right := by
    intros
    simp only [Algebra.TensorProduct.includeLeft_apply, TensorProduct.zero_tmul,
      TensorProduct.tmul_zero]

/-- Integration in the constant target is the identity exactly in complex
dimension zero and is zero otherwise.-/
def integrate (g : ℕ) (S : Type) [Fintype S] : R →ₗ[R] R :=
  if StableArity.dimension g S = 0 then LinearMap.id else 0

omit [Algebra ℚ R] in
/--
@isnad1 id=eq.0h1v.s6.c59e68df6e3b from=translated src=- shape=e56cba4a vocab=dd26f4a9
-/
@[simp]
theorem integrate_zero_fin_three : integrate R 0 (Fin 3) = LinearMap.id := by
  simp only [integrate, StableArity.dimension_zero_fin_three, ↓reduceIte]

/-- Top-degree integration for the constant stable-curve target.-/
def integration :
    StableCurveIntegration (constantStableCurveCohomology R) where
  integrate := fun g S _ h ↦ integrate R g S
  integrate_of_degree_ne := by
    intro g S _ h d x hx hd
    by_cases hdim : StableArity.dimension g S = 0
    · have hd0 : d ≠ 0 := by
        intro hd'
        apply hd
        simpa only [hd'] using hdim.symm
      have hx0 : x = 0 := by
        simpa only [constantDegree, hd0, ↓reduceIte, Submodule.mem_bot]
          using hx
      subst x
      simp only [integrate, map_zero]
    · simp only [integrate, hdim, ↓reduceIte, LinearMap.zero_apply]
  integrate_rename := by
    intro g S T _ _ hS hT e x
    change integrate R g T x = integrate R g S x
    unfold integrate
    rw [← StableArity.dimension_equiv e]

/-- Forgetful pushforward in the constant model is zero: its source has one
more complex dimension while the model has no positive-degree classes.-/
def forgetfulPushforward :
    ForgetfulPushforward (constantStableCurveCohomology R) (integration R) where
  push := fun _ _ _ _ ↦ 0
  push_rename := by intros; rfl
  push_degree := by intros; exact Submodule.zero_mem _
  push_eq_zero_of_degree_zero := by intros; rfl
  projection_formula := by
    intros
    simp only [AlgHom.coe_id, id_eq, LinearMap.zero_apply, mul_zero]
  integrate_push := by
    intro g S _ h x
    change integrate R g S 0 = integrate R g (Option S) x
    simp only [integrate, map_zero, StableArity.dimension_option h,
      Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte,
      LinearMap.zero_apply]

/-- The constant model has no rational-tail divisor and satisfies the
forgetful `psi` formula trivially.-/
def psiForgetFormula : PsiForgetFormula (psiClasses R) where
  boundaryTail := fun _ _ _ _ _ ↦ 0
  boundaryTail_degree := by intros; exact Submodule.zero_mem _
  psi_eq_forget_add_boundary := by
    intros
    simp only [psiClasses, AlgHom.coe_id, id_eq, add_zero]

/--
@isnad1 id=eq.1h4v.s7.724ba81c6abc from=translated src=- shape=4873cdbb vocab=08a54b08
-/
@[simp]
theorem kappa_eq_zero (g : ℕ) (S : Type) [Fintype S]
    (h : StableArity g S) (m : ℕ) :
    (psiClasses R).kappa (forgetfulPushforward R) g S h m = 0 := by
  rfl

end constantStableCurveCohomology

namespace TopologicalCohFT

variable {R V : Type u} [CommRing R] [Algebra ℚ R]
  [AddCommGroup V] [Module R V] [Module.Free R V] [Module.Finite R V]

/-- In the constant model, the zero-power genus-zero three-point ancestor is
the original topological correlator.
@isnad1 id=eq.0h4v.s8.a9538770eaf2 from=translated src=- shape=02120ac6 vocab=c26ecc49
-/
theorem toConstantCohFT_ancestor_zero_three (T : TopologicalCohFT R V)
    (a : Fin 3 → V) :
    T.toConstantCohFT.ancestor
        (constantStableCurveCohomology.psiClasses R)
        (constantStableCurveCohomology.integration R)
        0 (Fin 3) StableArity.zero_fin_three (fun _ ↦ 0) a =
      T.omega 0 (Fin 3) StableArity.zero_fin_three a := by
  rw [CohFT.ancestor_zero_apply]
  change constantStableCurveCohomology.integrate R 0 (Fin 3)
      (T.omega 0 (Fin 3) StableArity.zero_fin_three a) =
    T.omega 0 (Fin 3) StableArity.zero_fin_three a
  simp only [constantStableCurveCohomology.integrate_zero_fin_three,
    LinearMap.id_coe, id_eq]

end TopologicalCohFT

end AxiomaticGW
