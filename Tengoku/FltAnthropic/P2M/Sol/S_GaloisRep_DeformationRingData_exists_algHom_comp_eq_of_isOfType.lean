import Tengoku.FltAnthropic.Definitions.Def_GaloisRep_DeformationRingData
import Tengoku.FltAnthropic.Definitions.Def_GaloisRep_LocalConditions

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/
namespace Tengoku.FltAnthropic end Tengoku.FltAnthropic open Tengoku.FltAnthropic
/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_GaloisRep_DeformationRingData_exists_algHom_comp_eq_of_isOfType.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_GaloisRep_DeformationRingData_exists_algHom_comp_eq_of_isOfType

set_option autoImplicit false

open GaloisRep
open scoped TensorProduct

namespace WCOTXprime

section Naturality

variable {R S T : Type} [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra S T]
  [Algebra R T] [IsScalarTower R S T]
  {V W : Type} [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]

/--
@isnad1 id=eq.0h7v.s12.894d520a0a4f from=translated src=- shape=bcb966e4 vocab=31241617
-/
theorem cancel_naturality (φ : V →ₗ[R] W) (x : T ⊗[S] (S ⊗[R] V)) :
    TensorProduct.AlgebraTensorModule.cancelBaseChange R S T T W ((φ.baseChange S).baseChange T x) =
      φ.baseChange T (TensorProduct.AlgebraTensorModule.cancelBaseChange R S T T V x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul c y =>
    induction y using TensorProduct.induction_on with
    | zero => simp only [TensorProduct.tmul_zero, map_zero]
    | tmul b v =>
      simp only [LinearMap.baseChange_tmul, TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul]
    | add y₁ y₂ h₁ h₂ => simp only [TensorProduct.tmul_add, map_add, h₁, h₂]
  | add x y hx hy => simp only [map_add, hx, hy]

end Naturality

variable {A B C : Type} [CommRing A] [IsLocalRing A] [CommRing B] [IsLocalRing B]
  [CommRing C] [IsLocalRing C]

noncomputable def bcComp (ρ : GaloisRepAdic A) (f : A →+* B) (hf : IsLocalHom f)
    (g : B →+* C) (hg : IsLocalHom g) (hgf : IsLocalHom (g.comp f)) :
    GaloisRepAdic.Equiv ((ρ.baseChangeAlong f hf).baseChangeAlong g hg)
      (ρ.baseChangeAlong (g.comp f) hgf) :=
  letI : Algebra A B := f.toAlgebra
  letI : Algebra B C := g.toAlgebra
  letI : Algebra A C := (g.comp f).toAlgebra
  haveI : IsScalarTower A B C := IsScalarTower.of_algebraMap_eq fun _ => rfl
  { toLinearEquiv := TensorProduct.AlgebraTensorModule.cancelBaseChange A B C C ρ.V
    map_apply := fun σ x => by
      change TensorProduct.AlgebraTensorModule.cancelBaseChange A B C C ρ.V
          ((((ρ.ρ σ).baseChange B).baseChange C) x) =
        ((ρ.ρ σ).baseChange C) (TensorProduct.AlgebraTensorModule.cancelBaseChange A B C C ρ.V x)
      exact cancel_naturality (ρ.ρ σ) x }

variable {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
  [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪]
  {ρbar : ResidualGaloisRep (IsLocalRing.ResidueField 𝒪)}
  {𝒟₀ 𝒟' : ∀ ⦃A : Type⦄ [CommRing A] [IsLocalRing A] [Algebra 𝒪 A], GaloisRepAdic A → Prop}

end WCOTXprime

namespace WCOTUniv

open GaloisRep WCOTXprime IsLocalRing
open scoped TensorProduct

section Naturality

variable {R S T : Type} [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra S T]
  [Algebra R T] [IsScalarTower R S T]
  {V W : Type} [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]

/--
@isnad1 id=eq.0h7v.s13.2c8c2fb002f0 from=translated src=- shape=f771ec9c vocab=b6511b84
-/
theorem cancel_symm_naturality (φ : V →ₗ[R] W) (y : T ⊗[R] V) :
    (TensorProduct.AlgebraTensorModule.cancelBaseChange R S T T W).symm (φ.baseChange T y) =
      (φ.baseChange S).baseChange T
        ((TensorProduct.AlgebraTensorModule.cancelBaseChange R S T T V).symm y) := by
  rw [LinearEquiv.symm_apply_eq, cancel_naturality, LinearEquiv.apply_symm_apply]

end Naturality

section Adic

variable {A B : Type} [CommRing A] [IsLocalRing A] [CommRing B] [IsLocalRing B]

noncomputable def residualBC (ρ : GaloisRepAdic A) (f : A →+* B) (hf : IsLocalHom f) :
    ResidualGaloisRep.Equiv (ρ.baseChangeAlong f hf).residual
      (ρ.residual.baseChangeAlong (@ResidueField.map A B _ _ _ _ f hf)) :=
  haveI := hf
  letI : Algebra A B := f.toAlgebra
  letI : Algebra (ResidueField A) (ResidueField B) := (ResidueField.map f).toAlgebra
  letI : Module (ResidueField A) (ResidueField B) := Algebra.toModule
  haveI : IsScalarTower A (ResidueField A) (ResidueField B) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  { toLinearEquiv :=
      (TensorProduct.AlgebraTensorModule.cancelBaseChange A B (ResidueField B) (ResidueField B)
          ρ.V).trans
        (TensorProduct.AlgebraTensorModule.cancelBaseChange A (ResidueField A) (ResidueField B)
          (ResidueField B) ρ.V).symm
    map_apply := fun σ x => by
      change ((TensorProduct.AlgebraTensorModule.cancelBaseChange A (ResidueField A)
            (ResidueField B) (ResidueField B) ρ.V).symm
          (TensorProduct.AlgebraTensorModule.cancelBaseChange A B (ResidueField B) (ResidueField B)
            ρ.V ((((ρ.ρ σ).baseChange B).baseChange (ResidueField B)) x))) =
        ((ρ.ρ σ).baseChange (ResidueField A)).baseChange (ResidueField B)
          ((TensorProduct.AlgebraTensorModule.cancelBaseChange A (ResidueField A)
            (ResidueField B) (ResidueField B) ρ.V).symm
          (TensorProduct.AlgebraTensorModule.cancelBaseChange A B (ResidueField B) (ResidueField B)
            ρ.V x))
      exact (congrArg ((TensorProduct.AlgebraTensorModule.cancelBaseChange A (ResidueField A)
            (ResidueField B) (ResidueField B) ρ.V).symm) (cancel_naturality (ρ.ρ σ) x)).trans
        (cancel_symm_naturality (ρ.ρ σ) _) }

end Adic

section Residual

variable {k k' k'' : Type} [Field k] [Field k'] [Field k'']

noncomputable def rbcComp (ρ : ResidualGaloisRep k) (f : k →+* k') (g : k' →+* k'') :
    ResidualGaloisRep.Equiv ((ρ.baseChangeAlong f).baseChangeAlong g)
      (ρ.baseChangeAlong (g.comp f)) :=
  letI : Algebra k k' := f.toAlgebra
  letI : Algebra k' k'' := g.toAlgebra
  letI : Algebra k k'' := (g.comp f).toAlgebra
  haveI : IsScalarTower k k' k'' := IsScalarTower.of_algebraMap_eq fun _ => rfl
  { toLinearEquiv := TensorProduct.AlgebraTensorModule.cancelBaseChange k k' k'' k'' ρ.V
    map_apply := fun σ x => by
      change TensorProduct.AlgebraTensorModule.cancelBaseChange k k' k'' k'' ρ.V
          ((((ρ.ρ σ).baseChange k').baseChange k'') x) =
        ((ρ.ρ σ).baseChange k'') (TensorProduct.AlgebraTensorModule.cancelBaseChange k k' k'' k'' ρ.V x)
      exact cancel_naturality (ρ.ρ σ) x }

/--
@isnad1 id=isequiv.1h5v.s7.29712ca6919a from=translated src=- shape=1803edba vocab=72536d89
-/
theorem risEquiv_congr (ρ : ResidualGaloisRep k) {f g : k →+* k'} (hfg : ∀ x, f x = g x) :
    (ρ.baseChangeAlong f).IsEquiv (ρ.baseChangeAlong g) := by
  obtain rfl : f = g := RingHom.ext hfg
  exact ⟨ResidualGaloisRep.Equiv.refl _⟩

/--
@isnad1 id=isequiv.2h4v.s5.f4ff79ee742d from=translated src=- shape=46b34526 vocab=378f2fd0
-/
theorem risEquiv_trans {ρ₁ ρ₂ ρ₃ : ResidualGaloisRep k} (h₁ : ρ₁.IsEquiv ρ₂) (h₂ : ρ₂.IsEquiv ρ₃) :
    ρ₁.IsEquiv ρ₃ := by
  obtain ⟨e₁⟩ := h₁
  obtain ⟨e₂⟩ := h₂
  exact ⟨e₁.trans e₂⟩

end Residual

variable {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
  [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪]
  {ρbar : ResidualGaloisRep (IsLocalRing.ResidueField 𝒪)}
  {𝒟 𝒟₀ 𝒟' : ∀ ⦃A : Type⦄ [CommRing A] [IsLocalRing A] [Algebra 𝒪 A], GaloisRepAdic A → Prop}

/--
@isnad1 id=isequiv.1h6v.s9.6b8e28647303 from=translated src=- shape=755cff66 vocab=6f143221
-/
theorem residual_isEquiv_baseChangeAlong (D : DeformationRingData 𝒪 ρbar 𝒟)
    {A : Type} [CommRing A] [IsLocalRing A] [Algebra 𝒪 A] [IsLocalHom (algebraMap 𝒪 A)]
    (f : D.R →ₐ[𝒪] A) (hf : IsLocalHom (f : D.R →+* A)) :
    (D.ρ.baseChangeAlong (f : D.R →+* A) hf).residual.IsEquiv
      (ρbar.baseChangeAlong (ResidueField.map (algebraMap 𝒪 A))) := by
  haveI := hf
  refine risEquiv_trans ⟨residualBC D.ρ (f : D.R →+* A) hf⟩ ?_
  obtain ⟨e⟩ := D.residual_isEquiv
  refine risEquiv_trans ⟨e.baseChangeAlong (ResidueField.map (f : D.R →+* A))⟩ ?_
  refine risEquiv_trans ⟨rbcComp ρbar _ _⟩ (risEquiv_congr ρbar fun y => ?_)
  obtain ⟨r, rfl⟩ := IsLocalRing.residue_surjective y
  rw [RingHom.comp_apply, ResidueField.map_residue, ResidueField.map_residue, ResidueField.map_residue]
  exact congrArg (IsLocalRing.residue A) (f.commutes r)

/--
@isnad1 id=eq.4h8v.s10.5a0a7edb2b52 from=translated src=- shape=32456697 vocab=7683ff4d
-/
theorem algHom_eq_of_isEquiv (D : DeformationRingData 𝒪 ρbar 𝒟)
    (A : Type) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    [Algebra 𝒪 A] [IsLocalHom (algebraMap 𝒪 A)]
    (hres : Function.Surjective (IsLocalRing.residue A ∘ algebraMap 𝒪 A))
    (f g : D.R →ₐ[𝒪] A) (hf : IsLocalHom (f : D.R →+* A)) (hg : IsLocalHom (g : D.R →+* A))
    (h𝒟 : 𝒟 (D.ρ.baseChangeAlong (f : D.R →+* A) hf))
    (hfg : (D.ρ.baseChangeAlong (f : D.R →+* A) hf).IsEquiv (D.ρ.baseChangeAlong (g : D.R →+* A) hg)) :
    f = g := by
  have hu := D.universal A hres _ h𝒟 (residual_isEquiv_baseChangeAlong D f hf)
  obtain ⟨egf⟩ := hfg
  exact hu.unique ⟨hf, ⟨GaloisRepAdic.Equiv.refl _⟩⟩ ⟨hg, ⟨egf.symm⟩⟩

/--
@isnad1 id=ex.4h11v.s11.e62b6778a238 from=translated src=- shape=75ec428f vocab=a69ca817
-/
theorem exists_algHom_comp_eq
    (D₀ : DeformationRingData 𝒪 ρbar 𝒟₀) (D' : DeformationRingData 𝒪 ρbar 𝒟')
    (θ : D'.R →ₐ[𝒪] D₀.R) (hθ : IsLocalHom (θ : D'.R →+* D₀.R))
    (hθρ : (D'.ρ.baseChangeAlong (θ : D'.R →+* D₀.R) hθ).IsEquiv D₀.ρ)
    (A : Type) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    [Algebra 𝒪 A] [IsLocalHom (algebraMap 𝒪 A)]
    (hres : Function.Surjective (IsLocalRing.residue A ∘ algebraMap 𝒪 A))
    (xφ : D'.R →ₐ[𝒪] A) (hxφ : IsLocalHom (xφ : D'.R →+* A))
    (h𝒟' : 𝒟' (D'.ρ.baseChangeAlong (xφ : D'.R →+* A) hxφ))
    (h𝒟₀ : 𝒟₀ (D'.ρ.baseChangeAlong (xφ : D'.R →+* A) hxφ)) :
    ∃ ψ : D₀.R →ₐ[𝒪] A, IsLocalHom (ψ : D₀.R →+* A) ∧ ψ.comp θ = xφ := by
  obtain ⟨ψ, ⟨hψ, hequiv⟩, -⟩ := D₀.universal A hres _ h𝒟₀ (residual_isEquiv_baseChangeAlong D' xφ hxφ)
  refine ⟨ψ, hψ, ?_⟩
  have hcomp : ((ψ : D₀.R →+* A).comp (θ : D'.R →+* D₀.R)) = (ψ.comp θ : D'.R →+* A) :=
    RingHom.ext fun _ => rfl
  haveI := hθ; haveI := hψ
  have hg : IsLocalHom (ψ.comp θ : D'.R →+* A) := by
    rw [← hcomp]; exact RingHom.isLocalHom_comp _ _
  have hgf : IsLocalHom ((ψ : D₀.R →+* A).comp (θ : D'.R →+* D₀.R)) := by rw [hcomp]; exact hg

  have key : ∀ (f g : D'.R →+* A) (hf : IsLocalHom f) (hg : IsLocalHom g), f = g →
      (D'.ρ.baseChangeAlong f hf).IsEquiv (D'.ρ.baseChangeAlong g hg) := by
    intro f g hf hg hfg; subst hfg; exact ⟨GaloisRepAdic.Equiv.refl _⟩
  obtain ⟨e0⟩ := key _ _ hg hgf hcomp.symm
  obtain ⟨e1⟩ := hθρ
  obtain ⟨e2⟩ := hequiv
  have hiso : (D'.ρ.baseChangeAlong (xφ : D'.R →+* A) hxφ).IsEquiv
      (D'.ρ.baseChangeAlong (ψ.comp θ : D'.R →+* A) hg) :=
    ⟨(e0.trans ((bcComp D'.ρ (θ : D'.R →+* D₀.R) hθ (ψ : D₀.R →+* A) hψ hgf).symm.trans
      ((e1.baseChangeAlong (ψ : D₀.R →+* A) hψ).trans e2))).symm⟩
  exact (algHom_eq_of_isEquiv D' A hres xφ (ψ.comp θ) hxφ hg h𝒟' hiso).symm

end WCOTUniv

open GaloisRep

/--
@isnad1 id=ex.4h11v.s11.e62b6778a238 from=translated src=- shape=75ec428f vocab=a69ca817
-/
theorem solution
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪]
    {ρbar : ResidualGaloisRep (IsLocalRing.ResidueField 𝒪)}
    {𝒟₀ 𝒟' : ∀ ⦃A : Type⦄ [CommRing A] [IsLocalRing A] [Algebra 𝒪 A], GaloisRepAdic A → Prop}
    (D₀ : GaloisRep.DeformationRingData 𝒪 ρbar 𝒟₀) (D' : GaloisRep.DeformationRingData 𝒪 ρbar 𝒟')
    (θ : D'.R →ₐ[𝒪] D₀.R) (hθ : IsLocalHom (θ : D'.R →+* D₀.R))
    (hθρ : (D'.ρ.baseChangeAlong (θ : D'.R →+* D₀.R) hθ).IsEquiv D₀.ρ)
    (A : Type) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    [Algebra 𝒪 A] [IsLocalHom (algebraMap 𝒪 A)]
    (hres : Function.Surjective (IsLocalRing.residue A ∘ algebraMap 𝒪 A))
    (xφ : D'.R →ₐ[𝒪] A) (hxφ : IsLocalHom (xφ : D'.R →+* A))
    (h𝒟' : 𝒟' (D'.ρ.baseChangeAlong (xφ : D'.R →+* A) hxφ))
    (h𝒟₀ : 𝒟₀ (D'.ρ.baseChangeAlong (xφ : D'.R →+* A) hxφ)) :
    ∃ ψ : D₀.R →ₐ[𝒪] A, IsLocalHom (ψ : D₀.R →+* A) ∧ ψ.comp θ = xφ := by
  exact WCOTUniv.exists_algHom_comp_eq D₀ D' θ hθ hθρ A hres xφ hxφ h𝒟' h𝒟₀
-- Tengoku: root names of this library moved to Tengoku.FltAnthropic so they do not collide with other libraries (generated)
