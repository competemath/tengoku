import Tengoku.FltAnthropic.Definitions.Def_AlgebraicGeometry_CoherentBaseChange
import Tengoku.Seed.Algebra.Algebra.Hom
import Tengoku.Seed.LinearAlgebra.Prod
import Tengoku.Seed.LinearAlgebra.TensorProduct.Tower
import Tengoku.Seed.RingTheory.TensorProduct.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

noncomputable section

open scoped TensorProduct

universe u v w

namespace TwoChartCech

structure Cover (R : Type u) [CommRing R] where

  A0 : Type v

  A1 : Type v

  A01 : Type v
  [A0_commRing : CommRing A0]
  [A0_algebra : Algebra R A0]
  [A1_commRing : CommRing A1]
  [A1_algebra : Algebra R A1]
  [A01_commRing : CommRing A01]
  [A01_algebra : Algebra R A01]

  ρ0 : A0 →ₐ[R] A01

  ρ1 : A1 →ₐ[R] A01

attribute [instance] Cover.A0_commRing Cover.A0_algebra Cover.A1_commRing Cover.A1_algebra
  Cover.A01_commRing Cover.A01_algebra

structure Sections {R : Type u} [CommRing R] (𝒰 : Cover.{u, v} R) where

  M0 : Type w

  M1 : Type w

  M01 : Type w
  [M0_addCommGroup : AddCommGroup M0]
  [M0_moduleA : Module 𝒰.A0 M0]
  [M0_module : Module R M0]
  [M0_tower : IsScalarTower R 𝒰.A0 M0]
  [M1_addCommGroup : AddCommGroup M1]
  [M1_moduleA : Module 𝒰.A1 M1]
  [M1_module : Module R M1]
  [M1_tower : IsScalarTower R 𝒰.A1 M1]
  [M01_addCommGroup : AddCommGroup M01]
  [M01_moduleA : Module 𝒰.A01 M01]
  [M01_module : Module R M01]
  [M01_tower : IsScalarTower R 𝒰.A01 M01]

  r0 : M0 →ₗ[R] M01

  r1 : M1 →ₗ[R] M01

  r0_smul : ∀ (a : 𝒰.A0) (m : M0), r0 (a • m) = 𝒰.ρ0 a • r0 m

  r1_smul : ∀ (a : 𝒰.A1) (m : M1), r1 (a • m) = 𝒰.ρ1 a • r1 m

attribute [instance] Sections.M0_addCommGroup Sections.M0_moduleA Sections.M0_module
  Sections.M0_tower Sections.M1_addCommGroup Sections.M1_moduleA Sections.M1_module
  Sections.M1_tower Sections.M01_addCommGroup Sections.M01_moduleA Sections.M01_module
  Sections.M01_tower

namespace Sections

variable {R : Type u} [CommRing R] {𝒰 : Cover.{u, v} R} (S : Sections.{u, v, w} 𝒰)

def cechDiff : S.M0 × S.M1 →ₗ[R] S.M01 := (-S.r0).coprod S.r1

abbrev H0 : Submodule R (S.M0 × S.M1) := LinearMap.ker S.cechDiff

abbrev H1 : Type w := S.M01 ⧸ LinearMap.range S.cechDiff

end Sections

namespace Cover

variable {R : Type u} [CommRing R] (𝒰 : Cover.{u, v} R)

@[reducible] def lineBundle (t : 𝒰.A01ˣ) : Sections.{u, v, v} 𝒰 where
  M0 := 𝒰.A0
  M1 := 𝒰.A1
  M01 := 𝒰.A01
  r0 := 𝒰.ρ0.toLinearMap
  r1 := (t : 𝒰.A01) • 𝒰.ρ1.toLinearMap
  r0_smul a m := by simp
  r1_smul a m := by simp [mul_left_comm]

/--
@isnad1 id=eq.0h4v.s8.377738fb5e89 from=translated src=- shape=ed5077ac vocab=8e9368f0
-/
@[simp] theorem lineBundle_r0_apply (t : 𝒰.A01ˣ) (p : 𝒰.A0) : (𝒰.lineBundle t).r0 p = 𝒰.ρ0 p := rfl
/--
@isnad1 id=eq.0h4v.s8.9014bb159390 from=translated src=- shape=319c7fcf vocab=187770b4
-/
@[simp] theorem lineBundle_r1_apply (t : 𝒰.A01ˣ) (p : 𝒰.A1) :
    (𝒰.lineBundle t).r1 p = (t : 𝒰.A01) * 𝒰.ρ1 p := rfl

abbrev structureSheaf : Sections.{u, v, v} 𝒰 := 𝒰.lineBundle 1

end Cover

section Dock

variable {R : Type u} [CommRing R]
variable {C0 : Type v} {C1 : Type v} [AddCommGroup C0] [Module R C0] [AddCommGroup C1] [Module R C1]

def kerBaseChangeHom (d : C0 →ₗ[R] C1) (A : Type w) [CommRing A] [Algebra R A] :
    A ⊗[R] (LinearMap.ker d) →ₗ[A] LinearMap.ker (d.baseChange A) :=
  ((LinearMap.ker d).subtype.baseChange A).codRestrict (LinearMap.ker (d.baseChange A))
    (fun x => by
      rw [LinearMap.mem_ker, ← LinearMap.comp_apply, ← LinearMap.baseChange_comp]
      have h : d ∘ₗ (LinearMap.ker d).subtype = 0 := by
        ext ⟨y, hy⟩
        exact hy
      rw [h, LinearMap.baseChange_zero, LinearMap.zero_apply])

def kerMap {K0 : Type v} {K1 : Type v} [AddCommGroup K0] [Module R K0] [AddCommGroup K1]
    [Module R K1] (dK : K0 →ₗ[R] K1) (d : C0 →ₗ[R] C1) (ι0 : K0 →ₗ[R] C0) (ι1 : K1 →ₗ[R] C1)
    (comm : d ∘ₗ ι0 = ι1 ∘ₗ dK) : LinearMap.ker dK →ₗ[R] LinearMap.ker d :=
  ι0.restrict fun x hx => by
    rw [LinearMap.mem_ker] at hx ⊢
    rw [← LinearMap.comp_apply, comm, LinearMap.comp_apply, hx, map_zero]

def cokerMap {K0 : Type v} {K1 : Type v} [AddCommGroup K0] [Module R K0] [AddCommGroup K1]
    [Module R K1] (dK : K0 →ₗ[R] K1) (d : C0 →ₗ[R] C1) (ι0 : K0 →ₗ[R] C0) (ι1 : K1 →ₗ[R] C1)
    (comm : d ∘ₗ ι0 = ι1 ∘ₗ dK) : (K1 ⧸ LinearMap.range dK) →ₗ[R] (C1 ⧸ LinearMap.range d) :=
  Submodule.mapQ _ _ ι1 fun y hy => by
    obtain ⟨x, rfl⟩ := LinearMap.mem_range.mp hy
    rw [Submodule.mem_comap, ← LinearMap.comp_apply, ← comm, LinearMap.comp_apply]
    exact LinearMap.mem_range_self _ _

def kerMapBaseChange {K0 : Type v} {K1 : Type v} [AddCommGroup K0] [Module R K0] [AddCommGroup K1]
    [Module R K1] (dK : K0 →ₗ[R] K1) (d : C0 →ₗ[R] C1) (ι0 : K0 →ₗ[R] C0) (ι1 : K1 →ₗ[R] C1)
    (comm : d ∘ₗ ι0 = ι1 ∘ₗ dK) (A : Type w) [CommRing A] [Algebra R A] :
    LinearMap.ker (dK.baseChange A) →ₗ[A] LinearMap.ker (d.baseChange A) :=
  (ι0.baseChange A).restrict fun x hx => by
    rw [LinearMap.mem_ker] at hx ⊢
    rw [← LinearMap.comp_apply, ← LinearMap.baseChange_comp, comm, LinearMap.baseChange_comp,
      LinearMap.comp_apply, hx, map_zero]

def cokerMapBaseChange {K0 : Type v} {K1 : Type v} [AddCommGroup K0] [Module R K0] [AddCommGroup K1]
    [Module R K1] (dK : K0 →ₗ[R] K1) (d : C0 →ₗ[R] C1) (ι0 : K0 →ₗ[R] C0) (ι1 : K1 →ₗ[R] C1)
    (comm : d ∘ₗ ι0 = ι1 ∘ₗ dK) (A : Type w) [CommRing A] [Algebra R A] :
    ((A ⊗[R] K1) ⧸ LinearMap.range (dK.baseChange A)) →ₗ[A]
      ((A ⊗[R] C1) ⧸ LinearMap.range (d.baseChange A)) :=
  Submodule.mapQ _ _ (ι1.baseChange A) fun y hy => by
    obtain ⟨x, rfl⟩ := LinearMap.mem_range.mp hy
    rw [Submodule.mem_comap, ← LinearMap.comp_apply, ← LinearMap.baseChange_comp, ← comm,
      LinearMap.baseChange_comp, LinearMap.comp_apply]
    exact LinearMap.mem_range_self _ _

structure GrothendieckComplex (d : C0 →ₗ[R] C1) where

  G : CoherentBaseChange.TwoTermComplex.{u, v} R

  ι0 : G.C0 →ₗ[R] C0

  ι1 : G.C1 →ₗ[R] C1
  comm : d ∘ₗ ι0 = ι1 ∘ₗ G.d
  bijective_kerMap : ∀ (A : Type u) [CommRing A] [Algebra R A],
    Function.Bijective (kerMapBaseChange G.d d ι0 ι1 comm A)
  bijective_cokerMap : ∀ (A : Type u) [CommRing A] [Algebra R A],
    Function.Bijective (cokerMapBaseChange G.d d ι0 ι1 comm A)

end Dock

def Cover.trivial (R : Type u) [CommRing R] : Cover.{u, u} R where
  A0 := R
  A1 := R
  A01 := R
  ρ0 := AlgHom.id R R
  ρ1 := AlgHom.id R R

@[reducible] def Sections.ofSubmodules {R : Type u} [CommRing R] {F : Type v} [AddCommGroup F] [Module R F]
    (N0 N1 N01 : Submodule R F) (h0 : N0 ≤ N01) (h1 : N1 ≤ N01) : Sections.{u, u, v} (Cover.trivial R) :=

  letI : Module (Cover.trivial R).A0 N0 := inferInstanceAs (Module R N0)
  letI : Module (Cover.trivial R).A1 N1 := inferInstanceAs (Module R N1)
  letI : Module (Cover.trivial R).A01 N01 := inferInstanceAs (Module R N01)
  haveI : IsScalarTower R (Cover.trivial R).A0 N0 := ⟨fun a b m => mul_smul (a : R) (b : R) m⟩
  haveI : IsScalarTower R (Cover.trivial R).A1 N1 := ⟨fun a b m => mul_smul (a : R) (b : R) m⟩
  haveI : IsScalarTower R (Cover.trivial R).A01 N01 := ⟨fun a b m => mul_smul (a : R) (b : R) m⟩
  { M0 := N0
    M1 := N1
    M01 := N01
    r0 := Submodule.inclusion h0
    r1 := Submodule.inclusion h1
    r0_smul := fun _ _ => rfl
    r1_smul := fun _ _ => rfl }

section Gates

end Gates

end TwoChartCech

end
