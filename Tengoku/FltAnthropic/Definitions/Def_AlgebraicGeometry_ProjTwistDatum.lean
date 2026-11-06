import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_AlgebraicGeometry_ProjSpaceCover
import Tengoku.FltAnthropic.Definitions.Def_AlgebraicGeometry_ProjSpaceCechGradedModule

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory Opposite MvPolynomial HomogeneousLocalization

namespace AlgebraicGeometry.ProjSpace

attribute [local instance] MvPolynomial.gradedAlgebra

variable (A : Type u) [CommRing A] (N : ℕ)

local notation "𝒜" => MvPolynomial.homogeneousSubmodule (Fin (N + 1)) A
local notation "S" => MvPolynomial (Fin (N + 1)) A

end AlgebraicGeometry.ProjSpace

namespace AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra

namespace ProjSpace

variable {A : Type u} [CommRing A] {N : ℕ} {X : Scheme.{u}}
  (φ : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) A))

def pullbackChart (i : Fin (N + 1)) : X.Opens :=
  φ ⁻¹ᵁ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) A) (MvPolynomial.X i)

def frameUnit (i j : Fin (N + 1)) : Γ(X, pullbackChart φ i) :=
  (φ.app (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) A) (MvPolynomial.X i))).hom
    ((Proj.awayToSection _ (MvPolynomial.X i)).hom (ProjSpace.ratio A N i j))

abbrev restrictFun {U U' : X.Opens} (h : U ≤ U') : Γ(X, U') →+* Γ(X, U) :=
  (X.presheaf.map (homOfLE h).op).hom

def TwistCompat (m : ℕ) (U : X.Opens) (g : ∀ i : Fin (N + 1), Γ(X, U ⊓ pullbackChart φ i)) : Prop :=
  ∀ i j : Fin (N + 1),
    restrictFun (inf_le_left : (U ⊓ pullbackChart φ i) ⊓ pullbackChart φ j ≤ U ⊓ pullbackChart φ i) (g i)
      = restrictFun (le_trans inf_le_left inf_le_right : (U ⊓ pullbackChart φ i) ⊓ pullbackChart φ j ≤ pullbackChart φ i) (frameUnit φ i j) ^ m
        * restrictFun (le_inf (le_trans inf_le_left inf_le_left) inf_le_right : (U ⊓ pullbackChart φ i) ⊓ pullbackChart φ j ≤ U ⊓ pullbackChart φ j) (g j)

def twistSections (m : ℕ) (U : X.Opens) : AddSubgroup (∀ i : Fin (N + 1), Γ(X, U ⊓ pullbackChart φ i)) where
  carrier := {g | TwistCompat φ m U g}
  zero_mem' := fun i j => by simp
  add_mem' := by
    intro g g' hg hg' i j
    simp only [Pi.add_apply, map_add, hg i j, hg' i j, mul_add]
  neg_mem' := by
    intro g hg i j
    simp only [Pi.neg_apply, map_neg, hg i j, mul_neg]

theorem smul_mem_twistSections {m : ℕ} {U : X.Opens} (a : Γ(X, U)) {g : ∀ i, Γ(X, U ⊓ pullbackChart φ i)}
    (hg : g ∈ twistSections φ m U) :
    (fun i => restrictFun (inf_le_left : U ⊓ pullbackChart φ i ≤ U) a * g i) ∈ twistSections φ m U := by
  intro i j
  simp only [map_mul, hg i j]
  have h1 : restrictFun (inf_le_left : (U ⊓ pullbackChart φ i) ⊓ pullbackChart φ j ≤ U ⊓ pullbackChart φ i) (restrictFun (inf_le_left : U ⊓ pullbackChart φ i ≤ U) a)
      = restrictFun (le_inf (le_trans inf_le_left inf_le_left) inf_le_right : (U ⊓ pullbackChart φ i) ⊓ pullbackChart φ j ≤ U ⊓ pullbackChart φ j)
          (restrictFun (inf_le_left : U ⊓ pullbackChart φ j ≤ U) a) := by
    show (X.presheaf.map _ ≫ X.presheaf.map _).hom a = (X.presheaf.map _ ≫ X.presheaf.map _).hom a
    rw [← X.presheaf.map_comp, ← X.presheaf.map_comp]
    rfl
  rw [h1]
  ring

end ProjSpace

end AlgebraicGeometry

namespace AlgebraicGeometry
namespace ProjSpace

attribute [local instance] MvPolynomial.gradedAlgebra

variable {A : Type u} [CommRing A] {N : ℕ} {X : Scheme.{u}}

@[ext] structure twistObj (π : X ⟶ Spec (.of A)) (φ : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) A)) (m : ℕ) (U : X.Opens) : Type u where

  val : ∀ i : Fin (N + 1), Γ(X, U ⊓ pullbackChart φ i)

  compat : TwistCompat φ m U val

def twistObj.equivSections (π : X ⟶ Spec (.of A)) (φ : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) A)) (m : ℕ) (U : X.Opens) :
    twistObj π φ m U ≃ twistSections φ m U where
  toFun g := ⟨g.val, g.compat⟩
  invFun s := ⟨s.1, s.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance twistObj.addCommGroup (π : X ⟶ Spec (.of A)) (φ : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) A)) (m : ℕ) (U : X.Opens) : AddCommGroup (twistObj π φ m U) :=
  (twistObj.equivSections π φ m U).addCommGroup

theorem twistObj.val_injective {π : X ⟶ Spec (.of A)} {φ : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) A)} {m : ℕ} {U : X.Opens} :
    Function.Injective (twistObj.val (π := π) (φ := φ) (m := m) (U := U)) :=
  fun _ _ h => twistObj.ext h

instance twistObj.moduleSections (π : X ⟶ Spec (.of A)) (φ : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) A)) (m : ℕ) (U : X.Opens) : Module Γ(X, U) (twistObj π φ m U) where
  smul a g := ⟨fun i => restrictFun inf_le_left a * g.val i, smul_mem_twistSections φ a g.compat⟩
  one_smul g := by
    refine twistObj.ext (_root_.funext fun i => ?_)
    show restrictFun _ 1 * g.val i = g.val i
    rw [map_one, one_mul]
  mul_smul a b g := by
    refine twistObj.ext (_root_.funext fun i => ?_)
    show restrictFun _ (a * b) * g.val i = restrictFun _ a * (restrictFun _ b * g.val i)
    rw [map_mul, mul_assoc]
  smul_zero a := by
    refine twistObj.ext (_root_.funext fun i => ?_)
    show restrictFun _ a * (0 : Γ(X, U ⊓ pullbackChart φ i)) = 0
    rw [mul_zero]
  smul_add a g g' := by
    refine twistObj.ext (_root_.funext fun i => ?_)
    show restrictFun _ a * (g.val i + g'.val i) = restrictFun _ a * g.val i + restrictFun _ a * g'.val i
    rw [mul_add]
  add_smul a b g := by
    refine twistObj.ext (_root_.funext fun i => ?_)
    show restrictFun _ (a + b) * g.val i = restrictFun _ a * g.val i + restrictFun _ b * g.val i
    rw [map_add, add_mul]
  zero_smul g := by
    refine twistObj.ext (_root_.funext fun i => ?_)
    show restrictFun _ 0 * g.val i = 0
    rw [map_zero, zero_mul]

instance twistObj.module (π : X ⟶ Spec (.of A)) (φ : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) A)) (m : ℕ) (U : X.Opens) : Module A (twistObj π φ m U) :=
  letI := Scheme.TwoAffineOpenCover.algebraOfHom π U
  Module.compHom (twistObj π φ m U) (algebraMap A (Γ(X, U) : Type u))

theorem twistObj.algebraMap_smul {π : X ⟶ Spec (.of A)} {φ : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) A)} {m : ℕ} {U : X.Opens} (r : A) (g : twistObj π φ m U) :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom π U
    r • g = algebraMap A (Γ(X, U) : Type u) r • g := by rfl

end ProjSpace
end AlgebraicGeometry

namespace AlgebraicGeometry.ProjSpace

attribute [local instance] MvPolynomial.gradedAlgebra

variable {A : Type u} [CommRing A] {N : ℕ} {X : Scheme.{u}}
  (φ : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) A))

end AlgebraicGeometry.ProjSpace

namespace AlgebraicGeometry.ProjSpace

attribute [local instance] MvPolynomial.gradedAlgebra

variable {A : Type u} [CommRing A] {N : ℕ} {X : Scheme.{u}}

end AlgebraicGeometry.ProjSpace

namespace AlgebraicGeometry.ProjSpace

attribute [local instance] MvPolynomial.gradedAlgebra

variable {A : Type u} [CommRing A] {N : ℕ} {X : Scheme.{u}}

section GradedModuleOfTwist

variable (φ : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) A))

end GradedModuleOfTwist

end AlgebraicGeometry.ProjSpace

namespace AlgebraicGeometry.ProjSpace

attribute [local instance] MvPolynomial.gradedAlgebra

variable {A : Type u} [CommRing A] {N : ℕ} {X : Scheme.{u}}
  (φ : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) A))

end AlgebraicGeometry.ProjSpace

namespace AlgebraicGeometry.ProjSpace

attribute [local instance] MvPolynomial.gradedAlgebra

variable {A : Type u} [CommRing A] {N : ℕ} {X : Scheme.{u}}
  (φ : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) A))

end AlgebraicGeometry.ProjSpace

namespace AlgebraicGeometry.ProjSpace

attribute [local instance] MvPolynomial.gradedAlgebra

variable {A : Type u} [CommRing A] {N : ℕ} {X : Scheme.{u}}
  (φ : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) A))

end AlgebraicGeometry.ProjSpace

end
