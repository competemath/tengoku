import Tengoku.Brauerinduction.BrauerInduction.Background.ClassFun.Basic
import Tengoku.Brauerinduction.BrauerInduction.Background.FDRep.Character.Basic
import Tengoku.Brauerinduction.BrauerInduction.Background.FDRep.Simple

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!

# The action of class functions on representations

A class function `f : ClassFun k G` determines a linear operator on every
finite-dimensional representation `V` of `G` by

`∑ g : G, f g • V(g⁻¹)`.

Conjugacy invariance of `f` implies that this operator commutes with the
`G`-action, so it defines an endomorphism of `V`. This file develops the
basic properties of this construction: naturality with respect to
intertwining maps, its trace formula, scalarity on simple representations,
compatibility with isomorphisms and finite biproducts, and faithfulness on
the left regular representation.
-/
namespace Tengoku.Brauerinduction end Tengoku.Brauerinduction open Tengoku.Brauerinduction
universe u v

variable {k : Type u} [Field k] {G : Type v} [Group G]

open CategoryTheory CategoryTheory.Limits
open scoped BigOperators

namespace Tengoku.Brauerinduction.ClassFun

section LinearAction

/--
The linear operator on `V` associated to the class function `f`, defined by
`∑ g : G, f g • V(g⁻¹)`.-/
noncomputable def action [Fintype G]
  (f : ClassFun k G) (V : FDRep k G) : V →ₗ[k] V :=
  ∑ g, f g • V.ρ g⁻¹

/--
The operator associated to a class function commutes with the action of every
group element.
@isnad1 id=eq.0h5v.s13.0fa70a018e8e from=translated src=- shape=aac7fd88 vocab=9ff22860
-/
lemma action_comm [Fintype G] (f : ClassFun k G) (V : FDRep k G) (h : G) :
    action f V ∘ₗ V.ρ h = V.ρ h ∘ₗ action f V := by
  ext v
  simp only [action, LinearMap.comp_apply, LinearMap.sum_apply,
    LinearMap.smul_apply, map_sum, map_smul]
  let e : G ≃ G := MulAut.conj h
  have h_reindex := Equiv.sum_comp e (fun x => f x • V.ρ x⁻¹ (V.ρ h v))
  rw [← h_reindex]
  apply Finset.sum_congr rfl
  intro g _
  change
    f (h * g * h⁻¹) •
        (V.ρ (h * g * h⁻¹)⁻¹) ((V.ρ h) v)
      =
    f g • (V.ρ h) ((V.ρ g⁻¹) v)

  have hf_conj : f (h * g * h⁻¹) = f g := by
    let u : Gˣ := ⟨h⁻¹, h, by simp, by simp⟩
    exact f.map_conj (h * g * h⁻¹) g ⟨u, by
      change h⁻¹ * (h * g * h⁻¹) = g * h⁻¹
      group⟩

  have hρ :
      (V.ρ (h * g * h⁻¹)⁻¹) ((V.ρ h) v)
        =
      (V.ρ h) ((V.ρ g⁻¹) v) := by
    simp [map_mul, mul_assoc]

  rw [hf_conj, hρ]

/--
The trace of the action of a class function `f` on `V` is
`∑ g : G, f g * V.character g⁻¹`.
@isnad1 id=eq.0h4v.s12.da417b9c2fd2 from=translated src=- shape=93dd301d vocab=6e380f69
-/
lemma trace_action [Fintype G] (f : ClassFun k G) (V : FDRep k G) :
    LinearMap.trace k V (action f V) = ∑ g : G, f g * V.character g⁻¹ := by
  dsimp [action]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro g _
  have h_char : V.character g⁻¹ = LinearMap.trace k V (V.ρ g⁻¹) := rfl
  simp only [h_char, map_smul, smul_eq_mul]

end LinearAction

section EquivariantEndomorphism

/--
Package the class-function action as an equivariant endomorphism of `V`.-/
noncomputable def actionHom [Fintype G]
    (f : ClassFun k G) (V : FDRep k G) : V ⟶ V :=
  FDRep.homOfLinearMap (ClassFun.action f V) (ClassFun.action_comm f V)

/--
The class-function action is natural with respect to intertwining maps.
@isnad1 id=eq.0h6v.s11.61789d9543b8 from=translated src=- shape=22121ff6 vocab=0232c588
-/
lemma action_naturality
    [Fintype G]
    (f : ClassFun k G)
    {V W : FDRep k G}
    (α : V ⟶ W) :
    FDRep.homToLinearMap α ∘ₗ ClassFun.action f V =
      ClassFun.action f W ∘ₗ FDRep.homToLinearMap α := by
  ext v
  simp only [action]
  rw [LinearMap.comp_apply, LinearMap.sum_apply]
  rw [LinearMap.comp_apply, LinearMap.sum_apply]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro g _
  simp only [LinearMap.smul_apply, map_smul]
  congr 1
  exact FDRep.homToLinearMap_rho_apply α g⁻¹ v

/--
The endomorphisms obtained from the class-function action form a natural
family with respect to morphisms of representations.
@isnad1 id=eq.0h6v.s8.02b8c639d54e from=translated src=- shape=110d7b34 vocab=9a52cd1f
-/
lemma actionHom_naturality [Fintype G]
    (f : ClassFun k G) {A B : FDRep k G} (α : A ⟶ B) :
    actionHom f A ≫ α = α ≫ actionHom f B := by
  ext v
  exact LinearMap.congr_fun (action_naturality f α) v

/--
The bundled equivariant endomorphism associated to a class function is zero
if and only if its underlying linear action is zero.
@isnad1 id=iff.0h4v.s11.019919b79dde from=translated src=- shape=dab8c84f vocab=3722fabb
-/
lemma actionHom_eq_zero_iff [Fintype G]
    (f : ClassFun k G) (V : FDRep k G) :
    actionHom f V = 0 ↔ ClassFun.action f V = 0 := by
  constructor
  · intro h
    ext v
    have hv :=
      congrArg (fun m : V ⟶ V => FDRep.homToLinearMap m v) h
    exact LinearMap.mem_eqLocus.mp hv
  · intro h
    ext v
    exact LinearMap.congr_fun h v

end EquivariantEndomorphism

section SimpleRepresentations

/--
If the equivariant endomorphism associated to `f` is multiplication by
`lambda`, then its trace is `lambda` times the dimension of the representation.
@isnad1 id=eq.1h5v.s12.2fbef062babd from=translated src=- shape=55705e5e vocab=d005f357
-/
lemma trace_action_eq_scalar_mul_finrank
    [Fintype G] (f : ClassFun k G) (V : FDRep k G)
    (lambda : k) (h : actionHom f V = lambda • 𝟙 V) :
    LinearMap.trace k V (action f V) =
      lambda * (Module.finrank k V : k) := by
  let F : (V ⟶ V) → (V →ₗ[k] V) :=
    fun m => FDRep.homToLinearMap m

  have h_map :
      F (actionHom f V) = F (lambda • 𝟙 V) :=
    congrArg F h

  have h_LHS :
      F (actionHom f V) = action f V := by
    rfl

  have h_RHS :
      F (lambda • 𝟙 V) =
        lambda • (LinearMap.id : V →ₗ[k] V) := by
    ext v
    rfl

  have h_lin :
      action f V =
        lambda • (LinearMap.id : V →ₗ[k] V) := by
    simpa [h_LHS, h_RHS] using h_map

  rw [h_lin]
  simp only [map_smul, LinearMap.trace_id, smul_eq_mul]

/--
On a simple representation over an algebraically closed field, the
endomorphism associated to a class function is scalar.
@isnad1 id=ex.0h4v.s11.97e845915730 from=translated src=- shape=c6f69e58 vocab=8b3a6813
-/
lemma actionHom_is_scalar [Fintype G] [IsAlgClosed k]
  (f : ClassFun k G) (V : FDRep k G) [Simple V] :
    ∃ lambda : k, actionHom f V = lambda • 𝟙 V := by
  exact FDRep.end_eq_smul_id_of_simple V (actionHom f V)

end SimpleRepresentations

section IsomorphismsAndBiproducts

open Classical in
/--
Vanishing of the action of a class function is preserved when a
representation is replaced by an isomorphic representation.
@isnad1 id=eq.1h6v.s11.bea2cc6c9ce7 from=translated src=- shape=2261ad85 vocab=d3268260
-/
lemma action_zero_of_iso
    [Fintype G]
    (f : ClassFun k G)
    {A B : FDRep k G}
    (e : A ≅ B)
    (hB : ClassFun.action f B = 0) :
    ClassFun.action f A = 0 := by
  apply (actionHom_eq_zero_iff f A).mp

  have hBhom : actionHom f B = 0 :=
    (actionHom_eq_zero_iff f B).mpr hB

  rw [← cancel_mono e.hom]
  simpa [hBhom] using
    actionHom_naturality f e.hom

/--
A class function acts trivially on one representation if and only if it acts
trivially on any isomorphic representation.
@isnad1 id=iff.0h6v.s11.fda823327c38 from=translated src=- shape=3620e667 vocab=d3268260
-/
lemma action_eq_zero_iff_of_iso [Fintype G]
    {V W : FDRep k G}
    (f : ClassFun k G) (e : V ≅ W) :
    action f V = 0 ↔ action f W = 0 := by
  constructor
  · exact action_zero_of_iso f e.symm
  · exact action_zero_of_iso f e

/--
If a class function acts trivially on every representation in a finite family,
then the endomorphisms obtained from the class-function of their biproduct is
trivial.
@isnad1 id=eq.1h5v.s11.cf20942782bc from=translated src=- shape=b5213037 vocab=2007de99
-/
lemma actionHom_eq_zero_of_biproduct
    [Fintype G] {ι : Type*} [Finite ι]
    (f : ClassFun k G) (S : ι → FDRep k G)
    (hS : ∀ i, ClassFun.action f (S i) = 0) :
    actionHom f (biproduct S) = 0 := by
  apply biproduct.hom_ext
  intro i
  have hnat :
      actionHom f (biproduct S) ≫ biproduct.π S i =
        biproduct.π S i ≫ actionHom f (S i) :=
    actionHom_naturality f (biproduct.π S i)
  have hz : actionHom f (S i) = 0 :=
    (actionHom_eq_zero_iff f (S i)).mpr (hS i)
  rw [hz] at hnat
  simpa using hnat

/--
If a class function acts trivially on every representation in a finite
family, then it acts trivially on their biproduct.
@isnad1 id=eq.1h5v.s13.c85667593511 from=translated src=- shape=5fcd3918 vocab=13105f87
-/
lemma action_zero_of_biproduct
    [Fintype G] {ι : Type*} [Finite ι]
    (f : ClassFun k G) (S : ι → FDRep k G)
    (hS : ∀ i, ClassFun.action f (S i) = 0) :
    ClassFun.action f (biproduct S) = 0 := by
  exact
    (actionHom_eq_zero_iff f (biproduct S)).mp
      (actionHom_eq_zero_of_biproduct f S hS)

end IsomorphismsAndBiproducts

section LeftRegular

end LeftRegular

end Tengoku.Brauerinduction.ClassFun
-- Tengoku: root names of this library moved to Tengoku.Brauerinduction so they do not collide with other libraries (generated)
