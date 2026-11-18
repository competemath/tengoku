import Tengoku.Seed.RingTheory.Jacobson.Ring
import Tengoku.Seed.FieldTheory.IsAlgClosed.Basic
import Tengoku.Seed.RingTheory.LocalRing.ResidueField.Basic
import Tengoku.Seed.RingTheory.FiniteType
import Tengoku.Seed.RingTheory.Finiteness.Quotient

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_IsLocalRing_exists_algHom_residueField_ker_eq_of_isMaximal_of_finiteType.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_IsLocalRing_exists_algHom_residueField_ker_eq_of_isMaximal_of_finiteType

set_option autoImplicit false

universe u v

open IsLocalRing

/--
@isnad1 id=ex.1h3v.s8.804ca7f72658 from=translated src=- shape=f25143a0 vocab=4eb10643
-/
theorem solution
    {A : Type u} [CommRing A] [IsLocalRing A] [IsAlgClosed (ResidueField A)]
    {C : Type v} [CommRing C] [Algebra A C] [Algebra.FiniteType A C]
    (y : Ideal C) [y.IsMaximal] (hy : (maximalIdeal A).map (algebraMap A C) ≤ y) :
    ∃ ψ : C →ₐ[A] ResidueField A, RingHom.ker ψ.toRingHom = y := by
  classical
  letI : Field (C ⧸ y) := Ideal.Quotient.field y

  have hker : ∀ a ∈ maximalIdeal A, ((Ideal.Quotient.mk y).comp (algebraMap A C)) a = 0 := by
    intro a ha
    rw [RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem]
    exact hy (Ideal.mem_map_of_mem _ ha)
  let f : ResidueField A →+* C ⧸ y := Ideal.Quotient.lift (maximalIdeal A) ((Ideal.Quotient.mk y).comp (algebraMap A C)) hker
  have hf : ∀ a : A, f (residue A a) = Ideal.Quotient.mk y (algebraMap A C a) := fun a => rfl
  letI : Algebra (ResidueField A) (C ⧸ y) := f.toAlgebra
  haveI : IsScalarTower A (ResidueField A) (C ⧸ y) :=
    IsScalarTower.of_algebraMap_eq (fun a => (hf a).symm)

  haveI : Algebra.FiniteType A (C ⧸ y) :=
    (‹Algebra.FiniteType A C›).of_surjective (Ideal.Quotient.mkₐ A y) (Ideal.Quotient.mkₐ_surjective A y)
  haveI : Algebra.FiniteType (ResidueField A) (C ⧸ y) :=
    Algebra.FiniteType.of_restrictScalars_finiteType A (ResidueField A) (C ⧸ y)
  haveI : Module.Finite (ResidueField A) (C ⧸ y) := finite_of_finite_type_of_isJacobsonRing (ResidueField A) (C ⧸ y)
  haveI : Algebra.IsIntegral (ResidueField A) (C ⧸ y) := Algebra.IsIntegral.of_finite (ResidueField A) (C ⧸ y)

  have hbij : Function.Bijective (algebraMap (ResidueField A) (C ⧸ y)) :=
    IsAlgClosed.algebraMap_bijective_of_isIntegral (k := ResidueField A) (K := C ⧸ y)
  let e : ResidueField A ≃+* C ⧸ y := RingEquiv.ofBijective (algebraMap (ResidueField A) (C ⧸ y)) hbij
  have he : ∀ k : ResidueField A, e k = algebraMap (ResidueField A) (C ⧸ y) k := fun _ => rfl

  let ψ₀ : C →+* ResidueField A := e.symm.toRingHom.comp (Ideal.Quotient.mk y)
  have hψ₀ : ∀ c : C, e (ψ₀ c) = Ideal.Quotient.mk y c := fun c => e.apply_symm_apply _
  have hcomm : ∀ a : A, ψ₀ (algebraMap A C a) = algebraMap A (ResidueField A) a := by
    intro a
    apply e.injective
    rw [hψ₀, he]
    show Ideal.Quotient.mk y (algebraMap A C a) = f (algebraMap A (ResidueField A) a)
    exact (hf a).symm
  refine ⟨⟨ψ₀, hcomm⟩, ?_⟩
  ext c
  rw [RingHom.mem_ker]
  show ψ₀ c = 0 ↔ c ∈ y
  rw [← Ideal.Quotient.eq_zero_iff_mem, ← hψ₀, map_eq_zero_iff _ e.injective]
