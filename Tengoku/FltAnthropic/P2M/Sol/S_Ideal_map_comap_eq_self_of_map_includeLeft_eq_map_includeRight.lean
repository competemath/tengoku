import Tengoku.Seed.RingTheory.Flat.FaithfullyFlat.Algebra
import Tengoku.Seed.RingTheory.TensorProduct.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_Ideal_map_comap_eq_self_of_map_includeLeft_eq_map_includeRight.lean`: wrote out 4 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 2 `p2m_export`, 2 `p2m_open`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_Ideal_map_comap_eq_self_of_map_includeLeft_eq_map_includeRight

set_option autoImplicit false

universe u

open TensorProduct

namespace Ideal
export _root_.Ideal (map_le_iff_le_comap map_map Quotient.eq_zero_iff_mem Quotient.mkₐ comap_map_eq_self_of_faithfullyFlat Quotient.mk map_id map quotientMap_injective' ext map_comap_le quotientMapₐ mem_map_of_mem mem_comap map_mono comap Quotient.mkₐ_eq_mk)
open _root_.Ideal

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]

def DescentCondition (I : Ideal B) : Prop :=
  I.map (Algebra.TensorProduct.includeLeftRingHom : B →+* B ⊗[A] B) =
    I.map ((Algebra.TensorProduct.includeRight : B →ₐ[A] B ⊗[A] B) : B →+* B ⊗[A] B)

/--
@isnad1 id=eq.1h4v.s7.df7dfc02a30e from=translated src=- shape=7f34b0f8 vocab=43a65aae
-/
theorem map_comap_eq_self_of_descentCondition_of_section (σ : B →ₐ[A] A) (I : Ideal B)
    (hI : DescentCondition (A := A) I) :
    (I.comap (algebraMap A B)).map (algebraMap A B) = I := by
  refine le_antisymm Ideal.map_comap_le ?_

  let θ : B ⊗[A] B →ₐ[A] B :=
    Algebra.TensorProduct.lift ((Algebra.ofId A B).comp σ) (AlgHom.id A B) fun _ _ => Commute.all _ _
  have hθL : (θ : B ⊗[A] B →+* B).comp
      (Algebra.TensorProduct.includeLeftRingHom : B →+* B ⊗[A] B) =
      (algebraMap A B).comp (σ : B →+* A) := by
    ext b
    simp [θ, Algebra.TensorProduct.includeLeftRingHom]
  have hθR : (θ : B ⊗[A] B →+* B).comp
      ((Algebra.TensorProduct.includeRight : B →ₐ[A] B ⊗[A] B) : B →+* B ⊗[A] B) = RingHom.id B := by
    ext b
    simp [θ]

  have h2 : I.map (σ : B →+* A) ≤ I.comap (algebraMap A B) := by
    rw [Ideal.map_le_iff_le_comap]
    intro i hi
    change algebraMap A B (σ i) ∈ I
    have hmem : Algebra.TensorProduct.includeLeftRingHom i ∈
        I.map ((Algebra.TensorProduct.includeRight : B →ₐ[A] B ⊗[A] B) : B →+* B ⊗[A] B) := by
      rw [← show I.map _ = _ from hI]
      exact Ideal.mem_map_of_mem _ hi
    have := Ideal.mem_map_of_mem (θ : B ⊗[A] B →+* B) hmem
    rw [Ideal.map_map, hθR, Ideal.map_id] at this
    convert this using 1
    exact (RingHom.congr_fun hθL i).symm

  have h1 : I ≤ (I.map (σ : B →+* A)).map (algebraMap A B) := by
    intro i hi
    have hmem : ((Algebra.TensorProduct.includeRight : B →ₐ[A] B ⊗[A] B) : B →+* B ⊗[A] B) i ∈
        I.map (Algebra.TensorProduct.includeLeftRingHom : B →+* B ⊗[A] B) := by
      rw [show I.map _ = _ from hI]
      exact Ideal.mem_map_of_mem _ hi
    have := Ideal.mem_map_of_mem (θ : B ⊗[A] B →+* B) hmem
    rw [Ideal.map_map, hθL, ← Ideal.map_map] at this
    convert this using 1
    exact (RingHom.congr_fun hθR i).symm
  exact h1.trans (Ideal.map_mono h2)

end Ideal

namespace Ideal
export _root_.Ideal (map_le_iff_le_comap map_map Quotient.eq_zero_iff_mem Quotient.mkₐ comap_map_eq_self_of_faithfullyFlat Quotient.mk map_id map quotientMap_injective' ext map_comap_le quotientMapₐ mem_map_of_mem mem_comap map_mono comap Quotient.mkₐ_eq_mk)
open _root_.Ideal

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]

/--
@isnad1 id=eq.0h3v.s10.3bb159ebbc4f from=translated src=- shape=4d78ea98 vocab=d03fbfa7
-/
theorem comap_includeLeft_map_includeRight [Module.Flat A B] (I : Ideal B) :
    (I.map ((Algebra.TensorProduct.includeRight : B →ₐ[A] B ⊗[A] B) : B →+* B ⊗[A] B)).comap
        (Algebra.TensorProduct.includeLeftRingHom : B →+* B ⊗[A] B) =
      (I.comap (algebraMap A B)).map (algebraMap A B) := by
  set I₀ := I.comap (algebraMap A B) with hI₀
  refine le_antisymm ?_ ?_
  · intro b hb
    rw [Ideal.mem_comap] at hb

    let g : B ⊗[A] B →ₐ[A] B ⊗[A] (B ⧸ I) :=
      Algebra.TensorProduct.map (AlgHom.id A B) (Ideal.Quotient.mkₐ A I)
    have hker : I.map ((Algebra.TensorProduct.includeRight : B →ₐ[A] B ⊗[A] B) : B →+* B ⊗[A] B) ≤
        RingHom.ker (g : B ⊗[A] B →+* B ⊗[A] (B ⧸ I)) := by
      rw [Ideal.map_le_iff_le_comap]
      intro i hi
      rw [Ideal.mem_comap, RingHom.mem_ker]
      change g ((1 : B) ⊗ₜ[A] i) = 0
      rw [show g ((1 : B) ⊗ₜ[A] i) = (AlgHom.id A B 1) ⊗ₜ[A] (Ideal.Quotient.mkₐ A I i) from
        Algebra.TensorProduct.map_tmul _ _ _ _, Ideal.Quotient.mkₐ_eq_mk,
        Ideal.Quotient.eq_zero_iff_mem.mpr hi, TensorProduct.tmul_zero]
    have hb0 : b ⊗ₜ[A] (1 : B ⧸ I) = 0 := by
      have := hker hb
      simpa [g, Algebra.TensorProduct.includeLeftRingHom] using this

    have hH : I₀ ≤ I.comap (Algebra.ofId A B : A →+* B) := le_of_eq hI₀
    let ι : (A ⧸ I₀) →ₐ[A] (B ⧸ I) := Ideal.quotientMapₐ I (Algebra.ofId A B) hH
    have hι : Function.Injective ι.toLinearMap :=
      Ideal.quotientMap_injective' (I := I) (f := (Algebra.ofId A B : A →+* B)) (H := hH)
        (le_of_eq hI₀.symm)
    have hinj := Module.Flat.lTensor_preserves_injective_linearMap (M := B) ι.toLinearMap hι
    have h1 : (LinearMap.lTensor B ι.toLinearMap) (b ⊗ₜ[A] (1 : A ⧸ I₀)) = 0 := by
      rw [LinearMap.lTensor_tmul, AlgHom.toLinearMap_apply, map_one, hb0]
    have h2 : b ⊗ₜ[A] (1 : A ⧸ I₀) = 0 := hinj (by rw [h1, map_zero])

    have h3 : (Ideal.Quotient.mk (I₀.map (algebraMap A B)) b) = 0 := by
      apply (Algebra.TensorProduct.quotIdealMapEquivTensorQuot B I₀).injective
      rw [map_zero, Algebra.TensorProduct.quotIdealMapEquivTensorQuot_mk, h2]
    exact Ideal.Quotient.eq_zero_iff_mem.mp h3
  · rw [Ideal.map_le_iff_le_comap]
    intro a ha
    rw [Ideal.mem_comap] at ha
    rw [Ideal.mem_comap, Ideal.mem_comap]
    have : Algebra.TensorProduct.includeLeftRingHom (algebraMap A B a) =
        (Algebra.TensorProduct.includeRight : B →ₐ[A] B ⊗[A] B) (algebraMap A B a) := by
      simp [Algebra.TensorProduct.includeLeftRingHom, Algebra.algebraMap_eq_smul_one,
        TensorProduct.smul_tmul]
    rw [this]
    exact Ideal.mem_map_of_mem _ ha

/--
@isnad1 id=eq.1h3v.s7.25c3c4f30762 from=translated src=- shape=3f2d1879 vocab=b6b92010
-/
theorem map_comap_eq_self_of_descentCondition [Module.FaithfullyFlat A B] (I : Ideal B)
    (hI : DescentCondition (A := A) I) :
    (I.comap (algebraMap A B)).map (algebraMap A B) = I := by

  set iL : B →+* B ⊗[A] B := Algebra.TensorProduct.includeLeftRingHom with hiL
  set iR : B →+* B ⊗[A] B :=
    ((Algebra.TensorProduct.includeRight : B →ₐ[A] B ⊗[A] B) : B →+* B ⊗[A] B) with hiR
  have hI' : I.map iL = I.map iR := hI

  let jL : B ⊗[A] B →+* (B ⊗[A] B) ⊗[B] (B ⊗[A] B) := Algebra.TensorProduct.includeLeftRingHom
  let jR : B ⊗[A] B →+* (B ⊗[A] B) ⊗[B] (B ⊗[A] B) :=
    ((Algebra.TensorProduct.includeRight : (B ⊗[A] B) →ₐ[B] (B ⊗[A] B) ⊗[B] (B ⊗[A] B)) : B ⊗[A] B →+* (B ⊗[A] B) ⊗[B] (B ⊗[A] B))

  let χ₁ : B →ₐ[A] (B ⊗[A] B) ⊗[B] (B ⊗[A] B) :=
    ((Algebra.TensorProduct.includeLeft : (B ⊗[A] B) →ₐ[B] (B ⊗[A] B) ⊗[B] (B ⊗[A] B)).restrictScalars A).comp
      (Algebra.TensorProduct.includeRight : B →ₐ[A] B ⊗[A] B)
  let χ₂ : B →ₐ[A] (B ⊗[A] B) ⊗[B] (B ⊗[A] B) :=
    ((Algebra.TensorProduct.includeRight : (B ⊗[A] B) →ₐ[B] (B ⊗[A] B) ⊗[B] (B ⊗[A] B)).restrictScalars A).comp
      (Algebra.TensorProduct.includeRight : B →ₐ[A] B ⊗[A] B)
  let χ : B ⊗[A] B →ₐ[A] (B ⊗[A] B) ⊗[B] (B ⊗[A] B) :=
    Algebra.TensorProduct.lift χ₁ χ₂ fun x y => Commute.all (χ₁ x) (χ₂ y)
  have hχL : (χ : B ⊗[A] B →+* (B ⊗[A] B) ⊗[B] (B ⊗[A] B)).comp iL = jL.comp iR := by
    ext b
    simp [χ, χ₁, χ₂, iL, iR, jL, Algebra.TensorProduct.includeLeftRingHom]
    rfl
  have hχR : (χ : B ⊗[A] B →+* (B ⊗[A] B) ⊗[B] (B ⊗[A] B)).comp iR = jR.comp iR := by
    ext b
    simp [χ, χ₁, χ₂, iR, jR]
    rfl
  have hDC : DescentCondition (A := B) (I.map iR) := by
    change (I.map iR).map jL = (I.map iR).map jR
    rw [Ideal.map_map, Ideal.map_map, ← hχL, ← hχR, ← Ideal.map_map, ← Ideal.map_map, hI']

  have hsplit := map_comap_eq_self_of_descentCondition_of_section
    (Algebra.TensorProduct.lmul'' A (S := B)) (I.map iR) hDC

  have halg : algebraMap B (B ⊗[A] B) = iL := rfl
  rw [halg, comap_includeLeft_map_includeRight] at hsplit

  rw [← hI'] at hsplit
  have := congrArg (fun J => J.comap iL) hsplit
  rwa [← halg, Ideal.comap_map_eq_self_of_faithfullyFlat,
    Ideal.comap_map_eq_self_of_faithfullyFlat] at this

end Ideal

/--
@isnad1 id=eq.1h3v.s10.62d2dcf0372e from=translated src=- shape=8018e05b vocab=41d2937d
-/
theorem solution
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B] [Module.FaithfullyFlat A B]
    (I : Ideal B)
    (hI : I.map (Algebra.TensorProduct.includeLeftRingHom : B →+* B ⊗[A] B) =
      I.map ((Algebra.TensorProduct.includeRight : B →ₐ[A] B ⊗[A] B) : B →+* B ⊗[A] B)) :
    (I.comap (algebraMap A B)).map (algebraMap A B) = I :=
  Ideal.map_comap_eq_self_of_descentCondition I hI
