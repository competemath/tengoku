import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_HopfAlgebra_CharacterClosure

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_HopfAlgebra_map_mk_comul_eq_zero_and_counit_eq_zero_and_antipode_mem_of_mem_vanishingIdealOfPoints_ptSet.lean`: wrote out 2 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_export`, 1 `p2m_open`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_HopfAlgebra_map_mk_comul_eq_zero_and_counit_eq_zero_and_antipode_mem_of_mem_vanishingIdealOfPoints_ptSet
set_option autoImplicit false
open scoped TensorProduct

namespace HopfAlgebra
export _root_.HopfAlgebra (mk vanishingIdealOfPoints mem_vanishingIdealOfPoints_iff liftPoint_mk evalPair ptSet mem_ptSet_iff pointQuot)
open _root_.HopfAlgebra
namespace PointIdeal

open WithConv

variable {F : Type*} [Field F] {A : Type*} [CommRing A] [HopfAlgebra F A]
variable {L : Type*} [Field L] [Algebra F L]

theorem comul_clause (S : Submonoid (WithConv (A →ₐ[F] L)))
    (hsep : ∀ x : TensorProduct F (pointQuot S) (pointQuot S),
      (∀ (ν ν' : A →ₐ[F] L) (hν : ν ∈ ptSet S) (hν' : ν' ∈ ptSet S),
        evalPair (ptSet S) ν ν' hν hν' x = 0) → x = 0)
    (a : A) (ha : a ∈ vanishingIdealOfPoints (ptSet S)) :
    Algebra.TensorProduct.map
        (Ideal.Quotient.mkₐ F (vanishingIdealOfPoints (ptSet S)))
        (Ideal.Quotient.mkₐ F (vanishingIdealOfPoints (ptSet S)))
        (Coalgebra.comul (R := F) a) = 0 := by
  apply hsep
  intro ν ν' hν hν'
  have key : (evalPair (ptSet S) ν ν' hν hν').comp
      (Algebra.TensorProduct.map
        (Ideal.Quotient.mkₐ F (vanishingIdealOfPoints (ptSet S)))
        (Ideal.Quotient.mkₐ F (vanishingIdealOfPoints (ptSet S)))) =
      (Algebra.TensorProduct.lmul' F (S := L)).comp (Algebra.TensorProduct.map ν ν') := by
    ext x
    · simp [evalPair, Ideal.Quotient.mkₐ_eq_mk, liftPoint_mk]
    · simp [evalPair, Ideal.Quotient.mkₐ_eq_mk, liftPoint_mk]
  have happ := congrArg (fun φ : A ⊗[F] A →ₐ[F] L => φ (Coalgebra.comul (R := F) a)) key
  simp only [AlgHom.comp_apply] at happ
  rw [happ]

  have hmem : toConv ν * toConv ν' ∈ S := S.mul_mem hν hν'
  have hpt : (toConv ν * toConv ν').ofConv ∈ ptSet S := by
    rw [mem_ptSet_iff]; exact hmem
  have h0 : (toConv ν * toConv ν').ofConv a = 0 := (mem_vanishingIdealOfPoints_iff _ _).mp ha _ hpt
  rw [AlgHom.convMul_def] at h0
  simpa [Bialgebra.comulAlgHom_apply] using h0

theorem counit_clause (S : Submonoid (WithConv (A →ₐ[F] L)))
    (a : A) (ha : a ∈ vanishingIdealOfPoints (ptSet S)) :
    Coalgebra.counit (R := F) a = 0 := by
  have hpt : (1 : WithConv (A →ₐ[F] L)).ofConv ∈ ptSet S := by
    rw [mem_ptSet_iff]; exact S.one_mem
  have h0 : (1 : WithConv (A →ₐ[F] L)).ofConv a = 0 := (mem_vanishingIdealOfPoints_iff _ _).mp ha _ hpt
  have h1 : (1 : WithConv (A →ₐ[F] L)).ofConv a = algebraMap F L (Coalgebra.counit (R := F) a) :=
    AlgHom.convOne_apply a
  rw [h1] at h0
  exact (algebraMap F L).injective (by rw [h0, map_zero])

theorem antipode_clause (S : Submonoid (WithConv (A →ₐ[F] L)))
    (hinv : ∀ ν ∈ ptSet S, ∃ ν' ∈ ptSet S,
      ν'.toLinearMap = ν.toLinearMap ∘ₗ HopfAlgebraStruct.antipode (R := F))
    (a : A) (ha : a ∈ vanishingIdealOfPoints (ptSet S)) :
    HopfAlgebraStruct.antipode (R := F) a ∈ vanishingIdealOfPoints (ptSet S) := by
  rw [mem_vanishingIdealOfPoints_iff]
  intro ν hν
  obtain ⟨ν', hν', hcomp⟩ := hinv ν hν
  have := congrArg (fun φ : A →ₗ[F] L => φ a) hcomp
  simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply] at this
  rw [← this]
  exact (mem_vanishingIdealOfPoints_iff _ _).mp ha ν' hν'

end PointIdeal
end HopfAlgebra

theorem solution
    {F : Type*} [Field F] {A : Type*} [CommRing A] [HopfAlgebra F A]
    {L : Type*} [Field L] [Algebra F L]
    (S : Submonoid (WithConv (A →ₐ[F] L)))
    (hsep : ∀ x : TensorProduct F (HopfAlgebra.pointQuot S) (HopfAlgebra.pointQuot S),
      (∀ (ν ν' : A →ₐ[F] L) (hν : ν ∈ HopfAlgebra.ptSet S) (hν' : ν' ∈ HopfAlgebra.ptSet S),
        HopfAlgebra.evalPair (HopfAlgebra.ptSet S) ν ν' hν hν' x = 0) → x = 0)
    (hinv : ∀ ν ∈ HopfAlgebra.ptSet S, ∃ ν' ∈ HopfAlgebra.ptSet S,
      ν'.toLinearMap = ν.toLinearMap ∘ₗ HopfAlgebraStruct.antipode (R := F)) :
    (∀ a ∈ HopfAlgebra.vanishingIdealOfPoints (HopfAlgebra.ptSet S),
      Algebra.TensorProduct.map
        (Ideal.Quotient.mkₐ F (HopfAlgebra.vanishingIdealOfPoints (HopfAlgebra.ptSet S)))
        (Ideal.Quotient.mkₐ F (HopfAlgebra.vanishingIdealOfPoints (HopfAlgebra.ptSet S)))
        (Coalgebra.comul (R := F) a) = 0) ∧
    (∀ a ∈ HopfAlgebra.vanishingIdealOfPoints (HopfAlgebra.ptSet S), Coalgebra.counit (R := F) a = 0) ∧
    (∀ a ∈ HopfAlgebra.vanishingIdealOfPoints (HopfAlgebra.ptSet S),
      HopfAlgebraStruct.antipode (R := F) a ∈ HopfAlgebra.vanishingIdealOfPoints (HopfAlgebra.ptSet S)) :=
  ⟨HopfAlgebra.PointIdeal.comul_clause S hsep, HopfAlgebra.PointIdeal.counit_clause S,
    HopfAlgebra.PointIdeal.antipode_clause S hinv⟩
