import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_FLTPrelim_Ramification

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/
namespace Tengoku.FltAnthropic end Tengoku.FltAnthropic open Tengoku.FltAnthropic
set_option autoImplicit false

open scoped NNReal Pointwise

local instance _root_.Tengoku.FltAnthropic.isAlgebraicQbar_cb : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) :=
  AlgebraicClosure.isAlgebraic ℚ
local instance _root_.Tengoku.FltAnthropic.isAlgClosureQbar_cb : IsAlgClosure ℚ (AlgebraicClosure ℚ) :=
  ⟨inferInstance, inferInstance⟩
local instance _root_.Tengoku.FltAnthropic.normalQbar_cb : Normal ℚ (AlgebraicClosure ℚ) :=
  IsAlgClosure.normal ℚ (AlgebraicClosure ℚ)

variable (q : ℕ) [Fact q.Prime]

noncomputable def _root_.Tengoku.FltAnthropic.padicEmbedding : AlgebraicClosure ℚ →ₐ[ℚ] PadicAlgCl q :=
  IsAlgClosed.lift

noncomputable abbrev _root_.Tengoku.FltAnthropic.padicIntegers : ValuationSubring (PadicAlgCl q) :=
  (Valued.v : Valuation (PadicAlgCl q) ℝ≥0).valuationSubring

lemma _root_.Tengoku.FltAnthropic.mem_padicIntegers_iff {x : PadicAlgCl q} : x ∈ padicIntegers q ↔ ‖x‖₊ ≤ 1 := Iff.rfl

noncomputable def _root_.Tengoku.FltAnthropic.padicPlace : ValuationSubring (AlgebraicClosure ℚ) :=
  (padicIntegers q).comap (padicEmbedding q).toRingHom

theorem _root_.Tengoku.FltAnthropic.mem_padicPlace_iff {x : AlgebraicClosure ℚ} :
    x ∈ padicPlace q ↔ ‖padicEmbedding q x‖₊ ≤ 1 := Iff.rfl

section Galois

noncomputable local instance _root_.Tengoku.FltAnthropic.instAlgebraQbarPadic : Algebra (AlgebraicClosure ℚ) (PadicAlgCl q) :=
  (padicEmbedding q).toRingHom.toAlgebra
local instance _root_.Tengoku.FltAnthropic.instTowerQbarPadic :
    IsScalarTower ℚ (AlgebraicClosure ℚ) (PadicAlgCl q) :=
  IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
local instance _root_.Tengoku.FltAnthropic.instTowerQqPadic : IsScalarTower ℚ ℚ_[q] (PadicAlgCl q) :=
  IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)

noncomputable def _root_.Tengoku.FltAnthropic.localGaloisToGlobal :
    (PadicAlgCl q ≃ₐ[ℚ_[q]] PadicAlgCl q) →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :=
  (AlgEquiv.restrictNormalHom (F := ℚ) (K₁ := PadicAlgCl q) (AlgebraicClosure ℚ)).comp
    (MonoidHom.mk' (fun τ => τ.restrictScalars ℚ) (fun _ _ => rfl))

theorem _root_.Tengoku.FltAnthropic.padicEmbedding_localGaloisToGlobal (τ : PadicAlgCl q ≃ₐ[ℚ_[q]] PadicAlgCl q)
    (x : AlgebraicClosure ℚ) :
    padicEmbedding q (localGaloisToGlobal q τ x) = τ (padicEmbedding q x) :=
  AlgEquiv.restrictNormal_commutes (τ.restrictScalars ℚ) (AlgebraicClosure ℚ) x

theorem _root_.Tengoku.FltAnthropic.nnnorm_padicAlgCl_algEquiv (τ : PadicAlgCl q ≃ₐ[ℚ_[q]] PadicAlgCl q)
    (y : PadicAlgCl q) : ‖τ y‖₊ = ‖y‖₊ := by
  ext
  exact (spectralNorm_eq_of_equiv τ y).symm

theorem _root_.Tengoku.FltAnthropic.localGaloisToGlobal_mem_decompositionSubgroup
    (τ : PadicAlgCl q ≃ₐ[ℚ_[q]] PadicAlgCl q) :
    localGaloisToGlobal q τ ∈ (padicPlace q).decompositionSubgroup ℚ := by
  rw [MulAction.mem_stabilizer_iff]
  apply SetLike.ext
  intro x
  rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
  have hinv : (localGaloisToGlobal q τ)⁻¹ = localGaloisToGlobal q τ⁻¹ := (map_inv _ τ).symm
  rw [AlgEquiv.smul_def, hinv]
  rw [mem_padicPlace_iff, mem_padicPlace_iff, padicEmbedding_localGaloisToGlobal,
    nnnorm_padicAlgCl_algEquiv]

end Galois
-- Tengoku: root names of this library moved to Tengoku.FltAnthropic so they do not collide with other libraries (generated)
