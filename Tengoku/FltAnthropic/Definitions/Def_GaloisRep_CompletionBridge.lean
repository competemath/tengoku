import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_FLTPrelim_Ramification

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

open scoped NNReal Pointwise

/--
@isnad1 id=isalgebr.0h0v.s4.92f995461263 from=translated src=- shape=3905abf2 vocab=c7f7e443
-/
local instance isAlgebraicQbar_cb : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) :=
  AlgebraicClosure.isAlgebraic ℚ
/--
@isnad1 id=isalgclo.0h0v.s4.728a7497b292 from=translated src=- shape=3905abf2 vocab=215a97a1
-/
local instance isAlgClosureQbar_cb : IsAlgClosure ℚ (AlgebraicClosure ℚ) :=
  ⟨inferInstance, inferInstance⟩
/--
@isnad1 id=normal.0h0v.s4.8393bcded6c9 from=translated src=- shape=3905abf2 vocab=399da0a7
-/
local instance normalQbar_cb : Normal ℚ (AlgebraicClosure ℚ) :=
  IsAlgClosure.normal ℚ (AlgebraicClosure ℚ)

variable (q : ℕ) [Fact q.Prime]

noncomputable def padicEmbedding : AlgebraicClosure ℚ →ₐ[ℚ] PadicAlgCl q :=
  IsAlgClosed.lift

noncomputable abbrev padicIntegers : ValuationSubring (PadicAlgCl q) :=
  (Valued.v : Valuation (PadicAlgCl q) ℝ≥0).valuationSubring

/--
@isnad1 id=iff.0h2v.s6.cc437adef143 from=translated src=- shape=849d83d2 vocab=09105930
-/
lemma mem_padicIntegers_iff {x : PadicAlgCl q} : x ∈ padicIntegers q ↔ ‖x‖₊ ≤ 1 := Iff.rfl

noncomputable def padicPlace : ValuationSubring (AlgebraicClosure ℚ) :=
  (padicIntegers q).comap (padicEmbedding q).toRingHom

/--
@isnad1 id=iff.0h2v.s7.8a9b92415736 from=translated src=- shape=9dd33c23 vocab=5d197dca
-/
theorem mem_padicPlace_iff {x : AlgebraicClosure ℚ} :
    x ∈ padicPlace q ↔ ‖padicEmbedding q x‖₊ ≤ 1 := Iff.rfl

section Galois

noncomputable local instance instAlgebraQbarPadic : Algebra (AlgebraicClosure ℚ) (PadicAlgCl q) :=
  (padicEmbedding q).toRingHom.toAlgebra
/--
@isnad1 id=isscalar.0h1v.s6.a7a56e0900fb from=translated src=- shape=6d2aa784 vocab=ec54d80c
-/
local instance instTowerQbarPadic :
    IsScalarTower ℚ (AlgebraicClosure ℚ) (PadicAlgCl q) :=
  IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
/--
@isnad1 id=isscalar.0h1v.s6.f8ba8c67b234 from=translated src=- shape=3a23afc2 vocab=fc4b9623
-/
local instance instTowerQqPadic : IsScalarTower ℚ ℚ_[q] (PadicAlgCl q) :=
  IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)

noncomputable def localGaloisToGlobal :
    (PadicAlgCl q ≃ₐ[ℚ_[q]] PadicAlgCl q) →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :=
  (AlgEquiv.restrictNormalHom (F := ℚ) (K₁ := PadicAlgCl q) (AlgebraicClosure ℚ)).comp
    (MonoidHom.mk' (fun τ => τ.restrictScalars ℚ) (fun _ _ => rfl))

/--
@isnad1 id=eq.0h3v.s11.b88a2922e8de from=translated src=- shape=4d05f261 vocab=f1e67a67
-/
theorem padicEmbedding_localGaloisToGlobal (τ : PadicAlgCl q ≃ₐ[ℚ_[q]] PadicAlgCl q)
    (x : AlgebraicClosure ℚ) :
    padicEmbedding q (localGaloisToGlobal q τ x) = τ (padicEmbedding q x) :=
  AlgEquiv.restrictNormal_commutes (τ.restrictScalars ℚ) (AlgebraicClosure ℚ) x

/--
@isnad1 id=eq.0h3v.s8.7056c51dd5d0 from=translated src=- shape=258d7b47 vocab=b04624cf
-/
theorem nnnorm_padicAlgCl_algEquiv (τ : PadicAlgCl q ≃ₐ[ℚ_[q]] PadicAlgCl q)
    (y : PadicAlgCl q) : ‖τ y‖₊ = ‖y‖₊ := by
  ext
  exact (spectralNorm_eq_of_equiv τ y).symm

/--
@isnad1 id=mem.0h2v.s11.2642a998f1d5 from=translated src=- shape=76e755bb vocab=0e2960b4
-/
theorem localGaloisToGlobal_mem_decompositionSubgroup
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
