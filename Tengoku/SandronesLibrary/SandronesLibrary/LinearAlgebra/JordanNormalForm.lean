/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.SandronesLibrary.SandronesLibrary.LinearAlgebra.JordanMatrix
import Tengoku.Seed.Algebra.DirectSum.LinearMap

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# LinearAlgebra / JordanNormalForm —— Jordan 标准基存在性

> **Entry**: linear-algebra.eigen.jordan-normal-form
-/

namespace SandronesLibrary.LinearAlgebra.Jordan

open SandronesLibrary.LinearAlgebra.VectorSpace
open SandronesLibrary.LinearAlgebra.Coordinates

variable {K V : Type*} [Field K] [AddCommGroup V] [LinearSpace K V]

/-- Jordan 标准矩阵的有限块数据。-/
structure JordanFormData (K : Type u) where
  Block : Type u
  blockFintype : Fintype Block
  eigenvalue : Block → K
  length : Block → ℕ

/-- 由有限个 Jordan 块组成的 Jordan 标准矩阵。-/
noncomputable def jordanNormalMatrix (d : JordanFormData K) :
    Matrix (Σ i : d.Block, Fin (d.length i + 1))
      (Σ i : d.Block, Fin (d.length i + 1)) K := by
  letI := d.blockFintype
  classical
  exact Matrix.blockDiagonal' (fun i => jordanBlock (d.eigenvalue i) (d.length i))

/-- `T` 在某组基下由数据 `d` 给出的 Jordan 标准矩阵表示。-/
def HasJordanNormalBasis (T : V →ₗ[K] V) (d : JordanFormData K) : Prop := by
  letI := d.blockFintype
  classical
  exact ∃ (b : (p : Σ i : d.Block, Fin (d.length i + 1)) → V)
    (hb : IsBasis K b), operatorMatrix b hb T = jordanNormalMatrix d

/-- 代数闭域上，有限维线性算子存在 Jordan 标准基。
@isnad1 id=ex.0h3v.s6.0e5295ed75da from=translated src=- shape=5900860b vocab=b4e0db36
-/
theorem exists_jordan_normal_basis [IsAlgClosed K] [IsFiniteDimensional K V]
    (T : V →ₗ[K] V) :
    ∃ d : JordanFormData K, HasJordanNormalBasis T d := by
  classical
  let F : Module.End K V := T
  let E := {μ : K // F.maxGenEigenspace μ ≠ ⊥}
  have hEfinite : Set.Finite {μ : K | F.maxGenEigenspace μ ≠ ⊥} :=
    WellFoundedGT.finite_ne_bot_of_iSupIndep F.independent_maxGenEigenspace
  letI : Fintype E := hEfinite.fintype
  let S : E → Submodule K V := fun e => F.maxGenEigenspace e.1
  letI : ∀ e : E, LinearSpace K (S e) := fun _ => ⟨inferInstance⟩
  have hIndependent : iSupIndep S := by
    exact F.independent_maxGenEigenspace.comp Subtype.val_injective
  have hSup : ⨆ e, S e = ⊤ := by
    apply top_unique
    rw [← F.iSup_maxGenEigenspace_eq_top]
    refine iSup_le fun μ => ?_
    by_cases hμ : F.maxGenEigenspace μ = ⊥
    · rw [hμ]
      exact bot_le
    · exact le_iSup S (⟨μ, hμ⟩ : E)
  have hInternal : DirectSum.IsInternal S :=
    DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top hIndependent hSup
  let N (e : E) : S e →ₗ[K] S e :=
    (F - algebraMap K (Module.End K V) e.1).restrict
      (F.mapsTo_maxGenEigenspace_of_comm
        (Algebra.mul_sub_algebraMap_commutes F e.1) e.1)
  have hNil (e : E) : IsNilpotent (N e) := by
    simpa [N, S] using
      (F.isNilpotent_restrict_maxGenEigenspace_sub_algebraMap e.1)
  let decomposition (e : E) :=
    nilpotent_exists_jordanBasisFamily (K := K) (V := S e) (N e) (hNil e)
  let r (e : E) : ℕ := (decomposition e).choose
  let length (e : E) : Fin (r e) → ℕ := (decomposition e).choose_spec.choose
  let chain (e : E) : (i : Fin (r e)) → Fin (length e i + 1) → S e :=
    (decomposition e).choose_spec.choose_spec.choose
  have hchain (e : E) :
      IsJordanBasisFamily (N e) (r e) (fun _ => 0) (length e) (chain e) :=
    (decomposition e).choose_spec.choose_spec.choose_spec
  have hNcoe (e : E) (x : S e) :
      ((N e x : S e) : V) = T (x : V) - e.1 • (x : V) := by
    rfl
  let localIndex (e : E) := Σ i : Fin (r e), Fin (length e i + 1)
  let localBasis (e : E) : Module.Basis (localIndex e) K (S e) :=
    Module.Basis.mk (hchain e).1.1 (by simpa [(hchain e).1.2])
  let Block := Σ e : E, Fin (r e)
  let blockLength : Block → ℕ := fun q => length q.1 q.2
  let blockEigenvalue : Block → K := fun q => q.1.1
  let b : (q : Block) → Fin (blockLength q + 1) → V :=
    fun q j => ((chain q.1 q.2 j : S q.1) : V)
  have hbChain (q : Block) : IsJordanChain T (blockEigenvalue q) (b q) := by
    rcases q with ⟨e, i⟩
    have hc := (hchain e).2 i
    refine ⟨?_, ?_, ?_⟩
    · intro hz
      apply hc.1
      exact Subtype.ext hz
    · have hz := congrArg Subtype.val hc.2.1
      simp only [zero_smul] at hz
      rw [hNcoe] at hz
      have hz' : T (chain e i 0 : V) - e.1 • (chain e i 0 : V) = 0 := by
        simpa [N, F, LinearMap.sub_apply] using hz
      exact sub_eq_zero.mp hz'
    · intro j
      have hs := congrArg Subtype.val (hc.2.2 j)
      simp only [zero_smul, zero_add] at hs
      rw [hNcoe] at hs
      have hs' : T (chain e i j.succ : V) - e.1 • (chain e i j.succ : V) =
          (chain e i j.castSucc : V) := by
        simpa [N, F, LinearMap.sub_apply] using hs
      change T (chain e i j.succ : V) =
        e.1 • (chain e i j.succ : V) + (chain e i j.castSucc : V)
      calc
        T (chain e i j.succ : V) =
            (chain e i j.castSucc : V) + e.1 • (chain e i j.succ : V) :=
          sub_eq_iff_eq_add.mp hs'
        _ = e.1 • (chain e i j.succ : V) + (chain e i j.castSucc : V) :=
          add_comm _ _
  let collected := hInternal.collectedBasis localBasis
  let assoc : (Σ q : Block, Fin (blockLength q + 1)) ≃
      (Σ e : E, localIndex e) := Equiv.sigmaAssoc
        (fun e (i : Fin (r e)) => Fin (length e i + 1))
  let globalBasis : Module.Basis (Σ q : Block, Fin (blockLength q + 1)) K V :=
    collected.reindex assoc.symm
  have hGlobalBasisCoe :
      (globalBasis : (Σ q : Block, Fin (blockLength q + 1)) → V) =
        fun p => b p.1 p.2 := by
    funext p
    rcases p with ⟨⟨e, i⟩, j⟩
    change globalBasis ⟨⟨e, i⟩, j⟩ = (chain e i j : V)
    rw [Module.Basis.reindex_apply]
    change collected ⟨e, ⟨i, j⟩⟩ = (chain e i j : V)
    rw [DirectSum.IsInternal.collectedBasis_coe]
    simp [localBasis]
  have hbBasis : IsBasis K (fun p : Σ q : Block, Fin (blockLength q + 1) =>
      b p.1 p.2) := by
    rw [← hGlobalBasisCoe]
    exact ⟨globalBasis.linearIndependent, by
      simpa using globalBasis.span_eq⟩
  letI : DecidableEq Block := Classical.decEq Block
  let d : JordanFormData K :=
    { Block := Block
      blockFintype := inferInstance
      eigenvalue := blockEigenvalue
      length := blockLength }
  refine ⟨d, ?_⟩
  dsimp [HasJordanNormalBasis]
  letI := d.blockFintype
  refine ⟨fun p => b p.1 p.2, hbBasis, ?_⟩
  simpa [d, jordanNormalMatrix] using
    (operatorMatrix_eq_blockDiagonal_jordan T blockEigenvalue blockLength b
      ⟨hbBasis, hbChain⟩)

end SandronesLibrary.LinearAlgebra.Jordan
