import Tengoku.FormalizeTubalDemystPaper.TubalTensor.Prerequisites.JointDiag
import Tengoku.Seed.Analysis.Complex.Polynomial.Basic
import Tengoku.Seed.LinearAlgebra.Eigenspace.Semisimple
import Tengoku.Seed.LinearAlgebra.Eigenspace.Triangularizable
import Tengoku.Seed.LinearAlgebra.Dimension.Finrank

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
  TubalTensor/Prerequisites/MatDiagBridge.lean
  Bridge lemma: from Mathlib's semisimple endomorphism theory to our `IsMatDiag` predicate.

  Key result: A real matrix whose complexification is annihilated by a squarefree
  polynomial over ℂ is diagonalizable in the `IsMatDiag` sense (∃ S D with
  IsUnit S, D.IsDiag, A.map ↑ = S * D * S⁻¹).
-/

namespace TubalTensor

open Matrix Complex Module Polynomial BigOperators

variable {n : ℕ}

private abbrev toℂ : ℝ → ℂ := (↑)

/-- The complexification of a real matrix as an endomorphism of ℂⁿ.-/
private noncomputable abbrev complexEnd (A : Matrix (Fin n) (Fin n) ℝ) :
    Module.End ℂ (Fin n → ℂ) :=
  (A.map toℂ).mulVecLin

/-! ## Core bridge: eigenspaces span ⊤ → IsMatDiag -/

/-- Columns of a matrix as a family of vectors.-/
private theorem col_of_eq {m : ℕ} (S : Matrix (Fin m) (Fin m) ℂ)
    (v : Fin m → Fin m → ℂ) (hv : ∀ i j, S i j = v j i) :
    S.col = v := by
  ext j i; simp [Matrix.col, Matrix.transpose_apply, hv]

set_option synthInstance.maxHeartbeats 40000 in
/-- If the eigenspaces of the complexified matrix span the whole space,
    then A is diagonalizable in the `IsMatDiag` sense.-/
theorem isMatDiag_of_iSup_eigenspace_eq_top
    (A : Matrix (Fin n) (Fin n) ℝ)
    (h_top : (⨆ μ, (complexEnd A).eigenspace μ) = ⊤) :
    IsMatDiag A := by
  classical
  set Ac := A.map toℂ with hAc_def
  set f := complexEnd A with hf_def
  -- Step 1: Eigenspaces form an internal direct sum
  have h_ind : iSupIndep f.eigenspace := f.eigenspaces_iSupIndep
  have h_int : DirectSum.IsInternal (fun μ : ℂ => f.eigenspace μ) :=
    DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top h_ind h_top
  -- Step 2: Choose a basis for each eigenspace
  haveI (μ : ℂ) : Module.Free ℂ ↥(f.eigenspace μ) :=
    @Module.Free.of_divisionRing ℂ ↥(f.eigenspace μ) _ _ _
  set bμ := fun μ : ℂ => Module.finBasis ℂ ↥(f.eigenspace μ)
  -- Step 3: Collected basis (indexed by sigma type)
  set cb := h_int.collectedBasis bμ with hcb_def
  -- Step 4: Fintype on the sigma type and cardinality = n
  haveI : Finite (Σ μ : ℂ, Fin (finrank ℂ ↥(f.eigenspace μ))) :=
    Module.Finite.finite_basis cb
  haveI : Fintype (Σ μ : ℂ, Fin (finrank ℂ ↥(f.eigenspace μ))) := Fintype.ofFinite _
  have h_card : Fintype.card (Σ μ : ℂ, Fin (finrank ℂ ↥(f.eigenspace μ))) = n := by
    have h1 := finrank_eq_card_basis cb
    have h2 : finrank ℂ (Fin n → ℂ) = n := finrank_fin_fun ℂ
    linarith
  -- Step 5: Reindex to Fin n
  set e := (Fintype.equivFin _).trans (finCongr h_card)
  set b := cb.reindex e with hb_def
  -- Step 6: Eigenvalue for each basis vector
  set ev : Fin n → ℂ := fun j => (e.symm j).1
  -- Step 7: Each basis vector is an eigenvector
  have h_mem : ∀ j, (b j : Fin n → ℂ) ∈ f.eigenspace (ev j) := by
    intro j
    simp only [hb_def, Basis.reindex_apply, ev]
    rw [DirectSum.IsInternal.collectedBasis_coe]
    exact SetLike.coe_mem _
  have h_eig : ∀ j, f (b j) = ev j • (b j : Fin n → ℂ) := by
    intro j
    have hj := h_mem j
    rwa [Module.End.mem_eigenspace_iff] at hj
  -- Step 8: Define S and D directly
  set S : Matrix (Fin n) (Fin n) ℂ := Matrix.of (fun i j => (b j : Fin n → ℂ) i) with hS_def
  set D := Matrix.diagonal ev
  -- Step 9: S is invertible (columns are a basis, hence linearly independent)
  have hS_col : S.col = (↑b : Fin n → Fin n → ℂ) :=
    col_of_eq S (↑b) (fun i j => by simp [hS_def, Matrix.of_apply])
  have hSu : IsUnit S :=
    linearIndependent_cols_iff_isUnit.mp (hS_col ▸ b.linearIndependent)
  -- Step 10: D is diagonal
  have hDdiag : D.IsDiag := Matrix.isDiag_diagonal ev
  -- Step 11: Show Ac = S * D * S⁻¹
  -- Helper: S *ᵥ eⱼ = b j (column j of S)
  have hS_mulVec : ∀ j, S *ᵥ (Pi.single j 1 : Fin n → ℂ) = b j := by
    intro j; ext i
    simp [mulVec, dotProduct, hS_def, Matrix.of_apply, Pi.single_apply, Finset.sum_ite_eq']
  -- Ac * S = S * D (entry-by-entry)
  have hAS : Ac * S = S * D := by
    ext i j
    -- LHS entry: (Ac * S) i j = ∑ k, Ac i k * S k j = ∑ k, Ac i k * (b j) k = (Ac *ᵥ b j) i
    -- RHS entry: (S * D) i j = ∑ k, S i k * D k j = ∑ k, (b k) i * diag(ev) k j
    --          = (b j) i * ev j  (only k=j contributes)
    -- From eigenvector property: (Ac *ᵥ b j) i = ev j * (b j) i
    show ∑ k, Ac i k * S k j = ∑ k, S i k * D k j
    -- Simplify LHS
    have hLHS : ∑ k, Ac i k * S k j = (Ac *ᵥ (b j : Fin n → ℂ)) i := by
      simp only [mulVec, dotProduct, hS_def, Matrix.of_apply]
    -- Simplify RHS: S i k = (b k) i, D k j = diagonal ev k j = if k = j then ev k else 0
    have hRHS : ∑ k, S i k * D k j = (b j : Fin n → ℂ) i * ev j := by
      simp only [hS_def, Matrix.of_apply, D, diagonal_apply, mul_ite, mul_zero,
        Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    rw [hLHS, hRHS]
    -- Goal: (Ac *ᵥ b j) i = (b j) i * ev j
    have h := congr_fun (h_eig j) i
    simp only [hf_def, complexEnd, Matrix.mulVecLin_apply, Pi.smul_apply, smul_eq_mul] at h
    rw [h, mul_comm]
  -- Ac = S * D * S⁻¹
  have hSS : S * S⁻¹ = 1 :=
    mul_nonsing_inv S ((Matrix.isUnit_iff_isUnit_det S).mp hSu)
  refine ⟨S, D, hSu, hDdiag, ?_⟩
  calc Ac = Ac * 1 := (mul_one Ac).symm
    _ = Ac * (S * S⁻¹) := by rw [hSS]
    _ = Ac * S * S⁻¹ := (mul_assoc Ac S S⁻¹).symm
    _ = S * D * S⁻¹ := by rw [hAS]

/-! ## From squarefree annihilating polynomial to IsMatDiag -/

/-- A real matrix whose complexification is annihilated by a squarefree polynomial
    over ℂ is diagonalizable in the `IsMatDiag` sense.-/
theorem isMatDiag_of_squarefree_aeval_eq_zero
    (A : Matrix (Fin n) (Fin n) ℝ)
    {p : ℂ[X]} (hp_sq : Squarefree p)
    (hp_ann : Polynomial.aeval (complexEnd A) p = 0) :
    IsMatDiag A := by
  set f := complexEnd A
  have h_ss : f.IsSemisimple :=
    Module.End.isSemisimple_of_squarefree_aeval_eq_zero hp_sq hp_ann
  haveI : FiniteDimensional ℂ (Fin n → ℂ) := inferInstance
  haveI : IsAlgClosed ℂ := Complex.isAlgClosed
  have h_fss := h_ss.isFinitelySemisimple (R := ℂ) (M := Fin n → ℂ)
  have h_eq : ∀ μ : ℂ, f.maxGenEigenspace μ = f.eigenspace μ :=
    fun μ => h_fss.maxGenEigenspace_eq_eigenspace μ
  have h_top_gen : (⨆ μ, f.maxGenEigenspace μ) = ⊤ :=
    Module.End.iSup_maxGenEigenspace_eq_top f
  have h_top : (⨆ μ, f.eigenspace μ) = ⊤ := by
    simp_rw [← h_eq]; exact h_top_gen
  exact isMatDiag_of_iSup_eigenspace_eq_top A h_top

end TubalTensor
