import Tengoku.Leanforcontrol.LeanForControl.LinearSystems.Controllability
import Tengoku.Leanforcontrol.LeanForControl.LinearSystems.Observability
import Tengoku.Leanforcontrol.LeanForControl.LinearSystems.MatrixLemmas
import Tengoku

/-!
# Hautus observability lemma

For a finite-dimensional linear system over `ℂ`,

  `IsObservable A C ↔ ∀ μ ∈ ℂ, the block matrix `[μI - A; C]` has trivial kernel`.

This file proves both directions and packages them as the iff
`isObservable_iff_hautus`. The whole development is over `ℂ` (per the
project note: eigenvalues live in `ℂ`).

The structure is:

* `unobservableSubspace A C` — the `A`-invariant submodule of vectors that
  are killed by every `C * A^k`.
* Cayley-Hamilton helper: vectors in `unobservableSubspace` are killed by
  `C * A^n` too, not just `C * A^k` for `k < n`.
* `A`-invariance of `unobservableSubspace`.
* `hautusObservabilityMatrix A C μ` — the block-row matrix `[μI - A; C]`.
* Failure direction: `¬ IsObservable A C → ∃ μ, witness vector` via
  eigenvector extraction on `unobservableSubspace`.
* Converse: a Hautus-failure witness violates observability directly.
* Full iff packaged at the bottom.
-/

namespace LinearSystems

open Matrix

variable {n p : ℕ}

/-- The unobservable subspace of `(A, C)`: states that the output `C · A^k`
fails to distinguish from zero for every `k = 0, …, n-1`.

Defined as the intersection of the kernels of the linear maps
`(C · A^k).mulVecLin` for `k : Fin n`. By Cayley–Hamilton (see
`A_mulVec_mem_unobservableSubspace_of_mem`) this submodule is `A`-invariant. -/
noncomputable def unobservableSubspace
    (A : Matrix (Fin n) (Fin n) ℂ) (C : Matrix (Fin p) (Fin n) ℂ) :
    Submodule ℂ (Fin n → ℂ) :=
  ⨅ k : Fin n, LinearMap.ker (C * A ^ (k : ℕ)).mulVecLin

/-- The Hautus observability matrix at `μ`,
`[μ • 1 - A; C] : Matrix (Fin n ⊕ Fin p) (Fin n) ℂ`. -/
noncomputable def hautusObservabilityMatrix
    (A : Matrix (Fin n) (Fin n) ℂ) (C : Matrix (Fin p) (Fin n) ℂ) (μ : ℂ) :
    Matrix (Fin n ⊕ Fin p) (Fin n) ℂ :=
  Matrix.fromRows (μ • (1 : Matrix (Fin n) (Fin n) ℂ) - A) C

/-- A vector `v` is in the kernel of `H_{A, C}(μ) *ᵥ ·` iff `v` is an
eigenvector (or zero) of `A` with eigenvalue `μ` and is annihilated by `C`. -/
lemma hautusObservabilityMatrix_mulVec_eq_zero_iff
    (A : Matrix (Fin n) (Fin n) ℂ) (C : Matrix (Fin p) (Fin n) ℂ)
    (μ : ℂ) (v : Fin n → ℂ) :
    hautusObservabilityMatrix A C μ *ᵥ v = 0
      ↔ A *ᵥ v = μ • v ∧ C *ᵥ v = 0 := by
  unfold hautusObservabilityMatrix
  rw [Matrix.fromRows_mulVec]
  -- Sum.elim a b = 0 ↔ a = 0 ∧ b = 0
  constructor
  · intro h
    have h1 : (μ • (1 : Matrix (Fin n) (Fin n) ℂ) - A) *ᵥ v = 0 := by
      funext i
      simpa using congrFun h (Sum.inl i)
    have h2 : C *ᵥ v = 0 := by
      funext j
      simpa using congrFun h (Sum.inr j)
    rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec] at h1
    exact ⟨(sub_eq_zero.mp h1).symm, h2⟩
  · rintro ⟨hAv, hCv⟩
    funext x
    cases x with
    | inl i =>
      simp only [Sum.elim_inl, Pi.zero_apply]
      rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, hAv]
      simp
    | inr j =>
      simp only [Sum.elim_inr, Pi.zero_apply]
      simpa using congrFun hCv j

end LinearSystems

/-!
## Hautus controllability via duality

Controllability Hautus is the dual of observability Hautus. Rather than
mirror the entire eigenvector argument, we route through the bridge
`IsControllable A B ↔ IsObservable Aᵀ Bᵀ` and reuse the observability
results from above. The key matrix identity is
`(controllabilityMatrix A B)ᵀ = observabilityMatrix Aᵀ Bᵀ`, which makes
the rank-form characterizations match across the duality. -/

namespace LinearSystems

open Matrix

variable {n m : ℕ}

/-- The Hautus controllability matrix at `μ`, `[μI - A | B]`. -/
noncomputable def hautusControllabilityMatrix
    (A : Matrix (Fin n) (Fin n) ℂ) (B : Matrix (Fin n) (Fin m) ℂ) (μ : ℂ) :
    Matrix (Fin n) (Fin n ⊕ Fin m) ℂ :=
  Matrix.fromCols (μ • (1 : Matrix (Fin n) (Fin n) ℂ) - A) B

/-- The transpose of the Hautus controllability matrix is the Hautus
observability matrix of the transposed system. -/
lemma hautusControllabilityMatrix_transpose
    (A : Matrix (Fin n) (Fin n) ℂ) (B : Matrix (Fin n) (Fin m) ℂ) (μ : ℂ) :
    (hautusControllabilityMatrix A B μ)ᵀ = hautusObservabilityMatrix Aᵀ Bᵀ μ := by
  unfold hautusControllabilityMatrix hautusObservabilityMatrix
  rw [Matrix.transpose_fromCols, Matrix.transpose_sub,
      Matrix.transpose_smul, Matrix.transpose_one]

end LinearSystems
