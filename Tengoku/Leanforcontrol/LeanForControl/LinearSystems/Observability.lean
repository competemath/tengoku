import Tengoku.Leanforcontrol.LeanForControl.LinearSystems.Basic
import Tengoku.Leanforcontrol.LeanForControl.LinearSystems.MatrixLemmas
import Tengoku

/-!
# Observability of a finite-dimensional linear system

For a discrete- or continuous-time linear system

  ẋ = A x ,  y = C x

with `A : Matrix (Fin n) (Fin n) 𝕜` and `C : Matrix (Fin p) (Fin n) 𝕜`,
this file defines:

* `LinearSystems.observabilityMatrix A C`, the stacked block-row matrix
      [ C ; C·A ; C·A² ; ⋯ ; C·Aⁿ⁻¹ ]
  with row index `Fin n × Fin p` and column index `Fin n`;
* `LinearSystems.IsObservable A C`, the textbook condition that the only state
  annihilating `C·Aᵏ` for every `k = 0, …, n-1` is the zero state.

The milestone theorem is
`LinearSystems.isObservable_iff_observabilityMatrix_ker_trivial`, the bridge
between the two formulations: observability is exactly the triviality of the
kernel of the observability matrix acting by `*ᵥ`.
-/

namespace LinearSystems

open Matrix

variable {𝕜 : Type*} [Semiring 𝕜]
variable {n p : ℕ}

/-- The observability matrix of `(A, C)`.

The `(k, i)`-th row is the `i`-th row of `C · Aᵏ`, where `k : Fin n`
ranges over `0, 1, …, n-1`. We index rows by `Fin n × Fin p` so that
`A ^ (k : ℕ)` is available without first casting `k` through `Fin.val`. -/
def observabilityMatrix
    (A : Matrix (Fin n) (Fin n) 𝕜) (C : Matrix (Fin p) (Fin n) 𝕜) :
    Matrix (Fin n × Fin p) (Fin n) 𝕜 :=
  Matrix.of fun ki j => (C * A ^ (ki.1 : ℕ)) ki.2 j

/-- The textbook observability predicate: the only state for which
`C · Aᵏ` annihilates the state for every power `k = 0, …, n-1` is the zero
state. This phrasing does not mention `observabilityMatrix`, so the milestone
theorem `isObservable_iff_observabilityMatrix_ker_trivial` has real content. -/
def IsObservable
    (A : Matrix (Fin n) (Fin n) 𝕜) (C : Matrix (Fin p) (Fin n) 𝕜) : Prop :=
  ∀ x : Fin n → 𝕜, (∀ k : Fin n, (C * A ^ (k : ℕ)) *ᵥ x = 0) → x = 0

/-!
## Follow-ups for the Hautus track

The following helpers were not needed to prove
`isObservable_iff_observabilityMatrix_ker_trivial`, but will be needed before
attacking either Hautus or the rank-based reformulations:

* a rank-vs-trivial-kernel bridge for matrices of shape `Matrix (m × p) n 𝕜`,
  most naturally phrased through `Matrix.toLin'` and `LinearMap.ker`;
* block-matrix rank lemmas for stacked rows
  `[A₁ ; A₂ ; … ; Aₖ]`, lifting per-block kernels to the stack and back;
* a transition from `(C · Aᵏ) *ᵥ x = 0 ∀ k < n` to invariance of the
  unobservable subspace under `A` (Cayley–Hamilton style argument), needed
  to extract eigenvectors for the Hautus direction;
* coercion lemmas between `(C * A^k) *ᵥ x` and `C *ᵥ (A^k *ᵥ x)`, which
  are useful when restating observability in terms of trajectories rather
  than matrix powers.

These belong in `LinearSystems.MatrixLemmas` (matrix-level facts) and a future
`LinearSystems.Hautus` (control-level facts) once needed.
-/

end LinearSystems

/-!
## Rank-form characterization

We reopen `namespace LinearSystems` in a fresh section over `[Field 𝕜]` so
the typeclass diamond between the outer `[Semiring 𝕜]` (used for the
existing definitions and the kernel-form milestone) and the rank-side
`[Field 𝕜]` is broken: in the section below, the only scalar-typeclass on
`𝕜` is `Field`, and the `Semiring` derived from it is the canonical one,
matching the instance picked by `MatrixLemmas`.
-/

namespace LinearSystems

open Matrix

variable {𝕜 : Type*} [Field 𝕜] {n p : ℕ}

end LinearSystems
