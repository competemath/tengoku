import Tengoku.Leanforcontrol.LeanForControl.LinearSystems.Basic
import Tengoku.Leanforcontrol.LeanForControl.LinearSystems.MatrixLemmas
import Tengoku

/-!
# Controllability of a finite-dimensional linear system

For a linear system

  ẋ = A x + B u

with `A : Matrix (Fin n) (Fin n) 𝕜` and `B : Matrix (Fin n) (Fin m) 𝕜`, this
file defines the (finite-horizon) controllability matrix

  𝒞(A, B) = [ B   A·B   A²·B   ⋯   Aⁿ⁻¹·B ] .

We index columns by `Fin n × Fin m` so that `A ^ (k : ℕ)` is available without
casting `k : Fin n` through `Fin.val`.

This file deliberately stays at the *definition + shape lemma* level: the
controllability characterizations (reachable subspace = span of columns,
controllable iff full column rank) are second-milestone work. -/

namespace LinearSystems

open Matrix

variable {𝕜 : Type*} [Semiring 𝕜]
variable {n m : ℕ}

/-- The controllability matrix of `(A, B)`.

The `(k, j)`-th column is the `j`-th column of `Aᵏ · B`, where `k : Fin n`
ranges over `0, 1, …, n-1`. -/
def controllabilityMatrix
    (A : Matrix (Fin n) (Fin n) 𝕜) (B : Matrix (Fin n) (Fin m) 𝕜) :
    Matrix (Fin n) (Fin n × Fin m) 𝕜 :=
  Matrix.of fun i kj => (A ^ (kj.1 : ℕ) * B) i kj.2

/-- The textbook controllability predicate (existential reachability):
every state can be reached from the origin in `n` steps via some sequence
of inputs. Phrased in matrix-power language so the bridge theorem
`isControllable_iff_controllabilityMatrix_rank_eq` has real content. -/
def IsControllable
    (A : Matrix (Fin n) (Fin n) 𝕜) (B : Matrix (Fin n) (Fin m) 𝕜) : Prop :=
  ∀ x : Fin n → 𝕜, ∃ u : Fin n → (Fin m → 𝕜),
    x = ∑ k : Fin n, (A ^ (k : ℕ) * B) *ᵥ u k

end LinearSystems

/-!
## Rank-form characterization

Reopened namespace over `[Field 𝕜]` only, breaking the typeclass diamond
between the outer `[Semiring 𝕜]` and the rank-side `[Field 𝕜]`. -/

namespace LinearSystems

open Matrix

variable {𝕜 : Type*} [Field 𝕜] {n m : ℕ}

end LinearSystems
