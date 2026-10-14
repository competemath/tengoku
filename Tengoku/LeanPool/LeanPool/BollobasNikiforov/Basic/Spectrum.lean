/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
module

public import Tengoku.LeanPool.LeanPool.BollobasNikiforov.Basic.Inner
public import Tengoku

/-!
# Ordered spectrum of a Hermitian matrix

This file records the ordered real spectrum of a Hermitian matrix, matching the
conventions in `docs/sol.tex`. The ordered family is Mathlib's antitone
`eigenvalues₀`, which is the paper's `λ₁ ≥ ⋯ ≥ λₙ` with `λ₁` at index `0`.
`F` is the sum of squares of the two largest positive eigenvalues, with missing
terms replaced by zero.
-/

@[expose] public section

namespace BollobasNikiforov

open Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]
variable {A : Matrix n n ℝ}

/-- The eigenvalues of a Hermitian matrix in nonincreasing order. The value at
`i` is the paper's `λ_{i+1}`. -/
noncomputable def eigs₀ (hA : A.IsHermitian) : Fin (Fintype.card n) → ℝ :=
  hA.eigenvalues₀

/--
@isnad1 id=antitone.1h2v.s6.f97346b48168 from=translated src=- shape=892af1b9 vocab=b5b2ceb5
-/
lemma eigs₀_antitone (hA : A.IsHermitian) : Antitone (eigs₀ hA) :=
  hA.eigenvalues₀_antitone

/-- The largest eigenvalue `λ₁(A)`. -/
noncomputable def lambdaMax (hA : A.IsHermitian) [Nonempty n] : ℝ :=
  eigs₀ hA ⟨0, Fintype.card_pos⟩

/-- The second-largest eigenvalue `λ₂(A)`. -/
noncomputable def lambdaSecond (hA : A.IsHermitian) [Nontrivial n] : ℝ :=
  eigs₀ hA ⟨1, Fintype.one_lt_card⟩

/-- The sum of squares of the two largest positive eigenvalues of a Hermitian
matrix, with missing terms replaced by zero. -/
noncomputable def F (hA : A.IsHermitian) : ℝ :=
  if h0 : 0 < Fintype.card n then
    let t0 := (max (hA.eigenvalues₀ ⟨0, h0⟩) 0) ^ 2
    if h1 : 1 < Fintype.card n then
      t0 + (max (hA.eigenvalues₀ ⟨1, h1⟩) 0) ^ 2
    else t0
  else 0

/--
@isnad1 id=eq.1h2v.s7.e58aadc21dcb from=translated src=- shape=af08d807 vocab=ba7603d0
-/
lemma F_eq (hA : A.IsHermitian) [Nontrivial n] :
    F hA = (max (lambdaMax hA) 0) ^ 2 + (max (lambdaSecond hA) 0) ^ 2 := by
  have h1 : 1 < Fintype.card n := Fintype.one_lt_card
  have h0 : 0 < Fintype.card n := Nat.zero_lt_of_lt h1
  unfold F lambdaMax lambdaSecond eigs₀
  rw [dite_eq_left h0, dite_eq_left h1]

/--
@isnad1 id=le.1h2v.s5.7e6f2655d508 from=translated src=- shape=120c0918 vocab=6343a3b5
-/
lemma F_nonneg (hA : A.IsHermitian) : 0 ≤ F hA := by
  dsimp [F]
  split_ifs <;> positivity

/--
@isnad1 id=eq.0h1v.s5.2f6be774ff1c from=translated src=- shape=dab81812 vocab=918450ab
-/
lemma F_zero : F (A := (0 : Matrix n n ℝ)) isHermitian_zero = 0 := by
  have hz : (isHermitian_zero : (0 : Matrix n n ℝ).IsHermitian).eigenvalues₀ = 0 := by
    have h := (IsHermitian.eigenvalues_eq_zero_iff
        (A := (0 : Matrix n n ℝ)) isHermitian_zero).2 rfl
    funext i
    simpa [IsHermitian.eigenvalues] using
      congr_fun h ((Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card n))) i)
  dsimp [F]
  split_ifs <;> simp [hz]

/-! ### N11 — Adjacency Frobenius mass -/

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

omit [DecidableEq V] in
/-- The adjacency matrix is symmetric, so the Frobenius pairing with itself is
the trace of the square.
@isnad1 id=eq.0h2v.s6.cb65f1e7ccc9 from=translated src=- shape=46b76907 vocab=323e8dd6
-/
lemma inner_adjMatrix_eq_trace_mul :
    inner (G.adjMatrix ℝ) (G.adjMatrix ℝ) =
      (G.adjMatrix ℝ * G.adjMatrix ℝ).trace := by
  rw [inner, G.transpose_adjMatrix]

omit [DecidableEq V] in
/-- The diagonal of `A_G²` records vertex degrees.
@isnad1 id=eq.0h2v.s6.fc5c3b04c2fb from=translated src=- shape=a4a195a2 vocab=e5653704
-/
lemma trace_adjMatrix_mul_self :
    (G.adjMatrix ℝ * G.adjMatrix ℝ).trace = ∑ v, (G.degree v : ℝ) := by
  simp [trace, G.adjMatrix_mul_self_apply_self]

omit [DecidableEq V] in
/-- The Frobenius mass of the adjacency matrix is twice the number of edges.
@isnad1 id=eq.0h2v.s6.22ac8f942e3d from=translated src=- shape=d728cba7 vocab=1aeefd7b
-/
lemma inner_adjMatrix_self :
    inner (G.adjMatrix ℝ) (G.adjMatrix ℝ) = 2 * (G.edgeFinset.card : ℝ) := by
  rw [inner_adjMatrix_eq_trace_mul, trace_adjMatrix_mul_self, ← Nat.cast_sum,
    G.sum_degrees_eq_twice_card_edges]
  exact_mod_cast rfl

end BollobasNikiforov
