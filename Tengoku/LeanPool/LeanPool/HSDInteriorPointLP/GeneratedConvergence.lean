/-
Copyright (c) 2026 Makoto Yamashita. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Makoto Yamashita
-/
module

public import Tengoku.LeanPool.LeanPool.HSDInteriorPointLP.FixedYTMTheory

/-!
# Generated predictor-corrector algorithm and final convergence theorem

This is the main file to edit when the algorithmic proof changes.  The iterate
sequence is generated recursively from the initial point, so the dependency on the
fixed YTM theory is explicit and there is no hidden import of an old numbered file.

Lean-reading hints for beginners:
* `induction k with | zero => ... | succ k ih => ...` proves a statement for all
  natural numbers by proving the base case and the successor case.
* `calc ...` is a readable chain of equalities/inequalities.
* `omega` solves arithmetic goals over natural numbers and integers.
-/

@[expose] public section
noncomputable section

open scoped BigOperators

namespace HSDInteriorPointLP

/-!
## Lean comments for readers who know interior-point methods

This file is the final iteration-count layer.  The mathematical objects are the
predictor point, the corrector point, and the contraction estimate for the
homogenized gap.  A few Lean proof commands occur repeatedly.

* `intro k` introduces the iteration index in a theorem whose conclusion starts
  with `∀ k, ...`.
* `induction k with ...` proves a statement for all natural numbers by showing
  the base case `0` and then the step from `k` to `k+1`.
* `have h := ...` records an intermediate estimate, such as one-step contraction.
* `rw [lemma]` rewrites the current goal using an equality.
* `simpa [name₁, name₂] using h` unfolds the listed definitions, simplifies both
  sides, and then applies the already-proved fact `h`.
* `simp` is used only in very small base cases, such as `c^0 = 1`.
* `ring` closes purely algebraic real-number identities.
* `linarith` and `nlinarith` are used in imported files for linear and nonlinear
  real inequalities; here most inequalities are chained explicitly with `calc`.
-/

/-- A generated predictor-corrector algorithm: the iterate sequence is no longer a
field.  It is obtained recursively from the initial point by applying the canonical
Newton predictor step and the canonical Newton corrector step. -/
structure HSDGeneratedAlgorithm (n : Nat) where
  /-- Number of equality constraints in the LP data. -/
  m : Nat
  /-- Linear-programming data. -/
  P : LPData m n
  /-- Standard assumptions on the LP data. -/
  std : LPStandardAssumptions P
  /-- Initial HSD state. -/
  w0 : HSState n
  /-- Initial tight-neighborhood certificate. -/
  initial_neigh : HSDNeighborhood ytmBetaTight w0

namespace HSDGeneratedAlgorithm

/-- Canonical fixed predictor step from a tight-neighborhood point. -/
noncomputable def predictorStep {n : Nat} (alg : HSDGeneratedAlgorithm n)
    (w : HSState n) (h : HSDNeighborhood ytmBetaTight w) : HSState n :=
  addStep w (HSDNewtonDirection alg.P alg.std w h.1 0) (ytmPredictorAlpha n)

/-- Canonical full corrector step from a wide-neighborhood point. -/
noncomputable def correctorStep {n : Nat} (alg : HSDGeneratedAlgorithm n)
    (w : HSState n) (h : HSDNeighborhood ytmBetaWide w) : HSState n :=
  addStep w (HSDNewtonDirection alg.P alg.std w h.1 1) 1

/-- The generated corrector step returns to the tight neighborhood. -/
theorem correctorStep_tight {n : Nat} (alg : HSDGeneratedAlgorithm n)
    (w : HSState n) (h : HSDNeighborhood ytmBetaWide w) :
    HSDNeighborhood ytmBetaTight (alg.correctorStep w h) := by
  have hdir : HSDStepDirection w (HSDNewtonDirection alg.P alg.std w h.1 1) 1 :=
    HSDNewtonDirection_step alg.P alg.std w h.1 1
  have hg := corrector_step_guarantee_of_wide
    (w := w) (d := HSDNewtonDirection alg.P alg.std w h.1 1) h hdir
  simpa [correctorStep] using hg.neighborhood_next

/-- Even iterates, carrying the proof that they are in the tight neighborhood. -/
noncomputable def evenState {n : Nat} (alg : HSDGeneratedAlgorithm n) :
    Nat → {w : HSState n // HSDNeighborhood ytmBetaTight w}
  | 0 => ⟨alg.w0, alg.initial_neigh⟩
  | k + 1 =>
      let e := evenState alg k
      let o := alg.predictorStep e.1 e.2
      let ho := alg.predictorStep_wide e.1 e.2
      ⟨alg.correctorStep o ho, alg.correctorStep_tight o ho⟩

/-- Abstract paper-style stopping condition: the residual predicates are parameters,
because the current HLP skeleton has not yet introduced concrete primal and dual
residual maps. -/
structure PaperStyleStop {n : Nat}
    (PrimalResidualStop DualResidualStop : HSState n → Prop)
    (ε : ℝ) (w : HSState n) : Prop where
  mu_stop : YTMMuStop ε w
  primal_stop : PrimalResidualStop w
  dual_stop : DualResidualStop w

/-- Once residual estimates are available, this packages them with `μ ≤ ε`. -/
theorem PaperStyleStop.of_mu_and_residuals {n : Nat}
    {PrimalResidualStop DualResidualStop : HSState n → Prop}
    {ε : ℝ} {w : HSState n}
    (hmu : YTMMuStop ε w)
    (hp : PrimalResidualStop w) (hd : DualResidualStop w) :
    PaperStyleStop PrimalResidualStop DualResidualStop ε w :=
  ⟨hmu, hp, hd⟩

end HSDGeneratedAlgorithm

end HSDInteriorPointLP
