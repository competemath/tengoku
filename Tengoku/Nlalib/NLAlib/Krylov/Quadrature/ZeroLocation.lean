import Tengoku.Nlalib.NLAlib.Krylov.Quadrature.MomentOrthogonality
import Tengoku.Nlalib.NLAlib.Polynomial.OrthogonalPolynomials.SupportGaps

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # Actual Lanczos nodes in support intervals and gaps

The moment-polynomial zero theorems apply to actual Lanczos compressions,
including support termination. Spectral support is finite, so its infimum
and supremum give the sharp support enclosure without ambient inactive nodes.
Source: Gautschi (2004), Theorem 1.19.
-/

noncomputable section

open Polynomial MeasureTheory Set

namespace NLAlib

/-- Nonterminal Gauss nodes lie between the support infimum and supremum
whenever the support is bounded. Source: Gautschi (2004), Theorem 1.19.
atlas: orthogonal-polynomial-zeros (partial)-/
theorem gaussNodes_mem_Ioo_sInf_sSup_support {μ : Measure ℝ} (hμ : HasPolynomialMoments μ)
    {n : ℕ} (hn : (n + 1 : ℕ∞) ≤ μ.support.encard)
    (hlo : BddBelow μ.support) (hhi : BddAbove μ.support) (i : Fin n) :
    gaussNodes μ hμ n i ∈ Ioo (sInf μ.support) (sSup μ.support) := by
  apply gaussNodes_mem_Ioo hμ _ hn
  filter_upwards [μ.support_mem_ae] with x hx
  exact ⟨csInf_le hlo hx, le_csSup hhi hx⟩

/-- A support gap contains at most one canonical Gauss node, with terminal
orders included. Source: Gautschi (2004), Theorem 1.19.
atlas: orthogonal-polynomial-zeros (partial)-/
theorem eq_of_gaussNodes_mem_support_gap {μ : Measure ℝ} (hμ : HasPolynomialMoments μ)
    {n : ℕ} (hn : (n : ℕ∞) ≤ μ.support.encard) {a c : ℝ}
    (hg : Disjoint (Ioo a c) μ.support) {i j : Fin n}
    (hi : gaussNodes μ hμ n i ∈ Ioo a c) (hj : gaussNodes μ hμ n j ∈ Ioo a c) : i = j := by
  apply gaussNodes_injective hμ hn
  apply eq_of_eval_monicOrthogonalPolynomial_eq_zero_of_mem_support_gap_le hμ hn hg hi hj
  · exact (eval_monicOrthogonalPolynomial_eq_zero_iff_exists_gaussNodes hμ hn _).mpr ⟨i, rfl⟩
  · exact (eval_monicOrthogonalPolynomial_eq_zero_iff_exists_gaussNodes hμ hn _).mpr ⟨j, rfl⟩

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {A : Matrix ι ι ℝ} {b : ι → ℝ} {q : ℕ}

namespace LanczosDecomp

end LanczosDecomp

end NLAlib
