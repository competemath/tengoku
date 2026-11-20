import Tengoku.Jsp940Erdos1133Formalization.Erdos1133.FiniteTrigCore
import Tengoku.Jsp940Erdos1133Formalization.Erdos1133.ObstructionAssembly
import Tengoku.Jsp940Erdos1133Formalization.Erdos1133.Reduction

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

noncomputable section
open Filter Set

namespace Erdos1133

/-- The finite analytic input is proved, with no unresolved interpolation or
sampling assumptions. Indexed nodes may coincide.-/
theorem finite_bernstein_obstruction :
    ∀ H > (0 : ℝ), ∃ k : ℕ, 2 ≤ k ∧ FiniteBernsteinObstruction H k :=
  finiteBernsteinObstructions_of_finiteTrig finite_trig_obstruction

/-- An explicit threshold in terms of the finite obstruction size, together
with the nontrivial range `0 < ε < 1`.-/
theorem erdos_1133_with_threshold (C : ℝ) (hC : 0 < C) :
    ∃ k : ℕ, 2 ≤ k ∧ 0 < obstructionEpsilon k ∧ obstructionEpsilon k < 1 ∧
      ∀ n : ℕ, 4*k^2 ≤ n →
        ∀ x : Fin n → Icc (-1 : ℝ) 1,
          ∃ y : Fin n → Icc (-1 : ℝ) 1,
            ∀ P : Polynomial ℝ,
              (P.natDegree : ℝ) < (1+obstructionEpsilon k)*(n : ℝ) →
              ((Finset.univ.filter (fun i => P.eval (x i : ℝ)=(y i : ℝ))).card : ℝ) ≥
                (1-obstructionEpsilon k)*(n : ℝ) →
              ∃ z ∈ Icc (-1 : ℝ) 1, |P.eval z| > C := by
  obtain ⟨k,hk,hcore⟩ := finite_bernstein_obstruction C hC
  refine ⟨k,hk,obstructionEpsilon_pos hk,obstructionEpsilon_lt_one hk,?_⟩
  intro n hn x
  exact robust_labels_of_finite_obstruction hk hn hcore x

end Erdos1133
