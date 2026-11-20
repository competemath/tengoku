/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import Tengoku.Srg266NonexistenceLean.SRG266.Completion.MarkedDiscriminant
import Tengoku.Srg266NonexistenceLean.SRG266.Lattice.PrimaryNormalForms

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace SRG266

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem exists_lorentzMarked_normal_forms_from_graph (hG : IsHypothetical G) (x : V) :
    ∃ (c : IntegralGramLattice G x) (P : Submodule ℤ (ratGramSpace G x)),
      (11 : ℤ) • c = integralGramGeneratorSum G x ∧
      lorentzMarkedLattice G x c ≤ P ∧ Lattice.IsLattice ℚ P ∧
      Lattice.IsMaximalIntegral (lorentzGramForm G x c) P ∧
      Lattice.IsEven (lorentzGramForm G x c) P ∧
      (lorentzGramForm G x c).dualSubmodule P =
        Lattice.torsionPart (lorentzGramForm G x c) P 3 ⊔
          Lattice.torsionPart (lorentzGramForm G x c) P 5 ∧
      Lattice.HasPrimaryNormalForm (lorentzGramForm G x c) P 3 2 ∧
      Lattice.HasPrimaryNormalForm (lorentzGramForm G x c) P 5 4 := by
  obtain ⟨c, hc⟩ := exists_integral_centroid G hG x
  obtain ⟨P, hle, hlat, hmax, heven, S, T, hdual⟩ :=
    exists_lorentzMarked_orthogonal_glue G hG x c hc
  refine ⟨c, P, hc, hle, hlat, hmax, heven, ?_,
    S.normalForm_three (lorentzGramForm_isSymm G x c) hmax heven,
    T.normalForm_five (lorentzGramForm_isSymm G x c) hmax heven⟩
  rw [S.spans, T.spans, hdual, Submodule.span_union]
  exact sup_sup_distrib_left _ _ _

end SRG266
