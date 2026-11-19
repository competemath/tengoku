import Tengoku.MagicSquaresFieldsLean.MagicSquares.Stepanov.Lemma652.Degree
import Tengoku.MagicSquaresFieldsLean.MagicSquares.Stepanov.Lemma652.System
import Tengoku.Seed.Tactic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace MagicSquares
namespace LN97

open Polynomial

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-!
# Lemma 6.52 assembly with a degree bound

`StepanovLemma652System` already turns `S < A` into a nonzero auxiliary
polynomial with multiplicity at least `M` at every good point.  This file
adds the degree bookkeeping from `StepanovLemma652Degree`.

The result is very close to the abstract conclusion of LN97 Lemma 6.52:
once the concrete `s_{t,n}` system is instantiated, we simultaneously get
nonvanishing, high multiplicity, and an explicit degree bound.
-/

omit [Fintype F] in
/-- Constraint-system assembly, retaining the outer-degree information
needed for the auxiliary-polynomial degree estimate.
@isnad1 id=ex.6h11v.s9.a73d553f38fd from=translated src=- shape=cba8db1b vocab=63b3583b
-/
theorem stepanovAuxiliary_exists_of_constraintSystem_with_degree
    {m q D M u K G : ℕ} {f g : Polynomial F}
    (hf0 : f ≠ 0)
    (hfdeg : f.natDegree ≤ K)
    (hgdeg : g.natDegree ≤ G)
    (hind : QuotientPowerIndependent (F := F) m q D g)
    (sys : StepanovConstraintSystem F m q D M f g)
    (houter : ∀ v i, (sys.decode v i).natDegree ≤ u)
    (hSA : sys.S < sys.A) :
    ∃ E : Fin m → Polynomial (Polynomial F),
      (∃ i, E i ≠ 0) ∧
      stepanovAuxiliary q M f g E ≠ 0 ∧
      (∀ c, sys.good c →
        M ≤ rootMultiplicity c (stepanovAuxiliary q M f g E)) ∧
      (stepanovAuxiliary q M f g E).natDegree
        ≤ M * K + (D + q * u + (m - 1) * G) := by
  obtain ⟨v, hvne, hvker⟩ :=
    exists_ne_zero_mem_ker_of_lt
      (F := F) hSA sys.equations
  let E : Fin m → Polynomial (Polynomial F) := sys.decode v
  have hEne : ∃ i, E i ≠ 0 :=
    sys.decode_ne_zero hvne
  have hEcoeff :
      ∀ i j, ((E i).coeff j).natDegree ≤ D := by
    intro i j
    exact sys.degree_le v i j
  have hEouter :
      ∀ i, (E i).natDegree ≤ u := by
    intro i
    exact houter v i
  have haux :
      stepanovAuxiliary q M f g E ≠ 0 :=
    stepanovAuxiliary_ne_zero_of_nontrivial_coefficients
      (F := F) hf0 hind E hEcoeff hEne
  have hmult :
      ∀ c, sys.good c →
        M ≤ rootMultiplicity c (stepanovAuxiliary q M f g E) := by
    intro c hc
    apply stepanovAuxiliary_rootMultiplicity_of_quotientPowerIndependent
      (F := F) hf0 hind E hEcoeff hEne c
    exact sys.vanish_of_kernel hvker c hc
  have hdegree :
      (stepanovAuxiliary q M f g E).natDegree
        ≤ M * K + (D + q * u + (m - 1) * G) :=
    stepanovAuxiliary_natDegree_le
      (F := F) q M D u K G f g E
      hEouter hEcoeff hfdeg hgdeg
  exact ⟨E, hEne, haux, hmult, hdegree⟩

end LN97
end MagicSquares
