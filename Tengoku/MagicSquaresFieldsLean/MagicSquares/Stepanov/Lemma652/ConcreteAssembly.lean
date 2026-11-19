import Tengoku.MagicSquaresFieldsLean.MagicSquares.Stepanov.Lemma652.ConcreteConstraints
import Tengoku.MagicSquaresFieldsLean.MagicSquares.Stepanov.Lemma652.Degree
import Tengoku.Seed.Tactic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace MagicSquares
namespace LN97

open Polynomial

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-!
# A nearly literal LN97 Lemma 6.52 assembly theorem

At this point the unknowns and the equations are no longer abstract:

* the unknowns are exactly the coefficients of the `e_{ij}`;
* the equations are exactly the coefficients of the `s_{t,n}`;
* `S < A` is the literal inequality

      r M (N+1) < m (u+1) (D+1).

This lower-level theorem takes derivative data and quotient independence
as explicit inputs.  `DerivativeDataConstruct` supplies the former.
`Complete` proves the full book statement directly from absolute
irreducibility, using variable degree bounds for the exact coefficient
count and the completed Lemma 6.46 for nonvanishing.

Version 2 specifies the otherwise non-inferable parameter `r` in the
concrete coefficient-constraint map.
-/

/-- Concrete Stepanov auxiliary-polynomial existence theorem with the
literal coefficient count.-/
theorem ln97_6_52_of_derivativeData_and_quotientIndependence
    {m r u D M Emax N K G : ℕ}
    {f g B : Polynomial F}
    (hf : f ≠ 0)
    (hfdeg : f.natDegree ≤ K)
    (hgdeg : g.natDegree ≤ G)
    (hB : B.Monic)
    (hr : 0 < r)
    (hBdeg : B.natDegree = r)
    (data : StepanovDerivativeData F m u D M Emax f g)
    (hNu : Emax + u ≤ N)
    (hind :
      QuotientPowerIndependent
        (F := F) m (Fintype.card F) D g)
    (hcount :
      r * M * (N + 1) < m * (u + 1) * (D + 1)) :
    ∃ E : Fin m → Polynomial (Polynomial F),
      (∃ i, E i ≠ 0) ∧
      stepanovAuxiliary (Fintype.card F) M f g E ≠ 0 ∧
      (∀ c, B.IsRoot (eval c g) →
        M ≤ rootMultiplicity c
          (stepanovAuxiliary (Fintype.card F) M f g E)) ∧
      (stepanovAuxiliary (Fintype.card F) M f g E).natDegree
        ≤ M * K +
          (D + Fintype.card F * u + (m - 1) * G) := by
  let T :
      StepanovUnknowns F m u D →ₗ[F]
        StepanovConstraintSpace F r M N :=
    stepanovCoefficientConstraints (r := r) N B data
  obtain ⟨v, hvne, hvker⟩ :=
    exists_nonzero_stepanovUnknown_in_kernel
      (F := F) T hcount
  let E : Fin m → Polynomial (Polynomial F) :=
    stepanovDecode v
  have hEne : ∃ i, E i ≠ 0 := by
    exact exists_stepanovDecode_ne_zero_of_ne_zero v hvne
  have hEcoeff :
      ∀ i j, ((E i).coeff j).natDegree ≤ D := by
    intro i j
    exact stepanovDecode_coeff_natDegree_le v i j
  have hEouter : ∀ i, (E i).natDegree ≤ u := by
    intro i
    exact stepanovDecode_natDegree_le v i
  have haux :
      stepanovAuxiliary (Fintype.card F) M f g E ≠ 0 :=
    stepanovAuxiliary_ne_zero_of_nontrivial_coefficients
      (F := F) hf hind E hEcoeff hEne
  have hmult :
      ∀ c, B.IsRoot (eval c g) →
        M ≤ rootMultiplicity c
          (stepanovAuxiliary (Fintype.card F) M f g E) := by
    intro c hc
    apply stepanovAuxiliary_rootMultiplicity_of_quotientPowerIndependent
      (F := F) hf hind E hEcoeff hEne c
    exact hasse_vanish_of_coefficientConstraints_eq_zero
      (F := F) (r := r) B hB hr hBdeg data hNu v hvker c hc
  have hdegree :
      (stepanovAuxiliary (Fintype.card F) M f g E).natDegree
        ≤ M * K +
          (D + Fintype.card F * u + (m - 1) * G) :=
    stepanovAuxiliary_natDegree_le
      (F := F)
      (Fintype.card F) M D u K G f g E
      hEouter hEcoeff hfdeg hgdeg
  exact ⟨E, hEne, haux, hmult, hdegree⟩

end LN97
end MagicSquares
