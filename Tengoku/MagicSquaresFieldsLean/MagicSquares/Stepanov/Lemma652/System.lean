import Tengoku.MagicSquaresFieldsLean.MagicSquares.Stepanov.Lemma652.Core
import Tengoku.MagicSquaresFieldsLean.MagicSquares.Stepanov.Core.LinearSystem
import Tengoku.Seed.Tactic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace MagicSquares
namespace LN97

open Polynomial

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-!
# LN97 Lemma 6.52: packaging the coefficient constraints

The proof on pp. 306--307 constructs polynomials `s_{t,n}` whose
coefficients are homogeneous linear forms in the unknown coefficients
of the `e_{ij}`.  Once every coefficient of every `s_{t,n}` is set to
zero, all required Hasse derivatives vanish.

This file isolates that finite-dimensional linear system in a structure.
It lets the already-formalized nonvanishing and multiplicity machinery
consume the output of the coefficient-count argument directly.

The next implementation layer will instantiate this structure from the
actual `e_{ij}`, the reductions modulo `B`, and the polynomials `s_{t,n}`.
-/

/-- Abstract data of the homogeneous constraint system constructed on
LN97 pp. 306--307.

`A` is the number of unknown coefficients and `S` the number of
homogeneous equations.-/
structure StepanovConstraintSystem
    (F : Type*) [Field F]
    (m q D M : ℕ) (f g : Polynomial F) where
  A : ℕ
  S : ℕ
  equations : (Fin A → F) →ₗ[F] (Fin S → F)
  decode :
    (Fin A → F) → Fin m → Polynomial (Polynomial F)
  degree_le :
    ∀ v i j, ((decode v i).coeff j).natDegree ≤ D
  decode_ne_zero :
    ∀ {v}, v ≠ 0 → ∃ i, decode v i ≠ 0
  good : F → Prop
  vanish_of_kernel :
    ∀ {v}, equations v = 0 →
      ∀ c, good c →
        ∀ n < M,
          eval c
            ((hasseDeriv n)
              (stepanovAuxiliary q M f g (decode v))) = 0

omit [Fintype F] [DecidableEq F] in
/-- Once the concrete LN97 constraint system has `S < A`, the
homogeneous-system theorem produces a nonzero family `E`; Lemma 6.46
makes the corresponding auxiliary polynomial nonzero, and Lemma 6.51
gives multiplicity at least `M` at every good point.

This is the main assembly theorem for the linear-system half of
Lemma 6.52.-/
theorem stepanovAuxiliary_exists_of_constraintSystem
    {m q D M : ℕ} {f g : Polynomial F}
    (hf : f ≠ 0)
    (hind : QuotientPowerIndependent (F := F) m q D g)
    (sys : StepanovConstraintSystem F m q D M f g)
    (hSA : sys.S < sys.A) :
    ∃ E : Fin m → Polynomial (Polynomial F),
      (∃ i, E i ≠ 0) ∧
      stepanovAuxiliary q M f g E ≠ 0 ∧
      ∀ c, sys.good c →
        M ≤ rootMultiplicity c (stepanovAuxiliary q M f g E) := by
  obtain ⟨v, hvne, hvker⟩ :=
    exists_ne_zero_mem_ker_of_lt
      (F := F) hSA sys.equations
  let E : Fin m → Polynomial (Polynomial F) := sys.decode v
  have hEne : ∃ i, E i ≠ 0 := by
    exact sys.decode_ne_zero hvne
  have hEdeg : ∀ i j, ((E i).coeff j).natDegree ≤ D := by
    intro i j
    exact sys.degree_le v i j
  have haux :
      stepanovAuxiliary q M f g E ≠ 0 :=
    stepanovAuxiliary_ne_zero_of_nontrivial_coefficients
      (F := F) hf hind E hEdeg hEne
  refine ⟨E, hEne, haux, ?_⟩
  intro c hc
  apply stepanovAuxiliary_rootMultiplicity_of_quotientPowerIndependent
    (F := F) hf hind E hEdeg hEne c
  exact sys.vanish_of_kernel hvker c hc

end LN97
end MagicSquares
