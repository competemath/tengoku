import Tengoku.Nlalib.NLAlib.Probability.Free.WordMatrixVacuum
import Tengoku.Nlalib.NLAlib.Probability.Free.WordPolynomialUltracontractivity
import Tengoku.Seed.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Range

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The genuine closed matrix word algebra

The native operator matrices with entries in the norm-closed left-field
algebra form a closed star subalgebra of the actual amplified C*-algebra.
The vacuum is genuinely tracial only on this subalgebra. The construction
permits restriction to a native closed C*-algebra before trace-power
arguments, without asserting an ambient trace on all Hilbert operators.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Classical ComplexOrder ContinuousFunctionalCalculus

namespace NLAlib

variable {D ι : Type*} [Fintype D] [DecidableEq D]
local notation "W" => WordHilbertSpace ι
local notation "B" => W →L[ℂ] W
local notation "M" => CStarMatrix D D B

/-- The genuine star subalgebra of native matrices over the actual closed
field algebra. Its norm and operations are inherited from the existing
native amplified operator algebra.-/
def wordMatrixFieldAlgebra : StarSubalgebra ℂ M where
  carrier := {T | ∀ i j, T i j ∈ wordFieldAlgebra ι}
  zero_mem' := by intro i j; exact zero_mem _
  one_mem' := by
    intro i j
    by_cases hij : i=j <;> simp only [CStarMatrix.one_apply, hij, ite_true, ite_false]
    · exact one_mem _
    · exact zero_mem _
  add_mem' hS hT := by
    intro i j
    exact add_mem (hS i j) (hT i j)
  mul_mem' hS hT := by
    intro i j
    change (∑ k, _ * _) ∈ wordFieldAlgebra ι
    exact sum_mem fun k _ => mul_mem (hS i k) (hT k j)
  algebraMap_mem' z := by
    intro i j
    by_cases hij : i=j
    · simpa only [CStarMatrix.algebraMap_apply,hij,ite_true] using
        (wordFieldAlgebra ι).algebraMap_mem z
    · simpa only [CStarMatrix.algebraMap_apply,hij,ite_false] using
        (zero_mem (wordFieldAlgebra ι))
  star_mem' hT := by
    intro i j
    exact star_mem (hT j i)

/--
@isnad1 id=iff.0h3v.s16.9afebeb0e6fc from=translated src=- shape=85f40370 vocab=bd7f552e
-/
@[simp]
theorem mem_wordMatrixFieldAlgebra (T : M) :
    T ∈ wordMatrixFieldAlgebra (D := D) (ι := ι) ↔
      ∀ i j, T i j ∈ wordFieldAlgebra ι := Iff.rfl

/-- The native matrix field algebra is actually norm closed, by continuity
of the finitely many native coordinate maps and closedness of the scalar
field algebra.
@isnad1 id=isclosed.0h2v.s15.7ea1e23c3970 from=translated src=- shape=9bb6d0f7 vocab=88c0d00d
-/
theorem isClosed_wordMatrixFieldAlgebra :
    IsClosed (wordMatrixFieldAlgebra (D := D) (ι := ι) : Set M) := by
  have hclosed : IsClosed (wordFieldAlgebra ι : Set B) :=
    StarSubalgebra.isClosed_topologicalClosure _
  change IsClosed {T : M | ∀ i j, T i j ∈ wordFieldAlgebra ι}
  simp only [Set.ofPred_forall]
  apply isClosed_iInter
  intro i
  apply isClosed_iInter
  intro j
  have he : Continuous (fun T : M => T i j) :=
    (continuous_apply j).comp ((continuous_apply i).comp CStarMatrix.ofMatrixL.symm.continuous)
  exact hclosed.preimage he

/-- The actual bounded Wick degree spaces lie in the actual closed field
algebra; no formal-polynomial surrogate is used.
@isnad1 id=le.0h2v.s17.5c7553ec6bec from=translated src=- shape=cc02a6cb vocab=03958641
-/
theorem wordWickDegreeSpan_le_wordFieldAlgebra (k : ℕ) :
    wordWickDegreeSpan (ι := ι) k ≤ (wordFieldAlgebra ι).toSubalgebra.toSubmodule := by
  apply Submodule.span_le.mpr
  rintro T ⟨⟨m,w⟩,rfl⟩
  exact wordWickOperator_mem_wordFieldAlgebra w.toList

/-- Any actual bounded-degree amplified operator belongs to the genuine
closed matrix field algebra.
@isnad1 id=mem.1h4v.s16.10812a9c5c86 from=translated src=- shape=14196ab1 vocab=8db12214
-/
theorem mem_wordMatrixFieldAlgebra_of_entries_degree {T : M} {k : ℕ}
    (hT : ∀ i j, T i j ∈ wordWickDegreeSpan (ι := ι) k) :
    T ∈ wordMatrixFieldAlgebra (D := D) (ι := ι) :=
  fun i j => wordWickDegreeSpan_le_wordFieldAlgebra k (hT i j)

/-- Native continuous functional calculus preserves the actual closed
matrix word algebra. This includes resolvents and positive roots.
@isnad1 id=mem.1h4v.s17.5cd045354edd from=translated src=- shape=6b1363e4 vocab=011d4d9a
-/
theorem cfc_mem_wordMatrixFieldAlgebra (f : ℂ → ℂ) {T : M}
    (hT : T ∈ wordMatrixFieldAlgebra (D := D) (ι := ι)) :
    cfc f T ∈ wordMatrixFieldAlgebra (D := D) (ι := ι) := by
  let : IsClosed (wordMatrixFieldAlgebra (D := D) (ι := ι) : Set M) :=
    isClosed_wordMatrixFieldAlgebra
  exact cfc_mem f hT

end NLAlib

end
