import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generic.QuaternionActualWeightedPairData
import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generic.QuaternionActualWeightedPivotEquation
import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generic.QuaternionNonscalarBlockNormalizer

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms exists_pair_conjugator_of_actual_weighted_data` (it only prints; the queue checks the axioms of every declaration). -/

noncomputable section
namespace AlbertLean.Generic.QuaternionRow.WeightedProjectorGauge
open AlbertLean.Generic.QuaternionRow.BlockEigenbasis
open AlbertLean.Generic.QuaternionRow.WeightedBlockEquations
open AlbertLean.Generic.QuaternionRow.NonscalarBlockNormalizer
variable {K : Type*} [Field K] [CharZero K]

private theorem adj2_eq_adj (X : Mat2 K) : adj2 X = adj X := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [adj2, adj, matrix]

/-- Cancellation consumer for the data extracted from two actual projector
pairs.  In the intended call all displayed block identities and the two pivot
identities are supplied by `actual_same_ledger_weighted_pair_data` and
`actual_weighted_pivot_idempotent`; only the two stated nonvanishing conditions
are additional open conditions.-/
theorem exists_pair_conjugator_of_actual_weighted_data
    (B C : Fin 3 → Fin 3 → Mat2 K) (p q : Fin 3 → K)
    (hp : ∀ i, p i ≠ 0) (hp12 : p 1 + p 2 ≠ 0)
    (hdB : ∀ i, B i i = scalar2 (q i))
    (hdC : ∀ i, C i i = scalar2 (q i))
    (hrB : ∀ i, B i 0 + B i 1 + B i 2 = 0)
    (hcB : ∀ j, p 0 • B 0 j + p 1 • B 1 j + p 2 • B 2 j = 0)
    (hrC : ∀ i, C i 0 + C i 1 + C i 2 = 0)
    (hcC : ∀ j, p 0 • C 0 j + p 1 • C 1 j + p 2 • C 2 j = 0)
    (hsB : ∀ i j, p i • B i j = p j • adj2 (B j i))
    (hsC : ∀ i j, p i • C i j = p j • adj2 (C j i))
    (hiB : B 0 0 * B 0 0 + B 0 1 * B 1 0 + B 0 2 * B 2 0 = B 0 0)
    (hiC : C 0 0 * C 0 0 + C 0 1 * C 1 0 + C 0 2 * C 2 0 = C 0 0)
    (hdisc : trace2 (B 0 1) ^ 2 - 4 * determinant (B 0 1) ≠ 0) :
    ∃ T S : Mat2 K, T * S = 1 ∧ S * T = 1 ∧
      ∀ i j, B i j = T * C i j * S := by
  have hdB' : ∀ i, B i i = q i • (1 : Mat2 K) := by
    intro i; simpa [scalar2] using hdB i
  have hdC' : ∀ i, C i i = q i • (1 : Mat2 K) := by
    intro i; simpa [scalar2] using hdC i
  have hsB1 : p 1 • B 1 0 = p 0 • adj (B 0 1) := by
    simpa [adj2_eq_adj] using hsB 1 0
  have hsC1 : p 1 • C 1 0 = p 0 • adj (C 0 1) := by
    simpa [adj2_eq_adj] using hsC 1 0
  have hsB2 : p 2 • B 2 0 = p 0 • adj (B 0 2) := by
    simpa [adj2_eq_adj] using hsB 2 0
  have hsC2 : p 2 • C 2 0 = p 0 • adj (C 0 2) := by
    simpa [adj2_eq_adj] using hsC 2 0
  have htB := pivot_trace_relation B p q hdB' hrB hcB hsB1
  have htC := pivot_trace_relation C p q hdC' hrC hcC hsC1
  have ht : trace2 (B 0 1) = trace2 (C 0 1) := by
    apply (mul_left_cancel₀ (hp 0))
    linear_combination htB - htC
  have hdBrel := pivot_determinant_relation B p q hdB' hrB hcB hsB1 hsB2 hiB
  have hdCrel := pivot_determinant_relation C p q hdC' hrC hcC hsC1 hsC2 hiC
  have hd : determinant (B 0 1) = determinant (C 0 1) := by
    apply (mul_left_cancel₀ (mul_ne_zero (hp 0) hp12))
    rw [ht] at hdBrel
    linear_combination hdBrel - hdCrel
  have hBn := nonscalar_of_discriminant_ne_zero (B 0 1) hdisc
  have hCn : ¬ ∃ a : K, C 0 1 = a • (1 : Mat2 K) := by
    apply nonscalar_of_discriminant_ne_zero
    rw [← ht, ← hd]
    exact hdisc
  exact exists_all_blocks_conjugate B C p q (hp 1) (hp 2)
    hdB' hrB hcB hdC' hrC hcC hBn hCn ht hd

end AlbertLean.Generic.QuaternionRow.WeightedProjectorGauge
