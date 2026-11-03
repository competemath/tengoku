import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Residual.SectionFibre

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Recovering a nonzero scalar from its symmetric reciprocal sum

The equation `t + m/t = u + m/u` has the two explicit solutions `u = t`
and `u = m/t`. This scalar lemma will be applied only after a public ledger
entry has been proved to recover that sum.
-/

namespace AlbertLean.Generic.ParameterRootArithmetic

variable {K : Type*} [Field K]

theorem reciprocal_sum_eq_iff (m t u : K) (ht : t ≠ 0) (hu : u ≠ 0) :
    t + m / t = u + m / u ↔ u = t ∨ u = m / t := by
  have hfactor : (u - t) * (u - m / t) =
      u * (u + m / u - (t + m / t)) := by
    field_simp [ht, hu] <;> ring
  constructor
  · intro h
    have hz : u + m / u - (t + m / t) = 0 := sub_eq_zero.mpr h.symm
    have hp : (u - t) * (u - m / t) = 0 := by
      rw [hfactor, hz, mul_zero]
    simpa only [mul_eq_zero, sub_eq_zero] using hp
  · intro h
    have hp : (u - t) * (u - m / t) = 0 := by
      rcases h with h | h <;> simp [h]
    have hz := (mul_eq_zero.mp (hfactor.symm.trans hp)).resolve_left hu
    exact (sub_eq_zero.mp hz).symm

theorem reciprocal_involutive (m t : K) (hm : m ≠ 0) (ht : t ≠ 0) :
    m / (m / t) = t := by
  field_simp [hm, ht]

theorem reciprocal_sum_swap (m t : K) (hm : m ≠ 0) (ht : t ≠ 0) :
    m / t + m / (m / t) = t + m / t := by
  rw [reciprocal_involutive m t hm ht, add_comm]

end AlbertLean.Generic.ParameterRootArithmetic
