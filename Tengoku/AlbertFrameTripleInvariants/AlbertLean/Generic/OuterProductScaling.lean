import Tengoku.Seed.Tactic.FieldSimp
import Tengoku.Seed.Tactic.FinCases
import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generic.QuaternionHatAdjugate

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms outer_eq_scaling_at_pivot` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms outer_eq_scaling` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms same_a_scalar_fibre` (it only prints; the queue checks the axioms of every declaration). -/

noncomputable section
namespace AlbertLean.Generic.QuaternionRow.ScalarFibre

universe u
variable {K : Type u} [Field K] [CharZero K]

/-- Equality of two nonzero outer products gives the unique reciprocal
rescaling, using a displayed nonzero entry rather than any rank theorem.
@isnad1 id=ex.2h7v.s7.106d4ca9db54 from=translated src=- shape=fb34f812 vocab=4c2489d2
-/
theorem outer_eq_scaling_at_pivot
    (u v u' v' : Vec3 K) (i j : Fin 3)
    (houter : outer v u = outer v' u')
    (hpivot : v i * u j ≠ 0) :
    ∃ t : K, t ≠ 0 ∧ u' = t • u ∧ v' = t⁻¹ • v := by
  have hvi : v i ≠ 0 := fun h => hpivot (by simp [h])
  have huj : u j ≠ 0 := fun h => hpivot (by simp [h])
  have hp := congrFun (congrFun houter i) j
  simp only [outer] at hp
  have hv'i : v' i ≠ 0 := by
    intro h
    apply hpivot
    rw [hp, h, zero_mul]
  have hu'j : u' j ≠ 0 := by
    intro h
    apply hpivot
    rw [hp, h, mul_zero]
  let t : K := u' j / u j
  have ht : t ≠ 0 := div_ne_zero hu'j huj
  refine ⟨t, ht, ?_, ?_⟩
  · funext k
    have hik := congrFun (congrFun houter i) k
    simp only [outer] at hik
    have hcross : u' k * u j = u' j * u k := by
      apply mul_left_cancel₀ hv'i
      calc
        v' i * (u' k * u j) = (v' i * u' k) * u j := by ring
        _ = (v i * u k) * u j := by rw [← hik]
        _ = (v i * u j) * u k := by ring
        _ = (v' i * u' j) * u k := by rw [hp]
        _ = v' i * (u' j * u k) := by ring
    change u' k = t * u k
    dsimp [t]
    rw [div_mul_eq_mul_div]
    exact (eq_div_iff huj).2 hcross
  · funext k
    have hkj := congrFun (congrFun houter k) j
    simp only [outer] at hkj
    change v' k = t⁻¹ * v k
    rw [inv_div]
    rw [div_mul_eq_mul_div]
    apply (eq_div_iff hu'j).2
    calc
      v' k * u' j = v k * u j := hkj.symm
      _ = u j * v k := by ring

/-- Matrix nonzeroness supplies the displayed pivot required above.
@isnad1 id=ex.2h5v.s7.cdda4a815c83 from=translated src=- shape=fb34755c vocab=5ca19aeb
-/
theorem outer_eq_scaling
    (u v u' v' : Vec3 K)
    (houter : outer v u = outer v' u')
    (hne : outer v u ≠ 0) :
    ∃ t : K, t ≠ 0 ∧ u' = t • u ∧ v' = t⁻¹ • v := by
  classical
  have hpivot : ∃ i j, v i * u j ≠ 0 := by
    by_contra h
    push_neg at h
    apply hne
    ext i j
    simpa [outer] using h i j
  obtain ⟨i, j, hij⟩ := hpivot
  exact outer_eq_scaling_at_pivot u v u' v' i j houter hij

/-- Same `a`, actual projector block equations, and nonzero adjugate force the
entire skew-block fibre to be one reciprocal scalar orbit.
@isnad1 id=ex.4h6v.s9.3e7b87da358b from=translated src=- shape=e24e97e7 vocab=dab22ca0
-/
theorem same_a_scalar_fibre
    (a : Mat3 K) (u v u' v' : Vec3 K)
    (hblock : a * a - a = -(hat u * hat v))
    (hblock' : a * a - a = -(hat u' * hat v'))
    (htrace : Matrix.trace a = 1)
    (hnonzero : Matrix.adjugate a ≠ 0) :
    ∃ t : K, t ≠ 0 ∧ u' = t • u ∧ v' = t⁻¹ • v := by
  have hadj := adjugate_of_projector_trace_one a u v hblock htrace
  have hadj' := adjugate_of_projector_trace_one a u' v' hblock' htrace
  apply outer_eq_scaling u v u' v'
  · simpa only [neg_inj] using hadj.symm.trans hadj'
  · intro hout
    apply hnonzero
    rw [hadj, hout, neg_zero]

end AlbertLean.Generic.QuaternionRow.ScalarFibre
