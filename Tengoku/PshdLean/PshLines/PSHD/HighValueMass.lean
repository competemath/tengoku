import Tengoku.PshdLean.PshLines.Plurisubharmonic
import Tengoku.Seed.MeasureTheory.Integral.Lebesgue.Markov

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # Positive angular mass of high values

A strengthening of the nonemptiness step in `pshd-vibe`, Lemma 1.3,
using the project's nonnegative deficit normalization directly.
-/

open Set MeasureTheory
open scoped ENNReal

namespace PshLines.PSHD

/-- The high-value angles on every admissible affine circle have positive
Lebesgue measure. No ambient measurability assumption is needed.
@isnad1 id=lt.3h6v.s7.216433eed57b from=translated src=- shape=6ab3fdab vocab=aecb630a
-/
theorem volume_highValue_angles_pos
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {u : E → ℝ} {U : Set E}
    (hu : DiscPshOn (fun y => (u y : EReal)) U)
    (x v : E) {r : ℝ} (hr : 0 < r)
    (hD : affineClosedDisc x v r ⊆ U) :
    0 < volume {t ∈ Ioc 0 (2 * Real.pi) | u x ≤ u (x + circleMap 0 r t • v)} := by
  obtain ⟨C, hC⟩ := hu.exists_disc_upper_bound x v hr.le hD
  have hCx : u x ≤ C := EReal.coe_le_coe_iff.mp
    (hC x (center_mem_affineClosedDisc x v hr.le))
  have hp : 0 < 2 * Real.pi := by positivity
  have hm : volume (Ioc 0 (2 * Real.pi)) = ENNReal.ofReal (2 * Real.pi) := by
    simp
  by_contra hpos
  have hzero : volume {t ∈ Ioc 0 (2 * Real.pi) |
      u x ≤ u (x + circleMap 0 r t • v)} = 0 := by simpa using hpos
  have hlt : ∀ᵐ t ∂volume, t ∈ Ioc 0 (2 * Real.pi) →
      u (x + circleMap 0 r t • v) < u x := by
    simpa only [ae_iff, not_forall, not_lt, exists_prop] using hzero
  have hconst : (∫⁻ _t in Ioc 0 (2 * Real.pi), ENNReal.ofReal (C - u x)) =
      ENNReal.ofReal (2 * Real.pi) * ENNReal.ofReal (C - u x) := by
    simp [mul_comm]
  have hstrict := setLIntegral_strict_mono measurableSet_Ioc
    (by rw [hm]; exact (ENNReal.ofReal_pos.mpr hp).ne')
    (hu.measurable_circle_deficit x v hr.le hD C)
    (f := fun _t : ℝ => ENNReal.ofReal (C - u x))
    (by rw [hconst]; exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)
    (hlt.mono fun t ht hmem => by
      simp only [← EReal.coe_sub, EReal.real_coe_toENNReal]
      exact (ENNReal.ofReal_lt_ofReal_iff
        (sub_pos.mpr ((ht hmem).trans_le hCx))).mpr
        (sub_lt_sub_left (ht hmem) C))
  have hmean := hu.submean x v r hr hD C hC
  simp only [← EReal.coe_sub, EReal.real_coe_toENNReal] at hmean
  rw [hconst] at hstrict
  exact (not_lt_of_ge hmean) hstrict

end PshLines.PSHD
