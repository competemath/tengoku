import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generic.DetectorScaling
import Tengoku.Seed.Tactic.FieldSimp

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# A division-free detector separation circuit

This module clears the denominators in a Laurent family before evaluating the
public detector.  Its criterion is an exact polynomial circuit identity; no
coordinate expansion or formal claim about polynomial degree is used.
-/

namespace AlbertLean.Generic.DetectorSeparation

open DetectorScaling

/-- The second encoder in the Laurent family.-/
def laurentF (F₀ VF : Coord) (t : ℚ) : Coord :=
  F₀ + t⁻¹ • VF

/-- The third encoder in the Laurent family.-/
def laurentK (K₀ U V : Coord) (t : ℚ) : Coord :=
  K₀ + t • U + t⁻¹ • V

/-- The public triple at a Laurent-family parameter.-/
def laurentTriple (E F₀ VF K₀ U V : Coord) (t : ℚ) : WitnessTriple :=
  ⟨E, laurentF F₀ VF t, laurentK K₀ U V t⟩

/-- First denominator-cleared second encoder, equal to `t • F(t)` off zero.-/
def clearedA (F₀ VF : Coord) (t : ℚ) : Coord :=
  t • F₀ + VF

/-- First denominator-cleared third encoder, equal to `t • K(t)` off zero.-/
def clearedB (K₀ U V : Coord) (t : ℚ) : Coord :=
  t • K₀ + t ^ 2 • U + V

/-- Root-swapped denominator-cleared second encoder.-/
def swappedC (F₀ VF : Coord) (m t : ℚ) : Coord :=
  m • F₀ + t • VF

/-- Root-swapped denominator-cleared third encoder.-/
def swappedH (K₀ U V : Coord) (m t : ℚ) : Coord :=
  (m * t) • K₀ + m ^ 2 • U + t ^ 2 • V

/-- The division-free circuit whose nonvanishing detects separation of the
two Laurent-family parameters `t` and `m / t`.-/
def detectorDelta (E F₀ VF K₀ U V : Coord) (m t : ℚ) : ℚ :=
  m ^ 6 * traceCubeDetector ⟨E, clearedA F₀ VF t, clearedB K₀ U V t⟩ -
    t ^ 3 * traceCubeDetector
      ⟨E, swappedC F₀ VF m t, swappedH K₀ U V m t⟩

/-- Clearing the first Laurent denominator in the second encoder.
@isnad1 id=eq.1h3v.s5.68fd9a61ee3c from=translated src=- shape=0cd06752 vocab=37073c64
-/
theorem clearedA_eq_smul_laurentF (F₀ VF : Coord) (t : ℚ)
    (ht : t ≠ 0) :
    clearedA F₀ VF t = t • laurentF F₀ VF t := by
  simp [clearedA, laurentF, smul_add, smul_smul, ht]

/-- Clearing the first Laurent denominator in the third encoder.
@isnad1 id=eq.1h4v.s5.0c263839840c from=translated src=- shape=e021d20d vocab=72de2a61
-/
theorem clearedB_eq_smul_laurentK (K₀ U V : Coord) (t : ℚ)
    (ht : t ≠ 0) :
    clearedB K₀ U V t = t • laurentK K₀ U V t := by
  simp [clearedB, laurentK, smul_add, smul_smul, ht, pow_two]

/-- Clearing the swapped Laurent denominator in the second encoder.
@isnad1 id=eq.2h4v.s5.ae030e634966 from=translated src=- shape=98903b6f vocab=0fd627d5
-/
theorem swappedC_eq_smul_laurentF (F₀ VF : Coord) (m t : ℚ)
    (hm : m ≠ 0) (ht : t ≠ 0) :
    swappedC F₀ VF m t = m • laurentF F₀ VF (m / t) := by
  have hscalar : m * (m / t)⁻¹ = t := by
    field_simp [hm, ht] <;> ring
  simp only [swappedC, laurentF, smul_add, smul_smul]
  rw [hscalar]

/-- Clearing the swapped Laurent denominator in the third encoder.
@isnad1 id=eq.2h5v.s6.158c94f4ee5b from=translated src=- shape=1fc6b11a vocab=2ce10be9
-/
theorem swappedH_eq_smul_laurentK (K₀ U V : Coord) (m t : ℚ)
    (hm : m ≠ 0) (ht : t ≠ 0) :
    swappedH K₀ U V m t =
      (m * t) • laurentK K₀ U V (m / t) := by
  have hU : (m * t) * (m / t) = m ^ 2 := by
    field_simp [hm, ht] <;> ring
  have hV : (m * t) * (m / t)⁻¹ = t ^ 2 := by
    field_simp [hm, ht] <;> ring
  simp only [swappedH, laurentK, smul_add, smul_smul]
  rw [hU, hV]

/-- The first cleared detector is `t^6` times its Laurent value.
@isnad1 id=eq.1h7v.s6.d8573bf07c1d from=translated src=- shape=9b003c64 vocab=ed8ccf33
-/
theorem detector_clearedAB (E F₀ VF K₀ U V : Coord) (t : ℚ)
    (ht : t ≠ 0) :
    traceCubeDetector ⟨E, clearedA F₀ VF t, clearedB K₀ U V t⟩ =
      t ^ 6 * traceCubeDetector (laurentTriple E F₀ VF K₀ U V t) := by
  rw [clearedA_eq_smul_laurentF F₀ VF t ht,
    clearedB_eq_smul_laurentK K₀ U V t ht]
  change traceCubeDetector
      ⟨E, t • laurentF F₀ VF t, t • laurentK K₀ U V t⟩ = _
  rw [traceCubeDetector_scaleFK]
  change (t * t) ^ 3 * traceCubeDetector
      (laurentTriple E F₀ VF K₀ U V t) = _
  ring

/-- The swapped cleared detector is `m^6*t^3` times its Laurent value.
@isnad1 id=eq.2h8v.s6.abfb3711ae9b from=translated src=- shape=af880dae vocab=198f0450
-/
theorem detector_swappedCH (E F₀ VF K₀ U V : Coord) (m t : ℚ)
    (hm : m ≠ 0) (ht : t ≠ 0) :
    traceCubeDetector
        ⟨E, swappedC F₀ VF m t, swappedH K₀ U V m t⟩ =
      m ^ 6 * t ^ 3 *
        traceCubeDetector (laurentTriple E F₀ VF K₀ U V (m / t)) := by
  rw [swappedC_eq_smul_laurentF F₀ VF m t hm ht,
    swappedH_eq_smul_laurentK K₀ U V m t hm ht]
  change traceCubeDetector
      ⟨E, m • laurentF F₀ VF (m / t),
        (m * t) • laurentK K₀ U V (m / t)⟩ = _
  rw [traceCubeDetector_scaleFK]
  change (m * (m * t)) ^ 3 *
      traceCubeDetector (laurentTriple E F₀ VF K₀ U V (m / t)) = _
  ring

/-- Exact denominator clearing for the reconstruction detector difference.
@isnad1 id=eq.2h8v.s7.a2d8b4479384 from=translated src=- shape=ac2e84bc vocab=a918c04b
-/
theorem detectorDelta_eq (E F₀ VF K₀ U V : Coord) (m t : ℚ)
    (hm : m ≠ 0) (ht : t ≠ 0) :
    detectorDelta E F₀ VF K₀ U V m t =
      m ^ 6 * t ^ 6 *
        (traceCubeDetector (laurentTriple E F₀ VF K₀ U V t) -
          traceCubeDetector (laurentTriple E F₀ VF K₀ U V (m / t))) := by
  rw [detectorDelta, detector_clearedAB E F₀ VF K₀ U V t ht,
    detector_swappedCH E F₀ VF K₀ U V m t hm ht]
  ring

/-- Off the Laurent poles, the division-free circuit is nonzero exactly when
the two public detector values are distinct.
@isnad1 id=iff.2h8v.s6.ba1e770b6af9 from=translated src=- shape=c6d102a1 vocab=91ffe238
-/
theorem detectorDelta_ne_zero_iff (E F₀ VF K₀ U V : Coord) (m t : ℚ)
    (hm : m ≠ 0) (ht : t ≠ 0) :
    detectorDelta E F₀ VF K₀ U V m t ≠ 0 ↔
      traceCubeDetector (laurentTriple E F₀ VF K₀ U V t) ≠
        traceCubeDetector (laurentTriple E F₀ VF K₀ U V (m / t)) := by
  have hfactor : m ^ 6 * t ^ 6 ≠ 0 :=
    mul_ne_zero (pow_ne_zero 6 hm) (pow_ne_zero 6 ht)
  constructor
  · intro hDelta heq
    apply hDelta
    rw [detectorDelta_eq E F₀ VF K₀ U V m t hm ht, heq, sub_self,
      mul_zero]
  · intro hdet hDelta
    have hmul :
        m ^ 6 * t ^ 6 *
            (traceCubeDetector (laurentTriple E F₀ VF K₀ U V t) -
              traceCubeDetector
                (laurentTriple E F₀ VF K₀ U V (m / t))) = 0 := by
      rw [← detectorDelta_eq E F₀ VF K₀ U V m t hm ht]
      exact hDelta
    have hdiff :
        traceCubeDetector (laurentTriple E F₀ VF K₀ U V t) -
            traceCubeDetector (laurentTriple E F₀ VF K₀ U V (m / t)) = 0 :=
      (mul_eq_zero.mp hmul).resolve_left hfactor
    exact hdet (sub_eq_zero.mp hdiff)

end AlbertLean.Generic.DetectorSeparation
