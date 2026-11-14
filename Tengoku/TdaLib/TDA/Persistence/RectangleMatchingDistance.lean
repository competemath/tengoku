import Tengoku.TdaLib.TDA.Persistence.RectangleMatchingInterleaving
import Tengoku.TdaLib.TDA.Persistence.CoordinateInterleavingDistance
import Tengoku.Seed.Data.ENNReal.Inv

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Two-sided distance bounds for finite rectangle families

The bottleneck value is the infimum of radii admitting an actual occurrence
matching. Assembling each matching bounds the interleaving distance from above.
The proved matching-existence theorem gives the reverse estimate with factor
`2n−1` in positive dimension. Infima, including unattained and infinite ones,
are compared directly; no optimal matching radius is selected.
-/

set_option autoImplicit false

universe u

namespace TDA.Persistence.RectangleMatching

open RectangleFamily RectangleStabilityGeometry
open scoped TDA.Persistence NNReal ENNReal

variable {k : Type u} [Field k] {n : ℕ}
variable {ι κ : Type}

/-- The extended bottleneck value of finite decorated rectangle occurrences:
the infimum of all finite radii with an actual pair/deletion matching.-/
noncomputable def bottleneckDistance (R : ι → Rectangle n) (S : κ → Rectangle n) : ℝ≥0∞ :=
  ⨅ (ε : ℝ≥0) (M : OccurrenceMatching ι κ PEmpty.{1} PEmpty.{1})
    (_ : IsMatching (k := k) ε R S M), (ε : ℝ≥0∞)

/-- Every actual matching bounds the bottleneck infimum.
@isnad1 id=le.1h8v.s5.098f6f2a189e from=translated src=- shape=5aa03218 vocab=c19ae7b4
-/
theorem bottleneckDistance_le_of_matching {R : ι → Rectangle n} {S : κ → Rectangle n}
    {ε : ℝ≥0} {M : OccurrenceMatching ι κ PEmpty.{1} PEmpty.{1}}
    (hM : IsMatching (k := k) ε R S M) : bottleneckDistance (k := k) R S ≤ ε :=
  iInf_le_of_le ε (iInf_le_of_le M (iInf_le _ hM))

/-- Lower bounds are tested on all actual matching radii, including when
there are no matching witnesses.
@isnad1 id=iff.0h7v.s5.5a3c18c0dee6 from=translated src=- shape=1f7f502c vocab=c19ae7b4
-/
theorem le_bottleneckDistance_iff (R : ι → Rectangle n) (S : κ → Rectangle n) (r : ℝ≥0∞) :
    r ≤ bottleneckDistance (k := k) R S ↔ ∀ ε M, IsMatching (k := k) ε R S M → r ≤ ε := by
  simp only [bottleneckDistance, le_iInf_iff]

/-- Strict approximation above the infimum does not require attainment.
@isnad1 id=iff.0h7v.s6.dc8d5d63f098 from=translated src=- shape=b347b3f7 vocab=4b2edeb6
-/
theorem bottleneckDistance_lt_iff (R : ι → Rectangle n) (S : κ → Rectangle n) (r : ℝ≥0∞) :
    bottleneckDistance (k := k) R S < r ↔
      ∃ (ε : ℝ≥0) (M : OccurrenceMatching ι κ PEmpty.{1} PEmpty.{1}),
        (ε : ℝ≥0∞) < r ∧ IsMatching (k := k) ε R S M := by
  simp only [bottleneckDistance, iInf_lt_iff]
  constructor
  · rintro ⟨ε, M, hM, hε⟩
    exact ⟨ε, M, hε, hM⟩
  · rintro ⟨ε, M, hε, hM⟩
    exact ⟨ε, M, hM, hε⟩

variable [Fintype ι] [Fintype κ]

/-- Exchanging the occurrence families preserves the bottleneck value.
@isnad1 id=eq.0h6v.s5.ae00ed8caeba from=translated src=- shape=2f08fdcb vocab=5a9b5d88
-/
theorem bottleneckDistance_comm (R : ι → Rectangle n) (S : κ → Rectangle n) :
    bottleneckDistance (k := k) R S = bottleneckDistance (k := k) S R := by
  apply le_antisymm
  · exact le_iInf fun ε => le_iInf fun M => le_iInf fun hM =>
      bottleneckDistance_le_of_matching hM.reverse
  · exact le_iInf fun ε => le_iInf fun M => le_iInf fun hM =>
      bottleneckDistance_le_of_matching hM.reverse

/-- Every admissible matching assembles to an interleaving at the same radius;
taking infima gives the lower stability inequality in every coordinate dimension.
@isnad1 id=le.0h6v.s5.249ddc0c14c0 from=translated src=- shape=50f8752c vocab=3a50bb97
-/
theorem interleavingDistance_le_bottleneckDistance
    (R : ι → Rectangle n) (S : κ → Rectangle n) :
    coordinateInterleavingDistance (module (k := k) R) (module S) ≤
      bottleneckDistance (k := k) R S := by
  exact le_iInf fun ε => le_iInf fun M => le_iInf fun hM => hM.interleaving.distance_le

/-- The actual matching-existence theorem bounds the matching infimum by
`(2n−1)` times the interleaving infimum. Finite positive multiplication
commutes with both infima, including empty witness sets.
@isnad1 id=le.1h6v.s6.957d13c69f96 from=translated src=- shape=4d6edb12 vocab=3690778d
-/
theorem bottleneckDistance_le_interleavingDistance (hn : 0 < n)
    (R : ι → Rectangle n) (S : κ → Rectangle n) :
    bottleneckDistance (k := k) R S ≤ ((2 * n - 1 : ℕ) : ℝ≥0∞) *
      coordinateInterleavingDistance (module (k := k) R) (module S) := by
  have hc : (2 * n - 1 : ℕ) ≠ 0 := by omega
  have hc0 : (((2 * n - 1 : ℕ) : ℝ≥0∞)) ≠ 0 := by exact_mod_cast hc
  have hct : (((2 * n - 1 : ℕ) : ℝ≥0∞)) ≠ ⊤ := ENNReal.coe_ne_top
  unfold coordinateInterleavingDistance
  rw [ENNReal.mul_iInf_of_ne hc0 hct]
  apply le_iInf
  intro ε
  rw [ENNReal.mul_iInf_of_ne hc0 hct]
  apply le_iInf
  intro hI
  obtain ⟨M, hM⟩ := exists_matching hn R S ε hI.some
  simpa [stabilityRadius, ENNReal.coe_mul] using bottleneckDistance_le_of_matching hM

/-- The finite bounded decorated-rectangle two-sided distance estimate.
@isnad1 id=and.1h6v.s7.0c3c9196b1e9 from=translated src=- shape=378f5ad2 vocab=3690778d
-/
theorem two_sided_distance_bounds (hn : 0 < n)
    (R : ι → Rectangle n) (S : κ → Rectangle n) :
    coordinateInterleavingDistance (module (k := k) R) (module S) ≤
      bottleneckDistance (k := k) R S ∧
    bottleneckDistance (k := k) R S ≤ ((2 * n - 1 : ℕ) : ℝ≥0∞) *
      coordinateInterleavingDistance (module (k := k) R) (module S) :=
  ⟨interleavingDistance_le_bottleneckDistance R S,
    bottleneckDistance_le_interleavingDistance hn R S⟩

/-- The coefficient is one in dimension one, for the decorated occurrence-family
distance. This statement does not identify the separate endpoint-diagram API.
@isnad1 id=eq.0h5v.s6.2470dce9b1cc from=translated src=- shape=fce8f3d4 vocab=daa6c16d
-/
theorem bottleneckDistance_eq_interleavingDistance_one
    (R : ι → Rectangle 1) (S : κ → Rectangle 1) :
    bottleneckDistance (k := k) R S =
      coordinateInterleavingDistance (module (k := k) R) (module S) := by
  apply le_antisymm
  · simpa using bottleneckDistance_le_interleavingDistance (k := k) (by decide : 0 < 1) R S
  · exact interleavingDistance_le_bottleneckDistance R S

end TDA.Persistence.RectangleMatching
