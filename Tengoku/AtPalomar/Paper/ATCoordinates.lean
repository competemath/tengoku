module

public import Tengoku.AtPalomar.Paper.Gaussian
public import Tengoku.AtPalomar.Paper.ATAlgebra
public import Tengoku.AtPalomar.Paper.Targets
public import Tengoku.Seed.MeasureTheory.Measure.OpenPos

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

@[expose] public section

/-!
# Actual Gaussian zero-set coordinates for the AT boundary

This module proves both directions of the appendix's change of coordinates
using the concrete Gaussian integrals, including the strict fixed-point
bounds. It does not assume Gaussian derivative formulas or a smooth graph.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Paper

/-- A positive external field makes the actual squared-tanh expectation
strictly positive, for every variance coordinate.
@isnad1 id=lt.1h3v.s4.763dd88e49eb from=translated src=- shape=665d5371 vocab=5ba54f7c
-/
theorem overlapMap_pos_of_field_pos (β h q : ℝ) (hh : 0 < h) :
    0 < overlapMap β h q := by
  let : Measure.IsOpenPosMeasure (gaussianReal 0 1) :=
    (gaussianReal_absolutelyContinuous' (0 : ℝ)
      (by norm_num : (1 : ℝ≥0) ≠ 0)).isOpenPosMeasure
  have hc : Continuous (fun z => gaussianField β h q z) := by
    unfold gaussianField
    fun_prop
  have hcont : Continuous (fun z => Real.tanh (gaussianField β h q z) ^ 2) := by
    simp only [Real.tanh_eq_sinh_div_cosh]
    exact (((Real.continuous_sinh.comp hc).div (Real.continuous_cosh.comp hc)
      (fun z => ne_of_gt (Real.cosh_pos _))).pow 2)
  unfold overlapMap gaussianExpectation
  apply integral_pos_of_integrable_nonneg_nonzero hcont
    (integrable_gaussian_tanh_sq β h q) (fun z => sq_nonneg _) (x := 0)
  simpa [gaussianField] using (sq_pos_of_pos (tanh_pos hh)).ne'

/-- The time-coordinate `A` is strictly positive.
@isnad1 id=lt.0h2v.s4.648b0627f154 from=translated src=- shape=a120b2a8 vocab=b8ae05c1
-/
theorem gaussianA_pos (h t : ℝ) : 0 < gaussianA h t :=
  gaussian_sech_pow_pos h (Real.sqrt t) 2

/-- The time-coordinate `C` is strictly positive.
@isnad1 id=lt.0h2v.s4.0f8381172eb7 from=translated src=- shape=a120b2a8 vocab=27ca9fcf
-/
theorem gaussianC_pos (h t : ℝ) : 0 < gaussianC h t :=
  gaussian_sech_pow_pos h (Real.sqrt t) 4

/-- `tanh²+sech²=1` integrated in the time coordinates.
@isnad1 id=eq.0h2v.s5.93b2d580e08a from=translated src=- shape=952b9b8e vocab=f7cc5c5a
-/
theorem gaussianA_add_overlap_time (h t : ℝ) :
    overlapMap (Real.sqrt t) h 1 + gaussianA h t = 1 := by
  have he := overlapMap_add_sech_sq (Real.sqrt t) h 1
  simpa [gaussianA, gaussianField, add_comm] using he

/-- The strict upper bound needed for reconstructing the positive fixed point.
Strictness uses the actual Gaussian law, rather than an abstract expectation.
@isnad1 id=lt.1h2v.s4.0372e7d2e598 from=translated src=- shape=3f00eb23 vocab=b8ae05c1
-/
theorem gaussianA_lt_one_of_field_pos (h t : ℝ) (hh : 0 < h) :
    gaussianA h t < 1 := by
  have hp := overlapMap_pos_of_field_pos (Real.sqrt t) h 1 hh
  have he := gaussianA_add_overlap_time h t
  linarith

/-- The fourth sech moment is at most the second moment.
@isnad1 id=le.0h2v.s3.fb0f340cae77 from=translated src=- shape=6c8684e5 vocab=b780353f
-/
theorem gaussianC_le_gaussianA (h t : ℝ) : gaussianC h t ≤ gaussianA h t := by
  apply integral_mono (integrable_gaussian_sech_pow h (Real.sqrt t) 4)
    (integrable_gaussian_sech_pow h (Real.sqrt t) 2)
  intro z
  have hs : 0 ≤ sech (h + Real.sqrt t * z) ^ 2 := sq_nonneg _
  have hle := sech_sq_le_one (h + Real.sqrt t * z)
  nlinarith [mul_nonneg hs (sub_nonneg.mpr hle)]

/-- Positive external field makes the actual fourth sech moment less than one.
@isnad1 id=lt.1h2v.s4.a369e2a0d987 from=translated src=- shape=3f00eb23 vocab=27ca9fcf
-/
theorem gaussianC_lt_one_of_field_pos (h t : ℝ) (hh : 0 < h) :
    gaussianC h t < 1 :=
  lt_of_le_of_lt (gaussianC_le_gaussianA h t) (gaussianA_lt_one_of_field_pos h t hh)

/-- The Gaussian field agrees with the appendix's time parametrization.
@isnad1 id=eq.1h4v.s6.f75521715667 from=translated src=- shape=4d209b21 vocab=45bc64e7
-/
theorem gaussianField_eq_time (β h q z : ℝ) (hβ : 0 ≤ β) :
    gaussianField β h q z = h + Real.sqrt (β ^ 2 * q) * z := by
  rw [Real.sqrt_mul (sq_nonneg β), Real.sqrt_sq hβ]
  unfold gaussianField
  ring

/-- Any power of sech can be read in the time coordinates.
@isnad1 id=eq.1h4v.s6.0bd759985f9c from=translated src=- shape=4114c4e6 vocab=e8f52ea5
-/
theorem gaussian_sech_time_coordinate (β h q : ℝ) (n : ℕ) (hβ : 0 ≤ β) :
    gaussianExpectation (fun z => sech (gaussianField β h q z) ^ n) =
      gaussianExpectation (fun z => sech (h + Real.sqrt (β ^ 2 * q) * z) ^ n) := by
  congr 1
  ext z
  rw [gaussianField_eq_time β h q z hβ]

/-- The actual fixed-point and AT equations imply the appendix's zero equation.
@isnad1 id=eq.3h3v.s6.4131a5750e11 from=translated src=- shape=ce88b831 vocab=825d5c20
-/
theorem gaussian_at_critical_gives_zero (β h q : ℝ) (hβ : 0 < β)
    (hfixed : q = overlapMap β h q) (hcritical : atParameter β h q = 1) :
    atZeroFunction h (β ^ 2 * q) = 0 := by
  have hsum := overlapMap_add_sech_sq β h q
  rw [gaussian_sech_time_coordinate β h q 2 hβ.le] at hsum
  have hfixedA : q = 1 - gaussianA h (β ^ 2 * q) := by
    rw [← hfixed] at hsum
    change q + gaussianA h (β ^ 2 * q) = 1 at hsum
    linarith
  have hcriticalC : β ^ 2 * gaussianC h (β ^ 2 * q) = 1 := by
    unfold atParameter at hcritical
    rw [gaussian_sech_time_coordinate β h q 4 hβ.le] at hcritical
    exact hcritical
  exact at_critical_gives_zero β q (gaussianA h (β ^ 2 * q))
    (gaussianC h (β ^ 2 * q)) hfixedA hcriticalC

/-- The zero-coordinate inverse-temperature for a Gaussian AT point is exact.
@isnad1 id=eq.2h3v.s6.e635df4b10ee from=translated src=- shape=ca5f57d1 vocab=d594bf86
-/
theorem gaussian_at_critical_beta_coordinate (β h q : ℝ) (hβ : 0 < β)
    (hcritical : atParameter β h q = 1) :
    β = Real.sqrt (1 / gaussianC h (β ^ 2 * q)) := by
  have hC := gaussianC_pos h (β ^ 2 * q)
  have hcriticalC : β ^ 2 * gaussianC h (β ^ 2 * q) = 1 := by
    unfold atParameter at hcritical
    rw [gaussian_sech_time_coordinate β h q 4 hβ.le] at hcritical
    exact hcritical
  have hs : β ^ 2 = 1 / gaussianC h (β ^ 2 * q) :=
    (eq_div_iff (ne_of_gt hC)).mpr hcriticalC
  calc
    β = Real.sqrt (β ^ 2) := (Real.sqrt_sq hβ.le).symm
    _ = Real.sqrt (1 / gaussianC h (β ^ 2 * q)) := congrArg Real.sqrt hs

/-- Every positive-field critical Gaussian point has `β>1`, independently of
the yet-unproved smooth-graph parametrization.
@isnad1 id=lt.3h3v.s5.d3b11c4b40b2 from=translated src=- shape=7135925c vocab=49d0c5ef
-/
theorem gaussian_at_critical_beta_gt_one (β h q : ℝ) (hβ : 0 < β) (hh : 0 < h)
    (hcritical : atParameter β h q = 1) : 1 < β := by
  have hC := gaussianC_lt_one_of_field_pos h (β ^ 2 * q) hh
  have hcriticalC : β ^ 2 * gaussianC h (β ^ 2 * q) = 1 := by
    unfold atParameter at hcritical
    rw [gaussian_sech_time_coordinate β h q 4 hβ.le] at hcritical
    exact hcritical
  have hsq : 1 < β ^ 2 := by
    nlinarith [sq_pos_of_pos hβ]
  nlinarith

/-- A positive Gaussian zero produces an actual fixed point and AT-critical
inverse temperature, with the paper's strict overlap bounds.
@isnad1 id=other.3h2v.s6.721a49995d78 from=translated src=- shape=7972ec2b vocab=482e562f
-/
theorem gaussian_at_zero_reconstruction (h t : ℝ) (hh : 0 < h) (_ht : 0 < t)
    (hzero : atZeroFunction h t = 0) :
    let C := gaussianC h t
    let β := Real.sqrt (1 / C)
    let q := t * C
    0 < β ∧ q ∈ Set.Ioo (0 : ℝ) 1 ∧ q = overlapMap β h q ∧
      atParameter β h q = 1 := by
  dsimp
  have hC := gaussianC_pos h t
  have hApos := gaussianA_pos h t
  have hAlt := gaussianA_lt_one_of_field_pos h t hh
  have hzero' : atZeroQuantity t (gaussianA h t) (gaussianC h t) = 0 := hzero
  have hqbounds := at_zero_fixed_point_bounds t (gaussianA h t) (gaussianC h t)
    hzero' hApos hAlt
  have harg := at_sqrt_argument t (gaussianC h t) hC
  have hsum := overlapMap_add_sech_sq (Real.sqrt (1 / gaussianC h t)) h
    (t * gaussianC h t)
  have heq : gaussianExpectation
      (fun z => sech (gaussianField (Real.sqrt (1 / gaussianC h t)) h
        (t * gaussianC h t) z) ^ 2) = gaussianA h t := by
    unfold gaussianA
    congr 1
    ext z
    unfold gaussianField
    rw [harg]
    rw [add_comm]
  rw [heq] at hsum
  have hfixed := (at_zero_iff_fixed_point t (gaussianA h t) (gaussianC h t)).mp hzero'
  refine ⟨Real.sqrt_pos.2 (one_div_pos.mpr hC), hqbounds, ?_, ?_⟩
  · linarith
  · unfold atParameter
    have heq4 : gaussianExpectation
        (fun z => sech (gaussianField (Real.sqrt (1 / gaussianC h t)) h
          (t * gaussianC h t) z) ^ 4) = gaussianC h t := by
      conv_rhs => unfold gaussianC
      congr 1
      ext z
      unfold gaussianField
      rw [harg]
      rw [add_comm]
    rw [heq4]
    exact at_sqrt_coordinate_critical (gaussianC h t) hC

/-- Positive Gaussian zeros in the order `(h,t)` used by the appendix.-/
def positiveATZeroSet : Set (ℝ × ℝ) :=
  {p | 0 < p.1 ∧ 0 < p.2 ∧ atZeroFunction p.1 p.2 = 0}

/-- The change of coordinates from a zero `(h,t)` to an AT point `(β,h)`.-/
noncomputable def atZeroToBoundary (p : ℝ × ℝ) : ℝ × ℝ :=
  (Real.sqrt (1 / gaussianC p.1 p.2), p.1)

/-- Every positive Gaussian zero maps into the actual boundary definition.
@isnad1 id=mem.1h1v.s5.09c56d5436f4 from=translated src=- shape=1c278087 vocab=8ca14e07
-/
theorem atZeroToBoundary_mem {p : ℝ × ℝ} (hp : p ∈ positiveATZeroSet) :
    atZeroToBoundary p ∈ atBoundary := by
  rcases hp with ⟨hh, ht, hzero⟩
  have hr := gaussian_at_zero_reconstruction p.1 p.2 hh ht hzero
  apply Or.inl
  refine ⟨hr.1, hh, p.2 * gaussianC p.1 p.2, ?_, hr.2.2.1, hr.2.2.2⟩
  exact ⟨hr.2.1.1.le, hr.2.1.2.le⟩

/-- The appendix's complete zero-set image description, proved from the
concrete Gaussian quantities. Smooth parametrization remains a separate task.
@isnad1 id=eq.0h0v.s5.8891a1645aee from=translated src=- shape=87966d39 vocab=ade238fd
-/
theorem atBoundary_eq_zero_image :
    atBoundary = atZeroToBoundary '' positiveATZeroSet ∪ {(1, 0)} := by
  ext p
  constructor
  · intro hp
    rcases hp with hp | hp
    · rcases hp with ⟨hβ, hh, q, hq, hfixed, hcritical⟩
      have hqpos := fixedPoint_pos hh hq.1 hfixed
      have ht : 0 < p.1 ^ 2 * q := mul_pos (sq_pos_of_pos hβ) hqpos
      apply Or.inl
      refine ⟨(p.2, p.1 ^ 2 * q), ⟨hh, ht, ?_⟩, ?_⟩
      · exact gaussian_at_critical_gives_zero p.1 p.2 q hβ hfixed hcritical
      · apply Prod.ext
        · exact (gaussian_at_critical_beta_coordinate p.1 p.2 q hβ hcritical).symm
        · rfl
    · exact Or.inr hp
  · intro hp
    rcases hp with ⟨z, hz, hp⟩ | hp
    · rw [← hp]
      exact atZeroToBoundary_mem hz
    · exact Or.inr hp

end Paper
