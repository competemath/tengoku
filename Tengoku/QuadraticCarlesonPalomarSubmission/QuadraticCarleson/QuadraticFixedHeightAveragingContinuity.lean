/-
Copyright (c) 2026 Quadratic Carleson formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quadratic Carleson formalization contributors
-/
import Tengoku.QuadraticCarlesonPalomarSubmission.QuadraticCarleson.QuadraticFixedHeightAveragingCountable
import Tengoku.Seed.Topology.Instances.Rat

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Fixed-scale parameter continuity and rational approximation of half-open bands

Continuity is asserted only with the spatial scale held fixed. The density
lemma includes the lower endpoint by taking closure from inside the open
band, so it never crosses a jump of the selected dyadic scale.
-/

open MeasureTheory Set
open scoped ENNReal NNReal Topology

namespace QuadraticCarleson

/-- Compact spatial support and local integrability give a single integrable
majorant for every quadratic modulation parameter.
@isnad1 id=continuo.3h3v.s7.055f83fd7fd1 from=translated src=- shape=175322c3 vocab=d0d0670a
-/
theorem continuous_quadraticConvolution_parameter {a f : ℝ → ℂ}
    (ha : Continuous a) (has : HasCompactSupport a)
    (hf : LocallyIntegrable f) (x : ℝ) :
    Continuous (fun lam : ℝ ↦ ∫ t,
      a (x - t) * phase (lam * (x - t) ^ 2) * f t) := by
  have hi : Integrable (fun t ↦ a (x - t) * f t) :=
    hf.integrable_smul_left_of_hasCompactSupport
      (ha.comp (continuous_const.sub continuous_id))
      (has.comp_homeomorph (Homeomorph.subLeft x))
  apply continuous_of_dominated
    (bound := fun t ↦ ‖a (x - t) * f t‖)
  · intro lam
    have hp : Continuous (fun t : ℝ ↦ phase (lam * (x - t) ^ 2)) := by
      unfold phase
      fun_prop
    convert hi.aestronglyMeasurable.mul hp.aestronglyMeasurable using 1
    funext t
    simp only [Pi.mul_apply]
    ring
  · intro lam
    filter_upwards [] with t
    simp only [norm_mul, norm_phase, mul_one, le_refl]
  · exact hi.norm
  · filter_upwards [] with t
    unfold phase
    fun_prop

/--
@isnad1 id=hascompa.0h1v.s4.98062d3b3e99 from=translated src=- shape=101261e3 vocab=ed04b9fd
-/
theorem hasCompactSupport_complex_dyadicPsi (j : ℤ) :
    HasCompactSupport (fun t ↦ (dyadicPsi j t : ℂ)) := by
  apply HasCompactSupport.of_support_subset_isCompact
    (isCompact_Icc : IsCompact (Icc (-((2 : ℝ) ^ (j - 1))) ((2 : ℝ) ^ (j - 1))))
  intro t ht
  have hψ : dyadicPsi j t ≠ 0 := by
    intro hz
    exact ht (by simp [hz])
  have hb := (dyadicPsi_support_subset j hψ).2
  exact ⟨(abs_lt.mp hb).1.le, (abs_lt.mp hb).2.le⟩

/-- The concrete dyadic integral depends continuously on modulation when
the integer scale is held fixed.
@isnad1 id=continuo.1h3v.s7.d4302bd297fb from=translated src=- shape=0db9cef5 vocab=a40311de
-/
theorem continuous_dyadicQuadraticConvolution_parameter
    (j : ℤ) {f : ℝ → ℂ} (hf : LocallyIntegrable f) (x : ℝ) :
    Continuous (fun lam : ℝ ↦ ∫ t,
      (dyadicPsi j (x - t) : ℂ) * phase (lam * (x - t) ^ 2) * f t) := by
  apply continuous_quadraticConvolution_parameter
    (Complex.continuous_ofReal.comp (dyadicPsi_smooth j).continuous)
    (hasCompactSupport_complex_dyadicPsi j) hf x

/-- Explicit rational points strictly inside an interval approximate every
point of its half-open version, including the lower endpoint from the right.
@isnad1 id=le.1h2v.s5.e9f5708e9be9 from=translated src=- shape=27f4c3f9 vocab=d6fe105e
-/
theorem Ico_subset_closure_rational_Ioo {a b : ℝ} (hab : a < b) :
    Ico a b ⊆ closure (Ioo a b ∩ range (fun q : ℚ ↦ (q : ℝ))) := by
  have hd : Ioo a b ⊆ closure (Ioo a b ∩ range (fun q : ℚ ↦ (q : ℝ))) :=
    Rat.denseRange_cast.open_subset_closure_inter isOpen_Ioo
  have hc := closure_minimal hd isClosed_closure
  rw [closure_Ioo hab.ne] at hc
  exact Ico_subset_Icc_self.trans hc

/-- An explicit enumeration of all nonzero rational real modulations. The
unused or zero decoding values are assigned the harmless parameter one.-/
noncomputable def rationalModulationSequence (n : ℕ) : ℝ :=
  let q : ℚ := (Encodable.decode n).getD 1
  if q = 0 then 1 else (q : ℝ)

/--
@isnad1 id=ne.0h1v.s3.9f50315b2abc from=translated src=- shape=a311c14d vocab=32baf497
-/
theorem rationalModulationSequence_ne_zero (n : ℕ) :
    rationalModulationSequence n ≠ 0 := by
  dsimp only [rationalModulationSequence]
  split_ifs with h
  · norm_num
  · exact_mod_cast h

/--
@isnad1 id=ex.1h1v.s4.c8ae684ae54b from=translated src=- shape=294d9c65 vocab=60a536cd
-/
theorem exists_rationalModulationSequence (q : ℚ) (hq : q ≠ 0) :
    ∃ n, rationalModulationSequence n = (q : ℝ) := by
  refine ⟨Encodable.encode q, ?_⟩
  simp [rationalModulationSequence, hq]

end QuadraticCarleson
