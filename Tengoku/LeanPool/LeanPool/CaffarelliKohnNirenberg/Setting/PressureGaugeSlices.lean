/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Statements.SuitableWeakSolutionIntegrable
public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Topology
public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Core.Caccioppoli.LocalBox
public import Tengoku

/-!
# Slice identities behind the pressure gauge invariance

This file collects the measure-theoretic slice identities used in the proof of
the pressure gauge invariance of `rem:two-means` in `paper/ckn.tex`: a suitable
weak solution stays one when an arbitrary function of time is added to the
pressure.

The two facts that carry the analytic content are

* `gauge_divergence_pairing`: the gauge pairs integrably with the divergence of
  a space-time test field and the pairing vanishes, because the spatial
  integral of a divergence vanishes on every time slice;
* `gauge_velocity_pairing`: the gauge pairs integrably with `u · ∇ψ` and the
  pairing vanishes, because the divergence-free clause (S2) of `def:sws`,
  tested against `θ(t)ψ(x,t)`, forces the spatial pairing of the slice
  `u(·,t)` with `∇ψ(·,t)` to vanish for almost every time.

The uniform time-slice bound of the velocity comes from the essential
supremum of the slice energies in `def:sws` together with `x ≤ 1 + x²`; no
Gagliardo-Nirenberg input is needed.
-/

@[expose] public section

open MeasureTheory MeasureTheory.Measure Set Filter Metric
open scoped ENNReal NNReal Topology
open CKN.Foundation.Parabolic

noncomputable section

namespace CKN

/-- A local spatial box has finite volume. -/
private theorem localBox_volume_lt_top {Ω : Set Vec3} {I : Set ℝ} {Ω' : Set Vec3} {J : Set ℝ}
    (hbox : localBox Ω I Ω' J) : volume Ω' < ∞ :=
  lt_of_le_of_lt (measure_mono subset_closure) hbox.2.1.measure_lt_top

/-- A time-dependent gauge in `L^{3/2}(J)` lies in `L^{3/2}` of the space-time box.
@isnad1 id=memlp.2h5v.s7.8a0f5eba696d from=translated src=- shape=78368965 vocab=0b6e015a
-/
theorem memLp_gauge_on_box {Ω : Set Vec3} {I : Set ℝ} {Ω' : Set Vec3} {J : Set ℝ}
    (hbox : localBox Ω I Ω' J) {c : ℝ → ℝ}
    (hc : MemLp c (ENNReal.ofReal (3 / 2 : ℝ)) (volume.restrict J)) :
    MemLp (fun z : ParabolicPoint => c z.2) (ENNReal.ofReal (3 / 2 : ℝ))
      (volume.restrict (spaceTimeSet Ω' J)) := by
  have hfin : IsFiniteMeasure (volume.restrict Ω') := by
    refine ⟨?_⟩
    rw [Measure.restrict_apply_univ]
    exact localBox_volume_lt_top hbox
  have h := hc.comp_snd (volume.restrict Ω')
  rw [Measure.prod_restrict] at h
  rw [spaceTimeSet]
  exact h

/-- A spatial partial derivative vanishes off the topological support.
@isnad1 id=eq.1h3v.s6.7bb67dd6a10e from=translated src=- shape=a26c0557 vocab=650d9dd3
-/
theorem spatialPartial_eq_zero_off_tsupport {ψ : Vec3 × ℝ → ℝ}
    {z : Vec3 × ℝ} (hz : z ∉ tsupport ψ) (i : Fin 3) :
    spatialPartial ψ i z = 0 := by
  change (fderiv ℝ (fun x : Vec3 => ψ (x, z.2)) z.1) (basisVec i) = 0
  have hopen : (tsupport ψ)ᶜ ∈ 𝓝 z :=
    (isClosed_tsupport ψ).isOpen_compl.mem_nhds hz
  have hmap : Continuous (fun x : Vec3 => (x, z.2)) :=
    Continuous.prodMk continuous_id continuous_const
  have hev : (fun x : Vec3 => ψ (x, z.2)) =ᶠ[𝓝 z.1] (fun _ => (0 : ℝ)) := by
    filter_upwards [hmap.continuousAt.preimage_mem_nhds hopen] with x hx
    by_contra hne
    exact hx (subset_tsupport (f := ψ) (Function.mem_support.mpr hne))
  rw [hev.fderiv_eq, fderiv_const_apply]
  simp

/-- The parabolic topology and the product topology have the same closed
supports: the identity is a homeomorphism between them.
@isnad1 id=eq.0h2v.s6.37cffaca5624 from=translated src=- shape=9a6d5d65 vocab=18fecb6b
-/
theorem tsupport_parabolic_eq {V : Type} [Zero V] (f : Vec3 × ℝ → V) :
    tsupport (show ParabolicPoint → V from f) = tsupport f := by
  have hsupp : Function.support (show ParabolicPoint → V from f)
      = parabolicHomeomorph ⁻¹' (Function.support f) := rfl
  rw [tsupport, hsupp, ← parabolicHomeomorph.preimage_closure,
    parabolicHomeomorph_preimage, tsupport]

/-- The support of a spatial partial derivative lies in the support of the
function.
@isnad1 id=le.0h2v.s6.eb5589d723ad from=translated src=- shape=656b9f5d vocab=8249b37d
-/
theorem tsupport_spatialPartial_subset {ψ : Vec3 × ℝ → ℝ} (i : Fin 3) :
    tsupport (fun z : Vec3 × ℝ => spatialPartial ψ i z) ⊆ tsupport ψ := by
  refine closure_minimal ?_ (isClosed_tsupport ψ)
  intro z hz
  by_contra hcon
  exact hz (spatialPartial_eq_zero_off_tsupport hcon i)

/-- A time partial derivative vanishes off the topological support.
@isnad1 id=eq.1h2v.s6.7cf2fb9b785e from=translated src=- shape=311a74c2 vocab=80ea2ca9
-/
theorem timePartial_eq_zero_off_tsupport {ψ : Vec3 × ℝ → ℝ}
    {z : Vec3 × ℝ} (hz : z ∉ tsupport ψ) :
    timePartial ψ z = 0 := by
  change (fderiv ℝ (fun s : ℝ => ψ (z.1, s)) z.2) 1 = 0
  have hopen : (tsupport ψ)ᶜ ∈ 𝓝 z :=
    (isClosed_tsupport ψ).isOpen_compl.mem_nhds hz
  have hmap : Continuous (fun s : ℝ => (z.1, s)) :=
    Continuous.prodMk continuous_const continuous_id
  have hev : (fun s : ℝ => ψ (z.1, s)) =ᶠ[𝓝 z.2] (fun _ => (0 : ℝ)) := by
    filter_upwards [hmap.continuousAt.preimage_mem_nhds hopen] with s hs
    by_contra hne
    exact hs (subset_tsupport (f := ψ) (Function.mem_support.mpr hne))
  rw [hev.fderiv_eq, fderiv_const_apply]
  simp

/-- A component of a vector-valued test function has support inside the support
of the test function.
@isnad1 id=le.1h3v.s7.1539c5369080 from=translated src=- shape=53fbec89 vocab=54350d67
-/
theorem tsupport_component_subset
    {ι : Type} (φ : Vec3 × ℝ → ι → ℝ) (i : ι)
    (hzero : ∀ z, φ z = 0 → φ z i = 0) :
    tsupport (fun w => φ w i) ⊆ tsupport φ := by
  refine closure_mono ?_
  intro z hz
  by_contra hcon
  rw [Function.mem_support] at hz
  exact hz (hzero z (not_not.mp hcon))

end CKN
