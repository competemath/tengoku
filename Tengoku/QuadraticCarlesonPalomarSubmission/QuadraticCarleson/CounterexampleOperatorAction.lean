/-
Copyright (c) 2026 Quadratic Carleson formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quadratic Carleson formalization contributors
-/
import Tengoku.QuadraticCarlesonPalomarSubmission.QuadraticCarleson.OffSupportKernel
import Tengoku.QuadraticCarlesonPalomarSubmission.QuadraticCarleson.OffSupportOscillatory
import Tengoku.QuadraticCarlesonPalomarSubmission.QuadraticCarleson.SchwartzModularOperator

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The canonical operator on the counterexample away from its packets

This file identifies the distributionally defined quadratic Hilbert transform
with the ordinary off-support kernel integrals used in the negative endpoint
argument.  No pointwise value is assigned by convention: the equality follows
from the proved symmetric-truncation limit because the test function vanishes
near the singularity.
-/

open Filter MeasureTheory Set
open scoped SchwartzMap Topology

namespace QuadraticCarleson

set_option autoImplicit false

/--
@isnad1 id=eq.0h4v.s4.f544844f710b from=translated src=- shape=63300181 vocab=a55565f0
-/
@[simp]
theorem offSupportOscillatoryAction_eq_offSupportKernelAction
    (modulation s t x : ℝ) :
    offSupportOscillatoryAction modulation s t x =
      offSupportKernelAction modulation s t x :=
  rfl

/-- The rigorously proved two-fold integration-by-parts estimate, restated
for the ordinary kernel action used in the stationary/oscillatory split.
@isnad1 id=le.3h4v.s7.bc5722afdd2a from=translated src=- shape=19421895 vocab=f11ab865
-/
theorem offSupportKernelAction_oscillatory_norm_le
    {modulation s t x : ℝ} (hmod : 0 < modulation) (ht : 0 < t)
    (hx : x ∉ Icc (s - t / 2) (s + t / 2)) :
    ‖offSupportKernelAction modulation s t x‖ ≤
      offSupportOscillatoryConstant /
        (modulation ^ 2 * t ^ 2 * |x - s| ^ 3) := by
  simpa only [offSupportOscillatoryAction_eq_offSupportKernelAction] using
    offSupportOscillatoryAction_norm_le hmod ht hx

/-- If the translated Schwartz function vanishes on a genuine neighbourhood
of the singularity, its canonical distributional quadratic Hilbert transform
is the corresponding ordinary integral.
@isnad1 id=eq.2h4v.s7.ad9a50082461 from=translated src=- shape=de91ba2e vocab=1745f709
-/
theorem quadraticHilbertSchwartz_eq_integral_of_zero_near
    (modulation : ℝ) (f : 𝓢(ℝ, ℂ)) (x : ℝ) {r : ℝ} (hr : 0 < r)
    (hzero : ∀ y : ℝ, |y| < r → f (x - y) = 0) :
    quadraticHilbertSchwartz modulation f x =
      ∫ y : ℝ, f (x - y) * phase (modulation * y ^ 2) / (y : ℂ) := by
  let I : ℂ := ∫ y : ℝ, f (x - y) * phase (modulation * y ^ 2) / (y : ℂ)
  have heq : ∀ᶠ ε : ℝ in 𝓝[>] 0, quadraticHilbertTrunc modulation ε f x = I := by
    filter_upwards [eventually_mem_nhdsWithin,
      (eventually_lt_nhds hr).filter_mono nhdsWithin_le_nhds] with ε hε hεr
    unfold quadraticHilbertTrunc I
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro y hy
    have hyε : |y| ≤ ε := le_of_not_gt hy
    rw [hzero y (hyε.trans_lt hεr)]
    simp
  apply tendsto_nhds_unique (hasQuadraticPrincipalValue_schwartz modulation f x)
  exact tendsto_const_nhds.congr' (heq.mono fun _ h ↦ h.symm)

/-- A positive-scale wave packet, bundled as a Schwartz function.-/
noncomputable def wavePacketSchwartz (s t : ℝ) (ht : 0 < t) : 𝓢(ℝ, ℂ) :=
  ((wavePacket_hasCompactSupport s ht).comp_left Complex.ofReal_zero).toSchwartzMap
    (Complex.ofRealCLM.contDiff.comp (contDiff_wavePacket s t))

/--
@isnad1 id=eq.1h3v.s6.63b0b8f2302d from=translated src=- shape=0e941ab9 vocab=617c4fb9
-/
@[simp]
theorem wavePacketSchwartz_apply (s t : ℝ) (ht : 0 < t) (u : ℝ) :
    wavePacketSchwartz s t ht u = wavePacket s t u :=
  rfl

/-- Away from the packet interval, the canonical principal value is exactly
the ordinary action estimated in the paper's off-support lemma.
@isnad1 id=eq.2h4v.s6.9ab6c6b205a3 from=translated src=- shape=95449e6b vocab=d443e460
-/
theorem quadraticHilbertSchwartz_wavePacket_eq_offSupportKernelAction
    {modulation s t x : ℝ} (ht : 0 < t)
    (hx : x ∉ Icc (s - t / 2) (s + t / 2)) :
    quadraticHilbertSchwartz modulation (wavePacketSchwartz s t ht) x =
      offSupportKernelAction modulation s t x := by
  rw [quadraticHilbertSchwartz_eq_integral_of_zero_near modulation
    (wavePacketSchwartz s t ht) x (half_pos (half_pos ht))]
  · exact (offSupportKernelAction_eq_integral_kernel_variable modulation s t x).symm
  · intro y hy
    simp only [wavePacketSchwartz_apply]
    by_contra hpacket
    have hpacketReal : wavePacket s t (x - y) ≠ 0 := by
      intro h
      exact hpacket (by simp [h])
    have hsep := half_abs_sub_center_le_abs_sub ht hx hpacketReal
    have hdist := half_length_le_abs_sub_center ht hx
    have hyid : |x - (x - y)| = |y| := by congr 1; ring
    rw [hyid] at hsep
    linarith

/-- The quadratic transform is additive in its Schwartz input.
@isnad1 id=eq.0h4v.s7.fd4eac83c3a1 from=translated src=- shape=d1e09688 vocab=75776c60
-/
theorem quadraticHilbertSchwartz_add (modulation : ℝ) (f g : 𝓢(ℝ, ℂ)) (x : ℝ) :
    quadraticHilbertSchwartz modulation (f + g) x =
      quadraticHilbertSchwartz modulation f x + quadraticHilbertSchwartz modulation g x := by
  unfold quadraticHilbertSchwartz
  have hflip : schwartzFlipTranslate (f + g) x =
      schwartzFlipTranslate f x + schwartzFlipTranslate g x := by
    ext y
    simp only [schwartzFlipTranslate_apply, add_apply]
  rw [hflip, map_add]

/-- Finite additivity in the form needed for the wave-packet superposition.
@isnad1 id=eq.0h5v.s7.6aa27a861735 from=translated src=- shape=8a9b3409 vocab=d1452350
-/
theorem quadraticHilbertSchwartz_finset_sum {ι : Type*} (s : Finset ι)
    (f : ι → 𝓢(ℝ, ℂ)) (modulation x : ℝ) :
    quadraticHilbertSchwartz modulation (∑ i ∈ s, f i) x =
      ∑ i ∈ s, quadraticHilbertSchwartz modulation (f i) x := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      have hflip : schwartzFlipTranslate (0 : 𝓢(ℝ, ℂ)) x = 0 := by
        ext y
        simp only [schwartzFlipTranslate_apply, zero_apply]
      simp only [Finset.sum_empty]
      unfold quadraticHilbertSchwartz
      rw [hflip, map_zero]
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha,
        quadraticHilbertSchwartz_add, ih]

/-- The bundled counterexample is exactly the normalized finite sum of its
bundled wave packets.
@isnad1 id=eq.0h1v.s7.c8665b415a39 from=translated src=- shape=a0dfb097 vocab=a65629aa
-/
theorem counterexampleSchwartz_eq_wavePacketSchwartz_sum (N : ℕ) :
    counterexampleSchwartz N =
      (N : ℝ)⁻¹ • ∑ j ∈ Finset.Icc 1 N,
        wavePacketSchwartz (j : ℝ) (packetScale N j) (packetScale_pos N j) := by
  ext u
  rw [counterexampleSchwartz_apply]
  unfold counterexample
  rw [smul_apply]
  rw [counterexampleReal, packetSum, Finset.sum_apply]
  simp only [sum_apply, wavePacketSchwartz_apply]
  push_cast
  rw [Complex.real_smul]
  rw [Complex.ofReal_inv, Complex.ofReal_natCast]

/-- At a point outside every packet interval, the canonical transform of the
counterexample is the normalized finite sum of ordinary off-support actions.
@isnad1 id=eq.1h3v.s6.02c212bda87b from=translated src=- shape=54d0e7a3 vocab=9732b776
-/
theorem quadraticHilbertSchwartz_counterexample_eq_offSupport_sum
    (N : ℕ) (modulation x : ℝ)
    (hx : ∀ j ∈ Finset.Icc 1 N, x ∉ packetInterval N j) :
    quadraticHilbertSchwartz modulation (counterexampleSchwartz N) x =
      (N : ℝ)⁻¹ • ∑ j ∈ Finset.Icc 1 N,
        offSupportKernelAction modulation (j : ℝ) (packetScale N j) x := by
  rw [counterexampleSchwartz_eq_wavePacketSchwartz_sum N,
    quadraticHilbertSchwartz_real_smul,
    quadraticHilbertSchwartz_finset_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  exact quadraticHilbertSchwartz_wavePacket_eq_offSupportKernelAction
    (packetScale_pos N j) (hx j hj)

end QuadraticCarleson
