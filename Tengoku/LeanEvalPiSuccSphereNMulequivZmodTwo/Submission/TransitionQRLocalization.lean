import Tengoku
import Tengoku.LeanEvalPiSuccSphereNMulequivZmodTwo.Submission.PolarDecompositionCLM

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Localizing the Gram--Schmidt factorization

`PolarDecompositionCLM.contDiff_qrUpper` and
`PolarDecompositionCLM.contDiff_qrSOMatrix_apply` require a *globally* smooth
family of gauges with everywhere positive determinant.  The transition
automorphism of two presentations is only defined — let alone invertible — near
the common fiber, so those lemmas cannot be applied to it directly.

The obstruction is genuine: a globally smooth `GL⁺`-valued extension of the
transition would trivialize its `ℤ/2` loop class, which is exactly the
invariant the development computes.  What *is* available is a purely local
statement, and this file supplies it.

The device is a **smooth squashing of the ambient space into a ball**: for any
centre `c` and radius `r` there is a globally smooth map `squash c r` which is
the identity on the ball of radius `r` around `c` and whose image is contained
in the ball of radius `2 r`.  Precomposing a locally defined gauge family with
a squashing into a ball on which it is defined and invertible produces a
*globally* smooth family with everywhere positive determinant which agrees with
the original near `c`.  The committed global smoothness lemmas then apply, and
`ContDiffAt.congr_of_eventuallyEq` transports the conclusion back.

Contents:

* `ramp`, `squash` — the smooth squashing;
* `exists_global_of_contDiffOn` — the localization device;
* `qrSOTotal` — the `SO` factor, extended by the identity where the determinant
  is not positive, so that it is a total function;
* `contDiffAt_qrUpper_of_contDiffOn`, `contDiffAt_qrSOTotal_of_contDiffOn` —
  the local smoothness of both Gram--Schmidt factors.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000

noncomputable section

open Set Function
open scoped Topology ContDiff

namespace Submission
namespace TransitionQRLocalization

/-! ## A smooth radial damping profile -/

/-- The damping profile: `1` on `(-∞, 1]`, and `O(1/t)` for large `t`.-/
def ramp (t : ℝ) : ℝ := (1 + t * Real.smoothTransition (t - 1))⁻¹

/--
@isnad1 id=lt.0h1v.s5.6eea9cd3b8e9 from=translated src=- shape=6aac593b vocab=be38c370
-/
theorem ramp_denom_pos (t : ℝ) : 0 < 1 + t * Real.smoothTransition (t - 1) := by
  rcases le_or_gt t 1 with h | h
  · rw [Real.smoothTransition.zero_of_nonpos (by linarith), mul_zero, add_zero]
    norm_num
  · have h0 : 0 ≤ t := by linarith
    have h1 : 0 ≤ Real.smoothTransition (t - 1) :=
      Real.smoothTransition.nonneg _
    nlinarith

/--
@isnad1 id=le.1h1v.s5.46ab0f1ee394 from=translated src=- shape=e52db299 vocab=52bcbdbc
-/
theorem ramp_denom_one_le (t : ℝ) (ht : 0 ≤ t) :
    1 ≤ 1 + t * Real.smoothTransition (t - 1) := by
  have h1 : 0 ≤ Real.smoothTransition (t - 1) := Real.smoothTransition.nonneg _
  nlinarith

/--
@isnad1 id=contdiff.0h0v.s5.53f5314ec9df from=translated src=- shape=3cea26be vocab=f499c4f0
-/
theorem contDiff_ramp : ContDiff ℝ ∞ ramp := by
  have hden : ContDiff ℝ ∞ fun t : ℝ => 1 + t * Real.smoothTransition (t - 1) :=
    contDiff_const.add (contDiff_id.mul
      (Real.smoothTransition.contDiff.comp (contDiff_id.sub contDiff_const)))
  exact hden.inv fun t => (ramp_denom_pos t).ne'

/--
@isnad1 id=lt.0h1v.s3.d80d2e0ab2bc from=translated src=- shape=8a62b088 vocab=2b780d65
-/
theorem ramp_pos (t : ℝ) : 0 < ramp t := inv_pos.mpr (ramp_denom_pos t)

/--
@isnad1 id=eq.1h1v.s4.5d5f5242915b from=translated src=- shape=278e0375 vocab=21afdbb7
-/
theorem ramp_eq_one_of_le_one {t : ℝ} (ht : t ≤ 1) : ramp t = 1 := by
  rw [ramp, Real.smoothTransition.zero_of_nonpos (by linarith), mul_zero,
    add_zero, inv_one]

/--
@isnad1 id=le.1h1v.s4.b3714196aff2 from=translated src=- shape=3965f485 vocab=21afdbb7
-/
theorem ramp_le_one {t : ℝ} (ht : 0 ≤ t) : ramp t ≤ 1 := by
  rw [ramp]
  exact inv_le_one_of_one_le₀ (ramp_denom_one_le t ht)

/--
@isnad1 id=le.1h1v.s5.d030ccd3848f from=translated src=- shape=79f76bea vocab=8f089ce9
-/
theorem mul_ramp_sq_le {t : ℝ} (ht : 0 ≤ t) : t * ramp t ^ 2 ≤ 2 := by
  rcases le_or_gt t 2 with h | h
  · have h1 : ramp t ≤ 1 := ramp_le_one ht
    have h2 : 0 < ramp t := ramp_pos t
    nlinarith
  · have h3 : Real.smoothTransition (t - 1) = 1 :=
      Real.smoothTransition.one_of_one_le (by linarith)
    have hr : ramp t = (1 + t)⁻¹ := by rw [ramp, h3, mul_one]
    have hpos : 0 < 1 + t := by linarith
    rw [hr, inv_pow, ← div_eq_mul_inv, div_le_iff₀ (by positivity)]
    nlinarith

/-! ## Squashing the ambient space into a ball -/

section Squash

variable {N : ℕ}

/-- A globally smooth map which is the identity on the closed ball of radius
`r` about `c` and whose image lies in the open ball of radius `2 r`.-/
def squash (c : EuclideanSpace ℝ (Fin N)) (r : ℝ)
    (y : EuclideanSpace ℝ (Fin N)) : EuclideanSpace ℝ (Fin N) :=
  c + ramp (‖y - c‖ ^ 2 / r ^ 2) • (y - c)

/--
@isnad1 id=contdiff.0h3v.s7.4ab9f3d66a5a from=translated src=- shape=eb7335f3 vocab=198049d2
-/
theorem contDiff_squash (c : EuclideanSpace ℝ (Fin N)) (r : ℝ) :
    ContDiff ℝ ∞ (squash c r) := by
  have hsub : ContDiff ℝ ∞ fun y : EuclideanSpace ℝ (Fin N) => y - c :=
    contDiff_id.sub contDiff_const
  have hnorm : ContDiff ℝ ∞
      fun y : EuclideanSpace ℝ (Fin N) => ‖y - c‖ ^ 2 / r ^ 2 :=
    ((contDiff_norm_sq ℝ).comp hsub).div_const _
  exact contDiff_const.add ((contDiff_ramp.comp hnorm).smul hsub)

/--
@isnad1 id=eq.2h4v.s7.2930056e209b from=translated src=- shape=835c92ca vocab=70e8be6a
-/
theorem squash_eq_self {c : EuclideanSpace ℝ (Fin N)} {r : ℝ} (hr : 0 < r)
    {y : EuclideanSpace ℝ (Fin N)} (hy : ‖y - c‖ ≤ r) : squash c r y = y := by
  have ht : ‖y - c‖ ^ 2 / r ^ 2 ≤ 1 := by
    rw [div_le_one (by positivity)]
    have h0 : 0 ≤ ‖y - c‖ := norm_nonneg _
    nlinarith
  rw [squash, ramp_eq_one_of_le_one ht, one_smul, add_sub_cancel]

/--
@isnad1 id=lt.1h4v.s7.717d9dbb7fea from=translated src=- shape=48fb0065 vocab=6b474b21
-/
theorem norm_squash_sub_lt {c : EuclideanSpace ℝ (Fin N)} {r : ℝ} (hr : 0 < r)
    (y : EuclideanSpace ℝ (Fin N)) : ‖squash c r y - c‖ < 2 * r := by
  set t : ℝ := ‖y - c‖ ^ 2 / r ^ 2 with htdef
  have ht0 : 0 ≤ t := by positivity
  have hval : squash c r y - c = ramp t • (y - c) := by
    rw [squash, add_sub_cancel_left]
  have hsq : ‖squash c r y - c‖ ^ 2 = ramp t ^ 2 * ‖y - c‖ ^ 2 := by
    rw [hval, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  have hyt : ‖y - c‖ ^ 2 = t * r ^ 2 := by
    rw [htdef, div_mul_cancel₀]
    positivity
  have hbound : ‖squash c r y - c‖ ^ 2 ≤ 2 * r ^ 2 := by
    rw [hsq, hyt]
    have := mul_ramp_sq_le ht0
    nlinarith [sq_nonneg (ramp t), sq_nonneg r]
  have hnn : 0 ≤ ‖squash c r y - c‖ := norm_nonneg _
  nlinarith

end Squash

/-! ## The localization device -/

section Localize

variable {N k : ℕ}

/-- **Localization.**  A gauge family which is smooth and orientation
preserving on an open set is, near any point of that set, the restriction of a
globally smooth gauge family with everywhere positive determinant.
@isnad1 id=ex.4h5v.s11.48f834c8b444 from=translated src=- shape=e7f8880d vocab=318bca11
-/
theorem exists_global_of_contDiffOn
    (Phi : EuclideanSpace ℝ (Fin N) →
      EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin k))
    {V : Set (EuclideanSpace ℝ (Fin N))} (hV : IsOpen V)
    (hPhi : ContDiffOn ℝ ∞ Phi V)
    (hdet : ∀ x ∈ V, 0 < (PolarDecompositionCLM.clmMatrix (Phi x)).det)
    {c : EuclideanSpace ℝ (Fin N)} (hc : c ∈ V) :
    ∃ Psi : EuclideanSpace ℝ (Fin N) →
        EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin k),
      ContDiff ℝ ∞ Psi ∧
        (∀ x, 0 < (PolarDecompositionCLM.clmMatrix (Psi x)).det) ∧
        Psi =ᶠ[nhds c] Phi := by
  obtain ⟨d, hd, hball⟩ := Metric.isOpen_iff.mp hV c hc
  have hr : 0 < d / 4 := by linarith
  have hmem : ∀ y : EuclideanSpace ℝ (Fin N), squash c (d / 4) y ∈ V := by
    intro y
    apply hball
    have := norm_squash_sub_lt (c := c) hr y
    rw [Metric.mem_ball, dist_eq_norm]
    linarith
  refine ⟨fun y => Phi (squash c (d / 4) y), ?_, ?_, ?_⟩
  · rw [← contDiffOn_univ]
    exact hPhi.comp (contDiff_squash c (d / 4)).contDiffOn
      fun y _ => hmem y
  · intro x
    exact hdet _ (hmem x)
  · refine Filter.eventuallyEq_of_mem
      (Metric.ball_mem_nhds c (by linarith : (0:ℝ) < d / 4)) ?_
    intro y hy
    have : ‖y - c‖ ≤ d / 4 := by
      rw [Metric.mem_ball, dist_eq_norm] at hy
      exact hy.le
    exact congrArg Phi (squash_eq_self hr this)

end Localize

/-! ## The total `SO` factor and local smoothness of both factors -/

section Factors

variable {N k : ℕ}

/-- The special-orthogonal Gram--Schmidt factor, extended by the identity where
the determinant is not positive.  This is a *total* function of the gauge, so
it can be used to define families over the whole ambient space.-/
def qrSOTotal (A : EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin k)) :
    SOGroup k :=
  if h : 0 < (PolarDecompositionCLM.clmMatrix A).det then
    PolarDecompositionCLM.qrSO A h else 1

/--
@isnad1 id=eq.1h2v.s8.26da9026f594 from=translated src=- shape=e69712e5 vocab=18d837d8
-/
theorem qrSOTotal_eq (A : EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin k))
    (h : 0 < (PolarDecompositionCLM.clmMatrix A).det) :
    qrSOTotal A = PolarDecompositionCLM.qrSO A h := dite_eq_left h

/-- **The factorization in total form.**
@isnad1 id=eq.1h2v.s9.5d7b0a092b68 from=translated src=- shape=0c434e2f vocab=404278fa
-/
theorem qr_factorization_total
    (A : EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin k))
    (h : 0 < (PolarDecompositionCLM.clmMatrix A).det) :
    A = (SOFrameGauge.toCLM (qrSOTotal A)).comp
      (PolarDecompositionCLM.qrUpper A) := by
  rw [qrSOTotal_eq A h]
  exact PolarDecompositionCLM.qr_factorization h

variable (Phi : EuclideanSpace ℝ (Fin N) →
  EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin k))
variable {V : Set (EuclideanSpace ℝ (Fin N))}

/-- **Local smoothness of the triangular factor.**
@isnad1 id=contdiff.4h5v.s10.edd58236f1e5 from=translated src=- shape=6596936e vocab=65265843
-/
theorem contDiffAt_qrUpper_of_contDiffOn (hV : IsOpen V)
    (hPhi : ContDiffOn ℝ ∞ Phi V)
    (hdet : ∀ x ∈ V, 0 < (PolarDecompositionCLM.clmMatrix (Phi x)).det)
    {c : EuclideanSpace ℝ (Fin N)} (hc : c ∈ V) :
    ContDiffAt ℝ ∞ (fun x => PolarDecompositionCLM.qrUpper (Phi x)) c := by
  obtain ⟨Psi, hPsi, hPsidet, hEq⟩ :=
    exists_global_of_contDiffOn Phi hV hPhi hdet hc
  have hglob : ContDiff ℝ ∞ fun x => PolarDecompositionCLM.qrUpper (Psi x) :=
    PolarDecompositionCLM.contDiff_qrUpper hPsi hPsidet
  refine hglob.contDiffAt.congr_of_eventuallyEq ?_
  filter_upwards [hEq] with x hx
  rw [hx]

/-- **Local smoothness of the special-orthogonal factor.**
@isnad1 id=contdiff.4h7v.s10.94ff722b936f from=translated src=- shape=dd630bc2 vocab=2cfd8f6a
-/
theorem contDiffAt_qrSOTotal_of_contDiffOn (hV : IsOpen V)
    (hPhi : ContDiffOn ℝ ∞ Phi V)
    (hdet : ∀ x ∈ V, 0 < (PolarDecompositionCLM.clmMatrix (Phi x)).det)
    {c : EuclideanSpace ℝ (Fin N)} (hc : c ∈ V) (i j : Fin k) :
    ContDiffAt ℝ ∞
      (fun x => ((qrSOTotal (Phi x) : SOGroup k) :
        Matrix (Fin k) (Fin k) ℝ) i j) c := by
  obtain ⟨Psi, hPsi, hPsidet, hEq⟩ :=
    exists_global_of_contDiffOn Phi hV hPhi hdet hc
  have hglob : ContDiff ℝ ∞ fun x =>
      ((PolarDecompositionCLM.qrSO (Psi x) (hPsidet x) : SOGroup k) :
        Matrix (Fin k) (Fin k) ℝ) i j :=
    PolarDecompositionCLM.contDiff_qrSOMatrix_apply hPsi hPsidet i j
  have hglob' : ContDiff ℝ ∞ fun x =>
      ((qrSOTotal (Psi x) : SOGroup k) : Matrix (Fin k) (Fin k) ℝ) i j := by
    have : (fun x => ((qrSOTotal (Psi x) : SOGroup k) :
          Matrix (Fin k) (Fin k) ℝ) i j)
        = fun x => ((PolarDecompositionCLM.qrSO (Psi x) (hPsidet x) :
          SOGroup k) : Matrix (Fin k) (Fin k) ℝ) i j := by
      funext x
      rw [qrSOTotal_eq (Psi x) (hPsidet x)]
    rw [this]
    exact hglob
  refine hglob'.contDiffAt.congr_of_eventuallyEq ?_
  filter_upwards [hEq] with x hx
  rw [hx]

end Factors

end TransitionQRLocalization
end Submission
