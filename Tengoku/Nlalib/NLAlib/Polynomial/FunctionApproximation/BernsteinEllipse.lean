import Tengoku.Seed.Analysis.Complex.CauchyIntegral
import Tengoku.Seed.Analysis.Calculus.InverseFunctionTheorem.Deriv

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Bernstein ellipses and the Joukowski transform

The filled Bernstein ellipse is the image of `1 ≤ |w| ≤ ρ` under
`J(w)=(w+w⁻¹)/2`. Interior points with `1<|w|<ρ` are transported by a local inverse,
so the original holomorphic-ellipse hypothesis yields the annular analytic interface.
This is scalar infrastructure for `chebyshev-coeff-analytic-decay`.
-/

noncomputable section

open Complex Set Metric Filter
open scoped Topology

namespace NLAlib

/-- The classical Joukowski transform `J(w)=(w+w⁻¹)/2`.
Source: Trefethen, ATAP, Chapter 8; used by `chebyshev-coeff-analytic-decay`.-/
def joukowski (w : ℂ) : ℂ := (w + w⁻¹) / 2

/-- The filled Bernstein ellipse is the Joukowski image of the closed annulus
`1≤|w|≤ρ`. For `ρ>1` this has semiaxes `(ρ+ρ⁻¹)/2` and `(ρ-ρ⁻¹)/2`.
Source: Trefethen, ATAP, Chapter 8; used by `bernstein-ellipse-approx` and
`chebyshev-coeff-analytic-decay`.-/
def filledBernsteinEllipse (ρ : ℝ) : Set ℂ :=
  joukowski '' {w : ℂ | 1 ≤ ‖w‖ ∧ ‖w‖ ≤ ρ}

/-- The open Bernstein ellipse is the Joukowski image of the open annulus
`ρ⁻¹<|w|<ρ`, including the real segment. Its use imposes no boundary extension assumption.
Source: Trefethen, ATAP, Chapter 8 (`chebyshev-coeff-analytic-decay`, definition).-/
def openBernsteinEllipse (ρ : ℝ) : Set ℂ :=
  joukowski '' {w : ℂ | ρ⁻¹ < ‖w‖ ∧ ‖w‖ < ρ}

/-- Every strictly smaller closed Bernstein ellipse lies inside the larger open ellipse.
Source: Trefethen, ATAP, Chapter 8, radius-limit proof of Theorem 8.1
(`chebyshev-coeff-analytic-decay`, helper).
@isnad1 id=le.2h2v.s4.8107e4f24ed9 from=translated src=- shape=1922b641 vocab=7d88020d
-/
theorem filledBernsteinEllipse_subset_openBernsteinEllipse {r ρ : ℝ}
    (hρ : 1 < ρ) (hrρ : r < ρ) :
    filledBernsteinEllipse r ⊆ openBernsteinEllipse ρ := by
  rintro z ⟨w, hw, rfl⟩
  refine ⟨w, ⟨?_, hw.2.trans_lt hrρ⟩, rfl⟩
  exact (inv_lt_one₀ (zero_lt_one.trans hρ)).mpr hρ |>.trans_le hw.1

/-- The Joukowski transform is invariant under complex inversion.
Source: Trefethen, ATAP, Chapter 8 (`chebyshev-coeff-analytic-decay`, helper).
@isnad1 id=eq.0h1v.s3.d76ba89ca8c6 from=translated src=- shape=cd419dad vocab=4140a68a
-/
theorem joukowski_inv (w : ℂ) : joukowski w⁻¹ = joukowski w := by
  simp only [joukowski, inv_inv, add_comm]

/-- On the unit circle the Joukowski transform equals the real part.
Source: Trefethen, ATAP, Chapter 8 (`chebyshev-coeff-analytic-decay`, helper).
@isnad1 id=eq.1h1v.s4.7a5bd2559dfc from=translated src=- shape=52be62d1 vocab=ae4f36a2
-/
theorem joukowski_eq_re_of_norm_eq_one {w : ℂ} (hw : ‖w‖ = 1) :
    joukowski w = (w.re : ℂ) := by
  rw [joukowski, Complex.inv_eq_conj hw, Complex.add_conj]
  push_cast
  ring

/-- The real interval `[-1,1]` is contained in every filled Bernstein ellipse with `ρ≥1`.
Source: Trefethen, ATAP, Chapter 8 (`bernstein-ellipse-approx`, helper).
@isnad1 id=mem.2h2v.s5.80000c471107 from=translated src=- shape=89e87f48 vocab=36058c9d
-/
theorem ofReal_mem_filledBernsteinEllipse {ρ x : ℝ} (hρ : 1 ≤ ρ)
    (hx : x ∈ Icc (-1 : ℝ) 1) : (x : ℂ) ∈ filledBernsteinEllipse ρ := by
  let w : ℂ := ⟨x, Real.sqrt (1 - x ^ 2)⟩
  have hx2 : x ^ 2 ≤ 1 := (sq_le_one_iff_abs_le_one x).mpr (abs_le.mpr hx)
  have hnorm : ‖w‖ = 1 := by
    have hs := Real.sq_sqrt (sub_nonneg.mpr hx2)
    have hn : ‖w‖ ^ 2 = 1 := by
      rw [← Complex.normSq_eq_norm_sq]
      simp only [Complex.normSq_apply, w]
      nlinarith
    nlinarith [norm_nonneg w]
  refine ⟨w, ?_, joukowski_eq_re_of_norm_eq_one hnorm⟩
  change 1 ≤ ‖w‖ ∧ ‖w‖ ≤ ρ
  rw [hnorm]
  exact ⟨le_rfl, hρ⟩

/-- A closed-annulus point maps into the filled Bernstein ellipse by definition.
Source: Trefethen, ATAP, Chapter 8 (`chebyshev-coeff-analytic-decay`, helper).
@isnad1 id=mem.1h2v.s5.8437f75cbccf from=translated src=- shape=4b96e05e vocab=259dcfcc
-/
theorem joukowski_mem_filledBernsteinEllipse {ρ : ℝ} {w : ℂ}
    (hw : 1 ≤ ‖w‖ ∧ ‖w‖ ≤ ρ) : joukowski w ∈ filledBernsteinEllipse ρ :=
  ⟨w, hw, rfl⟩

/-- The Joukowski transform has its usual strict complex derivative away from zero.
Source: Trefethen, ATAP, Chapter 8 (`chebyshev-coeff-analytic-decay`, helper).
@isnad1 id=hasstric.1h1v.s6.aaf1d38d3ac9 from=translated src=- shape=f1a82273 vocab=e5dc7ee8
-/
theorem hasStrictDerivAt_joukowski {w : ℂ} (hw : w ≠ 0) :
    HasStrictDerivAt joukowski ((1 - (w ^ 2)⁻¹) / 2) w := by
  have h := ((hasStrictDerivAt_id w).add (hasStrictDerivAt_inv hw)).const_smul ((2 : ℂ)⁻¹)
  convert h using 1 <;> try rfl
  · funext z
    simp only [joukowski, Pi.smul_apply, smul_eq_mul, Pi.add_apply, id_eq]
    ring
  · simp only [smul_eq_mul]
    ring

/-- Outside the unit disk, the Joukowski derivative does not vanish.
Source: Trefethen, ATAP, Chapter 8 (`chebyshev-coeff-analytic-decay`, helper).
@isnad1 id=ne.1h1v.s6.619e24899cb8 from=translated src=- shape=3bf0e215 vocab=8280d452
-/
theorem joukowski_deriv_ne_zero {w : ℂ} (hw : 1 < ‖w‖) :
    (1 - (w ^ 2)⁻¹) / 2 ≠ 0 := by
  have hw0 : w ≠ 0 := norm_ne_zero_iff.mp (ne_of_gt (zero_lt_one.trans hw))
  have hw2 : w ^ 2 ≠ 1 := by
    intro h
    have hn := congrArg norm h
    simp only [norm_pow, norm_one] at hn
    nlinarith
  apply div_ne_zero _ (by norm_num)
  intro h
  have hinv : (w ^ 2)⁻¹ = 1 := by linear_combination -h
  have hp := congrArg (fun z : ℂ => z * w ^ 2) hinv
  rw [inv_mul_cancel₀ (pow_ne_zero 2 hw0), one_mul] at hp
  exact hw2 hp.symm

/-- A Joukowski image with `1<|w|<ρ` lies in the interior of the filled Bernstein ellipse.
The local inverse theorem supplies the neighborhood inclusion rather than an assumed
analyticity-domain certificate.
Source: Trefethen, ATAP, Chapter 8 (`chebyshev-coeff-analytic-decay`, helper).
@isnad1 id=mem.1h2v.s5.eb46291a6fec from=translated src=- shape=a6861703 vocab=34f96eb8
-/
theorem joukowski_mem_interior_filledBernsteinEllipse {ρ : ℝ} {w : ℂ}
    (hw : 1 < ‖w‖ ∧ ‖w‖ < ρ) : joukowski w ∈ interior (filledBernsteinEllipse ρ) := by
  let S := {z : ℂ | 1 < ‖z‖ ∧ ‖z‖ < ρ}
  have hS : IsOpen S := (isOpen_lt continuous_const continuous_norm).inter
    (isOpen_lt continuous_norm continuous_const)
  have hmem : S ∈ 𝓝 w := hS.mem_nhds hw
  have hImage : joukowski '' S ∈ Filter.map joukowski (𝓝 w) := Filter.image_mem_map hmem
  have hw0 : w ≠ 0 := norm_ne_zero_iff.mp (ne_of_gt (zero_lt_one.trans hw.1))
  rw [(hasStrictDerivAt_joukowski hw0).map_nhds_eq (joukowski_deriv_ne_zero hw.1)] at hImage
  apply mem_interior_iff_mem_nhds.mpr
  refine Filter.mem_of_superset hImage ?_
  rintro z ⟨u, hu, rfl⟩
  exact joukowski_mem_filledBernsteinEllipse ⟨hu.1.le, hu.2.le⟩

/-- The Joukowski transform is continuous on the closed annulus of inner radius one.
Source: Trefethen, ATAP, Chapter 8 (`chebyshev-coeff-analytic-decay`, helper).
@isnad1 id=continuo.0h1v.s6.81f95aa8dbfc from=translated src=- shape=1c1b0328 vocab=62be3f06
-/
theorem continuousOn_joukowski_closed_annulus (ρ : ℝ) :
    ContinuousOn joukowski (closedBall (0 : ℂ) ρ \ ball 0 1) := by
  apply ContinuousOn.div_const
  apply continuousOn_id.add
  apply continuousOn_id.inv₀
  intro w hw hzero
  change w = 0 at hzero
  have h := hw.2
  norm_num [hzero] at h

/-- A function holomorphic inside and continuous on the filled Bernstein ellipse pulls back
to a continuous function on the closed Joukowski annulus.
Source: Trefethen, ATAP, Chapter 8 (`chebyshev-coeff-analytic-decay`, helper).
@isnad1 id=continuo.1h2v.s6.b1d0976f10bb from=translated src=- shape=4a213bf9 vocab=91255979
-/
theorem continuousOn_comp_joukowski_closed_annulus {F : ℂ → ℂ} {ρ : ℝ}
    (hF : ContinuousOn F (filledBernsteinEllipse ρ)) :
    ContinuousOn (F ∘ joukowski) (closedBall (0 : ℂ) ρ \ ball 0 1) := by
  refine hF.comp (continuousOn_joukowski_closed_annulus ρ) ?_
  intro w hw
  apply joukowski_mem_filledBernsteinEllipse
  simp only [Set.mem_sdiff, mem_closedBall, mem_ball, dist_zero_right, not_lt] at hw
  exact ⟨hw.2, hw.1⟩

/-- The holomorphic-ellipse hypothesis yields complex differentiability at all
interior points of the outer Joukowski annulus.
Source: Trefethen, ATAP, Chapter 8 (`chebyshev-coeff-analytic-decay`, helper).
@isnad1 id=differen.2h3v.s7.0c34ab8fc8c7 from=translated src=- shape=a9a3acb5 vocab=5008781b
-/
theorem differentiableAt_comp_joukowski_open_annulus {F : ℂ → ℂ} {ρ : ℝ}
    (hF : DifferentiableOn ℂ F (interior (filledBernsteinEllipse ρ)))
    {w : ℂ} (hw : w ∈ ball (0 : ℂ) ρ \ closedBall 0 1) :
    DifferentiableAt ℂ (F ∘ joukowski) w := by
  have hw' : 1 < ‖w‖ ∧ ‖w‖ < ρ := by
    simpa only [Set.mem_sdiff, mem_ball, mem_closedBall, dist_zero_right, not_le, and_comm] using hw
  have hmem := joukowski_mem_interior_filledBernsteinEllipse hw'
  have hdiff := (hF _ hmem).differentiableAt (isOpen_interior.mem_nhds hmem)
  have hw0 : w ≠ 0 := norm_ne_zero_iff.mp (ne_of_gt (zero_lt_one.trans hw'.1))
  exact hdiff.comp w (hasStrictDerivAt_joukowski hw0).hasDerivAt.differentiableAt

end NLAlib
