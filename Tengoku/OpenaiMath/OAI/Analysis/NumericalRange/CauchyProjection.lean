import Tengoku.OpenaiMath.OAI.Analysis.NumericalRange.FourierResolution

namespace OAI

noncomputable section

universe u_44

open Set Filter Metric Complex
open scoped Topology ComplexConjugate
open MeasureTheory Set Complex
open scoped Topology Real
open MeasureTheory Set Metric Complex Filter
open scoped Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal InnerProductSpace
open scoped ComplexConjugate InnerProductSpace

namespace CompleteCrouzeix

section
open MeasureTheory Set Complex
open scoped Topology InnerProductSpace ComplexConjugate
local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

def circleTest (f : C(UnitAddCircle,ℂ)) : CircleL2 →L[ℂ] ℂ :=
  innerSL ℂ (ContinuousMap.toLp 2 AddCircle.haarAddCircle ℂ (star f))

lemma circleTest_apply (f : C(UnitAddCircle,ℂ)) (u : CircleL2) :
    circleTest f u = ∫ t, f t * u t ∂AddCircle.haarAddCircle := by
  change inner ℂ (ContinuousMap.toLp 2 AddCircle.haarAddCircle ℂ (star f)) u = _
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [ContinuousMap.coeFn_toLp (μ := AddCircle.haarAddCircle)
    (p := 2) (𝕜 := ℂ) (star f)] with t ht
  rw [ht]
  simp [RCLike.inner_apply, mul_comm]

lemma circleTest_add (f g : C(UnitAddCircle,ℂ)) :
    circleTest (f+g) = circleTest f+circleTest g := by
  ext u
  simp only [circleTest, star_add, map_add, add_apply]

lemma circleTest_fourier (f : C(UnitAddCircle,ℂ)) (n : ℤ) :
    circleTest f (fourierLp 2 n) = ∫ t, f t * fourier n t ∂AddCircle.haarAddCircle := by
  rw [circleTest_apply]
  apply integral_congr_ae
  filter_upwards [coeFn_fourierLp 2 n] with t ht
  rw [ht]

lemma circleCLM_ext {E : Type u_44} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {L J : CircleL2 →L[ℂ] E} (h : ∀ n : ℤ, L (fourierLp 2 n) = J (fourierLp 2 n)) : L = J := by
  apply ContinuousLinearMap.ext_on (s := Set.range (fourierLp (T := 1) 2))
  · change ∀ x, x ∈ (Submodule.span ℂ (Set.range (fourierLp (T := 1) 2))).topologicalClosure
    rw [span_fourierLp_closure_eq_top (by norm_num : (2 : ENNReal) ≠ ∞)]
    intro x; trivial
  · rintro _ ⟨n,rfl⟩; exact h n

lemma circleTest_const_positive :
    (circleTest (1 : C(UnitAddCircle,ℂ))).comp (scalarFourier.proj 1) = 0 := by
  apply circleCLM_ext
  intro n
  simp only [ContinuousLinearMap.comp_apply, scalarFourier_fourier,
    zero_apply]
  split_ifs with hn
  · have hn' : 0 < n := by
      by_contra hnonpos
      by_cases hzero : n = 0
      · simp [frequencyPart, hzero] at hn
      · simp [frequencyPart, hzero, hnonpos] at hn
    rw [circleTest_fourier]
    simpa using integral_fourier_nonzero n (ne_of_gt hn')
  · exact map_zero _

namespace AnalyticBidiskKernel
variable (K : AnalyticBidiskKernel)

end AnalyticBidiskKernel
end

open MeasureTheory Set Complex
open scoped Topology
local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

def analyticCircleTrace (f : ℂ → ℂ) (hf : AnalyticOnNhd ℂ f (Metric.closedBall 0 1)) :
    C(UnitAddCircle,ℂ) :=
  ⟨fun t => f (t.toCircle : ℂ), hf.continuousOn.comp_continuous
    (continuous_subtype_val.comp AddCircle.continuous_toCircle)
    (fun t => Metric.sphere_subset_closedBall t.toCircle.property)⟩

end CompleteCrouzeix

open Set Metric Filter Complex
open scoped Topology
namespace CompleteCrouzeix

section

section

theorem analytic_circle_gluing {U : Set ℂ} (hU : IsOpen U)
    (hTU : sphere 0 1 ⊆ U) {f g : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f (ball 0 1)) (hg : AnalyticOnNhd ℂ g U)
    (he : ∀ z ∈ U ∩ ball 0 1, f z = g z) :
    ∃ q : ℂ → ℂ, AnalyticOnNhd ℂ q (closedBall 0 1) ∧ EqOn q g (sphere 0 1) := by
  classical
  let q := fun z => if z ∈ ball (0 : ℂ) 1 then f z else g z
  refine ⟨q,?_,?_⟩
  · intro z hz
    by_cases hi : z ∈ ball (0 : ℂ) 1
    · apply (hf z hi).congr
      filter_upwards [isOpen_ball.mem_nhds hi] with w hw
      simp only [q, ite_eq_left hw]
    · have hs : z ∈ sphere (0 : ℂ) 1 := by
        change dist z 0 = 1
        exact le_antisymm hz (le_of_not_gt hi)
      apply (hg z (hTU hs)).congr
      filter_upwards [hU.mem_nhds (hTU hs)] with w hw
      dsimp [q]
      split_ifs with hwi
      · exact (he w ⟨hw,hwi⟩).symm
      · rfl
  · intro z hz
    have hi : z ∉ ball (0 : ℂ) 1 := by
      intro hh
      exact ne_of_lt hh hz
    simp only [q, ite_eq_right hi]

open Set Metric Complex MeasureTheory
open scoped Topology
local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

end

open MeasureTheory Set Metric Complex
open scoped Topology
local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

lemma canonicalCircleCauchy_analytic {u : UnitAddCircle → ℂ} (hu : Continuous u) :
    AnalyticOnNhd ℂ (fun w => ∫ t : UnitAddCircle,
      u t*((t.toCircle : ℂ)/((t.toCircle : ℂ)-w)) ∂AddCircle.haarAddCircle) (ball 0 1) := by
  have h : AnalyticOnNhd ℂ (physicalCauchy id u) (ball 0 1) :=
    physicalCauchy_analytic analyticOnNhd_id hu isOpen_ball (by
      intro z hz t he
      have ht := t.toCircle.property
      change (t.toCircle : ℂ) = z at he
      rw [he] at ht
      exact ne_of_lt hz ht)
  convert h using 1
  funext w
  simp [physicalCauchy]

end

theorem reciprocalCorrection_continuousOn {a : ℂ} {h : ℂ → ℂ} {U : Set ℂ}
    (hU : IsOpen U) (hh : AnalyticOnNhd ℂ h U)
    (hne : ∀ x ∈ U, ∀ y ∈ U, exteriorDividedDifference a h x y ≠ 0) :
    ContinuousOn (Function.uncurry (reciprocalCorrection a h)) (U ×ˢ U) := by
  apply continuousOn_of_analytic_left_offDiagonal hU
    (fun y hy => reciprocalCorrection_analytic_left hU hh hne hy)
  let V := {p : ℂ × ℂ | p.1 ∈ U ∧ p.2 ∈ U ∧ p.1 ≠ p.2}
  let H := fun z : ℂ => z*h z
  have hH : AnalyticOnNhd ℂ H U := analyticOnNhd_id.mul hh
  have ch1 : ContinuousOn (fun p : ℂ × ℂ => h p.1) V :=
    hh.continuousOn.comp continuousOn_fst (fun p hp => hp.1)
  have ch2 : ContinuousOn (fun p : ℂ × ℂ => h p.2) V :=
    hh.continuousOn.comp continuousOn_snd (fun p hp => hp.2.1)
  have cH1 : ContinuousOn (fun p : ℂ × ℂ => H p.1) V :=
    hH.continuousOn.comp continuousOn_fst (fun p hp => hp.1)
  have cH2 : ContinuousOn (fun p : ℂ × ℂ => H p.2) V :=
    hH.continuousOn.comp continuousOn_snd (fun p hp => hp.2.1)
  have cdH2 : ContinuousOn (fun p : ℂ × ℂ => deriv H p.2) V :=
    hH.deriv.continuousOn.comp continuousOn_snd (fun p hp => hp.2.1)
  have cz : ∀ p ∈ V, p.1-p.2 ≠ 0 := fun p hp => sub_ne_zero.mpr hp.2.2
  have cq : ContinuousOn (fun p : ℂ × ℂ => (h p.1-h p.2)/(p.1-p.2)) V :=
    (ch1.sub ch2).div (continuousOn_fst.sub continuousOn_snd) cz
  have cr : ContinuousOn (fun p : ℂ × ℂ =>
      ((H p.1-H p.2)/(p.1-p.2)-deriv H p.2)/(p.1-p.2)) V :=
    (((cH1.sub cH2).div (continuousOn_fst.sub continuousOn_snd) cz).sub cdH2).div
      (continuousOn_fst.sub continuousOn_snd) cz
  have cqeq (p : ℂ × ℂ) (hp : p ∈ V) :
      exteriorDividedDifference a h p.1 p.2 =
        a-p.1*p.2*((h p.1-h p.2)/(p.1-p.2)) := by
    rw [exteriorDividedDifference, dslope_comm h p.1 p.2,
      dslope_of_ne _ hp.2.2, slope_def_field]
  have cc : ContinuousOn (fun p : ℂ × ℂ =>
      p.1*p.2*(((H p.1-H p.2)/(p.1-p.2)-deriv H p.2)/(p.1-p.2)) /
        (a-p.1*p.2*((h p.1-h p.2)/(p.1-p.2)))) V :=
    ((continuousOn_fst.mul continuousOn_snd).mul cr).div
      (continuousOn_const.sub ((continuousOn_fst.mul continuousOn_snd).mul cq))
      (fun p hp => (cqeq p hp) ▸ hne p.1 hp.1 p.2 hp.2.1)
  apply cc.congr
  intro p hp
  change reciprocalCorrection a h p.1 p.2 = _
  rw [reciprocalCorrection, cqeq p hp, dslope_of_ne _ hp.2.2, slope_def_field,
    dslope_of_ne _ hp.2.2, slope_def_field, dslope_same]

end CompleteCrouzeix

end

end OAI
