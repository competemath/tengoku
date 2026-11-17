import Tengoku.PaperCLean.PaperCV282.SaddleBranch
import Tengoku.PaperCLean.PaperCV282.ExponentialIntegral

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Existence and uniqueness of the two implicit cutoff scales

A positive scalar a treats both equations V=a D(H/V). The paper uses a=1
and a=2. The threshold is explicit in the fixed scalar and precedes H.
No prime-counting estimate or asymptotic expansion is assumed.
-/

namespace PaperC.V282.SaddleParameters

open Set Filter Topology SaddleBranch ExponentialIntegral

noncomputable section

def saddleCost (nu : ℝ) : ℝ :=
  nu * upperSaddleBranch nu - exponentialIntegral (upperSaddleBranch nu)

/--
@isnad1 id=eq.1h1v.s4.5fecdcbbd64b from=translated src=- shape=c7e89d76 vocab=dec54139
-/
theorem saddleCost_eq_param {nu : ℝ} (hnu : Real.exp 1 ≤ nu) :
    saddleCost nu = saddleCostParam (upperSaddleBranch nu) := by
  unfold saddleCost saddleCostParam
  rw [exp_upperSaddleBranch hnu]

/--
@isnad1 id=eq.1h1v.s4.7c8ddf20d3c7 from=translated src=- shape=13dc2a3c vocab=7cd168ce
-/
theorem saddleCost_saddleRatio {u : ℝ} (hu : 1 ≤ u) :
    saddleCost (saddleRatio u) = saddleCostParam u := by
  unfold saddleCost saddleCostParam
  rw [upperSaddleBranch_saddleRatio hu]
  rw [saddleRatio]
  field_simp [show u ≠ 0 by linarith]

/--
@isnad1 id=strictmo.0h0v.s4.b68fd655e4ae from=translated src=- shape=81225c50 vocab=0ef1b0b7
-/
theorem strictMonoOn_saddleCost :
    StrictMonoOn saddleCost (Ici (Real.exp 1)) := by
  intro nu hnu mu hmu hlt
  rw [saddleCost_eq_param hnu, saddleCost_eq_param hmu]
  exact strictMonoOn_saddleCostParam (upperSaddleBranch_spec hnu).1
    (upperSaddleBranch_spec hmu).1 (strictMonoOn_upperSaddleBranch hnu hmu hlt)

/--
@isnad1 id=tendsto.0h0v.s3.c7b6c171d817 from=translated src=- shape=41b74a9e vocab=d74e862a
-/
theorem tendsto_saddleCost_atTop : Tendsto saddleCost atTop atTop := by
  apply (tendsto_saddleCostParam_atTop.comp tendsto_upperSaddleBranch_atTop).congr'
  filter_upwards [eventually_ge_atTop (Real.exp 1)] with nu hnu
  exact (saddleCost_eq_param hnu).symm

def saddleParameterBase : ℝ := max 2 (3 - saddleCostParam 2)

/--
@isnad1 id=le.0h0v.s3.2404c7735991 from=translated src=- shape=ff3a10fc vocab=2959cfdb
-/
theorem saddleParameterBase_ge_two : 2 ≤ saddleParameterBase := le_max_left _ _

/--
@isnad1 id=le.0h0v.s3.a4f5e15e1cd2 from=translated src=- shape=a1bca669 vocab=dcb7d0f7
-/
theorem saddleCostParam_base_ge_one : 1 ≤ saddleCostParam saddleParameterBase := by
  have h := saddleCostParam_linear_lower saddleParameterBase_ge_two
  have hb : 3 - saddleCostParam 2 ≤ saddleParameterBase := le_max_right _ _
  linarith

def saddleHeight (a u : ℝ) : ℝ := a * saddleRatio u * saddleCostParam u

def saddleThreshold (a : ℝ) : ℝ := saddleHeight a saddleParameterBase

/--
@isnad1 id=lt.5h3v.s6.bfcb326e823b from=translated src=- shape=7606a476 vocab=95b832c5
-/
theorem saddleHeight_strict {a u v : ℝ} (ha : 0 < a)
    (hu : 1 ≤ u) (hv : 1 ≤ v) (hcost : 0 ≤ saddleCostParam u) (huv : u < v) :
    saddleHeight a u < saddleHeight a v := by
  have hf : 0 < saddleRatio u := div_pos (Real.exp_pos _) (by linarith)
  have hg := strictMonoOn_saddleCostParam hu hv huv
  have hgv : 0 ≤ saddleCostParam v := hcost.trans hg.le
  unfold saddleHeight
  calc
    a * saddleRatio u * saddleCostParam u < a * saddleRatio u * saddleCostParam v :=
      mul_lt_mul_of_pos_left hg (mul_pos ha hf)
    _ ≤ a * saddleRatio v * saddleCostParam v :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (strictMonoOn_saddleRatio hu hv huv).le ha.le) hgv

/--
@isnad1 id=strictmo.1h1v.s4.93c1e61b85db from=translated src=- shape=7fa19294 vocab=bd5c35e8
-/
theorem strictMonoOn_saddleHeight {a : ℝ} (ha : 0 < a) :
    StrictMonoOn (saddleHeight a) (Ici saddleParameterBase) := by
  intro u hu v hv huv
  have hb : 1 ≤ saddleParameterBase := by linarith [saddleParameterBase_ge_two]
  have hcost := strictMonoOn_saddleCostParam.monotoneOn hb (hb.trans hu) hu
  exact saddleHeight_strict ha (hb.trans hu) (hb.trans hv)
    ((by linarith [saddleCostParam_base_ge_one] : 0 ≤ saddleCostParam saddleParameterBase).trans hcost) huv

/--
@isnad1 id=continuo.0h1v.s4.4a3795d63a1b from=translated src=- shape=36486a8b vocab=78f16957
-/
theorem continuousOn_saddleHeight (a : ℝ) :
    ContinuousOn (saddleHeight a) (Ici saddleParameterBase) := by
  have hsub : Ici saddleParameterBase ⊆ Ici (1 : ℝ) := by
    intro u hu
    change 1 ≤ u
    linarith [show saddleParameterBase ≤ u from hu, saddleParameterBase_ge_two]
  exact (continuousOn_const.mul (continuousOn_saddleRatio.mono hsub)).mul
    (continuousOn_saddleCostParam.mono hsub)

/--
@isnad1 id=tendsto.1h1v.s4.f34b7adcc69a from=translated src=- shape=52e44ca1 vocab=1ab0f3b3
-/
theorem tendsto_saddleHeight_atTop {a : ℝ} (ha : 0 < a) :
    Tendsto (saddleHeight a) atTop atTop := by
  exact (tendsto_saddleRatio_atTop.const_mul_atTop ha).atTop_mul_atTop₀
    tendsto_saddleCostParam_atTop

/--
@isnad1 id=lt.1h1v.s4.87c9c680fe7b from=translated src=- shape=35bd48ee vocab=f3505140
-/
theorem saddleThreshold_pos {a : ℝ} (ha : 0 < a) : 0 < saddleThreshold a := by
  unfold saddleThreshold saddleHeight
  have hb : 0 < saddleParameterBase := by linarith [saddleParameterBase_ge_two]
  exact mul_pos (mul_pos ha (div_pos (Real.exp_pos _) hb))
    (by linarith [saddleCostParam_base_ge_one])

/--
@isnad1 id=existsun.2h2v.s5.8d1b8dedcdc3 from=translated src=- shape=72474630 vocab=ff8726c3
-/
theorem existsUnique_saddleHeight {a H : ℝ} (ha : 0 < a) (hH : saddleThreshold a ≤ H) :
    ∃! u : ℝ, saddleParameterBase ≤ u ∧ saddleHeight a u = H := by
  obtain ⟨u, hu, heq⟩ := intermediate_value_Ici (continuousOn_saddleHeight a)
    (tendsto_saddleHeight_atTop ha) hH
  refine ⟨u, ⟨hu, heq⟩, ?_⟩
  intro v hv
  exact (strictMonoOn_saddleHeight ha).injOn hv.1 hu (hv.2.trans heq.symm)

def saddleParameter (a H : ℝ) : ℝ :=
  if h : 0 < a ∧ saddleThreshold a ≤ H then
    Classical.choose (existsUnique_saddleHeight h.1 h.2)
  else saddleParameterBase

/--
@isnad1 id=and.2h2v.s5.89f256d4e007 from=translated src=- shape=d26b2c2b vocab=8016a9a1
-/
theorem saddleParameter_spec {a H : ℝ} (ha : 0 < a) (hH : saddleThreshold a ≤ H) :
    saddleParameterBase ≤ saddleParameter a H ∧ saddleHeight a (saddleParameter a H) = H := by
  rw [saddleParameter, dite_eq_left ⟨ha, hH⟩]
  exact (Classical.choose_spec (existsUnique_saddleHeight ha hH)).1

def saddleCutoff (a H : ℝ) : ℝ := a * saddleCostParam (saddleParameter a H)

/--
@isnad1 id=lt.2h2v.s5.83650cc86baa from=translated src=- shape=610280c5 vocab=eec60e01
-/
theorem saddleCutoff_pos {a H : ℝ} (ha : 0 < a) (hH : saddleThreshold a ≤ H) :
    0 < saddleCutoff a H := by
  have hu := (saddleParameter_spec ha hH).1
  have hb : 1 ≤ saddleParameterBase := by linarith [saddleParameterBase_ge_two]
  have hcost := strictMonoOn_saddleCostParam.monotoneOn hb (hb.trans hu) hu
  exact mul_pos ha (by linarith [saddleCostParam_base_ge_one])

/--
@isnad1 id=eq.2h2v.s5.40fc70875736 from=translated src=- shape=e6a0513f vocab=32d34144
-/
theorem div_saddleCutoff_eq_ratio {a H : ℝ} (ha : 0 < a) (hH : saddleThreshold a ≤ H) :
    H / saddleCutoff a H = saddleRatio (saddleParameter a H) := by
  apply (div_eq_iff (ne_of_gt (saddleCutoff_pos ha hH))).2
  calc
    H = saddleHeight a (saddleParameter a H) := (saddleParameter_spec ha hH).2.symm
    _ = _ := by unfold saddleHeight saddleCutoff; ring

/--
@isnad1 id=le.2h2v.s5.43f341dcf858 from=translated src=- shape=175eb43f vocab=9c772ace
-/
theorem saddleCutoff_domain {a H : ℝ} (ha : 0 < a) (hH : saddleThreshold a ≤ H) :
    Real.exp 1 ≤ H / saddleCutoff a H := by
  rw [div_saddleCutoff_eq_ratio ha hH]
  have hu : 1 ≤ saddleParameter a H :=
    (by linarith [saddleParameterBase_ge_two] : 1 ≤ saddleParameterBase).trans
      (saddleParameter_spec ha hH).1
  simpa only [saddleRatio, div_one] using strictMonoOn_saddleRatio.monotoneOn
    (show (1 : ℝ) ∈ Ici 1 by simp) hu hu

/--
@isnad1 id=eq.2h2v.s5.ac2eb6da5b1b from=translated src=- shape=0cb39d7a vocab=289dfb00
-/
theorem upperSaddleBranch_div_saddleCutoff {a H : ℝ} (ha : 0 < a)
    (hH : saddleThreshold a ≤ H) :
    upperSaddleBranch (H / saddleCutoff a H) = saddleParameter a H := by
  rw [div_saddleCutoff_eq_ratio ha hH]
  exact upperSaddleBranch_saddleRatio
    ((by linarith [saddleParameterBase_ge_two] : 1 ≤ saddleParameterBase).trans
      (saddleParameter_spec ha hH).1)

/--
@isnad1 id=eq.2h2v.s5.b1e190c24311 from=translated src=- shape=c1b6e61a vocab=7cc779ee
-/
theorem saddleCutoff_equation {a H : ℝ} (ha : 0 < a) (hH : saddleThreshold a ≤ H) :
    saddleCutoff a H = a * saddleCost (H / saddleCutoff a H) := by
  rw [saddleCost_eq_param (saddleCutoff_domain ha hH),
    upperSaddleBranch_div_saddleCutoff ha hH]
  rfl

/--
@isnad1 id=eq.5h3v.s6.130ade46b02c from=translated src=- shape=8beea1dc vocab=889f9c02
-/
theorem saddleCutoff_unique {a H V : ℝ} (ha : 0 < a) (hH : saddleThreshold a ≤ H)
    (hV : 0 < V) (hnu : Real.exp 1 ≤ H / V) (heq : V = a * saddleCost (H / V)) :
    V = saddleCutoff a H := by
  have hself := saddleCutoff_equation ha hH
  have hselfpos := saddleCutoff_pos ha hH
  have hselfnu := saddleCutoff_domain ha hH
  have hHpos : 0 < H := (saddleThreshold_pos ha).trans_le hH
  rcases lt_trichotomy V (saddleCutoff a H) with hlt | hequal | hgt
  · have hdiv : H / saddleCutoff a H < H / V := div_lt_div_of_pos_left hHpos hV hlt
    have hcost := strictMonoOn_saddleCost hselfnu hnu hdiv
    have hprod := mul_lt_mul_of_pos_left hcost ha
    linarith
  · exact hequal
  · have hdiv : H / V < H / saddleCutoff a H :=
      div_lt_div_of_pos_left hHpos hselfpos hgt
    have hcost := strictMonoOn_saddleCost hnu hselfnu hdiv
    have hprod := mul_lt_mul_of_pos_left hcost ha
    linarith

/--
@isnad1 id=existsun.2h2v.s6.afbdac33769b from=translated src=- shape=3f7ae943 vocab=ddd6b570
-/
theorem existsUnique_saddleCutoff {a H : ℝ} (ha : 0 < a)
    (hH : saddleThreshold a ≤ H) :
    ∃! V : ℝ, 0 < V ∧ Real.exp 1 ≤ H / V ∧ V = a * saddleCost (H / V) := by
  exact ⟨saddleCutoff a H,
    ⟨saddleCutoff_pos ha hH, saddleCutoff_domain ha hH, saddleCutoff_equation ha hH⟩,
    fun V hV => saddleCutoff_unique ha hH hV.1 hV.2.1 hV.2.2⟩

/--
@isnad1 id=ex.0h0v.s7.09a64fe4b96a from=translated src=- shape=27effefb vocab=4c71bd2d
-/
theorem hard_and_soft_saddles_exist :
    ∃ Hzero : ℝ, ∀ H ≥ Hzero,
      (∃! V : ℝ, 0 < V ∧ Real.exp 1 ≤ H / V ∧ V = saddleCost (H / V)) ∧
      (∃! V : ℝ, 0 < V ∧ Real.exp 1 ≤ H / V ∧ V = 2 * saddleCost (H / V)) := by
  refine ⟨max (saddleThreshold 1) (saddleThreshold 2), ?_⟩
  intro H hH
  constructor
  · simpa only [one_mul] using existsUnique_saddleCutoff (by norm_num : (0 : ℝ) < 1)
      ((le_max_left _ _).trans hH)
  · exact existsUnique_saddleCutoff (by norm_num : (0 : ℝ) < 2)
      ((le_max_right _ _).trans hH)

end

end PaperC.V282.SaddleParameters
