import Tengoku
import Tengoku.LeanEvalPiSuccSphereNMulequivZmodTwo.Submission.FiberSign

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The nonvanishing north/south label on bridge cobordisms

This module starts the labelled refinement of the forward Pontryagin--Thom bridge.
For the common-value middle cobordism the label is simply the last coordinate of the
space-time sphere map `nprepCob`.  Its norm-one property and the smallness of the
regular value prove that this label never vanishes on the cobordism fiber.
-/

noncomputable section

namespace Submission

open Set Function Metric Topology.Homotopy
open scoped Topology unitInterval RealInnerProductSpace ContDiff

variable {n : ℕ}

variable
  {p₁ p₂ : Ω^ (Fin (n + 1))
    (UnitSphere (EuclideanSpace ℝ (Fin (n + 1)))) (southPole n)}
  {a₁ : Approximation p₁} {a₂ : Approximation p₂}

/-- The common-value middle cobordism, enhanced with its canonical nonvanishing
north/south label.-/
def signedMiddleCob (c : CobApproximation a₁ a₂)
    (y : EuclideanSpace ℝ (Fin n)) (hy0 : y ≠ 0)
    (hreg : IsRegularValue (hMapCobE c) y) (hylt : ‖y‖ < 1) :
    SignedFramedLevelCobordism
      (bridgeFiberSignOf a₁ y hy0 (isRegularValue_left_of_cob c hreg) hylt)
      (bridgeFiberSignOf a₂ y hy0 (isRegularValue_right_of_cob c hreg) hylt) where
  cobordism := middleCob c y hy0 hreg
  source_eq := rfl
  target_eq := rfl
  toFun X := vertC (nprepCob c (WithLp.ofLp X))
  continuous := by
    exact (EuclideanSpace.proj (Fin.last n) (𝕜 := ℝ)).continuous.comp
      ((contDiff_nprepCob c).continuous.comp
        (EuclideanSpace.equiv (Fin (n + 1 + 1)) ℝ).continuous)
  nonzero := by
    intro X hX hzero
    have hfib : hMapCobE c X = y := sub_eq_zero.mp hX
    have hsplit := norm_sq_split (nprepCob c (WithLp.ofLp X))
    have hinit : initCLM n (nprepCob c (WithLp.ofLp X)) = y := hfib
    rw [norm_nprepCob c, hinit, hzero] at hsplit
    norm_num at hsplit
    have hy0' := norm_nonneg y
    nlinarith
  collar_zero := by
    intro x t ht
    change vertC (nprepCob c (WithLp.ofLp (spaceTime x t))) =
      vertC (nprep a₁ (WithLp.ofLp x))
    rw [nprepCob_left c (by rw [piTime_ofLp_spaceTime]; exact ht),
      piInit_ofLp_spaceTime]
  collar_one := by
    intro x t ht
    change vertC (nprepCob c (WithLp.ofLp (spaceTime x t))) =
      vertC (nprep a₂ (WithLp.ofLp x))
    rw [nprepCob_right c (by rw [piTime_ofLp_spaceTime]; exact ht),
      piInit_ofLp_spaceTime]

/-! ## The value-change pieces -/

/-- The moving horizontal target stays inside the open unit ball when the two end
values and the flat-Sard perturbation are small.-/
lemma valueTarget_norm_lt_one
    {y y' w : EuclideanSpace ℝ (Fin n)}
    (hy : ‖y‖ < 1 / 8) (hy' : ‖y'‖ < 1 / 8) (hw : ‖w‖ < 1 / 8)
    (v : EuclideanSpace ℝ (Fin (n + 1 + 1))) :
    ‖valueTarget y y' w v‖ < 1 := by
  let s := timeProfile (vertC v)
  let q := valueWeight v
  have hs0 : 0 ≤ s := Real.smoothTransition.nonneg _
  have hs1 : s ≤ 1 := Real.smoothTransition.le_one _
  have hq0 : 0 ≤ q := valueWeight_nonneg v
  have hq1 : q ≤ 1 := valueWeight_le_one v
  have hA : ‖(1 - s) • y‖ = (1 - s) * ‖y‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hs1)]
  have hB : ‖s • y'‖ = s * ‖y'‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hs0]
  have hC : ‖q • w‖ = q * ‖w‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hq0]
  change ‖(1 - s) • y + s • y' + q • w‖ < 1
  calc
    ‖(1 - s) • y + s • y' + q • w‖
        ≤ ‖(1 - s) • y + s • y'‖ + ‖q • w‖ := norm_add_le _ _
    _ ≤ (‖(1 - s) • y‖ + ‖s • y'‖) + ‖q • w‖ :=
      add_le_add (norm_add_le _ _) le_rfl
    _ = (1 - s) * ‖y‖ + s * ‖y'‖ + q * ‖w‖ := by rw [hA, hB, hC]
    _ < 1 := by nlinarith [norm_nonneg y, norm_nonneg y', norm_nonneg w]

/-- The fixed sphere representative supplies the sheet label on a value-change
cobordism.-/
theorem exists_signedValueCobordism (hn : 0 < n)
    {p : Ω^ (Fin (n + 1))
      (UnitSphere (EuclideanSpace ℝ (Fin (n + 1)))) (southPole n)}
    (a : Approximation p) (i : Fin n)
    {y y' : EuclideanSpace ℝ (Fin n)}
    (hypos : 0 < y i) (hy'pos : 0 < y' i)
    (hy8 : ‖y‖ < 1 / 8) (hy'8 : ‖y'‖ < 1 / 8)
    (hy0 : y ≠ 0) (hy'0 : y' ≠ 0)
    (h : IsRegularValue (bridgeHMapE a) y)
    (h' : IsRegularValue (bridgeHMapE a) y') :
    Nonempty
      (SignedFramedLevelCobordism
        (bridgeFiberSignOf a y hy0 h (hy8.trans (by norm_num)))
        (bridgeFiberSignOf a y' hy'0 h' (hy'8.trans (by norm_num)))) := by
  obtain ⟨C, w, hC₀, hC₁, hw, hCG⟩ :=
    exists_valueChange_cobordism_spec hn a i hypos hy'pos hy0 hy'0 h h'
  have hycoord : y i ≤ ‖y‖ := by
    have hi := PiLp.norm_apply_le y i
    rwa [Real.norm_eq_abs, abs_of_pos hypos] at hi
  have hw8 : ‖w‖ < 1 / 8 := by
    have hmin : min (y i) (y' i) ≤ y i := min_le_left _ _
    nlinarith
  refine ⟨{
    cobordism := C
    source_eq := hC₀
    target_eq := hC₁
    toFun := fun v => vertC (nprep a (WithLp.ofLp (initCLM (n + 1) v)))
    continuous := ?_
    nonzero := ?_
    collar_zero := ?_
    collar_one := ?_
  }⟩
  · exact (EuclideanSpace.proj (Fin.last n) (𝕜 := ℝ)).continuous.comp
      ((contDiff_nprep a).continuous.comp
        ((EuclideanSpace.equiv (Fin (n + 1)) ℝ).continuous.comp
          (initCLM (n + 1)).continuous))
  · intro v hv hzero
    have hv' : valueCobFun a y y' w v = 0 := by rwa [← hCG]
    have hfx0 : bridgeHMapE a (initCLM (n + 1) v) - valueTarget y y' w v = 0 := by
      simpa [valueCobFun, valueBase, valueTarget, sub_sub] using hv'
    have hfx : bridgeHMapE a (initCLM (n + 1) v) = valueTarget y y' w v :=
      sub_eq_zero.mp hfx0
    have hsplit := norm_sq_split
      (nprep a (WithLp.ofLp (initCLM (n + 1) v)))
    have hinit : initCLM n (nprep a (WithLp.ofLp (initCLM (n + 1) v))) =
        valueTarget y y' w v := hfx
    rw [norm_nprep a, hinit, hzero] at hsplit
    norm_num at hsplit
    have ht0 := norm_nonneg (valueTarget y y' w v)
    have ht1 := valueTarget_norm_lt_one hy8 hy'8 hw8 v
    nlinarith
  · intro x t ht
    change vertC (nprep a (WithLp.ofLp (initCLM (n + 1) (spaceTime x t)))) =
      vertC (nprep a (WithLp.ofLp x))
    rw [initCLM_spaceTime]
  · intro x t ht
    change vertC (nprep a (WithLp.ofLp (initCLM (n + 1) (spaceTime x t)))) =
      vertC (nprep a (WithLp.ofLp x))
    rw [initCLM_spaceTime]

/-! ## The labelled bridge theorem -/

/-- The forward Pontryagin--Thom bridge can be chosen with a continuous
nonvanishing north/south label.  In particular, its positive (northern) union of
components is tracked through both value slides and the common-value middle
cobordism.-/
theorem exists_signedBridgeCobordism (hn : 0 < n)
    {z : HomotopyGroup (Fin (n + 1))
      (UnitSphere (EuclideanSpace ℝ (Fin (n + 1)))) (southPole n)}
    (B₁ B₂ : BridgeData n z) :
    Nonempty (SignedFramedLevelCobordism B₁.fiberSign B₂.fiberSign) := by
  have hclass : (⟦B₁.approx.representative⟧ :
      HomotopyGroup (Fin (n + 1))
        (UnitSphere (EuclideanSpace ℝ (Fin (n + 1)))) (southPole n))
      = ⟦B₂.approx.representative⟧ :=
    B₁.class_eq.symm.trans B₂.class_eq
  have hpq : GenLoop.Homotopic B₁.approx.representative B₂.approx.representative :=
    Quotient.exact hclass
  obtain ⟨c⟩ := exists_cobApproximation hpq
  obtain ⟨y, hypos, hy8, hyaxis, hyreg⟩ :=
    exists_small_regular_value hn (contDiff_hMapCobE c)
  have hy0 : y ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hypos
    exact lt_irrefl 0 hypos
  have hy1 : ‖y‖ < 1 := hy8.trans (by norm_num)
  have hleft : IsRegularValue (bridgeHMapE B₁.approx) y :=
    isRegularValue_left_of_cob c hyreg
  have hright : IsRegularValue (bridgeHMapE B₂.approx) y :=
    isRegularValue_right_of_cob c hyreg
  obtain ⟨Cleft⟩ :=
    exists_signedValueCobordism hn B₁.approx ⟨0, hn⟩
      (B₁.axis_pos hn) hyaxis B₁.norm_y_lt hy8
      B₁.y_ne_zero hy0 B₁.regular_y hleft
  let Cmid := signedMiddleCob c y hy0 hyreg hy1
  obtain ⟨Cright⟩ :=
    exists_signedValueCobordism hn B₂.approx ⟨0, hn⟩
      hyaxis (B₂.axis_pos hn) hy8 B₂.norm_y_lt
      hy0 B₂.y_ne_zero hright B₂.regular_y
  exact ⟨SignedFramedLevelCobordism.trans
    (SignedFramedLevelCobordism.trans Cleft Cmid) Cright⟩

end Submission
