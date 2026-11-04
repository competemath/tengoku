import Tengoku.Pi2Lean.Row12.BetaContourAnalytic
import Tengoku.Pi2Lean.Row12.CircleParametric
import Tengoku.Pi2Lean.Row12.OuterPrimitive
import Tengoku.Seed.Analysis.Calculus.FDeriv.Analytic
import Tengoku.Seed.Topology.UniformSpace.HeineCantor

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms Row12.dualState_entry_analyticAt` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Row12.circleIntegral_analyticAt_of_joint_analyticOnTube` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Row12.escapePoint_sq` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Row12.escapePoint_mem` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Row12.escape_path_x` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Row12.escape_complex_x` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Row12.escape_radius_domain` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Row12.escape_circle_regular` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Row12.escapeBetaDenominator_continuous` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Row12.escape_B_continuousAt` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Row12.escape_regular_tube` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Row12.escapeClearedBetaIntegrand_joint_analyticAt` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Row12.escapeClearedBetaCircle_analyticAt` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Row12.escape_cleared_beta_entry_eq` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Row12.escape_cleared_beta_integrand_eq` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Row12.escape_cleared_beta_circle_eq` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Row12.escape_cleared_outer_basis_eq` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Row12.escape_cleared_outer_row_eq` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Row12.escape_cleared_outer_flux_eq` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Row12.escape_cleared_outer_basis_analyticAt` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Row12.escape_cleared_outer_row_analyticAt` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Row12.sixthNormalState_entry_analyticAt` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Row12.escape_cleared_outer_flux_analyticAt` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Row12.escapeClearedTotal_analyticAt` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Row12.escapeClearedTotal_eq` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Row12.escapeClearedTotal_clears_near` (it only prints; the queue checks the axioms of every declaration). -/

open MeasureTheory Set Metric Complex Filter
open scoped Topology

namespace Row12

attribute [local fun_prop] analyticAt_fst analyticAt_snd

/-- A joint analytic tube gives the actual analytic parameter circle integral.
@isnad1 id=analytic.3h5v.s7.d1e6fdf437a6 from=translated src=- shape=e1c5a5cc vocab=d3a1a0fc
-/
theorem circleIntegral_analyticAt_of_joint_analyticOnTube
    (F : ℂ → ℂ → ℂ) (a c : ℂ) (r ε : ℝ) (hr : 0 ≤ r) (hε : 0 < ε)
    (hF : ∀ p ∈ closedBall a ε ×ˢ sphere c r,
      AnalyticAt ℂ (fun q : ℂ × ℂ => F q.1 q.2) p) :
    AnalyticAt ℂ (fun z => ∮ s in C(c,r), F z s) a := by
  let F' : ℂ → ℂ → ℂ := fun z s =>
    (fderiv ℂ (fun p : ℂ × ℂ => F p.1 p.2) (z,s)) (1,0)
  have hd : DifferentiableOn ℂ (fun z => ∮ s in C(c,r), F z s) (ball a (ε/2)) := by
    intro z hz
    have hsub : closedBall z (ε/2) ⊆ closedBall a ε := by
      intro w hw
      apply mem_closedBall.mpr
      have hwz := mem_closedBall.mp hw
      have hza := mem_ball.mp hz
      exact le_of_lt ((dist_triangle w z a).trans_lt (by linarith))
    have hFc : ContinuousOn (fun p : ℂ × ℂ => F p.1 p.2)
        (closedBall z (ε/2) ×ˢ sphere c r) := by
      intro p hp
      exact (hF p ⟨hsub hp.1,hp.2⟩).continuousAt.continuousWithinAt
    have hF'c : ContinuousOn (fun p : ℂ × ℂ => F' p.1 p.2)
        (closedBall z (ε/2) ×ˢ sphere c r) := by
      intro p hp
      exact ((hF p ⟨hsub hp.1,hp.2⟩).fderiv.continuousAt.clm_apply
        continuousAt_const).continuousWithinAt
    have hFD : ∀ w ∈ closedBall z (ε/2), ∀ s ∈ sphere c r,
        HasDerivAt (fun q => F q s) (F' w s) w := by
      intro w hw s hs
      have hh := ((hF (w,s) ⟨hsub hw,hs⟩).differentiableAt.hasFDerivAt.comp
        w (hasFDerivAt_prodMk_left w s)).hasDerivAt
      convert! hh using 1
    exact (circleParametric_hasDerivAt F F' z c r (ε/2) hr
      (by positivity) hFc hF'c hFD).differentiableAt.differentiableWithinAt
  exact hd.analyticAt (isOpen_ball.mem_nhds (mem_ball_self (by positivity)))

noncomputable def escapePoint : ℝ := 7/(3*Real.sqrt 11)
noncomputable def escapeRadius : ℝ :=
  Real.sqrt (scalarLambda (scalarPathX escapePoint))
noncomputable def escapeFactor (U : ℂ) : ℂ := 99*betaFrameX U-50

/-- The denominator after removing exactly the squared escape factor.-/
noncomputable def escapeBetaDenominator (U s : ℂ) : ℂ :=
  (betaFrameX U)^4*betaFrameM (betaFrameX U)*betaFrameF (betaFrameX U) s

noncomputable def escapeClearedBetaMatrix (U s : ℂ) : Matrix (Fin 3) (Fin 3) ℂ :=
  fun i j => U*(2*betaFrameLP (betaFrameX U) i j*(s-betaFrameMid (betaFrameX U))+
    2*betaFrameEll (betaFrameX U)*betaFrameM (betaFrameX U)*
      betaFrameRP (betaFrameX U) i j)/escapeBetaDenominator U s

noncomputable def escapeClearedBetaIntegrand (U s : ℂ) : ℂ :=
  betaPair (escapeClearedBetaMatrix U s) (dualState s) (dualState (betaFrameB U s))

noncomputable def escapeClearedBetaCircle (U : ℂ) (r : ℝ) : ℂ :=
  (2*Real.pi*I:ℂ)⁻¹*(∮ s in C(0,r), escapeClearedBetaIntegrand U s)

/-- The exact Fin15 basis retains both escape rows and every polynomial row.-/
noncomputable def escapeClearedOuterBasis (x : ℂ) : Fin 15 → ℂ :=
  let E := 99*x-50
  ![E^2/x,E^2/x^2,E^2/x^3,E^2/x^4,E,1,E^2,E^2*x,
    E^2*x^2,E^2*x^3,E^2*x^4,E^2*x^5,E^2*x^6,E^2*x^7,E^2*x^8]

noncomputable def escapeClearedOuterRow (x : ℂ) : Fin 6 → ℂ :=
  fun j => ∑ k : Fin 15, outerPrimitiveCoefficients k j*escapeClearedOuterBasis x k

noncomputable def escapeClearedOuterFlux (U : ℂ) : ℂ :=
  U*dotProduct (escapeClearedOuterRow (1-U^2))
    (sixthNormalState (outerPrimitiveLambda (1-U^2)))

noncomputable def escapeClearedTotal (U : ℂ) : ℂ :=
  escapeClearedBetaCircle U escapeRadius+escapeClearedOuterFlux U

/--
@isnad1 id=eq.0h0v.s5.131e3e4a51d1 from=translated src=- shape=bce64568 vocab=fed0670f
-/
theorem escapePoint_sq : escapePoint^2=(49/99:ℝ) := by
  have hs : (Real.sqrt (11:ℝ))^2=11 := Real.sq_sqrt (by norm_num)
  unfold escapePoint
  rw [div_pow,mul_pow,hs]
  norm_num

/--
@isnad1 id=and.0h0v.s4.b697d9d6654f from=translated src=- shape=149fafef vocab=f30e41c0
-/
theorem escapePoint_mem : 0<escapePoint ∧ escapePoint<1 := by
  have hp : 0<escapePoint := div_pos (by norm_num)
    (mul_pos (by norm_num) (Real.sqrt_pos.2 (by norm_num)))
  refine ⟨hp,?_⟩
  nlinarith [escapePoint_sq]

/--
@isnad1 id=eq.0h0v.s4.4383445cf628 from=translated src=- shape=c29dca45 vocab=2fe95dd9
-/
theorem escape_path_x : scalarPathX escapePoint=(50/99:ℝ) := by
  rw [scalarPathX,escapePoint_sq]
  norm_num

/--
@isnad1 id=eq.0h0v.s4.2592551fa9b5 from=translated src=- shape=c896535a vocab=91a9be75
-/
theorem escape_complex_x : betaFrameX (escapePoint:ℂ)=(50/99:ℂ) := by
  have hx : betaFrameX (escapePoint:ℂ)=(scalarPathX escapePoint:ℂ) := by
    simp [betaFrameX,scalarPathX]
  rw [hx,escape_path_x]
  norm_num

/--
@isnad1 id=and.0h0v.s5.836a2b389fa7 from=translated src=- shape=bafac9fe vocab=8f06486a
-/
theorem escape_radius_domain :
    0<escapeRadius ∧ escapeRadius<1 ∧
      ‖betaFrameLambda (betaFrameX (escapePoint:ℂ))‖<escapeRadius := by
  have hl0 : 0<scalarLambda (scalarPathX escapePoint) :=
    scalarLambda_pos (scalarPathX_mem escapePoint_mem.1 escapePoint_mem.2).1
  have hl1 : scalarLambda (scalarPathX escapePoint)<1 := by
    rw [escape_path_x]
    norm_num [scalarLambda,rho]
  have hr0 : 0<escapeRadius := Real.sqrt_pos.2 hl0
  have hrsq : escapeRadius^2=scalarLambda (scalarPathX escapePoint) := Real.sq_sqrt hl0.le
  have hr1 : escapeRadius<1 := by nlinarith
  have hx : betaFrameX (escapePoint:ℂ)=(scalarPathX escapePoint:ℂ) := by
    simp [betaFrameX,scalarPathX]
  have hlambda := (betaFrame_real_agreement (scalarPathX escapePoint)).2.2.2.2.2.2
  refine ⟨hr0,hr1,?_⟩
  rw [hx,hlambda,Complex.norm_of_nonneg hl0.le]
  nlinarith

/--
@isnad1 id=and.1h1v.s6.383ac0639e6f from=translated src=- shape=c9ba71bc vocab=27b38374
-/
theorem escape_circle_regular (s : ℂ) (hs : s ∈ sphere (0:ℂ) escapeRadius) :
    escapeBetaDenominator (escapePoint:ℂ) s ≠ 0 ∧ s ≠ 0 ∧ ‖s‖<1 ∧
      ‖betaFrameB (escapePoint:ℂ) s‖<1 := by
  obtain ⟨hr0,hr1,hlambda⟩ := escape_radius_domain
  obtain ⟨hs0,_,_,hs1,hb⟩ := angular_circle_domain hr0 hr1 hlambda hs
  have hsn : ‖s‖=escapeRadius := by simpa using mem_sphere.mp hs
  have ha := scalarPolePlus_pos_lt_radius escapePoint_mem.1 escapePoint_mem.2
  have hbR := scalarPoleMinus_gt_radius escapePoint_mem.1 escapePoint_mem.2
  have hplus : scalarPolePlus escapePoint<escapeRadius := ha.2
  have hminus : escapeRadius<scalarPoleMinus escapePoint := hbR
  have hsa : s-(scalarPolePlus escapePoint:ℂ) ≠ 0 := by
    intro he
    rw [sub_eq_zero.mp he,Complex.norm_of_nonneg ha.1.le] at hsn
    exact hplus.ne hsn
  have hsb : s-(scalarPoleMinus escapePoint:ℂ) ≠ 0 := by
    intro he
    rw [sub_eq_zero.mp he,Complex.norm_of_nonneg (hr0.trans hminus).le] at hsn
    exact hminus.ne' hsn
  have hF : betaFrameF (betaFrameX (escapePoint:ℂ)) s ≠ 0 := by
    rw [scalar_beta_pole_factor escapePoint_mem.1 escapePoint_mem.2]
    exact mul_ne_zero hsa hsb
  have hx : betaFrameX (escapePoint:ℂ) ≠ 0 := by rw [escape_complex_x]; norm_num
  have hM : betaFrameM (betaFrameX (escapePoint:ℂ)) ≠ 0 := by
    rw [escape_complex_x]
    norm_num [betaFrameM]
  refine ⟨mul_ne_zero (mul_ne_zero (pow_ne_zero 4 hx) hM) hF,hs0,hs1,?_⟩
  simpa only [betaFrameB] using hb

/--
@isnad1 id=continuo.0h0v.s5.3d99612e640f from=translated src=- shape=1c9bbd5f vocab=103b8c88
-/
theorem escapeBetaDenominator_continuous :
    Continuous (fun p : ℂ × ℂ => escapeBetaDenominator p.1 p.2) := by
  unfold escapeBetaDenominator betaFrameX betaFrameM betaFrameF betaFrameMid betaFrameLambda
  fun_prop

/--
@isnad1 id=continuo.1h1v.s6.49b5c753194b from=translated src=- shape=9f2c3121 vocab=f395fc7b
-/
theorem escape_B_continuousAt (p : ℂ × ℂ) (hs0 : p.2 ≠ 0) :
    ContinuousAt (fun q : ℂ × ℂ => betaFrameB q.1 q.2) p := by
  unfold betaFrameB betaFrameLambda betaFrameX
  fun_prop (disch := assumption)

/--
@isnad1 id=ex.0h0v.s6.949f2904fd4f from=translated src=- shape=30bdefc3 vocab=1a9b4206
-/
theorem escape_regular_tube :
    ∃ ε > 0, ∀ U ∈ closedBall (escapePoint:ℂ) ε, ∀ s ∈ sphere (0:ℂ) escapeRadius,
      escapeBetaDenominator U s ≠ 0 ∧ s ≠ 0 ∧ ‖s‖<1 ∧ ‖betaFrameB U s‖<1 := by
  have hev : ∀ᶠ U : ℂ in 𝓝 (escapePoint:ℂ), ∀ s ∈ sphere (0:ℂ) escapeRadius,
      escapeBetaDenominator U s ≠ 0 ∧ s ≠ 0 ∧ ‖s‖<1 ∧ ‖betaFrameB U s‖<1 := by
    apply (isCompact_sphere (0:ℂ) escapeRadius).eventually_forall_of_forall_eventually
    intro s hs
    obtain ⟨hD,hs0,hs1,hb⟩ := escape_circle_regular s hs
    have hDn : ∀ᶠ p : ℂ × ℂ in 𝓝 ((escapePoint:ℂ),s),
        escapeBetaDenominator p.1 p.2 ≠ 0 :=
      escapeBetaDenominator_continuous.continuousAt.eventually_ne hD
    have hs0n : ∀ᶠ p : ℂ × ℂ in 𝓝 ((escapePoint:ℂ),s), p.2 ≠ 0 :=
      continuousAt_snd.eventually_ne hs0
    have hs1n : ∀ᶠ p : ℂ × ℂ in 𝓝 ((escapePoint:ℂ),s), ‖p.2‖<1 :=
      continuousAt_snd.norm.eventually (Iio_mem_nhds hs1)
    have hbn : ∀ᶠ p : ℂ × ℂ in 𝓝 ((escapePoint:ℂ),s), ‖betaFrameB p.1 p.2‖<1 :=
      (escape_B_continuousAt ((escapePoint:ℂ),s) hs0).norm.eventually (Iio_mem_nhds hb)
    filter_upwards [hDn,hs0n,hs1n,hbn] with p hpD hps0 hps1 hpb
    exact ⟨hpD,hps0,hps1,hpb⟩
  obtain ⟨δ,hδ,hball⟩ := Metric.mem_nhds_iff.mp hev
  refine ⟨δ/2,by positivity,?_⟩
  intro U hU s hs
  exact hball (mem_ball.mpr ((mem_closedBall.mp hU).trans_lt (by linarith))) s hs

/--
@isnad1 id=analytic.4h1v.s7.bcae6c08f53b from=translated src=- shape=f287aa3e vocab=51627c35
-/
theorem escapeClearedBetaIntegrand_joint_analyticAt (p : ℂ × ℂ)
    (hD : escapeBetaDenominator p.1 p.2 ≠ 0) (hs0 : p.2 ≠ 0)
    (hs : ‖p.2‖<1) (hb : ‖betaFrameB p.1 p.2‖<1) :
    AnalyticAt ℂ (fun q : ℂ × ℂ => escapeClearedBetaIntegrand q.1 q.2) p := by
  have hB : AnalyticAt ℂ (fun q : ℂ × ℂ => betaFrameB q.1 q.2) p := by
    unfold betaFrameB betaFrameLambda betaFrameX
    fun_prop (disch := assumption)
  have hX (i : Fin 3) : AnalyticAt ℂ (fun q : ℂ × ℂ => dualState q.2 i) p :=
    (dualState_entry_analyticAt i p.2 hs).fun_comp analyticAt_snd
  have hZ (j : Fin 3) : AnalyticAt ℂ
      (fun q : ℂ × ℂ => dualState (betaFrameB q.1 q.2) j) p :=
    (dualState_entry_analyticAt j (betaFrameB p.1 p.2) hb).comp
      (f := fun q : ℂ × ℂ => betaFrameB q.1 q.2) (x := p) hB
  have hR (i j : Fin 3) : AnalyticAt ℂ
      (fun q : ℂ × ℂ => escapeClearedBetaMatrix q.1 q.2 i j) p := by
    unfold escapeClearedBetaMatrix
    apply AnalyticAt.div
    · apply analyticAt_fst.mul
      fin_cases i <;> fin_cases j <;>
        simp [betaFrameLP,betaFrameRP,betaFrameX,betaFrameMid,betaFrameEll,betaFrameM] <;>
        fun_prop
    · unfold escapeBetaDenominator betaFrameX betaFrameM betaFrameF betaFrameMid betaFrameLambda
      fun_prop
    · exact hD
  unfold escapeClearedBetaIntegrand betaPair
  exact Finset.analyticAt_fun_sum _ (fun i _ => Finset.analyticAt_fun_sum _ (fun j _ =>
    ((hX i).mul (hR i j)).mul (hZ j)))

/--
@isnad1 id=analytic.0h0v.s5.768699a41fbe from=translated src=- shape=3e436b0a vocab=763d04b6
-/
theorem escapeClearedBetaCircle_analyticAt :
    AnalyticAt ℂ (fun U => escapeClearedBetaCircle U escapeRadius) (escapePoint:ℂ) := by
  obtain ⟨ε,hε,hreg⟩ := escape_regular_tube
  have hjoint : ∀ p ∈ closedBall (escapePoint:ℂ) ε ×ˢ sphere (0:ℂ) escapeRadius,
      AnalyticAt ℂ (fun q : ℂ × ℂ => escapeClearedBetaIntegrand q.1 q.2) p := by
    intro p hp
    obtain ⟨hD,hs0,hs,hb⟩ := hreg p.1 hp.1 p.2 hp.2
    exact escapeClearedBetaIntegrand_joint_analyticAt p hD hs0 hs hb
  exact (analyticAt_const : AnalyticAt ℂ (fun _ : ℂ => (2*Real.pi*I:ℂ)⁻¹)
    (escapePoint:ℂ)).mul (circleIntegral_analyticAt_of_joint_analyticOnTube
      escapeClearedBetaIntegrand (escapePoint:ℂ) 0 escapeRadius ε
      escape_radius_domain.1.le hε hjoint)

/--
@isnad1 id=eq.2h4v.s6.879d9ef59a36 from=translated src=- shape=cdf74a71 vocab=33a4e9ee
-/
theorem escape_cleared_beta_entry_eq (U s : ℂ)
    (hD : escapeBetaDenominator U s ≠ 0) (hE : escapeFactor U ≠ 0) (i j : Fin 3) :
    escapeClearedBetaMatrix U s i j=escapeFactor U^2*scalarBetaSFull U s i j := by
  have hx : betaFrameX U ≠ 0 := by
    intro he
    simp [escapeBetaDenominator,he] at hD
  have hM : betaFrameM (betaFrameX U) ≠ 0 := (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hD).1).2
  have hF : betaFrameF (betaFrameX U) s ≠ 0 := (mul_ne_zero_iff.mp hD).2
  change U*(2*betaFrameLP (betaFrameX U) i j*(s-betaFrameMid (betaFrameX U))+
    2*betaFrameEll (betaFrameX U)*betaFrameM (betaFrameX U)*betaFrameRP (betaFrameX U) i j)/
    ((betaFrameX U)^4*betaFrameM (betaFrameX U)*betaFrameF (betaFrameX U) s)=
    (99*betaFrameX U-50)^2*(U*((2*betaFrameLP (betaFrameX U) i j*(s-betaFrameMid (betaFrameX U))+
      2*betaFrameEll (betaFrameX U)*betaFrameM (betaFrameX U)*betaFrameRP (betaFrameX U) i j)/
      ((betaFrameX U)^4*betaFrameM (betaFrameX U)*(99*betaFrameX U-50)^2*
        betaFrameF (betaFrameX U) s)))
  have hEn : 99*betaFrameX U-50 ≠ 0 := hE
  generalize he : 99*betaFrameX U-50 = E at hEn ⊢
  field_simp [hx,hM,hF,hEn]

/--
@isnad1 id=eq.2h2v.s5.0648d33b8d55 from=translated src=- shape=bfa563f1 vocab=34e32c3b
-/
theorem escape_cleared_beta_integrand_eq (U s : ℂ)
    (hD : escapeBetaDenominator U s ≠ 0) (hE : escapeFactor U ≠ 0) :
    escapeClearedBetaIntegrand U s=escapeFactor U^2*betaFluxIntegrand U s := by
  unfold escapeClearedBetaIntegrand betaFluxIntegrand betaPair
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [escape_cleared_beta_entry_eq U s hD hE i j]
  ring

/--
@isnad1 id=eq.3h2v.s6.42186f776007 from=translated src=- shape=529d7e1d vocab=ab84a5be
-/
theorem escape_cleared_beta_circle_eq (U : ℂ) {r : ℝ} (hr : 0 ≤ r)
    (hD : ∀ s ∈ sphere (0:ℂ) r, escapeBetaDenominator U s ≠ 0)
    (hE : escapeFactor U ≠ 0) :
    escapeClearedBetaCircle U r=escapeFactor U^2*betaFluxCircle U r := by
  have hi : (∮ s in C(0,r), escapeClearedBetaIntegrand U s)=
      ∮ s in C(0,r), escapeFactor U^2*betaFluxIntegrand U s :=
    circleIntegral.integral_congr hr (fun s hs => escape_cleared_beta_integrand_eq U s (hD s hs) hE)
  unfold escapeClearedBetaCircle betaFluxCircle
  rw [hi,circleIntegral.integral_const_mul]
  ring

/--
@isnad1 id=eq.2h2v.s6.8d00460f66a4 from=translated src=- shape=35528bf4 vocab=84e28ac8
-/
theorem escape_cleared_outer_basis_eq (x : ℂ) (hx : x ≠ 0)
    (hE : 99*x-50 ≠ 0) (k : Fin 15) :
    escapeClearedOuterBasis x k=(99*x-50)^2*outerPrimitiveBasis x k := by
  fin_cases k
  · change (99*x-50)^2/x=(99*x-50)^2*(1/x)
    generalize he : 99*x-50 = E at hE ⊢
    field_simp [hx,hE]
  · change (99*x-50)^2/x^2=(99*x-50)^2*(1/x^2)
    generalize he : 99*x-50 = E at hE ⊢
    field_simp [hx,hE]
  · change (99*x-50)^2/x^3=(99*x-50)^2*(1/x^3)
    generalize he : 99*x-50 = E at hE ⊢
    field_simp [hx,hE]
  · change (99*x-50)^2/x^4=(99*x-50)^2*(1/x^4)
    generalize he : 99*x-50 = E at hE ⊢
    field_simp [hx,hE]
  · change 99*x-50=(99*x-50)^2*(1/(99*x-50))
    generalize he : 99*x-50 = E at hE ⊢
    field_simp [hx,hE]
  · change 1=(99*x-50)^2*(1/(99*x-50)^2)
    generalize he : 99*x-50 = E at hE ⊢
    field_simp [hx,hE]
  · change (99*x-50)^2=(99*x-50)^2*(1)
    generalize he : 99*x-50 = E at hE ⊢
    field_simp [hx,hE]
  · change (99*x-50)^2*x=(99*x-50)^2*(x)
    generalize he : 99*x-50 = E at hE ⊢
    field_simp [hx,hE]
  · change (99*x-50)^2*x^2=(99*x-50)^2*(x^2)
    generalize he : 99*x-50 = E at hE ⊢
    field_simp [hx,hE]
  · change (99*x-50)^2*x^3=(99*x-50)^2*(x^3)
    generalize he : 99*x-50 = E at hE ⊢
    field_simp [hx,hE]
  · change (99*x-50)^2*x^4=(99*x-50)^2*(x^4)
    generalize he : 99*x-50 = E at hE ⊢
    field_simp [hx,hE]
  · change (99*x-50)^2*x^5=(99*x-50)^2*(x^5)
    generalize he : 99*x-50 = E at hE ⊢
    field_simp [hx,hE]
  · change (99*x-50)^2*x^6=(99*x-50)^2*(x^6)
    generalize he : 99*x-50 = E at hE ⊢
    field_simp [hx,hE]
  · change (99*x-50)^2*x^7=(99*x-50)^2*(x^7)
    generalize he : 99*x-50 = E at hE ⊢
    field_simp [hx,hE]
  · change (99*x-50)^2*x^8=(99*x-50)^2*(x^8)
    generalize he : 99*x-50 = E at hE ⊢
    field_simp [hx,hE]

/--
@isnad1 id=eq.2h2v.s6.1e955eb78037 from=translated src=- shape=35528bf4 vocab=10c84cbf
-/
theorem escape_cleared_outer_row_eq (x : ℂ) (hx : x ≠ 0) (hE : 99*x-50 ≠ 0) (j : Fin 6) :
    escapeClearedOuterRow x j=(99*x-50)^2*outerPrimitiveRow x j := by
  unfold escapeClearedOuterRow outerPrimitiveRow
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [escape_cleared_outer_basis_eq x hx hE k]
  ring

/--
@isnad1 id=eq.2h1v.s5.1f3dd13a5d90 from=translated src=- shape=815b5722 vocab=08d4466b
-/
theorem escape_cleared_outer_flux_eq (U : ℂ)
    (hx : betaFrameX U ≠ 0) (hE : escapeFactor U ≠ 0) :
    escapeClearedOuterFlux U=escapeFactor U^2*outerPrimitiveFlux U := by
  have hxn : 1-U^2 ≠ 0 := hx
  have hEn : 99*(1-U^2)-50 ≠ 0 := hE
  unfold escapeClearedOuterFlux outerPrimitiveFlux dotProduct
  have hi : (∑ j : Fin 6, escapeClearedOuterRow (1-U^2) j*
      sixthNormalState (outerPrimitiveLambda (1-U^2)) j)=
      (99*(1-U^2)-50)^2*(∑ j : Fin 6, outerPrimitiveRow (1-U^2) j*
        sixthNormalState (outerPrimitiveLambda (1-U^2)) j) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [escape_cleared_outer_row_eq (1-U^2) hxn hEn j]
    ring
  rw [hi]
  change _=(99*(1-U^2)-50)^2*_
  ring

/--
@isnad1 id=analytic.1h2v.s5.3ca8cb556056 from=translated src=- shape=1a031d3a vocab=fcfa1659
-/
theorem escape_cleared_outer_basis_analyticAt (k : Fin 15) (x : ℂ) (hx : x ≠ 0) :
    AnalyticAt ℂ (fun z => escapeClearedOuterBasis z k) x := by
  fin_cases k
  · change AnalyticAt ℂ (fun z : ℂ => (99*z-50)^2/z) x
    fun_prop (disch := first | assumption | exact pow_ne_zero _ hx)
  · change AnalyticAt ℂ (fun z : ℂ => (99*z-50)^2/z^2) x
    fun_prop (disch := first | assumption | exact pow_ne_zero _ hx)
  · change AnalyticAt ℂ (fun z : ℂ => (99*z-50)^2/z^3) x
    fun_prop (disch := first | assumption | exact pow_ne_zero _ hx)
  · change AnalyticAt ℂ (fun z : ℂ => (99*z-50)^2/z^4) x
    fun_prop (disch := first | assumption | exact pow_ne_zero _ hx)
  · change AnalyticAt ℂ (fun z : ℂ => 99*z-50) x
    fun_prop (disch := first | assumption | exact pow_ne_zero _ hx)
  · change AnalyticAt ℂ (fun z : ℂ => 1) x
    fun_prop (disch := first | assumption | exact pow_ne_zero _ hx)
  · change AnalyticAt ℂ (fun z : ℂ => (99*z-50)^2) x
    fun_prop (disch := first | assumption | exact pow_ne_zero _ hx)
  · change AnalyticAt ℂ (fun z : ℂ => (99*z-50)^2*z) x
    fun_prop (disch := first | assumption | exact pow_ne_zero _ hx)
  · change AnalyticAt ℂ (fun z : ℂ => (99*z-50)^2*z^2) x
    fun_prop (disch := first | assumption | exact pow_ne_zero _ hx)
  · change AnalyticAt ℂ (fun z : ℂ => (99*z-50)^2*z^3) x
    fun_prop (disch := first | assumption | exact pow_ne_zero _ hx)
  · change AnalyticAt ℂ (fun z : ℂ => (99*z-50)^2*z^4) x
    fun_prop (disch := first | assumption | exact pow_ne_zero _ hx)
  · change AnalyticAt ℂ (fun z : ℂ => (99*z-50)^2*z^5) x
    fun_prop (disch := first | assumption | exact pow_ne_zero _ hx)
  · change AnalyticAt ℂ (fun z : ℂ => (99*z-50)^2*z^6) x
    fun_prop (disch := first | assumption | exact pow_ne_zero _ hx)
  · change AnalyticAt ℂ (fun z : ℂ => (99*z-50)^2*z^7) x
    fun_prop (disch := first | assumption | exact pow_ne_zero _ hx)
  · change AnalyticAt ℂ (fun z : ℂ => (99*z-50)^2*z^8) x
    fun_prop (disch := first | assumption | exact pow_ne_zero _ hx)

/--
@isnad1 id=analytic.1h2v.s5.05b73430a881 from=translated src=- shape=1a031d3a vocab=4766cd44
-/
theorem escape_cleared_outer_row_analyticAt (j : Fin 6) (x : ℂ) (hx : x ≠ 0) :
    AnalyticAt ℂ (fun z => escapeClearedOuterRow z j) x := by
  unfold escapeClearedOuterRow
  exact Finset.analyticAt_fun_sum _ (fun k _ => analyticAt_const.mul
    (escape_cleared_outer_basis_analyticAt k x hx))

/--
@isnad1 id=analytic.1h2v.s5.61ec5fbf0a36 from=translated src=- shape=d4daed34 vocab=d4128771
-/
theorem sixthNormalState_entry_analyticAt (j : Fin 6) (q : ℂ) (hq : ‖q‖<1) :
    AnalyticAt ℂ (fun z => sixthNormalState z j) q := by
  unfold sixthNormalState Matrix.mulVec dotProduct
  exact Finset.analyticAt_fun_sum _ (fun k _ => analyticAt_const.mul
    (sixth_state_analyticAt k q hq))

/--
@isnad1 id=analytic.2h1v.s5.b581912f772c from=translated src=- shape=72008e51 vocab=040d6e82
-/
theorem escape_cleared_outer_flux_analyticAt (U : ℂ) (hx : betaFrameX U ≠ 0)
    (hlambda : ‖outerPrimitiveLambda (betaFrameX U)‖<1) :
    AnalyticAt ℂ escapeClearedOuterFlux U := by
  have hX : AnalyticAt ℂ (fun z : ℂ => 1-z^2) U := by fun_prop
  have hL : AnalyticAt ℂ (fun z : ℂ => outerPrimitiveLambda (1-z^2)) U := by
    unfold outerPrimitiveLambda
    fun_prop
  have hR (j : Fin 6) : AnalyticAt ℂ (fun z => escapeClearedOuterRow (1-z^2) j) U :=
    (escape_cleared_outer_row_analyticAt j (betaFrameX U) hx).fun_comp hX
  have hY (j : Fin 6) : AnalyticAt ℂ
      (fun z => sixthNormalState (outerPrimitiveLambda (1-z^2)) j) U :=
    (sixthNormalState_entry_analyticAt j (outerPrimitiveLambda (betaFrameX U)) hlambda).comp
      (f := fun z : ℂ => outerPrimitiveLambda (1-z^2)) (x := U) hL
  unfold escapeClearedOuterFlux dotProduct
  exact analyticAt_id.mul (Finset.analyticAt_fun_sum _ (fun j _ => (hR j).mul (hY j)))

/--
@isnad1 id=analytic.0h0v.s5.851227cbeb9f from=translated src=- shape=f9ffc11e vocab=879e1ed0
-/
theorem escapeClearedTotal_analyticAt : AnalyticAt ℂ escapeClearedTotal (escapePoint:ℂ) := by
  have hx : betaFrameX (escapePoint:ℂ) ≠ 0 := by rw [escape_complex_x]; norm_num
  have hlambda : ‖outerPrimitiveLambda (betaFrameX (escapePoint:ℂ))‖<1 := by
    rw [escape_complex_x]
    norm_num [outerPrimitiveLambda,norm_div,norm_mul,norm_pow]
  exact escapeClearedBetaCircle_analyticAt.add
    (escape_cleared_outer_flux_analyticAt (escapePoint:ℂ) hx hlambda)

/--
@isnad1 id=eq.3h1v.s6.74ad4c5b2b55 from=translated src=- shape=a15c0d79 vocab=e1bc4b8a
-/
theorem escapeClearedTotal_eq (U : ℂ) (hx : betaFrameX U ≠ 0)
    (hE : escapeFactor U ≠ 0)
    (hD : ∀ s ∈ sphere (0:ℂ) escapeRadius, escapeBetaDenominator U s ≠ 0) :
    escapeClearedTotal U=escapeFactor U^2*(betaFluxCircle U escapeRadius+outerPrimitiveFlux U) := by
  unfold escapeClearedTotal
  rw [escape_cleared_beta_circle_eq U escape_radius_domain.1.le hD hE,
    escape_cleared_outer_flux_eq U hx hE]
  ring

/--
@isnad1 id=eventual.0h0v.s6.68c05142c8ae from=translated src=- shape=27ca7f94 vocab=19cae577
-/
theorem escapeClearedTotal_clears_near :
    ∀ᶠ U : ℂ in 𝓝 (escapePoint:ℂ), escapeFactor U ≠ 0 →
      escapeClearedTotal U=escapeFactor U^2*(betaFluxCircle U escapeRadius+outerPrimitiveFlux U) := by
  obtain ⟨ε,hε,hreg⟩ := escape_regular_tube
  have hx0 : betaFrameX (escapePoint:ℂ) ≠ 0 := by rw [escape_complex_x]; norm_num
  have hxc : Continuous (betaFrameX : ℂ → ℂ) := by unfold betaFrameX; fun_prop
  filter_upwards [closedBall_mem_nhds (escapePoint:ℂ) hε,
    hxc.continuousAt.eventually_ne hx0] with U hU hx
  intro hE
  exact escapeClearedTotal_eq U hx hE (fun s hs => (hreg U hU s hs).1)

end Row12

