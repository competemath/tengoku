import Tengoku.PshdLean.PshLines.CircleSubmean
import Tengoku.PshdLean.PshLines.PshAddition
import Tengoku.Seed.Analysis.Complex.Harmonic.MeanValue
import Tengoku.Seed.Analysis.InnerProductSpace.Harmonic.Constructions

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Harmonic functions as disc-plurisubharmonic functions

A real harmonic function on the complex plane remains harmonic after
precomposition with a complex-affine map.  Its mean-value equality therefore
supplies both directions of the disc-PSH test, so adding or subtracting such a
function preserves plurisubharmonicity.
-/

open InnerProductSpace Metric Set Topology MeasureTheory

namespace PshLines

/-- Harmonicity on `ℂ` is preserved by precomposition with a complex-affine
map.  The local holomorphic primitive gives a short proof without expanding
the real Hessian of complex multiplication.
@isnad1 id=harmonic.1h4v.s6.fb0560ace1be from=translated src=- shape=e8d41a7c vocab=8a403630
-/
theorem HarmonicAt.comp_complexAffine {h : ℂ → ℝ} {x v z : ℂ}
    (hh : HarmonicAt h (x + z * v)) :
    HarmonicAt (fun w : ℂ => h (x + w * v)) z := by
  let A : ℂ → ℂ := fun w => x + w * v
  obtain ⟨ε, hε, hball⟩ :=
    isOpen_iff.1 (isOpen_setOfPred_harmonicAt (f := h)) (A z) hh
  obtain ⟨F, hF, hFre⟩ :=
    InnerProductSpace.HarmonicOnNhd.exists_analyticOnNhd_ball_re_eq
      (fun y hy => hball hy)
  have hAz_ball : A z ∈ ball (A z) ε := mem_ball_self hε
  have hA : AnalyticAt ℂ A z := by
    dsimp [A]
    fun_prop
  have hFA : AnalyticAt ℂ (F ∘ A) z := (hF (A z) hAz_ball).comp hA
  have hnear : ∀ᶠ w in 𝓝 z, A w ∈ ball (A z) ε :=
    hA.continuousAt.eventually (isOpen_ball.mem_nhds hAz_ball)
  have heq : (fun w : ℂ => ((F ∘ A) w).re) =ᶠ[𝓝 z]
      (fun w : ℂ => h (x + w * v)) := by
    filter_upwards [hnear] with w hw
    exact hFre hw
  exact (harmonicAt_congr_nhds heq).mp (AnalyticAt.harmonicAt_re hFA)

/-- Setwise form of complex-affine pullback invariance.
@isnad1 id=harmonic.2h5v.s6.f078ea529cb7 from=translated src=- shape=c88cf608 vocab=fec8d7df
-/
theorem HarmonicOnNhd.comp_complexAffine {h : ℂ → ℝ} {S T : Set ℂ} (x v : ℂ)
    (hh : HarmonicOnNhd h S)
    (hmap : ∀ z ∈ T, x + z * v ∈ S) :
    HarmonicOnNhd (fun z : ℂ => h (x + z * v)) T :=
  fun z hz => HarmonicAt.comp_complexAffine (hh _ (hmap z hz))

/-- A real harmonic function on a set satisfies the disc-PSH criterion there.
Only continuity on that set is used.
@isnad1 id=discpsho.1h2v.s5.8dd6461013f2 from=translated src=- shape=af65cb0f vocab=81e9e4c7
-/
theorem HarmonicOnNhd.discPshOn {h : ℂ → ℝ} {U : Set ℂ}
    (hh : HarmonicOnNhd h U) :
    DiscPshOn (fun z => (h z : EReal)) U := by
  refine ⟨fun _ _ => EReal.coe_ne_top _,
    (continuous_coe_real_ereal.comp_continuousOn hh.continuousOn).upperSemicontinuousOn,
    ?_⟩
  intro x v r hr hD C hC
  have hpull : HarmonicOnNhd (fun z : ℂ => h (x + z * v)) (closedBall 0 |r|) := by
    apply HarmonicOnNhd.comp_complexAffine x v hh
    intro z hz
    apply hD
    refine ⟨z, ?_, rfl⟩
    simpa [abs_of_pos hr] using hz
  have hmean : h x = Real.circleAverage (fun z : ℂ => h (x + z * v)) 0 r := by
    rw [InnerProductSpace.HarmonicOnNhd.circleAverage_eq hpull]
    simp
  have hcirc : Continuous (fun t : ℝ => h (x + circleMap 0 r t * v)) := by
    have hpath : Continuous (fun t : ℝ => x + circleMap 0 r t * v) := by fun_prop
    apply hh.continuousOn.comp_continuous hpath
    intro t
    apply hD
    exact circle_mem_affineClosedDisc x v hr.le t
  apply (circleDeficit_coe_le_iff x v r C (hcirc.intervalIntegrable _ _)
    (fun t => EReal.coe_le_coe_iff.mp
      (hC _ (circle_mem_affineClosedDisc x v hr.le t)))
    (EReal.coe_le_coe_iff.mp
      (hC x (center_mem_affineClosedDisc x v hr.le)))).mpr
  exact hmean.le

/-- The coercion of a globally harmonic real function is disc-PSH on every
set.
@isnad1 id=discpsho.1h2v.s5.dcc1294b6b44 from=translated src=- shape=bf98da5e vocab=5e67eb97
-/
theorem HarmonicOnNhd.discPshOn_of_univ {h : ℂ → ℝ} {U : Set ℂ}
    (hh : HarmonicOnNhd h univ) :
    DiscPshOn (fun z => (h z : EReal)) U := by
  apply discPshOn_of_circleAverage (continuousOn_univ.mp hh.continuousOn)
  intro x v r hr _hD
  have hpull : HarmonicOnNhd (fun z : ℂ => h (x + z * v)) (closedBall 0 |r|) := by
    apply HarmonicOnNhd.comp_complexAffine x v hh
    simp
  have hmean := InnerProductSpace.HarmonicOnNhd.circleAverage_eq hpull
  simpa using hmean.ge

/-- A harmonic germ defines a plurisubharmonic extended-real germ.
@isnad1 id=plurisub.1h2v.s5.f67de700b3dd from=translated src=- shape=72c5aff4 vocab=1fd8d87e
-/
theorem HarmonicAt.plurisubharmonicAt {h : ℂ → ℝ} {x : ℂ}
    (hh : HarmonicAt h x) :
    PlurisubharmonicAt (fun z => (h z : EReal)) x := by
  refine ⟨{y | HarmonicAt h y}, isOpen_setOfPred_harmonicAt h, hh, ?_⟩
  exact HarmonicOnNhd.discPshOn (fun _ hy => hy)

/-- Harmonicity along an arbitrary set supplies ambient plurisubharmonic germs
at all its points.
@isnad1 id=plurisub.1h2v.s5.eeb5616ed248 from=translated src=- shape=af65cb0f vocab=d2830ddc
-/
theorem HarmonicOnNhd.plurisubharmonicOn {h : ℂ → ℝ} {U : Set ℂ}
    (hh : HarmonicOnNhd h U) :
    PlurisubharmonicOn (fun z => (h z : EReal)) U :=
  fun x hx => HarmonicAt.plurisubharmonicAt (hh x hx)

/-- Adding a harmonic real function preserves the disc-PSH criterion.
@isnad1 id=discpsho.2h3v.s6.6fdbfa7bf2b4 from=translated src=- shape=65c373da vocab=11e6d579
-/
theorem DiscPshOn.add_harmonic {u : ℂ → EReal} {h : ℂ → ℝ} {U : Set ℂ}
    (hu : DiscPshOn u U) (hh : HarmonicOnNhd h U) :
    DiscPshOn (fun z => u z + (h z : EReal)) U :=
  hu.add (HarmonicOnNhd.discPshOn hh)

/-- Subtracting a harmonic real function preserves the disc-PSH criterion.
@isnad1 id=discpsho.2h3v.s6.828e8e9a9d4b from=translated src=- shape=65c373da vocab=ce0952f8
-/
theorem DiscPshOn.sub_harmonic {u : ℂ → EReal} {h : ℂ → ℝ} {U : Set ℂ}
    (hu : DiscPshOn u U) (hh : HarmonicOnNhd h U) :
    DiscPshOn (fun z => u z - (h z : EReal)) U := by
  simpa only [sub_eq_add_neg, Pi.neg_apply, EReal.coe_neg] using
    hu.add (HarmonicOnNhd.discPshOn hh.neg)

/-- Adding a harmonic real function preserves plurisubharmonicity.
@isnad1 id=plurisub.2h3v.s6.646630f322bd from=translated src=- shape=65c373da vocab=9cec546c
-/
theorem PlurisubharmonicOn.add_harmonic {u : ℂ → EReal} {h : ℂ → ℝ} {U : Set ℂ}
    (hu : PlurisubharmonicOn u U) (hh : HarmonicOnNhd h U) :
    PlurisubharmonicOn (fun z => u z + (h z : EReal)) U :=
  hu.add (HarmonicOnNhd.plurisubharmonicOn hh)

/-- Subtracting a harmonic real function preserves plurisubharmonicity.
@isnad1 id=plurisub.2h3v.s6.a3b36eb24019 from=translated src=- shape=65c373da vocab=b0683ebe
-/
theorem PlurisubharmonicOn.sub_harmonic {u : ℂ → EReal} {h : ℂ → ℝ} {U : Set ℂ}
    (hu : PlurisubharmonicOn u U) (hh : HarmonicOnNhd h U) :
    PlurisubharmonicOn (fun z => u z - (h z : EReal)) U := by
  simpa only [sub_eq_add_neg, Pi.neg_apply, EReal.coe_neg] using
    hu.add (HarmonicOnNhd.plurisubharmonicOn hh.neg)

end PshLines
