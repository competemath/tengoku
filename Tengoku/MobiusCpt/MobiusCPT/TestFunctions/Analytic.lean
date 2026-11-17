import Tengoku.Seed.Analysis.Calculus.ContDiff.Bounds
import Tengoku.Seed.Analysis.Calculus.TangentCone.Real
import Tengoku.Seed.Analysis.Complex.AbsMax
import Tengoku.Seed.Analysis.Complex.RealDeriv
import Tengoku.Seed.Analysis.Complex.RemovableSingularity
import Tengoku.Seed.Analysis.Normed.Field.Lemmas
import Tengoku.Seed.Analysis.Normed.Module.Convex
import Tengoku.Seed.Topology.Compactification.OnePoint.Basic
import Tengoku.Seed.Topology.MetricSpace.Bounded
import Tengoku.MobiusCpt.MobiusCPT.Mobius.ComplexBoost
import Tengoku.MobiusCpt.MobiusCPT.TestFunctions.Split

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# MobiusCPT.TestFunctions.Analytic

The analytic test-function class on the exterior of the unit disk and its restrictions to the
circle and its two open semicircles.
-/

namespace MobiusCPT

open Filter Set
open scoped ContDiff Topology

noncomputable section

/-- [T26], Definition 3.2; the finite part of `𝕆 = { z : |z| ≥ 1 } ∪ {∞}`.-/
def Oexterior : Set ℂ := {z : ℂ | 1 ≤ ‖z‖}

/-- [T26], Definition 3.2; the interior of `𝕆` inside `ℂ`.-/
def OexteriorInterior : Set ℂ := {z : ℂ | 1 < ‖z‖}

/-- [T26], Definition 3.2; the analytic test-function class `𝓧`: smooth on `𝕆`, holomorphic in
its interior, vanishing at `∞`, and vanishing to all orders at `±1`.-/
structure AnalyticTestFn where
  toFun : ℂ → ℂ
  contDiffOn : ContDiffOn ℝ ∞ toFun Oexterior
  differentiableOn : DifferentiableOn ℂ toFun OexteriorInterior
  tendsto_zero : Filter.Tendsto toFun (Filter.cocompact ℂ) (nhds 0)
  flat_one : ∀ n : ℕ, iteratedFDerivWithin ℝ n toFun Oexterior 1 = 0
  flat_neg_one : ∀ n : ℕ, iteratedFDerivWithin ℝ n toFun Oexterior (-1) = 0

/-- [T26], Definition 3.2; the interior of the finite exterior is open.
@isnad1 id=isopen.0h0v.s4.3a36ae1e1bf7 from=translated src=- shape=25b03439 vocab=0018d37f
-/
theorem isOpen_OexteriorInterior : IsOpen OexteriorInterior := by
  change IsOpen {z : ℂ | (1 : ℝ) < ‖z‖}
  exact isOpen_lt continuous_const continuous_norm

/-- [T26], Definition 3.2; the finite exterior is closed.
@isnad1 id=isclosed.0h0v.s4.67bc2a36f3a9 from=translated src=- shape=25b03439 vocab=3d9ae57e
-/
theorem isClosed_Oexterior : IsClosed Oexterior := by
  change IsClosed {z : ℂ | (1 : ℝ) ≤ ‖z‖}
  exact isClosed_le continuous_const continuous_norm

/-- [T26], Definition 3.2; the finite interior is contained in the finite exterior.
@isnad1 id=le.0h0v.s2.8bf75ec13d15 from=translated src=- shape=836e6cbb vocab=4dcdde35
-/
theorem OexteriorInterior_subset_Oexterior : OexteriorInterior ⊆ Oexterior := by
  intro z hz
  have hz' : (1 : ℝ) < ‖z‖ := hz
  exact hz'.le

/-- [T26], Definition 3.2; the unit circle is contained in the finite exterior.
@isnad1 id=mem.0h1v.s6.9491c3852df9 from=translated src=- shape=a19c4d96 vocab=641026c7
-/
theorem circle_subset_Oexterior : ∀ z : Circle, (z : ℂ) ∈ Oexterior := by
  intro z
  change (1 : ℝ) ≤ ‖(z : ℂ)‖
  rw [Circle.norm_coe]

/-- [T26], Definition 3.2; the finite exterior has the unique differentiability property.
@isnad1 id=uniquedi.0h0v.s5.238b6c249d94 from=translated src=- shape=54c8eceb vocab=4f56bdaa
-/
theorem uniqueDiffOn_Oexterior : UniqueDiffOn ℝ Oexterior := by
  intro z hz
  change (1 : ℝ) ≤ ‖z‖ at hz
  by_cases hzgt : 1 < ‖z‖
  · exact (isOpen_OexteriorInterior.uniqueDiffWithinAt hzgt).mono
      OexteriorInterior_subset_Oexterior
  have hzeq : ‖z‖ = 1 := le_antisymm (le_of_not_gt hzgt) hz
  have hball : Metric.closedBall (2 * z) 1 ⊆ Oexterior := by
    intro w hw
    change (1 : ℝ) ≤ ‖w‖
    have hdist : ‖w - 2 * z‖ ≤ 1 := by
      simpa [Metric.mem_closedBall, dist_eq_norm] using hw
    have hdist' : ‖2 * z - w‖ ≤ 1 := by
      simpa [norm_sub_rev] using hdist
    have hcenter : ‖(2 : ℂ) * z‖ = 2 := by
      rw [norm_mul, hzeq]
      norm_num
    have htriangle : ‖(2 : ℂ) * z‖ ≤ ‖w‖ + ‖(2 : ℂ) * z - w‖ := by
      calc
        ‖(2 : ℂ) * z‖ = ‖w + ((2 : ℂ) * z - w)‖ := by
          congr 1
          ring
        _ ≤ ‖w‖ + ‖(2 : ℂ) * z - w‖ := norm_add_le _ _
    linarith
  have hzball : z ∈ Metric.closedBall (2 * z) 1 := by
    rw [Metric.mem_closedBall, dist_eq_norm]
    have hsub : z - 2 * z = -z := by ring
    rw [hsub, norm_neg, hzeq]
  have hinterior : (interior (Metric.closedBall (2 * z) 1)).Nonempty := by
    refine ⟨2 * z, mem_interior_iff_mem_nhds.mpr ?_⟩
    exact Metric.closedBall_mem_nhds _ one_pos
  exact (uniqueDiffWithinAt_convex (convex_closedBall (2 * z) 1) hinterior
    (subset_closure hzball)).mono hball

/-- The circle exponential, regarded as a complex-valued real map, is smooth.
@isnad1 id=contdiff.0h0v.s7.55069388a719 from=translated src=- shape=84399fc0 vocab=30662176
-/
theorem contDiff_circle_map : ContDiff ℝ ∞ (fun θ : ℝ => (Circle.exp θ : ℂ)) := by
  rw [show (fun θ : ℝ => (Circle.exp θ : ℂ)) =
      (fun θ : ℝ => Complex.exp ((θ : ℂ) * Complex.I)) by
    funext θ
    exact Circle.coe_exp θ]
  exact Complex.contDiff_exp.comp (Complex.ofRealCLM.contDiff.mul contDiff_const)

/-- A crude common bound for the iterated real derivatives of the circle exponential at a point.
Only its existence is used: in the composition estimate below the outer constant is `0`, so the
inner constant is irrelevant and no closed form for these derivatives is needed.
@isnad1 id=ex.0h2v.s8.c89e2486a8a0 from=translated src=- shape=6b79a4c1 vocab=73b38af6
-/
theorem exists_bound_iteratedFDeriv_circle_map (n : ℕ) (θ : ℝ) :
    ∃ D : ℝ, 1 ≤ D ∧ ∀ i : ℕ, 1 ≤ i → i ≤ n →
      ‖iteratedFDeriv ℝ i (fun θ : ℝ => (Circle.exp θ : ℂ)) θ‖ ≤ D ^ i := by
  classical
  have hsum : (0 : ℝ) ≤ ∑ i ∈ Finset.range (n + 1),
      ‖iteratedFDeriv ℝ i (fun θ : ℝ => (Circle.exp θ : ℂ)) θ‖ :=
    Finset.sum_nonneg fun i _ => norm_nonneg _
  refine ⟨1 + ∑ i ∈ Finset.range (n + 1),
      ‖iteratedFDeriv ℝ i (fun θ : ℝ => (Circle.exp θ : ℂ)) θ‖, by linarith, ?_⟩
  intro i hi hin
  have hD1 : (1 : ℝ) ≤ 1 + ∑ i ∈ Finset.range (n + 1),
      ‖iteratedFDeriv ℝ i (fun θ : ℝ => (Circle.exp θ : ℂ)) θ‖ := by linarith
  have hmem : i ∈ Finset.range (n + 1) := Finset.mem_range.mpr (by omega)
  have hle : ‖iteratedFDeriv ℝ i (fun θ : ℝ => (Circle.exp θ : ℂ)) θ‖ ≤
      ∑ j ∈ Finset.range (n + 1),
        ‖iteratedFDeriv ℝ j (fun θ : ℝ => (Circle.exp θ : ℂ)) θ‖ :=
    Finset.single_le_sum
      (f := fun j : ℕ => ‖iteratedFDeriv ℝ j (fun θ : ℝ => (Circle.exp θ : ℂ)) θ‖)
      (fun j _ => norm_nonneg _) hmem
  calc ‖iteratedFDeriv ℝ i (fun θ : ℝ => (Circle.exp θ : ℂ)) θ‖
      ≤ 1 + ∑ j ∈ Finset.range (n + 1),
          ‖iteratedFDeriv ℝ j (fun θ : ℝ => (Circle.exp θ : ℂ)) θ‖ := by linarith
    _ ≤ (1 + ∑ j ∈ Finset.range (n + 1),
          ‖iteratedFDeriv ℝ j (fun θ : ℝ => (Circle.exp θ : ℂ)) θ‖) ^ i :=
        le_self_pow₀ hD1 (by omega)

/-- [T26], Definition 3.2; an analytic test function restricts smoothly to the circle angle.
@isnad1 id=contdiff.0h1v.s7.198d2eae09bf from=translated src=- shape=ddf94565 vocab=462311ee
-/
theorem AnalyticTestFn.contDiff_boundary (F : AnalyticTestFn) :
    ContDiff ℝ ∞ (fun θ : ℝ => F.toFun (Circle.exp θ)) := by
  have hmaps : MapsTo (fun θ : ℝ => (Circle.exp θ : ℂ)) Set.univ Oexterior := by
    intro θ hθ
    exact circle_subset_Oexterior (Circle.exp θ)
  have hcomp := F.contDiffOn.comp contDiff_circle_map.contDiffOn hmaps
  have heq : (fun θ : ℝ => F.toFun (Circle.exp θ)) =
      F.toFun ∘ fun θ : ℝ => (Circle.exp θ : ℂ) := rfl
  rw [heq]
  exact contDiffOn_univ.mp hcomp

/-- [T26], Definition 3.2; the analytic boundary restriction is periodic.
@isnad1 id=periodic.0h1v.s6.769a5d701b4c from=translated src=- shape=77a9ab35 vocab=caca0422
-/
theorem AnalyticTestFn.periodic_boundary (F : AnalyticTestFn) :
    Function.Periodic (fun θ : ℝ => F.toFun (Circle.exp θ)) (2 * Real.pi) := by
  intro θ
  simp only [Circle.exp_add, Circle.exp_two_pi, mul_one]

/-- [T26], Definition 3.2; the restriction `F ↦ F|_{S¹}`.-/
noncomputable def xRestrictS1 (F : AnalyticTestFn) : TestFn :=
  Classical.choose (exists_toAngle_eq F.contDiff_boundary F.periodic_boundary)

/-- [T26], Definition 3.2; the angle description of the restriction to `S¹`.
@isnad1 id=eq.0h1v.s6.3ade05f3ad51 from=translated src=- shape=c98a0c39 vocab=1c8ae5f7
-/
theorem toAngle_xRestrictS1 (F : AnalyticTestFn) :
    toAngle (xRestrictS1 F) = fun θ : ℝ => F.toFun (Circle.exp θ) := by
  exact (Classical.choose_spec (exists_toAngle_eq F.contDiff_boundary F.periodic_boundary))

/-- [T26], Definition 3.2; pointwise evaluation of the restriction to `S¹`.
@isnad1 id=eq.0h2v.s6.53f521bf4c60 from=translated src=- shape=52bbea6f vocab=707c9265
-/
theorem xRestrictS1_apply (F : AnalyticTestFn) (z : Circle) :
    xRestrictS1 F z = F.toFun z := by
  obtain ⟨θ, hθ⟩ := Circle.exp_surjective z
  have h := congrFun (toAngle_xRestrictS1 F) θ
  change xRestrictS1 F (Circle.exp θ) = F.toFun (Circle.exp θ) at h
  rw [hθ] at h
  exact h

/-- The analytic boundary function is flat whenever the circle exponential reaches `±1`.
@isnad1 id=eq.1h3v.s8.91a11bc17e58 from=translated src=- shape=1eefb53a vocab=3a14c790
-/
theorem AnalyticTestFn.iteratedDeriv_boundary_eq_zero (F : AnalyticTestFn) (n : ℕ) {θ : ℝ}
    (hθ : (Circle.exp θ : ℂ) = 1 ∨ (Circle.exp θ : ℂ) = -1) :
    iteratedDeriv n (fun θ : ℝ => F.toFun (Circle.exp θ)) θ = 0 := by
  have hC : ∀ i, i ≤ n →
      ‖iteratedFDerivWithin ℝ i F.toFun Oexterior (Circle.exp θ : ℂ)‖ ≤ 0 := by
    intro i hi
    rcases hθ with hθ | hθ
    · rw [hθ, F.flat_one i]
      simp
    · rw [hθ, F.flat_neg_one i]
      simp
  obtain ⟨D, hD1, hDbound⟩ := exists_bound_iteratedFDeriv_circle_map n θ
  have hD : ∀ i, 1 ≤ i → i ≤ n →
      ‖iteratedFDerivWithin ℝ i
          (fun θ : ℝ => (Circle.exp θ : ℂ)) Set.univ θ‖ ≤ D ^ i := by
    intro i hi hni
    rw [iteratedFDerivWithin_univ]
    exact hDbound i hi hni
  have hbound :
      ‖iteratedFDerivWithin ℝ n
          (F.toFun ∘ (fun θ : ℝ => (Circle.exp θ : ℂ))) Set.univ θ‖ ≤
        (Nat.factorial n : ℝ) * (0 : ℝ) * D ^ n :=
    norm_iteratedFDerivWithin_comp_le (𝕜 := ℝ) (g := F.toFun)
      (f := fun θ : ℝ => (Circle.exp θ : ℂ)) (n := n) (s := Set.univ) (t := Oexterior)
      (x := θ) F.contDiffOn contDiff_circle_map.contDiffOn (by exact_mod_cast le_top)
      uniqueDiffOn_Oexterior uniqueDiffOn_univ
      (by
        intro x hx
        exact circle_subset_Oexterior (Circle.exp x)) (mem_univ θ) (C := 0) (D := D) hC hD
  have hnorm :
      ‖iteratedDeriv n
          (F.toFun ∘ (fun θ : ℝ => (Circle.exp θ : ℂ))) θ‖ ≤ 0 := by
    rw [← norm_iteratedFDeriv_eq_norm_iteratedDeriv]
    simpa [iteratedFDerivWithin_univ] using hbound
  have hzero : iteratedDeriv n
      (F.toFun ∘ (fun θ : ℝ => (Circle.exp θ : ℂ))) θ = 0 :=
    norm_eq_zero.mp (le_antisymm hnorm (norm_nonneg _))
  have heq : (fun θ : ℝ => F.toFun (Circle.exp θ)) =
      F.toFun ∘ fun θ : ℝ => (Circle.exp θ : ℂ) := rfl
  rw [heq]
  exact hzero

/-- [T26], Definition 3.2; the restriction to the circle is endpoint-flat.
@isnad1 id=isendpoi.0h1v.s2.8ffec4ee9904 from=translated src=- shape=76a08d12 vocab=5c100dab
-/
theorem AnalyticTestFn.isEndpointFlat (F : AnalyticTestFn) :
    IsEndpointFlat (xRestrictS1 F) := by
  refine ⟨fun n => ?_, fun n => ?_⟩
  · rw [toAngle_xRestrictS1]
    apply F.iteratedDeriv_boundary_eq_zero n
    left
    simp
  · rw [toAngle_xRestrictS1]
    apply F.iteratedDeriv_boundary_eq_zero n
    right
    simp [Circle.coe_exp, Complex.exp_pi_mul_I]

/-- [T26], Definition 3.2; the restriction to `I₊`, extended by zero.-/
noncomputable def xRestrictUpper (F : AnalyticTestFn) : TestFn :=
  splitUpper (xRestrictS1 F) F.isEndpointFlat

/-- [T26], Definition 3.2; the restriction to `I₋`, extended by zero.-/
noncomputable def xRestrictLower (F : AnalyticTestFn) : TestFn :=
  splitLower (xRestrictS1 F) F.isEndpointFlat

/-- [T26], Definition 3.2; the upper restriction has upper semicircle support.
@isnad1 id=suppuppe.0h1v.s2.c407c1ae55a1 from=translated src=- shape=76a08d12 vocab=489ca998
-/
theorem xRestrictUpper_supp (F : AnalyticTestFn) : SuppUpper (xRestrictUpper F) := by
  exact suppUpper_splitUpper (xRestrictS1 F) F.isEndpointFlat

/-- [T26], Definition 3.2; the lower restriction has lower semicircle support.
@isnad1 id=supplowe.0h1v.s2.1a61606705ae from=translated src=- shape=76a08d12 vocab=687185d4
-/
theorem xRestrictLower_supp (F : AnalyticTestFn) : SuppLower (xRestrictLower F) := by
  exact suppLower_splitLower (xRestrictS1 F) F.isEndpointFlat

/-- [T26], Definition 3.2; the two semicircle restrictions sum to the circle restriction.
@isnad1 id=eq.0h1v.s4.5427510590bb from=translated src=- shape=c45662b3 vocab=ec9d6d85
-/
theorem xRestrict_split (F : AnalyticTestFn) :
    xRestrictS1 F = xRestrictUpper F + xRestrictLower F := by
  exact (splitUpper_add_splitLower (xRestrictS1 F) F.isEndpointFlat).symm

/-- [T26], Definition 3.2; the representative of `F` read on the Riemann sphere, with `∞ ↦ 0`
(the value `F(∞)` of the source, see `AnalyticTestFn.differentiableAt_inv`).  This is exported for
Issue #8, whose argument `vApplyNegSphere τ z` lies in `Oset`; on `Oset` the value depends only on
the element of `𝓧` and not on the representative, by `evalSphere_congr` together with
`eqOn_Oexterior_of_xRestrictS1_eq`.  Off `Oset` — that is, inside the open unit disc — it reads the
representative's arbitrary values and carries no meaning.-/
def AnalyticTestFn.evalSphere (F : AnalyticTestFn) : OnePoint ℂ → ℂ :=
  fun p => p.elim 0 F.toFun

/-- [T26], Definition 3.2; evaluation of `𝓧` at the point at infinity.
@isnad1 id=eq.0h1v.s3.d472b0c3bd39 from=translated src=- shape=0d507416 vocab=92689008
-/
@[simp] theorem AnalyticTestFn.evalSphere_infty (F : AnalyticTestFn) :
    F.evalSphere OnePoint.infty = 0 := rfl

/-- [T26], Definition 3.2; evaluation of `𝓧` at a finite point of the sphere.
@isnad1 id=eq.0h2v.s3.bd37ea8b5cca from=translated src=- shape=50a971f2 vocab=7284bbaf
-/
@[simp] theorem AnalyticTestFn.evalSphere_coe (F : AnalyticTestFn) (w : ℂ) :
    F.evalSphere (w : OnePoint ℂ) = F.toFun w := rfl

/-- [T26], Definition 3.2; on `𝕆` the sphere evaluation depends only on the values of the
representative there, hence — with `eqOn_Oexterior_of_xRestrictS1_eq` — only on `F|_{S¹}`.
@isnad1 id=eq.2h3v.s5.5bdb4c119c96 from=translated src=- shape=fa39ccf3 vocab=539f8134
-/
theorem AnalyticTestFn.evalSphere_congr {F G : AnalyticTestFn}
    (h : Set.EqOn F.toFun G.toFun Oexterior) {p : OnePoint ℂ} (hp : p ∈ Oset) :
    F.evalSphere p = G.evalSphere p := by
  rcases hp with hp | ⟨w, hw, rfl⟩
  · rw [hp]
    rfl
  · show F.toFun w = G.toFun w
    exact h hw

/-- [T26], Definition 3.2; `F` is holomorphic at `∞` with value `0`: the inverted function
extends holomorphically over the origin.
@isnad1 id=differen.0h1v.s6.af9e4ab6f410 from=translated src=- shape=de8ae920 vocab=df5a350a
-/
theorem AnalyticTestFn.differentiableAt_inv (F : AnalyticTestFn) :
    DifferentiableAt ℂ (fun w : ℂ => if w = 0 then 0 else F.toFun w⁻¹) 0 := by
  let q : ℂ → ℂ := fun w => if w = 0 then 0 else F.toFun w⁻¹
  have hd : ∀ᶠ z in 𝓝[≠] (0 : ℂ), DifferentiableAt ℂ q z := by
    filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds (0 : ℂ) one_pos)] with z hz0 hzball
    have hz0' : z ≠ 0 := by
      simpa only [mem_compl_iff, mem_singleton_iff] using hz0
    have hzball' : dist z 0 < (1 : ℝ) := by
      exact hzball
    have hzball'' : ‖z‖ < 1 := by
      simpa [dist_eq_norm] using hzball'
    have hinvnorm : 1 < ‖z⁻¹‖ := by
      rw [norm_inv]
      exact (one_lt_inv₀ (norm_pos_iff.mpr hz0')).2 hzball''
    have hF : DifferentiableAt ℂ F.toFun z⁻¹ :=
      (F.differentiableOn z⁻¹ hinvnorm).differentiableAt
        (isOpen_OexteriorInterior.mem_nhds hinvnorm)
    have hcomp : DifferentiableAt ℂ (F.toFun ∘ (fun w : ℂ => w⁻¹)) z :=
      hF.comp z (differentiableAt_inv_iff.mpr hz0')
    apply hcomp.congr_of_eventuallyEq
    filter_upwards [isOpen_ne.mem_nhds hz0'] with w hw
    simp [q, hw]
  have hinv : Tendsto (fun w : ℂ => w⁻¹) (𝓝[≠] (0 : ℂ)) (cocompact ℂ) := by
    rw [← Metric.cobounded_eq_cocompact (α := ℂ)]
    exact Filter.tendsto_inv₀_nhdsNE_zero
  have hlim : Tendsto (F.toFun ∘ (fun w : ℂ => w⁻¹))
      (𝓝[≠] (0 : ℂ)) (nhds 0) := F.tendsto_zero.comp hinv
  have hq_lim : Tendsto q (𝓝[≠] (0 : ℂ)) (nhds 0) := by
    refine Tendsto.congr' ?_ hlim
    filter_upwards [self_mem_nhdsWithin] with z hz
    have hz0' : z ≠ 0 := by
      simpa only [mem_compl_iff, mem_singleton_iff] using hz
    simp [q, hz0']
  have hq_cont : ContinuousAt q 0 := by
    rw [continuousAt_iff_punctured_nhds]
    simpa [q] using hq_lim
  -- The weak removable-singularity theorem applies directly: `F.tendsto_zero` gives
  -- continuity of the punctured inverse composition at the value assigned at zero.
  have hq_diff : DifferentiableAt ℂ q 0 :=
    (Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt
      hd hq_cont).differentiableAt
  simpa [q] using hq_diff

/-- [T26], Definition 3.2; the inversion `w ↦ F(w⁻¹)` of an element of `𝓧`, filled in at the
origin by `F(∞) = 0`.  It is holomorphic on the open unit disc and continuous up to its boundary,
which is what makes the restriction `F ↦ F|_{S¹}` injective on `𝕆`.-/
noncomputable def AnalyticTestFn.invExt (F : AnalyticTestFn) : ℂ → ℂ :=
  fun w => if w = 0 then 0 else F.toFun w⁻¹

/--
@isnad1 id=eq.1h2v.s4.fc26ad7f3bf3 from=translated src=- shape=13073f1a vocab=e9033c97
-/
theorem AnalyticTestFn.invExt_of_ne {F : AnalyticTestFn} {w : ℂ} (hw : w ≠ 0) :
    F.invExt w = F.toFun w⁻¹ := by
  rw [AnalyticTestFn.invExt, ite_eq_right hw]

/-- The inverted function is holomorphic inside the unit disc and continuous up to its closure.
@isnad1 id=diffcont.0h1v.s5.5eeb88b6ffbf from=translated src=- shape=4ee979c2 vocab=2203fb99
-/
theorem AnalyticTestFn.diffContOnCl_invExt (F : AnalyticTestFn) :
    DiffContOnCl ℂ F.invExt (Metric.ball (0 : ℂ) 1) := by
  constructor
  · intro w hw
    by_cases hw0 : w = 0
    · subst w
      exact (F.differentiableAt_inv).differentiableWithinAt
    · have hnorm : ‖w‖ < 1 := by simpa [Metric.mem_ball, dist_eq_norm] using hw
      have hinv : (1 : ℝ) < ‖w⁻¹‖ := by
        rw [norm_inv]
        exact (one_lt_inv₀ (norm_pos_iff.mpr hw0)).2 hnorm
      have hF : DifferentiableAt ℂ F.toFun w⁻¹ :=
        (F.differentiableOn w⁻¹ hinv).differentiableAt
          (isOpen_OexteriorInterior.mem_nhds hinv)
      have hcomp : DifferentiableAt ℂ (fun u : ℂ => F.toFun u⁻¹) w :=
        hF.comp w (differentiableAt_inv_iff.mpr hw0)
      refine (hcomp.congr_of_eventuallyEq ?_).differentiableWithinAt
      filter_upwards [isOpen_ne.mem_nhds hw0] with u hu
      rw [AnalyticTestFn.invExt_of_ne hu]
  · rw [closure_ball (0 : ℂ) one_ne_zero]
    intro w hw
    have hnorm : ‖w‖ ≤ 1 := by simpa [Metric.mem_closedBall, dist_eq_norm] using hw
    by_cases hw0 : w = 0
    · subst w
      exact (F.differentiableAt_inv).continuousAt.continuousWithinAt
    · have hnormpos : 0 < ‖w‖ := norm_pos_iff.mpr hw0
      have hinv : (1 : ℝ) ≤ ‖w⁻¹‖ := by
        rw [norm_inv]
        exact (one_le_inv₀ hnormpos).2 hnorm
      set t : Set ℂ := Metric.closedBall (0 : ℂ) 1 ∩ {u : ℂ | u ≠ 0} with ht
      have hmaps : Set.MapsTo (fun u : ℂ => u⁻¹) t Oexterior := by
        intro u hu
        have hu0 : u ≠ 0 := hu.2
        have hupos : 0 < ‖u‖ := norm_pos_iff.mpr hu0
        have hule : ‖u‖ ≤ 1 := by
          simpa [Metric.mem_closedBall, dist_eq_norm] using hu.1
        show (1 : ℝ) ≤ ‖u⁻¹‖
        rw [norm_inv]
        exact (one_le_inv₀ hupos).2 hule
      have hF : ContinuousWithinAt F.toFun Oexterior w⁻¹ :=
        (F.contDiffOn.continuousOn) w⁻¹ hinv
      have hinvcont : ContinuousWithinAt (fun u : ℂ => u⁻¹) t w :=
        (continuousAt_inv₀ hw0).continuousWithinAt
      have hcomp : ContinuousWithinAt (fun u : ℂ => F.toFun u⁻¹) t w :=
        hF.comp hinvcont hmaps
      have hcongr : ContinuousWithinAt F.invExt t w := by
        refine hcomp.congr (fun u hu => ?_) ?_
        · rw [AnalyticTestFn.invExt_of_ne hu.2]
        · rw [AnalyticTestFn.invExt_of_ne hw0]
      have hmem : t ∈ nhdsWithin w (Metric.closedBall (0 : ℂ) 1) := by
        rw [ht]
        exact inter_mem_nhdsWithin _ (isOpen_ne.mem_nhds hw0)
      exact hcongr.mono_of_mem_nhdsWithin hmem

/-- [T26], Definition 3.2; the restriction `F ↦ F|_{S¹}` is injective on `𝕆`: two elements of the
class whose circle restrictions agree agree at every point of `𝕆`.  The source states this (via
Schwarz reflection and the identity theorem) in order to regard `𝓧` as a subset of `C^∞(S¹)`; here
it is proved from the maximum modulus principle applied to the inverted functions, and it is what
makes the values of the representative `toFun` inside the open unit disc irrelevant.
@isnad1 id=eqon.1h2v.s4.b62f24b7f4ad from=translated src=- shape=ab91b775 vocab=48d70b35
-/
theorem eqOn_Oexterior_of_xRestrictS1_eq {F G : AnalyticTestFn}
    (h : xRestrictS1 F = xRestrictS1 G) : Set.EqOn F.toFun G.toFun Oexterior := by
  have hfront : Set.EqOn F.invExt G.invExt (frontier (Metric.ball (0 : ℂ) 1)) := by
    rw [frontier_ball (0 : ℂ) one_ne_zero]
    intro w hw
    have hnorm : ‖w‖ = 1 := by simpa [Metric.mem_sphere, dist_eq_norm] using hw
    have hw0 : w ≠ 0 := by
      intro h0
      rw [h0] at hnorm
      norm_num at hnorm
    have hcirc : ‖w⁻¹‖ = 1 := by rw [norm_inv, hnorm, inv_one]
    have hmem : w⁻¹ ∈ Metric.sphere (0 : ℂ) 1 := by
      simpa [Metric.mem_sphere, dist_eq_norm] using hcirc
    have hval : F.toFun w⁻¹ = G.toFun w⁻¹ := by
      have hF := xRestrictS1_apply F ⟨w⁻¹, hmem⟩
      have hG := xRestrictS1_apply G ⟨w⁻¹, hmem⟩
      rw [← hF, ← hG, h]
    rw [AnalyticTestFn.invExt_of_ne hw0, AnalyticTestFn.invExt_of_ne hw0, hval]
  have hball : Set.EqOn F.invExt G.invExt (Metric.ball (0 : ℂ) 1) :=
    Complex.eqOn_of_eqOn_frontier (Metric.isBounded_ball) F.diffContOnCl_invExt
      G.diffContOnCl_invExt hfront
  intro z hz
  have hz1 : (1 : ℝ) ≤ ‖z‖ := hz
  rcases eq_or_lt_of_le hz1 with hz_eq | hz_lt
  · have hmem : z ∈ Metric.sphere (0 : ℂ) 1 := by
      simpa [Metric.mem_sphere, dist_eq_norm] using hz_eq.symm
    have hF := xRestrictS1_apply F ⟨z, hmem⟩
    have hG := xRestrictS1_apply G ⟨z, hmem⟩
    rw [← hF, ← hG, h]
  · have hz0 : z ≠ 0 := by
      intro h0
      rw [h0] at hz1
      norm_num at hz1
    have hzinv : z⁻¹ ∈ Metric.ball (0 : ℂ) 1 := by
      have : ‖z⁻¹‖ < 1 := by
        rw [norm_inv]
        exact inv_lt_one_of_one_lt₀ hz_lt
      simpa [Metric.mem_ball, dist_eq_norm] using this
    have hval := hball hzinv
    have hzz : (z⁻¹)⁻¹ = z := inv_inv z
    have hz0' : z⁻¹ ≠ 0 := inv_ne_zero hz0
    rw [AnalyticTestFn.invExt_of_ne hz0', AnalyticTestFn.invExt_of_ne hz0', hzz] at hval
    exact hval

end

end MobiusCPT
