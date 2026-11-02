import Tengoku.HodgeStructuresLean4.HodgePilot.PolydiscCauchy2
import Tengoku.Seed.Analysis.Complex.Basic
import Tengoku.Seed.Analysis.Complex.RealDeriv
import Tengoku.Seed.Analysis.Calculus.DifferentialForm.Basic
import Tengoku.Seed.Analysis.Normed.Module.Alternating.Curry
import Tengoku.Seed.Analysis.Calculus.ParametricIntervalIntegral
import Tengoku.Seed.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Tengoku.Seed.Analysis.Calculus.FDeriv.Analytic
import Tengoku.Seed.Analysis.Calculus.FDeriv.CompCLM
import Tengoku.Seed.Analysis.Calculus.Deriv.Pow
import Tengoku.Seed.Analysis.Calculus.Deriv.Mul
import Tengoku.Seed.Topology.Algebra.Module.Alternating.Topology

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The holomorphic Poincaré lemma on polydiscs in `ℂⁿ` (positive degrees)

Stage 3 of the several-complex-variables campaign (route P1 of
`wall1_poincare_design_memo.md` §4.4): **exactness of closed holomorphic
forms of positive degree on polydiscs in every dimension**, at the level
of unbundled forms.  If
`ω : (Fin n → ℂ) → ((Fin n → ℂ) [⋀^Fin (q+1)]→L[ℂ] F)` is a (jointly)
analytic `(q+1)`-form on an open polydisc with `extDeriv ω = 0` on the
polydisc, then `ω = extDeriv η` there for a (jointly) analytic `q`-form
`η`, for every `n`, every `q`, and every complete normed `ℂ`-space `F`.

## Route

Instead of the variable-by-variable induction sketched in the design
memo, this file runs the **radial (star-shaped) homotopy** once, in all
dimensions and degrees simultaneously: the primitive is the radial
contraction

`(radialContract c ω) z = ∫ t in 0..1, tᑫ • (ω (c + t•(z-c))).curryLeft (z - c)`,

whose exterior derivative is computed by differentiating under the
integral sign (`intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le`),
the Cartan-style alternating-sum identity
(`ContinuousAlternatingMap.alternatizeUncurryFin_curryLeft` plus the
closedness of `ω`), and the fundamental theorem of calculus along the
radial segments.  The **joint analyticity of the primitive** is exactly
what stage 2 unlocked: the radial contraction is jointly complex
differentiable by the parametric-integral theorem, and jointly
differentiable functions on open subsets of `ℂⁿ` are analytic
(`analyticOnNhd_of_differentiableOn` below, from the stage-2 polydisc
power series `HodgePilot.PolydiscCauchy.analyticAt_of_differentiableOn_closedPolydisc`).

All statements are proved for any open set that is star-shaped about `c`
under complex disc scaling (`DiscStar`), and instantiated on open
polydiscs and on sup-norm balls (which are the equal-radii polydiscs).

## Main declarations

* `HodgePilot.PolydiscPoincare.analyticOnNhd_of_differentiableOn`:
  a function `(Fin n → ℂ) → F` complex differentiable on an *open* set
  is jointly analytic there (several variables, joint hypothesis).
* `HodgePilot.PolydiscPoincare.radialContract`: the radial-contraction
  operator taking `(q+1)`-forms to `q`-forms.
* `HodgePilot.PolydiscPoincare.hasFDerivAt_radialContract`,
  `analyticOnNhd_radialContract`: its joint differentiability (with the
  differentiated-under-the-integral formula) and joint analyticity.
* `HodgePilot.PolydiscPoincare.extDeriv_radialContract_of_closed`: for a
  closed analytic `(q+1)`-form `ω` on a `DiscStar` open set,
  `extDeriv (radialContract c ω) = ω` there.
* `HodgePilot.PolydiscPoincare.exists_primitive_form_polydisc` /
  `exists_primitive_form_ball` / `exists_primitive_form_locally`:
  the existence statements — every closed analytic form of positive
  degree on an open polydisc (resp. ball; resp. locally, on a ball
  around each point of any open set) is the exterior derivative of an
  analytic form.
* `HodgePilot.PolydiscPoincare.const_of_extDeriv_eq_zero_ball`: degree
  `0` — a `0`-form on a ball with vanishing exterior derivative is
  constant (all dimensions).

## Scope discipline

This module proves **local exactness statements for unbundled
holomorphic forms on polydiscs, sup-norm balls, and `DiscStar` open
subsets of `ℂⁿ`, exactly as stated — nothing more**.  All hypotheses
are *joint* analyticity (no Osgood/Hartogs-type weakening to separate
holomorphy is provided or claimed).  It makes **no sheaf-level
statement**: no sheaf morphism, no stalk statement, no quasi-isomorphism,
and no "resolution" claim of any kind (the transport of these existence
statements into the sheaf layer of `HodgePilot.StalkDetect` is a later,
separate stage).  No comparison-type statement of any kind is made.  The
one-variable disc statements of `HodgePilot.HolomorphicSheaf` and
`HodgePilot.DiscResolution` are untouched.

## Credits

The differential-forms layer (`extDeriv`, `curryLeft`,
`alternatizeUncurryFin`) is Mathlib's 2025 normed-space forms layer
(Kudryashov–Lindauer–Wieser); the parametric interval integral is
Mathlib's `Analysis/Calculus/ParametricIntervalIntegral`; the polydisc
power series consumed here is stage 2, `HodgePilot.PolydiscCauchy2`.
-/

open Metric Set MeasureTheory ContinuousAlternatingMap

namespace HodgePilot
namespace PolydiscPoincare

open PolydiscCauchy

variable {n q : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]

/-! ## Openness of polydiscs and the sup-norm dictionary -/

/-- The open polydisc is open.-/
theorem isOpen_polydisc (c : Fin n → ℂ) (R : Fin n → ℝ) : IsOpen (polydisc c R) :=
  isOpen_set_pi finite_univ fun _ _ => isOpen_ball

/-- Closed sup-norm balls in `Fin n → ℂ` are the closed polydiscs with equal
radii.-/
theorem closedBall_eq_closedPolydisc (x : Fin n → ℂ) {r : ℝ} (hr : 0 ≤ r) :
    closedBall x r = closedPolydisc x (fun _ => r) := by
  ext z
  rw [mem_closedBall, dist_pi_le_iff hr, mem_closedPolydisc]
  exact forall_congr' fun i => by rw [mem_closedBall]

/-- **Complex differentiability implies joint analyticity on open subsets of
`ℂⁿ`** (several variables): a function `(Fin n → ℂ) → F` that is complex
differentiable (jointly, in the Fréchet sense) on an open set is analytic at
every point of the set.  Around each point the open set contains a closed
sup-norm ball, i.e. a closed polydisc, and the stage-2 Cauchy power series
(`HodgePilot.PolydiscCauchy.analyticAt_of_differentiableOn_closedPolydisc`)
applies.  The hypothesis is *joint* differentiability; no separate-variable
weakening is claimed.-/
theorem analyticOnNhd_of_differentiableOn [CompleteSpace F] {f : (Fin n → ℂ) → F}
    {s : Set (Fin n → ℂ)} (hs : IsOpen s) (hf : DifferentiableOn ℂ f s) :
    AnalyticOnNhd ℂ f s := by
  intro z hz
  obtain ⟨r, hr0, hball⟩ := Metric.isOpen_iff.mp hs z hz
  have hsub : closedPolydisc z (fun _ => r / 2) ⊆ s := by
    rw [← closedBall_eq_closedPolydisc z (by positivity)]
    exact (closedBall_subset_ball (half_lt_self hr0)).trans hball
  exact analyticAt_of_differentiableOn_closedPolydisc (hf.mono hsub) fun _ => half_pos hr0

/-! ## Star-shaped sets under complex disc scaling -/

/-- A set `U` is *disc-star-shaped* about `c` if it absorbs the complex disc
scalings of its points towards `c`: for `z ∈ U` and `‖s‖ ≤ 1`, the point
`c + s • (z - c)` is in `U`.  Open polydiscs and balls centred at `c` have
this property; it is what the radial homotopy needs.-/
def DiscStar (c : Fin n → ℂ) (U : Set (Fin n → ℂ)) : Prop :=
  ∀ z ∈ U, ∀ s : ℂ, ‖s‖ ≤ 1 → c + s • (z - c) ∈ U

/-- Polydiscs absorb complex disc scalings about their centre.-/
theorem discStar_polydisc (c : Fin n → ℂ) (R : Fin n → ℝ) :
    DiscStar c (polydisc c R) := by
  intro z hz s hs
  refine mem_polydisc.2 fun i => ?_
  rw [mem_ball_iff_norm]
  have h1 : (c + s • (z - c)) i - c i = s * (z i - c i) := by
    simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    ring
  rw [h1, norm_mul]
  calc ‖s‖ * ‖z i - c i‖ ≤ 1 * ‖z i - c i‖ :=
        mul_le_mul_of_nonneg_right hs (norm_nonneg _)
    _ = ‖z i - c i‖ := one_mul _
    _ < R i := mem_ball_iff_norm.1 (mem_polydisc.1 hz i)

/-- Balls absorb complex disc scalings about their centre.-/
theorem discStar_ball (c : Fin n → ℂ) (r : ℝ) : DiscStar c (ball c r) := by
  intro z hz s hs
  rw [mem_ball_iff_norm] at hz ⊢
  rw [add_sub_cancel_left, norm_smul]
  calc ‖s‖ * ‖z - c‖ ≤ 1 * ‖z - c‖ := mul_le_mul_of_nonneg_right hs (norm_nonneg _)
    _ = ‖z - c‖ := one_mul _
    _ < r := hz

/-- The scaled radial segment map: `segMap c t z = c + t • (z - c)`.-/
def segMap (c : Fin n → ℂ) (t : ℝ) (z : Fin n → ℂ) : Fin n → ℂ :=
  c + (t : ℂ) • (z - c)

theorem segMap_mem {c : Fin n → ℂ} {U : Set (Fin n → ℂ)} (hst : DiscStar c U)
    {z : Fin n → ℂ} (hz : z ∈ U) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    segMap c t z ∈ U := by
  refine hst z hz _ ?_
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht.1]
  exact ht.2

@[simp] theorem segMap_one (c z : Fin n → ℂ) : segMap c 1 z = z := by
  simp only [segMap, Complex.ofReal_one, one_smul]
  ring

theorem continuousOn_segMap (c : Fin n → ℂ) (z : Fin n → ℂ) :
    ContinuousOn (fun t : ℝ => segMap c t z) (Icc 0 1) :=
  (continuous_const.add (Complex.continuous_ofReal.smul continuous_const)).continuousOn

/-! ## Alternating-map utilities -/

/-- `removeNth` at a successor index commutes with `Fin.cons`.-/
theorem removeNth_succ_cons {α : Type*} (x : α) (v : Fin (q + 1) → α) (i : Fin (q + 1)) :
    Fin.removeNth (α := fun _ => α) i.succ (Fin.cons x v) =
      Fin.cons x (Fin.removeNth i v) := by
  funext k
  induction k using Fin.cases with
  | zero => simp [Fin.removeNth_apply]
  | succ m => simp [Fin.removeNth_apply, Fin.succ_succAbove_succ]

/-- Currying at the 0-th slot and evaluating at a fixed vector `u`, as a
continuous linear map on continuous alternating maps.-/
noncomputable def curryApplyCLM (u : Fin n → ℂ) :
    ((Fin n → ℂ) [⋀^Fin (q + 1)]→L[ℂ] F) →L[ℂ] ((Fin n → ℂ) [⋀^Fin q]→L[ℂ] F) :=
  LinearMap.mkContinuous
    { toFun := fun A => A.curryLeft u
      map_add' := fun A B => by simp
      map_smul' := fun c A => by simp }
    ‖u‖ (fun A => by
      calc ‖A.curryLeft u‖ ≤ ‖A.curryLeft‖ * ‖u‖ := (A.curryLeft).le_opNorm u
      _ = ‖u‖ * ‖A‖ := by rw [norm_curryLeft]; ring)

@[simp] theorem curryApplyCLM_apply (u : Fin n → ℂ)
    (A : (Fin n → ℂ) [⋀^Fin (q + 1)]→L[ℂ] F) :
    curryApplyCLM u A = A.curryLeft u := rfl

/-- `(A, u) ↦ A.curryLeft u` is a bounded bilinear map (with constant `1`).-/
theorem isBoundedBilinearMap_curryApply :
    IsBoundedBilinearMap ℂ (fun p :
      ((Fin n → ℂ) [⋀^Fin (q + 1)]→L[ℂ] F) × (Fin n → ℂ) => p.1.curryLeft p.2) where
  add_left A B u := by simp
  smul_left a A u := by simp
  add_right A u v := by simp
  smul_right a A u := by simp
  bound := ⟨1, one_pos, fun A u => by
    rw [one_mul]
    calc ‖A.curryLeft u‖ ≤ ‖A.curryLeft‖ * ‖u‖ := (A.curryLeft).le_opNorm u
    _ = ‖A‖ * ‖u‖ := by rw [norm_curryLeft]⟩

/-! ## The radial contraction -/

section Radial

variable {c : Fin n → ℂ} {U : Set (Fin n → ℂ)}
variable {ω : (Fin n → ℂ) → ((Fin n → ℂ) [⋀^Fin (q + 1)]→L[ℂ] F)}

/-- The integrand of the radial contraction:
`t ↦ tᑫ • (ω (c + t•(z-c))).curryLeft (z - c)`.-/
noncomputable def radialIntegrand (c : Fin n → ℂ)
    (ω : (Fin n → ℂ) → ((Fin n → ℂ) [⋀^Fin (q + 1)]→L[ℂ] F)) (t : ℝ) (z : Fin n → ℂ) :
    (Fin n → ℂ) [⋀^Fin q]→L[ℂ] F :=
  (t : ℂ) ^ q • (ω (segMap c t z)).curryLeft (z - c)

/-- The `z`-derivative of the radial integrand (for `ω` differentiable at
`segMap c t z`).-/
noncomputable def radialIntegrandFDeriv (c : Fin n → ℂ)
    (ω : (Fin n → ℂ) → ((Fin n → ℂ) [⋀^Fin (q + 1)]→L[ℂ] F)) (t : ℝ) (z : Fin n → ℂ) :
    (Fin n → ℂ) →L[ℂ] ((Fin n → ℂ) [⋀^Fin q]→L[ℂ] F) :=
  (t : ℂ) ^ (q + 1) • ((curryApplyCLM (z - c)).comp (fderiv ℂ ω (segMap c t z))) +
    (t : ℂ) ^ q • (ω (segMap c t z)).curryLeft

/-- **The radial contraction**: the candidate primitive of a `(q+1)`-form,
`(radialContract c ω) z = ∫ t in 0..1, tᑫ • (ω (c + t•(z-c))).curryLeft (z - c)`.-/
noncomputable def radialContract (c : Fin n → ℂ)
    (ω : (Fin n → ℂ) → ((Fin n → ℂ) [⋀^Fin (q + 1)]→L[ℂ] F)) (z : Fin n → ℂ) :
    (Fin n → ℂ) [⋀^Fin q]→L[ℂ] F :=
  ∫ t in (0 : ℝ)..1, radialIntegrand c ω t z

/-- Continuity of the radial integrand in the parameter `t`.-/
theorem continuousOn_radialIntegrand (hst : DiscStar c U) (hω : AnalyticOnNhd ℂ ω U)
    {z : Fin n → ℂ} (hz : z ∈ U) :
    ContinuousOn (fun t : ℝ => radialIntegrand c ω t z) (Icc 0 1) := by
  have hmaps : MapsTo (fun t : ℝ => segMap c t z) (Icc 0 1) U :=
    fun t ht => segMap_mem hst hz ht
  have hωγ : ContinuousOn (fun t : ℝ => ω (segMap c t z)) (Icc 0 1) :=
    hω.continuousOn.comp (continuousOn_segMap c z) hmaps
  have hcurry : ContinuousOn
      (fun t : ℝ => (ω (segMap c t z)).curryLeft (z - c)) (Icc 0 1) :=
    (curryApplyCLM (z - c)).continuous.comp_continuousOn hωγ
  exact (Complex.continuous_ofReal.pow q).continuousOn.smul hcurry

theorem intervalIntegrable_radialIntegrand (hst : DiscStar c U)
    (hω : AnalyticOnNhd ℂ ω U) {z : Fin n → ℂ} (hz : z ∈ U) :
    IntervalIntegrable (fun t : ℝ => radialIntegrand c ω t z) volume 0 1 := by
  apply ContinuousOn.intervalIntegrable
  rw [Set.uIcc_of_le zero_le_one]
  exact continuousOn_radialIntegrand hst hω hz

/-- Pointwise differentiability of the radial integrand in `z`, with
derivative `radialIntegrandFDeriv` (through the bounded-bilinear-map calculus
of `curryLeft`).-/
theorem hasFDerivAt_radialIntegrand (hst : DiscStar c U) (hω : AnalyticOnNhd ℂ ω U)
    {z : Fin n → ℂ} (hz : z ∈ U) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    HasFDerivAt (fun y => radialIntegrand c ω t y) (radialIntegrandFDeriv c ω t z) z := by
  have hmem : segMap c t z ∈ U := segMap_mem hst hz ht
  have hA : HasFDerivAt ω (fderiv ℂ ω (segMap c t z)) (segMap c t z) :=
    (hω _ hmem).differentiableAt.hasFDerivAt
  have hsub : HasFDerivAt (fun y : Fin n → ℂ => y - c)
      (ContinuousLinearMap.id ℂ (Fin n → ℂ)) z := (hasFDerivAt_id z).sub_const c
  have hseg : HasFDerivAt (fun y => segMap c t y)
      ((t : ℂ) • ContinuousLinearMap.id ℂ (Fin n → ℂ)) z := by
    have h2 := hsub.const_smul ((t : ℂ))
    exact h2.const_add c
  have hωσ : HasFDerivAt (fun y => ω (segMap c t y))
      ((fderiv ℂ ω (segMap c t z)).comp
        ((t : ℂ) • ContinuousLinearMap.id ℂ (Fin n → ℂ))) z := hA.comp z hseg
  have hpair := hωσ.prodMk hsub
  have hbil := (isBoundedBilinearMap_curryApply (n := n) (q := q) (F := F)).hasFDerivAt
    (ω (segMap c t z), z - c)
  have hcomp := hbil.comp z hpair
  have hfinal := hcomp.const_smul ((t : ℂ) ^ q)
  have heq : (t : ℂ) ^ q •
      (((isBoundedBilinearMap_curryApply (n := n) (q := q) (F := F)).deriv
          (ω (segMap c t z), z - c)).comp
        (((fderiv ℂ ω (segMap c t z)).comp
            ((t : ℂ) • ContinuousLinearMap.id ℂ (Fin n → ℂ))).prod
          (ContinuousLinearMap.id ℂ (Fin n → ℂ)))) =
      radialIntegrandFDeriv c ω t z := by
    ext w
    simp only [radialIntegrandFDeriv, _root_.smul_apply, _root_.add_apply,
      ContinuousLinearMap.coe_comp, Function.comp_apply,
      ContinuousLinearMap.prod_apply, ContinuousLinearMap.coe_id', id_eq,
      IsBoundedBilinearMap.deriv_apply, map_smul, curryLeft_smul,
      curryApplyCLM_apply, smul_add]
    rw [smul_smul ((t : ℂ) ^ q) ((t : ℂ)), ← pow_succ (t : ℂ) q]
    exact add_comm _ _
  exact heq ▸ hfinal

/-- **Differentiation under the integral sign for the radial contraction**:
at every point of a `DiscStar` open set on which `ω` is analytic, the radial
contraction is complex differentiable (jointly) with derivative
`∫ t in 0..1, radialIntegrandFDeriv c ω t z₀`.-/
theorem hasFDerivAt_radialContract [CompleteSpace F] (hU : IsOpen U) (hst : DiscStar c U)
    (hω : AnalyticOnNhd ℂ ω U) {z₀ : Fin n → ℂ} (hz₀ : z₀ ∈ U) :
    HasFDerivAt (radialContract c ω)
      (∫ t in (0 : ℝ)..1, radialIntegrandFDeriv c ω t z₀) z₀ := by
  obtain ⟨r, hr0, hball⟩ := Metric.isOpen_iff.mp hU z₀ hz₀
  have hδ0 : 0 < r / 2 := half_pos hr0
  have hδU : closedBall z₀ (r / 2) ⊆ U :=
    (closedBall_subset_ball (half_lt_self hr0)).trans hball
  have hballU : ball z₀ (r / 2) ⊆ U := ball_subset_closedBall.trans hδU
  -- the compact segment tube and uniform bounds for `ω` and `fderiv ω` on it
  have hcont2 : Continuous (fun p : ℝ × (Fin n → ℂ) => segMap c p.1 p.2) :=
    continuous_const.add ((Complex.continuous_ofReal.comp continuous_fst).smul
      (continuous_snd.sub continuous_const))
  have hKcomp : IsCompact ((fun p : ℝ × (Fin n → ℂ) => segMap c p.1 p.2) ''
      (Icc 0 1 ×ˢ closedBall z₀ (r / 2))) :=
    (isCompact_Icc.prod (isCompact_closedBall z₀ (r / 2))).image hcont2
  have hKU : (fun p : ℝ × (Fin n → ℂ) => segMap c p.1 p.2) ''
      (Icc 0 1 ×ˢ closedBall z₀ (r / 2)) ⊆ U := by
    rintro y ⟨⟨t, x⟩, ⟨ht, hx⟩, rfl⟩
    exact segMap_mem hst (hδU hx) ht
  obtain ⟨M₁, hM₁⟩ := hKcomp.exists_bound_of_continuousOn (hω.continuousOn.mono hKU)
  obtain ⟨M₂, hM₂⟩ :=
    hKcomp.exists_bound_of_continuousOn (((hω.fderiv_of_isOpen hU).continuousOn).mono hKU)
  have hmaps : MapsTo (fun t : ℝ => segMap c t z₀) (Icc 0 1) U :=
    fun t ht => segMap_mem hst hz₀ ht
  have huIoc : Set.uIoc (0 : ℝ) 1 = Ioc (0 : ℝ) 1 := Set.uIoc_of_le zero_le_one
  refine intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le
    (F := fun x t => radialIntegrand c ω t x)
    (F' := fun x t => radialIntegrandFDeriv c ω t x)
    (bound := fun _ => max ((‖z₀ - c‖ + r / 2) * M₂ + M₁) 0)
    (ball_mem_nhds z₀ hδ0) ?_ ?_ ?_ ?_ ?_ ?_
  · -- measurability of the integrand near `z₀`
    refine Filter.eventually_iff_exists_mem.mpr
      ⟨ball z₀ (r / 2), ball_mem_nhds z₀ hδ0, fun x hx => ?_⟩
    rw [huIoc]
    exact ((continuousOn_radialIntegrand hst hω (hballU hx)).mono
      Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc
  · exact intervalIntegrable_radialIntegrand hst hω hz₀
  · -- measurability of the derivative family at `z₀`
    rw [huIoc]
    refine ContinuousOn.aestronglyMeasurable (ContinuousOn.mono ?_ Ioc_subset_Icc_self)
      measurableSet_Ioc
    have hωγ := hω.continuousOn.comp (continuousOn_segMap c z₀) hmaps
    have hD := ((hω.fderiv_of_isOpen hU).continuousOn).comp (continuousOn_segMap c z₀) hmaps
    refine ContinuousOn.add ?_ ?_
    · refine ContinuousOn.smul ((Complex.continuous_ofReal.pow (q + 1)).continuousOn) ?_
      exact ((ContinuousLinearMap.compL ℂ (Fin n → ℂ)
        ((Fin n → ℂ) [⋀^Fin (q + 1)]→L[ℂ] F) ((Fin n → ℂ) [⋀^Fin q]→L[ℂ] F)
        (curryApplyCLM (z₀ - c))).continuous).comp_continuousOn hD
    · refine ContinuousOn.smul ((Complex.continuous_ofReal.pow q).continuousOn) ?_
      have hlip : LipschitzWith 1
          (fun A : (Fin n → ℂ) [⋀^Fin (q + 1)]→L[ℂ] F => A.curryLeft) := by
        refine LipschitzWith.of_dist_le_mul fun A B => ?_
        rw [dist_eq_norm, dist_eq_norm, NNReal.coe_one, one_mul]
        have hsub2 : A.curryLeft - B.curryLeft = (A - B).curryLeft := by
          ext w v
          simp
        rw [hsub2, norm_curryLeft]
      exact hlip.continuous.comp_continuousOn hωγ
  · -- the uniform derivative bound on the ball
    refine Filter.Eventually.of_forall fun t ht => ?_
    rw [huIoc] at ht
    have ht' : t ∈ Icc (0 : ℝ) 1 := Ioc_subset_Icc_self ht
    intro x hx
    have hxc : ‖x - c‖ ≤ ‖z₀ - c‖ + r / 2 := by
      calc ‖x - c‖ = ‖x - z₀ + (z₀ - c)‖ := by rw [sub_add_sub_cancel]
      _ ≤ ‖x - z₀‖ + ‖z₀ - c‖ := norm_add_le _ _
      _ ≤ r / 2 + ‖z₀ - c‖ :=
          add_le_add (mem_ball_iff_norm.1 hx).le le_rfl
      _ = ‖z₀ - c‖ + r / 2 := add_comm _ _
    have hmemK : segMap c t x ∈ (fun p : ℝ × (Fin n → ℂ) => segMap c p.1 p.2) ''
        (Icc 0 1 ×ˢ closedBall z₀ (r / 2)) :=
      ⟨(t, x), ⟨ht', ball_subset_closedBall hx⟩, rfl⟩
    have hDb : ‖fderiv ℂ ω (segMap c t x)‖ ≤ M₂ := hM₂ _ hmemK
    have hAb : ‖ω (segMap c t x)‖ ≤ M₁ := hM₁ _ hmemK
    have htpow : ∀ k : ℕ, ‖(t : ℂ) ^ k‖ ≤ 1 := fun k => by
      rw [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht.1]
      exact pow_le_one₀ ht.1.le ht.2
    refine ContinuousLinearMap.opNorm_le_bound _ (le_max_right _ 0) fun w => ?_
    have happly : radialIntegrandFDeriv c ω t x w =
        (t : ℂ) ^ (q + 1) • (fderiv ℂ ω (segMap c t x) w).curryLeft (x - c) +
          (t : ℂ) ^ q • (ω (segMap c t x)).curryLeft w := by
      simp only [radialIntegrandFDeriv, _root_.add_apply, _root_.smul_apply,
        ContinuousLinearMap.coe_comp, Function.comp_apply, curryApplyCLM_apply]
    have hDw : ‖fderiv ℂ ω (segMap c t x) w‖ ≤ M₂ * ‖w‖ :=
      ContinuousLinearMap.le_of_opNorm_le _ hDb w
    have hDw0 : (0 : ℝ) ≤ M₂ * ‖w‖ :=
      (norm_nonneg (fderiv ℂ ω (segMap c t x) w)).trans hDw
    have h1 : ‖(t : ℂ) ^ (q + 1) • (fderiv ℂ ω (segMap c t x) w).curryLeft (x - c)‖ ≤
        (‖z₀ - c‖ + r / 2) * M₂ * ‖w‖ := by
      rw [norm_smul]
      calc ‖(t : ℂ) ^ (q + 1)‖ * ‖(fderiv ℂ ω (segMap c t x) w).curryLeft (x - c)‖
          ≤ 1 * ‖(fderiv ℂ ω (segMap c t x) w).curryLeft (x - c)‖ :=
            mul_le_mul_of_nonneg_right (htpow _) (norm_nonneg _)
        _ = ‖(fderiv ℂ ω (segMap c t x) w).curryLeft (x - c)‖ := one_mul _
        _ ≤ ‖(fderiv ℂ ω (segMap c t x) w).curryLeft‖ * ‖x - c‖ :=
            ContinuousLinearMap.le_opNorm _ _
        _ = ‖fderiv ℂ ω (segMap c t x) w‖ * ‖x - c‖ := by rw [norm_curryLeft]
        _ ≤ (M₂ * ‖w‖) * ‖x - c‖ :=
            mul_le_mul_of_nonneg_right hDw (norm_nonneg _)
        _ ≤ (M₂ * ‖w‖) * (‖z₀ - c‖ + r / 2) :=
            mul_le_mul_of_nonneg_left hxc hDw0
        _ = (‖z₀ - c‖ + r / 2) * M₂ * ‖w‖ := by ring
    have h2 : ‖(t : ℂ) ^ q • (ω (segMap c t x)).curryLeft w‖ ≤ M₁ * ‖w‖ := by
      rw [norm_smul]
      calc ‖(t : ℂ) ^ q‖ * ‖(ω (segMap c t x)).curryLeft w‖
          ≤ 1 * ‖(ω (segMap c t x)).curryLeft w‖ :=
            mul_le_mul_of_nonneg_right (htpow _) (norm_nonneg _)
        _ = ‖(ω (segMap c t x)).curryLeft w‖ := one_mul _
        _ ≤ ‖(ω (segMap c t x)).curryLeft‖ * ‖w‖ := ContinuousLinearMap.le_opNorm _ _
        _ = ‖ω (segMap c t x)‖ * ‖w‖ := by rw [norm_curryLeft]
        _ ≤ M₁ * ‖w‖ := mul_le_mul_of_nonneg_right hAb (norm_nonneg _)
    calc ‖radialIntegrandFDeriv c ω t x w‖
        ≤ ‖(t : ℂ) ^ (q + 1) • (fderiv ℂ ω (segMap c t x) w).curryLeft (x - c)‖ +
          ‖(t : ℂ) ^ q • (ω (segMap c t x)).curryLeft w‖ := by
          rw [happly]
          exact norm_add_le _ _
      _ ≤ (‖z₀ - c‖ + r / 2) * M₂ * ‖w‖ + M₁ * ‖w‖ := add_le_add h1 h2
      _ = ((‖z₀ - c‖ + r / 2) * M₂ + M₁) * ‖w‖ := by ring
      _ ≤ max ((‖z₀ - c‖ + r / 2) * M₂ + M₁) 0 * ‖w‖ :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)
  · exact intervalIntegrable_const
  · -- pointwise differentiability on the ball
    refine Filter.Eventually.of_forall fun t ht => ?_
    rw [huIoc] at ht
    intro x hx
    exact hasFDerivAt_radialIntegrand hst hω (hballU hx) (Ioc_subset_Icc_self ht)

/-- **Joint analyticity of the radial contraction** on a `DiscStar` open set:
differentiation under the integral sign gives joint complex differentiability,
and stage 2 upgrades joint differentiability to joint analyticity on open
subsets of `ℂⁿ`.-/
theorem analyticOnNhd_radialContract [CompleteSpace F] (hU : IsOpen U)
    (hst : DiscStar c U) (hω : AnalyticOnNhd ℂ ω U) :
    AnalyticOnNhd ℂ (radialContract c ω) U :=
  analyticOnNhd_of_differentiableOn hU fun _ hz =>
    (hasFDerivAt_radialContract hU hst hω hz).differentiableAt.differentiableWithinAt

/-! ## The Cartan identity and the fundamental theorem of calculus -/

/-- A complex derivative restricts to a real derivative along the real axis
(vector-valued version of `HasDerivAt.comp_ofReal`).-/
theorem hasDerivAt_comp_ofReal {W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W]
    {h : ℂ → W} {h' : W} {t : ℝ} (hf : HasDerivAt h h' (t : ℂ)) :
    HasDerivAt (fun τ : ℝ => h τ) h' t := by
  simpa [Function.comp_def] using
    (hf.hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt t Complex.ofRealCLM.hasDerivAt

/-- Evaluation of continuous linear maps (into the forms space) at a fixed
vector is Lipschitz.-/
theorem lipschitzWith_clm_apply (u : Fin n → ℂ) :
    LipschitzWith ‖u‖₊
      (fun M : (Fin n → ℂ) →L[ℂ] ((Fin n → ℂ) [⋀^Fin (q + 1)]→L[ℂ] F) => M u) := by
  refine LipschitzWith.of_dist_le_mul fun M M' => ?_
  rw [dist_eq_norm, dist_eq_norm, coe_nnnorm]
  calc ‖M u - M' u‖ = ‖(M - M') u‖ := by rw [_root_.sub_apply]
    _ ≤ ‖M - M'‖ * ‖u‖ := ContinuousLinearMap.le_opNorm _ _
    _ = ‖u‖ * ‖M - M'‖ := mul_comm _ _

/-- The signed-sum formula for `alternatizeUncurryFin`, with the signs read in
`ℂ` (the library's `zsmul` signs converted through the module structure).-/
theorem alternatizeUncurryFin_apply_complexSign
    (f : (Fin n → ℂ) →L[ℂ] ((Fin n → ℂ) [⋀^Fin q]→L[ℂ] F))
    (v : Fin (q + 1) → (Fin n → ℂ)) :
    alternatizeUncurryFin f v =
      ∑ i : Fin (q + 1), (-1 : ℂ) ^ (i : ℕ) • f (v i) (Fin.removeNth i v) := by
  rw [alternatizeUncurryFin_apply]
  simp only [← Int.cast_smul_eq_zsmul ℂ, Int.cast_pow, Int.cast_neg, Int.cast_one]

/-- The closedness relation: if `extDeriv ω = 0` on `U`, then the contraction
of `fderiv ω` against a fixed vector `u` is the signed sum of the values of
`fderiv ω` on the `Fin.cons`-tuples.-/
theorem fderiv_contraction_of_closed (hcl : ∀ y ∈ U, extDeriv ω y = 0)
    {y : Fin n → ℂ} (hy : y ∈ U) (u : Fin n → ℂ) (v : Fin (q + 1) → (Fin n → ℂ)) :
    (fderiv ℂ ω y u) v =
      ∑ i : Fin (q + 1), (-1 : ℂ) ^ (i : ℕ) •
        (fderiv ℂ ω y (v i)) (Fin.cons u (Fin.removeNth i v)) := by
  have h0 : alternatizeUncurryFin (fderiv ℂ ω y) (Fin.cons u v) = 0 := by
    rw [show ContinuousAlternatingMap.alternatizeUncurryFin (fderiv ℂ ω y) =
      extDeriv ω y from rfl, hcl y hy]
    simp
  rw [alternatizeUncurryFin_apply_complexSign, Fin.sum_univ_succ] at h0
  simp only [Fin.cons_zero, Fin.cons_succ, Fin.val_zero, pow_zero, one_smul,
    Fin.removeNth_zero, Fin.tail_cons, Fin.val_succ, pow_succ, mul_neg_one,
    removeNth_succ_cons, neg_smul, Finset.sum_neg_distrib] at h0
  exact add_neg_eq_zero.mp h0

/-- **The pointwise Cartan identity for the radial integrand**: for a closed
`ω`, the signed evaluation sum of the `z`-derivative of the radial integrand
is the `t`-derivative of `t ↦ t^(q+1) • ω (segMap c t z)`, evaluated at `v`.-/
theorem alternatizeUncurryFin_radialIntegrandFDeriv
    (hcl : ∀ y ∈ U, extDeriv ω y = 0) {z : Fin n → ℂ} {t : ℝ}
    (hy : segMap c t z ∈ U) (v : Fin (q + 1) → (Fin n → ℂ)) :
    alternatizeUncurryFin (radialIntegrandFDeriv c ω t z) v =
      (t : ℂ) ^ (q + 1) • (fderiv ℂ ω (segMap c t z) (z - c)) v +
        (((q : ℂ) + 1) * (t : ℂ) ^ q) • (ω (segMap c t z)) v := by
  rw [alternatizeUncurryFin_apply_complexSign]
  have happly : ∀ w, radialIntegrandFDeriv c ω t z w =
      (t : ℂ) ^ (q + 1) • (fderiv ℂ ω (segMap c t z) w).curryLeft (z - c) +
        (t : ℂ) ^ q • (ω (segMap c t z)).curryLeft w := fun w => by
    simp only [radialIntegrandFDeriv, _root_.add_apply, _root_.smul_apply,
      ContinuousLinearMap.coe_comp, Function.comp_apply, curryApplyCLM_apply]
  have hterm : ∀ i : Fin (q + 1),
      (-1 : ℂ) ^ (i : ℕ) • (radialIntegrandFDeriv c ω t z (v i)) (Fin.removeNth i v) =
        (t : ℂ) ^ (q + 1) • ((-1 : ℂ) ^ (i : ℕ) •
          (fderiv ℂ ω (segMap c t z) (v i)) (Fin.cons (z - c) (Fin.removeNth i v))) +
        (t : ℂ) ^ q • ((-1 : ℂ) ^ (i : ℕ) •
          ((ω (segMap c t z)).curryLeft (v i)) (Fin.removeNth i v)) := fun i => by
    rw [happly (v i), ContinuousAlternatingMap.add_apply,
      ContinuousAlternatingMap.smul_apply, ContinuousAlternatingMap.smul_apply,
      show ((fderiv ℂ ω (segMap c t z) (v i)).curryLeft (z - c)) (Fin.removeNth i v)
        = (fderiv ℂ ω (segMap c t z) (v i)) (Fin.cons (z - c) (Fin.removeNth i v)) from rfl,
      smul_add, smul_comm ((-1 : ℂ) ^ (i : ℕ)) ((t : ℂ) ^ (q + 1)),
      smul_comm ((-1 : ℂ) ^ (i : ℕ)) ((t : ℂ) ^ q)]
  rw [Finset.sum_congr rfl fun i _ => hterm i, Finset.sum_add_distrib,
    ← Finset.smul_sum, ← Finset.smul_sum,
    ← fderiv_contraction_of_closed hcl hy (z - c) v]
  congr 1
  rw [show (∑ i : Fin (q + 1), (-1 : ℂ) ^ (i : ℕ) •
        ((ω (segMap c t z)).curryLeft (v i)) (Fin.removeNth i v)) =
      alternatizeUncurryFin ((ω (segMap c t z)).curryLeft) v from
    (alternatizeUncurryFin_apply_complexSign _ v).symm]
  rw [alternatizeUncurryFin_curryLeft, ContinuousAlternatingMap.smul_apply,
    ← Nat.cast_smul_eq_nsmul ℂ (q + 1) ((ω (segMap c t z)) v), smul_smul]
  congr 1
  push_cast
  ring

/-- **The radial contraction is a primitive**: for a closed analytic
`(q+1)`-form `ω` on a `DiscStar` open set `U`, the exterior derivative of the
radial contraction recovers `ω` at every point of `U`.-/
theorem extDeriv_radialContract_of_closed [CompleteSpace F] (hU : IsOpen U)
    (hst : DiscStar c U) (hω : AnalyticOnNhd ℂ ω U)
    (hcl : ∀ y ∈ U, extDeriv ω y = 0) {z : Fin n → ℂ} (hz : z ∈ U) :
    extDeriv (radialContract c ω) z = ω z := by
  have hmaps : MapsTo (fun t : ℝ => segMap c t z) (Icc 0 1) U :=
    fun t ht => segMap_mem hst hz ht
  have huIcc : Set.uIcc (0 : ℝ) 1 = Icc (0 : ℝ) 1 := Set.uIcc_of_le zero_le_one
  have hωγ := hω.continuousOn.comp (continuousOn_segMap c z) hmaps
  have hD := ((hω.fderiv_of_isOpen hU).continuousOn).comp (continuousOn_segMap c z) hmaps
  have hK := hasFDerivAt_radialContract hU hst hω hz
  refine ContinuousAlternatingMap.ext fun v => ?_
  -- continuity of the evaluated families
  have hvi : ∀ w : Fin n → ℂ,
      ContinuousOn (fun t : ℝ => radialIntegrandFDeriv c ω t z w) (Icc 0 1) := by
    intro w
    have hfun : (fun t : ℝ => radialIntegrandFDeriv c ω t z w) = fun t : ℝ =>
        (t : ℂ) ^ (q + 1) • (fderiv ℂ ω (segMap c t z) w).curryLeft (z - c) +
          (t : ℂ) ^ q • (ω (segMap c t z)).curryLeft w := funext fun t => by
      simp only [radialIntegrandFDeriv, _root_.add_apply, _root_.smul_apply,
        ContinuousLinearMap.coe_comp, Function.comp_apply, curryApplyCLM_apply]
    rw [hfun]
    refine ContinuousOn.add ?_ ?_
    · exact ((Complex.continuous_ofReal.pow (q + 1)).continuousOn).smul
        ((curryApplyCLM (z - c)).continuous.comp_continuousOn
          ((lipschitzWith_clm_apply w).continuous.comp_continuousOn hD))
    · exact ((Complex.continuous_ofReal.pow q).continuousOn).smul
        ((curryApplyCLM w).continuous.comp_continuousOn hωγ)
  -- exchange: evaluation of the integral is the integral of the evaluations
  have hexch : ∀ i : Fin (q + 1),
      ((∫ t in (0 : ℝ)..1, radialIntegrandFDeriv c ω t z) (v i)) (Fin.removeNth i v) =
        ∫ t in (0 : ℝ)..1,
          ((radialIntegrandFDeriv c ω t z) (v i)) (Fin.removeNth i v) := by
    intro i
    have hint_i : IntervalIntegrable
        (fun t : ℝ => radialIntegrandFDeriv c ω t z (v i)) volume 0 1 := by
      apply ContinuousOn.intervalIntegrable
      rw [huIcc]
      exact hvi (v i)
    rw [ContinuousLinearMap.intervalIntegral_apply
      (φ := fun t : ℝ => radialIntegrandFDeriv c ω t z) (μ := volume) (by
        apply ContinuousOn.intervalIntegrable
        rw [Set.uIcc_of_le (zero_le_one (α := ℝ))]
        refine ContinuousOn.add ?_ ?_
        · refine ContinuousOn.smul
            ((Complex.continuous_ofReal.pow (q + 1)).continuousOn) ?_
          exact ((ContinuousLinearMap.compL ℂ (Fin n → ℂ)
            ((Fin n → ℂ) [⋀^Fin (q + 1)]→L[ℂ] F) ((Fin n → ℂ) [⋀^Fin q]→L[ℂ] F)
            (curryApplyCLM (z - c))).continuous).comp_continuousOn hD
        · refine ContinuousOn.smul ((Complex.continuous_ofReal.pow q).continuousOn) ?_
          have hlip : LipschitzWith 1
              (fun A : (Fin n → ℂ) [⋀^Fin (q + 1)]→L[ℂ] F => A.curryLeft) := by
            refine LipschitzWith.of_dist_le_mul fun A B => ?_
            rw [dist_eq_norm, dist_eq_norm, NNReal.coe_one, one_mul]
            have hsub2 : A.curryLeft - B.curryLeft = (A - B).curryLeft := by
              ext w v'
              simp
            rw [hsub2, norm_curryLeft]
          exact hlip.continuous.comp_continuousOn hωγ) (v i)]
    exact ((ContinuousAlternatingMap.apply ℂ (Fin n → ℂ) F
      (Fin.removeNth i v)).intervalIntegral_comp_comm hint_i).symm
  -- the boundary function and its derivative
  set g : ℝ → F := fun τ => (τ : ℂ) ^ (q + 1) • (ω (segMap c τ z)) v with hgdef
  set g' : ℝ → F := fun τ =>
    (τ : ℂ) ^ (q + 1) • (fderiv ℂ ω (segMap c τ z) (z - c)) v +
      (((q : ℂ) + 1) * (τ : ℂ) ^ q) • (ω (segMap c τ z)) v with hg'def
  -- step 1: expand the exterior derivative as a signed sum of integrals
  have hstep1 : extDeriv (radialContract c ω) z v =
      ∑ i : Fin (q + 1), (-1 : ℂ) ^ (i : ℕ) • ∫ t in (0 : ℝ)..1,
        ((radialIntegrandFDeriv c ω t z) (v i)) (Fin.removeNth i v) := by
    show (alternatizeUncurryFin (fderiv ℂ (radialContract c ω) z)) v = _
    rw [hK.fderiv, alternatizeUncurryFin_apply_complexSign]
    exact Finset.sum_congr rfl fun i _ => by rw [hexch i]
  -- step 2: move signs and the finite sum inside the integral
  have hstep2 : (∑ i : Fin (q + 1), (-1 : ℂ) ^ (i : ℕ) • ∫ t in (0 : ℝ)..1,
      ((radialIntegrandFDeriv c ω t z) (v i)) (Fin.removeNth i v)) =
      ∫ t in (0 : ℝ)..1, ∑ i : Fin (q + 1), (-1 : ℂ) ^ (i : ℕ) •
        ((radialIntegrandFDeriv c ω t z) (v i)) (Fin.removeNth i v) := by
    have hsmul : ∀ i : Fin (q + 1),
        (-1 : ℂ) ^ (i : ℕ) • (∫ t in (0 : ℝ)..1,
          ((radialIntegrandFDeriv c ω t z) (v i)) (Fin.removeNth i v)) =
        ∫ t in (0 : ℝ)..1, (-1 : ℂ) ^ (i : ℕ) •
          ((radialIntegrandFDeriv c ω t z) (v i)) (Fin.removeNth i v) := fun i =>
      (intervalIntegral.integral_smul _ _).symm
    rw [Finset.sum_congr rfl fun i _ => hsmul i]
    refine (intervalIntegral.integral_finsetSum fun i _ => ?_).symm
    apply ContinuousOn.intervalIntegrable
    rw [huIcc]
    exact continuousOn_const.smul
      ((ContinuousAlternatingMap.apply ℂ (Fin n → ℂ) F
        (Fin.removeNth i v)).continuous.comp_continuousOn (hvi (v i)))
  -- step 3: the Cartan identity under the integral
  have hstep3 : (∫ t in (0 : ℝ)..1, ∑ i : Fin (q + 1), (-1 : ℂ) ^ (i : ℕ) •
      ((radialIntegrandFDeriv c ω t z) (v i)) (Fin.removeNth i v)) =
      ∫ t in (0 : ℝ)..1, g' t := by
    refine intervalIntegral.integral_congr fun τ hτ => ?_
    rw [huIcc] at hτ
    rw [← alternatizeUncurryFin_apply_complexSign]
    exact alternatizeUncurryFin_radialIntegrandFDeriv hcl (segMap_mem hst hz hτ) v
  -- step 4: the fundamental theorem of calculus along the radial segment
  have hderiv : ∀ τ ∈ Set.uIcc (0 : ℝ) 1, HasDerivAt g (g' τ) τ := by
    intro τ hτ
    rw [huIcc] at hτ
    have hyU : segMap c τ z ∈ U := segMap_mem hst hz hτ
    have hp : HasDerivAt (fun s : ℂ => s ^ (q + 1))
        (((q : ℂ) + 1) * (τ : ℂ) ^ q) ((τ : ℝ) : ℂ) := by
      simpa using hasDerivAt_pow (q + 1) ((τ : ℝ) : ℂ)
    have hδ : HasDerivAt (fun s : ℂ => c + s • (z - c)) (z - c) ((τ : ℝ) : ℂ) := by
      simpa using ((hasDerivAt_id ((τ : ℝ) : ℂ)).smul_const (z - c)).const_add c
    have hωd : HasFDerivAt ω (fderiv ℂ ω (segMap c τ z)) (segMap c τ z) :=
      (hω _ hyU).differentiableAt.hasFDerivAt
    have hcomp : HasDerivAt (fun s : ℂ => ω (c + s • (z - c)))
        (fderiv ℂ ω (segMap c τ z) (z - c)) ((τ : ℝ) : ℂ) :=
      hωd.comp_hasDerivAt _ hδ
    have happ : HasDerivAt (fun s : ℂ => (ω (c + s • (z - c))) v)
        ((fderiv ℂ ω (segMap c τ z) (z - c)) v) ((τ : ℝ) : ℂ) :=
      ((ContinuousAlternatingMap.apply ℂ (Fin n → ℂ) F
        v).hasFDerivAt).comp_hasDerivAt _ hcomp
    have hprod : HasDerivAt (fun s : ℂ => s ^ (q + 1) • (ω (c + s • (z - c))) v)
        ((τ : ℂ) ^ (q + 1) • ((fderiv ℂ ω (segMap c τ z) (z - c)) v) +
          (((q : ℂ) + 1) * (τ : ℂ) ^ q) • ((ω (segMap c τ z)) v)) ((τ : ℝ) : ℂ) :=
      hp.smul happ
    exact hasDerivAt_comp_ofReal hprod
  have hg'int : IntervalIntegrable g' volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    rw [huIcc]
    refine ContinuousOn.add ?_ ?_
    · exact ((Complex.continuous_ofReal.pow (q + 1)).continuousOn).smul
        ((ContinuousAlternatingMap.apply ℂ (Fin n → ℂ) F v).continuous.comp_continuousOn
          ((lipschitzWith_clm_apply (z - c)).continuous.comp_continuousOn hD))
    · exact ((continuous_const.mul
        (Complex.continuous_ofReal.pow q)).continuousOn).smul
        ((ContinuousAlternatingMap.apply ℂ (Fin n → ℂ) F v).continuous.comp_continuousOn
          hωγ)
  have hftc : (∫ t in (0 : ℝ)..1, g' t) = g 1 - g 0 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hg'int
  have hg1 : g 1 = (ω z) v := by
    rw [hgdef]
    simp only [Complex.ofReal_one, one_pow, one_smul, segMap_one]
  have hg0 : g 0 = 0 := by
    rw [hgdef]
    simp only [Complex.ofReal_zero, zero_pow (Nat.succ_ne_zero q), zero_smul]
  calc extDeriv (radialContract c ω) z v
      = ∑ i : Fin (q + 1), (-1 : ℂ) ^ (i : ℕ) • ∫ t in (0 : ℝ)..1,
          ((radialIntegrandFDeriv c ω t z) (v i)) (Fin.removeNth i v) := hstep1
    _ = ∫ t in (0 : ℝ)..1, ∑ i : Fin (q + 1), (-1 : ℂ) ^ (i : ℕ) •
          ((radialIntegrandFDeriv c ω t z) (v i)) (Fin.removeNth i v) := hstep2
    _ = ∫ t in (0 : ℝ)..1, g' t := hstep3
    _ = g 1 - g 0 := hftc
    _ = (ω z) v := by rw [hg1, hg0, sub_zero]

end Radial

/-! ## The existence statements: primitives of closed forms of positive degree -/

section Existence

variable {c : Fin n → ℂ} {ω : (Fin n → ℂ) → ((Fin n → ℂ) [⋀^Fin (q + 1)]→L[ℂ] F)}

/-- **Primitives on disc-star-shaped open sets**: a closed analytic
`(q+1)`-form on an open `DiscStar` set has an analytic `q`-form primitive.-/
theorem exists_primitive_form_discStar [CompleteSpace F] {U : Set (Fin n → ℂ)}
    (hU : IsOpen U) (hst : DiscStar c U) (hω : AnalyticOnNhd ℂ ω U)
    (hcl : ∀ z ∈ U, extDeriv ω z = 0) :
    ∃ η : (Fin n → ℂ) → ((Fin n → ℂ) [⋀^Fin q]→L[ℂ] F),
      AnalyticOnNhd ℂ η U ∧ ∀ z ∈ U, extDeriv η z = ω z :=
  ⟨radialContract c ω, analyticOnNhd_radialContract hU hst hω,
    fun _ hz => extDeriv_radialContract_of_closed hU hst hω hcl hz⟩

/-- **The holomorphic Poincaré lemma on polydiscs, positive degrees**: every
closed analytic `(q+1)`-form on an open polydisc in `ℂⁿ` is the exterior
derivative of an analytic `q`-form on the polydisc — in every dimension `n`,
every degree `q + 1 ≥ 1`, and with values in every complete normed
`ℂ`-space.-/
theorem exists_primitive_form_polydisc [CompleteSpace F] {R : Fin n → ℝ}
    (hω : AnalyticOnNhd ℂ ω (polydisc c R))
    (hcl : ∀ z ∈ polydisc c R, extDeriv ω z = 0) :
    ∃ η : (Fin n → ℂ) → ((Fin n → ℂ) [⋀^Fin q]→L[ℂ] F),
      AnalyticOnNhd ℂ η (polydisc c R) ∧ ∀ z ∈ polydisc c R, extDeriv η z = ω z :=
  exists_primitive_form_discStar (isOpen_polydisc c R) (discStar_polydisc c R) hω hcl

/-- The holomorphic Poincaré lemma on sup-norm balls in `ℂⁿ` (the equal-radii
polydiscs), positive degrees.-/
theorem exists_primitive_form_ball [CompleteSpace F] {r : ℝ}
    (hω : AnalyticOnNhd ℂ ω (ball c r)) (hcl : ∀ z ∈ ball c r, extDeriv ω z = 0) :
    ∃ η : (Fin n → ℂ) → ((Fin n → ℂ) [⋀^Fin q]→L[ℂ] F),
      AnalyticOnNhd ℂ η (ball c r) ∧ ∀ z ∈ ball c r, extDeriv η z = ω z :=
  exists_primitive_form_discStar isOpen_ball (discStar_ball c r) hω hcl

end Existence

/-! ## Degree zero: closed 0-forms are constant on balls -/

/-- **Degree-`0` rigidity in all dimensions**: a `0`-form on a ball in `ℂⁿ`
with vanishing exterior derivative takes the same value at any two points of
the ball (the degree-`0` companion of the positive-degree exactness above;
dimension-generic port of the one-variable
`HodgePilot.DiscResolution.const_of_extDeriv_eq_zero`).-/
theorem const_of_extDeriv_eq_zero_ball {x : Fin n → ℂ} {r : ℝ}
    {g : (Fin n → ℂ) → ((Fin n → ℂ) [⋀^Fin 0]→L[ℂ] F)}
    (hg : AnalyticOnNhd ℂ g (ball x r))
    (hd : ∀ y ∈ ball x r, extDeriv g y = 0) :
    ∀ y ∈ ball x r, ∀ z ∈ ball x r, g y = g z := by
  set σ : ((Fin n → ℂ) [⋀^Fin 0]→L[ℂ] F) →L[ℂ] F :=
    ((constOfIsEmptyLIE ℂ (Fin n → ℂ) F (Fin 0)).symm.toContinuousLinearEquiv :
      ((Fin n → ℂ) [⋀^Fin 0]→L[ℂ] F) ≃L[ℂ] F).toContinuousLinearMap with hσ
  set k : (Fin n → ℂ) → F := fun v => σ (g v) with hk
  have hgk : g = fun v => constOfIsEmpty ℂ (Fin n → ℂ) (Fin 0) (k v) := by
    funext v
    have h1 : constOfIsEmpty ℂ (Fin n → ℂ) (Fin 0) (k v) =
        (constOfIsEmptyLIE ℂ (Fin n → ℂ) F (Fin 0))
          ((constOfIsEmptyLIE ℂ (Fin n → ℂ) F (Fin 0)).symm (g v)) := rfl
    rw [h1, LinearIsometryEquiv.apply_symm_apply]
  have hkdiff : DifferentiableOn ℂ k (ball x r) :=
    σ.differentiable.comp_differentiableOn hg.differentiableOn
  have hk0 : Set.EqOn (fderiv ℂ k) 0 (ball x r) := by
    intro y hy
    have hder : extDeriv g y =
        ofSubsingleton ℂ (Fin n → ℂ) F (0 : Fin 1) (fderiv ℂ k y) := by
      conv_lhs => rw [hgk]
      exact extDeriv_constOfIsEmpty k y
    have h0 : ofSubsingleton ℂ (Fin n → ℂ) F (0 : Fin 1) (fderiv ℂ k y) = 0 :=
      hder.symm.trans (hd y hy)
    show fderiv ℂ k y = 0
    ext w
    have h1 : (ofSubsingleton ℂ (Fin n → ℂ) F (0 : Fin 1) (fderiv ℂ k y))
        (fun _ => w) = 0 := by rw [h0]; rfl
    rw [ofSubsingleton_apply_apply] at h1
    exact h1
  intro y hy z hz
  have hconst : k y = k z :=
    isOpen_ball.is_const_of_fderiv_eq_zero (convex_ball x r).isPreconnected
      hkdiff hk0 hy hz
  rw [hgk]
  exact congrArg (constOfIsEmpty ℂ (Fin n → ℂ) (Fin 0)) hconst

end PolydiscPoincare
end HodgePilot
