/-
Copyright (c) 2026 Michael R. Douglas, Sarah Hoback, Anna Mei, Ron Nissim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R. Douglas, Sarah Hoback, Anna Mei, Ron Nissim
-/
module

public import Tengoku.LeanPool.LeanPool.OSforGFF.Spacetime.Basic
public import Tengoku

/-!
# Euclidean Group E(4) and Its Actions

Defines the Euclidean group E(4) = ℝ⁴ ⋊ O(4) with action g • x = R(x) + t
on spacetime, and its induced actions on test functions (g • f)(x) = f(g⁻¹ • x).

Key properties: measure preservation (d⁴(E⁻¹x) = d⁴x), temperate growth of
pullbacks (needed for Schwartz space), and continuity of all actions.
Foundation for the OS2 axiom.
-/

@[expose] public section

open MeasureTheory NNReal ENNReal
open TopologicalSpace Measure

noncomputable section

/-OS2 R^d with d=4, where mu is the Lebegue measure.
We know the OS2 dp must be Euclidean invariant -/

open scoped Real InnerProductSpace SchwartzMap

namespace QFT

/-- Orthogonal linear isometries of ℝ⁴ (the group O(4)).
LinearIsometry is an orthogonal linear map, ie an element of O(4)
-/
abbrev O4 : Type :=
  LinearIsometry (RingHom.id ℝ) SpaceTime SpaceTime

/-!  Euclidean group -/
/-- Euclidean motion = rotation / reflection + translation. E= R^4 x O(4) -/
structure E where
  /-- Orthogonal linear part of the Euclidean motion. -/
  R : O4
  /-- Translation part of the Euclidean motion. -/
  t : SpaceTime

/-- Action of g : E on a spacetime point x.
Impliments the pullback map x to Rx+ t
-/
def act (g : E) (x : SpaceTime) : SpaceTime := g.R x + g.t

/-act_one, act_mul and act_inv lemmas prove
identity, composition and inverse. They are needed to say Euclidean sym
form a group. This mirrors OS-2's S_j= S_{EJ} -/
/--
@isnad1 id=eq.0h1v.s7.cb5048f82877 from=translated src=- shape=10aafb38 vocab=ddd903b9
-/
@[simp] lemma act_one (x : SpaceTime) : act ⟨1,0⟩ x = x := by simp [act]

/--
@isnad1 id=eq.0h3v.s10.d43a3ce2bc4a from=translated src=- shape=dfb3b21a vocab=0288ed18
-/
@[simp] lemma act_mul (g h : E) (x : SpaceTime) :
    act ⟨g.R.comp h.R, g.R h.t + g.t⟩ x = g.R (h.R x + h.t) + g.t := by
  simp [act, add_comm, add_left_comm]

/--
@isnad1 id=eq.0h2v.s9.ef9f552114e2 from=translated src=- shape=b897c782 vocab=0f88da5c
-/
@[simp] lemma act_inv (g : E) (x : SpaceTime) :
    act ⟨g.R, -g.R g.t⟩ x = g.R (x - g.t) := by
  -- unfold the two sides and use linearity of g.R
  simp [act, sub_eq_add_neg, map_add, map_neg]
        -- the map_sub lemma is in mathlib
/- Linear-iso helper lemmas are explicitly in Os-2
but are used as a counter part to rotations that preserve the metric and R^-1 R=1-/
open LinearIsometryEquiv

namespace LinearIsometry
/-- Inverse of a linear isometry : we turn the canonical equivalence
    (available in finite dimension) back into a `LinearIsometry`.
-/
noncomputable def inv (g : O4) : O4 :=
  ((g.toLinearIsometryEquiv rfl).symm).toLinearIsometry

/--
@isnad1 id=eq.0h3v.s10.64d5dad3d096 from=translated src=- shape=09e76765 vocab=6fba2782
-/
@[simp] lemma comp_apply (g h : O4) (x : SpaceTime) :
    (g.comp h) x = g (h x) := rfl

/--
@isnad1 id=eq.0h2v.s8.19aa2e1a7ae0 from=translated src=- shape=a81c6a65 vocab=17d2f9a8
-/
@[simp] lemma inv_apply (g : O4) (x : SpaceTime) :
    (LinearIsometry.inv g) (g x) = x := by
  dsimp [LinearIsometry.inv]
  simpa using
    (LinearIsometryEquiv.symm_apply_apply (g.toLinearIsometryEquiv rfl) x)
/--
@isnad1 id=eq.0h1v.s8.b530e55a5737 from=translated src=- shape=f7a2987b vocab=a4af3f28
-/
@[simp] lemma one_apply (x : SpaceTime) : (1 : O4) x = x := rfl

/--
@isnad1 id=eq.0h1v.s9.0d34322fc03b from=translated src=- shape=a95620e6 vocab=b4bf9014
-/
@[simp] lemma one_comp (R : O4) : (1 : O4).comp R = R := by
  ext x; simp [comp_apply, one_apply]

/--
@isnad1 id=eq.0h1v.s9.896eef670129 from=translated src=- shape=3395f98a vocab=b4bf9014
-/
@[simp] lemma comp_one (R : O4) : R.comp (1 : O4) = R := by
  ext x; simp [comp_apply, one_apply]

/--
@isnad1 id=eq.0h1v.s10.ca1761ac538e from=translated src=- shape=41a8e8fc vocab=5cd0438e
-/
@[simp] lemma inv_comp (R : O4) :
    (LinearIsometry.inv R).comp R = 1 := by
  ext x i
  simp [comp_apply, inv_apply, one_apply]
/--
@isnad1 id=eq.0h1v.s10.656915ce8272 from=translated src=- shape=51a9b0da vocab=5cd0438e
-/
@[simp] lemma comp_inv (R : O4) :
    R.comp (LinearIsometry.inv R) = 1 := by
  -- equality of linear-isometries, proved coordinate-wise
  ext x i
  have h : (R.toLinearIsometryEquiv rfl) ((LinearIsometry.inv R) x) = x :=
    LinearIsometryEquiv.apply_symm_apply (R.toLinearIsometryEquiv rfl) x
  simpa [comp_apply, inv_apply, one_apply] using congrArg (fun v : SpaceTime => v i) h

end LinearIsometry

/-(extentionality) Allows Lean to prove equality of Euclidean motions by checking the R and t
components separately—hugely convenient for the group-law proofs. -/
@[ext] lemma _root_.QFT.E.ext {g h : E} (hR : g.R = h.R) (ht : g.t = h.t) : g = h := by
  cases g; cases h; cases hR; cases ht; rfl

/-!  ##  Group structure on `E`  ----------------------------------------- -/

/- 1.  Primitive instances of group operations
Implements the semidirect-product multiplication in OS-2:
first rotate, then translate the second translation by the first rotation. -/
instance : Mul E where
  mul g h := ⟨g.R.comp h.R, g.R h.t + g.t⟩

instance : One E where
  one := ⟨1, 0⟩

instance : Inv E where
  inv g := ⟨LinearIsometry.inv g.R, -(LinearIsometry.inv g.R) g.t⟩

/-- We need a `Div` instance because `Group` extends `DivInvMonoid`. -/
instance : Div E where
  div g h := g * h⁻¹

/- helper lemmas mirroring (g. h)_R= g_R dot h_r, and
(g.h)_t= g_R h_t+ g_t)-
-/
/--
@isnad1 id=eq.0h2v.s8.583d6e033e00 from=translated src=- shape=57c224c0 vocab=18485d6e
-/
@[simp] lemma mul_R (g h : E) : (g * h).R = g.R.comp h.R := rfl
/--
@isnad1 id=eq.0h2v.s8.4d4a569660d6 from=translated src=- shape=58d18dd2 vocab=10d86893
-/
@[simp] lemma mul_t (g h : E) : (g * h).t = g.R h.t + g.t := rfl
/--
@isnad1 id=eq.0h0v.s7.06f1ca801c71 from=translated src=- shape=1ac31801 vocab=0d3a71b7
-/
@[simp] lemma one_R : (1 : E).R = 1 := rfl
/--
@isnad1 id=eq.0h0v.s5.24d51889ceb9 from=translated src=- shape=1ac31801 vocab=339d5e4b
-/
@[simp] lemma one_t : (1 : E).t = 0 := rfl
/--
@isnad1 id=eq.0h1v.s3.6764b7760c9b from=translated src=- shape=09cc885e vocab=c6d85183
-/
@[simp] lemma inv_R (g : E) : (g⁻¹).R = LinearIsometry.inv g.R := rfl
/--
@isnad1 id=eq.0h1v.s8.4fe46e90d530 from=translated src=- shape=cf8d29a6 vocab=27def70c
-/
@[simp] lemma inv_t (g : E) : (g⁻¹).t = -(LinearIsometry.inv g.R) g.t := rfl

/-Provides the formal group demanded by OS-2's statement
“Euclidean transformations define a group.”-/
instance : Group E where
  mul := (· * ·)
  one := (1 : E)
  inv := Inv.inv
  -- associativity
  mul_assoc a b c := by
    apply E.ext <;> simp [mul_R, mul_t, LinearIsometry.comp_assoc, add_comm, add_left_comm]
  -- left and right identity
  one_mul a := by apply E.ext <;> simp [mul_R, mul_t, LinearIsometry.one_comp, one_t]
  mul_one a := by apply E.ext <;> simp [mul_R, mul_t, LinearIsometry.comp_one, one_t]
  inv_mul_cancel a := by
    apply E.ext <;> simp [mul_R, mul_t, inv_R, inv_t, one_R, one_t, LinearIsometry.inv_comp]

/-theorem ---------------------------------------------

     For all Euclidean motions g,h and every point x ∈ ℝ⁴ we have
         act (g * h) x  =  act g (act h x).
     In words: the `act` map is a group action of E on spacetime.

     We also prove the inverse law
         act g⁻¹ (act g x) = x.
-/

/-for all Euclidean motions g and h and any point x ∈ ℝ⁴, pulling x forward by the product g*h
  equals pulling by h first and then by g.
This is precisely the group-action law(𝑔h)⋅𝑥=𝑔.(h. 𝑥)(gh)⋅x=g⋅(h⋅x).-/

/--
@isnad1 id=eq.0h3v.s4.e8fdbbfad49b from=translated src=- shape=7177eae1 vocab=11a30fe1
-/
@[simp] lemma act_mul_general (g h : E) (x : SpaceTime) :
    act (g * h) x = act g (act h x) := by
  cases g with
  | mk gR gt =>
    cases h with
    | mk hR ht =>
      simp [act, mul_R, mul_t, add_comm, add_left_comm]

/-Statement: applying g to x and then applying the inverse motion g⁻¹ returns you to x.
This is the inverse law of a group action.-/
/-Result: we’ve established that act : E → (ℝ⁴ → ℝ⁴) is a homomorphism into the
  function-composition monoid—exactly what OS-2 needs for its pull-back action on fields.-/

/--
@isnad1 id=eq.0h2v.s3.96b655dacd89 from=translated src=- shape=2f232696 vocab=d77f0b79
-/
@[simp] lemma act_inv_general (g : E) (x : SpaceTime) :
    act g⁻¹ (act g x) = x := by
  cases g with
  | mk gR gt =>
      simp [act, inv_R, inv_t, add_comm, add_assoc]

/-! ### Lebesgue measure is invariant under every Euclidean motion --------- -/

open MeasureTheory

/-- For every rigid motion `g : E`, the push‑forward of Lebesgue measure `μ`
    by the map `x ↦ g • x` is again `μ`.  Equivalently, `act g` is
    measure‑preserving.
@isnad1 id=measurep.0h1v.s6.5dbd7e060d4f from=translated src=- shape=60a911a9 vocab=9c0dd888
-/
lemma measurePreserving_act (g : E) :
    MeasurePreserving (fun x : SpaceTime => act g x) μ μ := by
  have rot : MeasurePreserving (fun x : SpaceTime => g.R x) μ μ := by
    simpa using (g.R.toLinearIsometryEquiv rfl).measurePreserving
  have trans : MeasurePreserving (fun x : SpaceTime => x + g.t) μ μ := by
    refine ⟨(continuous_id.add continuous_const).measurable, ?_⟩
    simpa using map_add_right_eq_self μ g.t
  change MeasurePreserving ((fun x : SpaceTime => x + g.t) ∘ fun x : SpaceTime => g.R x) μ μ
  exact trans.comp rot

-- Helper functions for temperate growth (adapted from OS2.lean)
open Function

private lemma contDiff_act_inv (g : E) :
    ContDiff ℝ ⊤ (act g⁻¹) := by
  change ContDiff ℝ ⊤ (fun x : SpaceTime => g⁻¹.R x + g⁻¹.t)
  exact g⁻¹.R.contDiff.add contDiff_const

private theorem fderiv_act_inv_eq_linear (g : E) :
  (fun x => fderiv ℝ (act g⁻¹) x) = fun _ => g⁻¹.R.toContinuousLinearMap := by
  ext x v i
  let L := g⁻¹.R.toContinuousLinearMap
  calc (fderiv ℝ (act g⁻¹) x v) i
      = ((fderiv ℝ (fun y => L y + g⁻¹.t) x) v) i := rfl
      _ = ((fderiv ℝ L x) v) i := by rw [fderiv_add_const]
      _ = (L v) i := by rw [ContinuousLinearMap.fderiv]

private theorem fderiv_has_temperate_growth (g : E) :
    Function.HasTemperateGrowth (fun x => fderiv ℝ (act g⁻¹) x) := by
  rw [fderiv_act_inv_eq_linear g]
  exact Function.HasTemperateGrowth.const _

private theorem act_inv_poly_bound (g : E) :
    ∃ k : ℕ, ∃ C : ℝ, ∀ x : SpaceTime, ‖act g⁻¹ x‖ ≤ C * (1 + ‖x‖) ^ k := by
  use 1, (1 + ‖g⁻¹.t‖)
  intro x
  have : act g⁻¹ x = g⁻¹.R x + g⁻¹.t := by simp [act]
  rw [this]
  calc ‖g⁻¹.R x + g⁻¹.t‖
      ≤ ‖g⁻¹.R x‖ + ‖g⁻¹.t‖ := norm_add_le _ _
    _ = ‖x‖ + ‖g⁻¹.t‖ := by rw [g⁻¹.R.norm_map x]
    _ ≤ (1 + ‖g⁻¹.t‖) * (1 + ‖x‖)^1 := by
        simp only [pow_one]
        nlinarith [norm_nonneg x, norm_nonneg g⁻¹.t]
/-! ### Unified Action of Euclidean group on function spaces ---------

    UNIFIED EUCLIDEAN ACTION FRAMEWORK

    This section demonstrates how the same geometric transformation (euclideanPullback)
    can be used to define Euclidean actions on both test functions and L² functions:

    1. **Common foundation**: All actions are based on the pullback map x ↦ g⁻¹ • x
    2. **Key enabling result**: measurePreserving_act proves this map preserves Lebesgue measure
    3. **Dual routes**:
       - Test functions: Use temperate growth + Schwartz space structure
       - L² functions: Use measure preservation + Lp space structure
    4. **Unified interface**: Both yield continuous linear maps with the same group action laws

    This approach eliminates code duplication and ensures consistency between
    the test function and L² formulations of the Osterwalder-Schrader axioms.
-/

/-- The fundamental pullback map for Euclidean actions.
    This is the geometric transformation x ↦ g⁻¹ • x that underlies
    all Euclidean actions on function spaces.
-/
noncomputable def euclideanPullback (g : E) : SpaceTime → SpaceTime := act g⁻¹

/-- The Euclidean pullback map has temperate growth (needed for Schwartz space actions).
@isnad1 id=hastempe.0h1v.s7.19657df8917e from=translated src=- shape=8735051e vocab=49888927
-/
lemma euclidean_pullback_temperate_growth (g : E) :
    Function.HasTemperateGrowth (euclideanPullback g) := by
  unfold euclideanPullback
  obtain ⟨k, C, hbound⟩ := act_inv_poly_bound g
  exact Function.HasTemperateGrowth.of_fderiv
    (fderiv_has_temperate_growth g)
    ((contDiff_act_inv g).differentiable WithTop.top_ne_zero)
    hbound

/-- The Euclidean pullback map satisfies polynomial growth bounds.
@isnad1 id=ex.0h1v.s6.80a6ce80021a from=translated src=- shape=c3633840 vocab=5104c9e1
-/
lemma euclidean_pullback_polynomial_bounds (g : E) :
    ∃ (k : ℕ) (C : ℝ), ∀ (x : SpaceTime), ‖x‖ ≤ C * (1 + ‖euclideanPullback g x‖) ^ k := by
  use 1, (1 + ‖g⁻¹.t‖)
  intro x
  simp only [pow_one, euclideanPullback, act]
  have h_iso : ‖g⁻¹.R x‖ = ‖x‖ := g⁻¹.R.norm_map x
  rw [← h_iso]
  calc ‖g⁻¹.R x‖
      ≤ ‖g⁻¹.R x + g⁻¹.t‖ + ‖g⁻¹.t‖ := norm_le_add_norm_add _ _
    _ ≤ (1 + ‖g⁻¹.t‖) * (1 + ‖g⁻¹.R x + g⁻¹.t‖) := by
        nlinarith [norm_nonneg (g⁻¹.R x + g⁻¹.t), norm_nonneg g⁻¹.t]

/-- Action of Euclidean group on test functions via pullback.
    For g ∈ E and f ∈ TestFunctionℂ, define (g • f)(x) = f(g⁻¹ • x).
    This is the standard pullback action: to evaluate the transformed function
    at x, we evaluate the original function at the inverse-transformed point.
-/
noncomputable def euclideanAction (g : E) (f : TestFunctionℂ) : TestFunctionℂ :=
  SchwartzMap.compCLM (𝕜 := ℂ)
    (hg := euclidean_pullback_temperate_growth g)
    (hg_upper := euclidean_pullback_polynomial_bounds g) f

/-- Action of Euclidean group on real test functions via pullback.
    For g ∈ E and f ∈ OSforGFF.TestFunction, define (g • f)(x) = f(g⁻¹ • x).
    This is the real version of euclideanAction for OSforGFF.TestFunction = SchwartzMap SpaceTime ℝ.
-/
noncomputable def euclideanActionReal (g : E) (f : OSforGFF.TestFunction) : OSforGFF.TestFunction :=
  SchwartzMap.compCLM (𝕜 := ℝ)
    (hg := euclidean_pullback_temperate_growth g)
    (hg_upper := euclidean_pullback_polynomial_bounds g) f

/-- The measure preservation result enables both test function and L² actions.
    This is the key unifying lemma that works specifically for the spacetime measure μ.
@isnad1 id=measurep.0h1v.s6.a50827ab7bec from=translated src=- shape=9350a664 vocab=4f12be25
-/
lemma euclidean_action_unified_basis (g : E) :
    MeasurePreserving (euclideanPullback g) (μ : Measure SpaceTime) μ := by
  -- This is just measurePreserving_act applied to g⁻¹
  unfold euclideanPullback
  exact measurePreserving_act g⁻¹

/-- Action of Euclidean group on L² functions via pullback.
    For g ∈ E and f ∈ Lp ℂ 2 μ, define (g • f)(x) = f(g⁻¹ • x).
    This uses the same fundamental pullback transformation as the test function action,
    but leverages measure preservation instead of temperate growth bounds.
    Specialized for SpaceTime with Lebesgue measure.
-/
noncomputable def euclideanActionL2 (g : E)
    (f : Lp ℂ 2 (μ : Measure SpaceTime)) : Lp ℂ 2 μ :=
  Lp.compMeasurePreserving (p := 2) (euclideanPullback g) (euclidean_action_unified_basis g) f

/-- The Euclidean action as a continuous linear map on test functions.
    This leverages the Schwartz space structure and temperate growth bounds.
-/
noncomputable def euclideanActionCLM (g : E) : TestFunctionℂ →L[ℂ] TestFunctionℂ :=
  SchwartzMap.compCLM (𝕜 := ℂ)
    (hg := euclidean_pullback_temperate_growth g)
    (hg_upper := euclidean_pullback_polynomial_bounds g)

/-- Both actions are instances of the same abstract pattern.
@isnad1 id=and.0h1v.s12.6158e797c81c from=translated src=- shape=be3ddf1a vocab=5ddf366e
-/
lemma euclidean_actions_unified (g : E) :
    (∃ (T_test : TestFunctionℂ →L[ℂ] TestFunctionℂ),
       ∀ f, euclideanAction g f = T_test f) ∧
    (∃ (T_L2 : Lp ℂ 2 μ → Lp ℂ 2 μ),
       ∀ f, euclideanActionL2 g f = T_L2 f) := by
  exact ⟨⟨euclideanActionCLM g, fun _ => rfl⟩, ⟨euclideanActionL2 g, fun _ => rfl⟩⟩

end QFT
