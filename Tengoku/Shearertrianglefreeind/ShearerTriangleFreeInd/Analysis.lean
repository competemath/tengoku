/-
Copyright (c) 2024 Pjotr Buys. All rights reserved.
Authors: Pjotr Buys
-/

import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Convexity of the Shearer function.

This file analyzes the function `F : ℝ → ℝ` defined by
```
F(x) = (x * log x - x + 1) / (x - 1)²  for x > 0, x ≠ 1
F(1) = 1/2
```

The main result is that `F` is convex on `(0, ∞)`.

## Main definitions

* `F` : The function under study, with explicit handling of the singularity at `x = 1`.
* `F'`, `F''` : The first and second derivatives of `F`, also with explicit singularity handling.
* `S` : The domain `{x | 0 < x ∧ x ≠ 1}` where `F` has the standard rational form.

## Main results

* `F_convex` : The function `F` is convex on `(0, ∞)`
* `F_convex_inequality` : For `0 ≤ x` and `0 < y`, we have `F x ≥ F y + F' y * (x - y)`
* `F'_nonpositive` : For `0 < x`, we have `F' x ≤ 0`
* `F_diff_equation` : The funxtion `F` satisfies `1 + (x - x^2) * F' x - (x + 1) * F x = 0`.

## Implementation notes

The proof goes by defining `F'` and `F''` explicitly, showing that they are the first and second
derivative of `F`, and proving (using the explicit form of `F''`) that `F''` is nonnegative and thus
`F` convex.

## Technical notes

* The section `General` contains auxiliary lemmas, most importantly `ContinuousAt.lhopital_iterated`
  which generalizes L'Hôpital's rule to higher-order singularities
* The section `Calculations` handles derivatives: we use `HasDerivAt.div` for `x ≠ 1` and
  the custom lemma `HasDerivAt.extend_to_singularity` for extending to `x = 1`.
-/
namespace Tengoku.Shearertrianglefreeind end Tengoku.Shearertrianglefreeind open Tengoku.Shearertrianglefreeind
open Set Filter

variable {x y : ℝ} {f f' g g' : ℝ → ℝ} {U : Set ℝ}

section General

/-!
### Derivative extension lemmas
-/

-- Extension lemma for HasDerivAt

/-!
### Auxiliary analysis lemmas
-/

lemma _root_.Tengoku.Shearertrianglefreeind.pos_of_dist_one_lt_one (hx : dist x 1 < 1) : 0 < x := by
  rw [Real.dist_eq, abs_sub_lt_iff] at hx
  linarith

-- Propagate zeros to derivatives
lemma _root_.Tengoku.Shearertrianglefreeind.frequently_deriv_eq_zero_of_frequently_eq_zero
    (hx : g x = 0)
    (hDer : ∀ᶠ (y : ℝ) in nhds x, HasDerivAt g (g' y) y)
    (hgZero : ∃ᶠ (y : ℝ) in nhdsWithin x {x}ᶜ, g y = 0) :
    ∃ᶠ (y : ℝ) in nhdsWithin x {x}ᶜ, g' y = 0 := by
  rw [frequently_nhdsWithin_iff, frequently_nhds_iff]
  intro U hxU hUopen
  rw [eventually_nhds_iff] at hDer
  have ⟨V, hVder, hVopen, hxV⟩ := hDer
  have ⟨ε, hε, hBall⟩ := Metric.isOpen_iff.1 (hUopen.inter hVopen) _ ⟨hxU, hxV⟩
  rw [frequently_nhdsWithin_iff, frequently_nhds_iff] at hgZero
  have ⟨y, hUy, hy, hynx⟩ :=  hgZero (Metric.ball x ε) (Metric.mem_ball_self hε) Metric.isOpen_ball
  rw [Set.mem_compl_singleton_iff] at hynx
  let a := min x y; let b := max x y
  have rw_cases : a = x ∧ b = y ∨ a = y ∧ b = x := by
    rcases (lt_or_gt_of_ne hynx) with hyx | hxy
    · right; exact ⟨min_eq_right_of_lt hyx, max_eq_left_of_lt hyx⟩
    · left; exact ⟨min_eq_left_of_lt hxy, max_eq_right_of_lt hxy⟩
  have hab : a < b := min_lt_max.2 hynx.symm
  have hsub : Set.Icc a b ⊆ U ∩ V := by
    refine subset_trans ?_ hBall
    refine IsConnected.Icc_subset (Metric.isConnected_ball hε) ?_ ?_
    · rcases rw_cases with h | h <;> rw[h.1]
      · exact Metric.mem_ball_self hε
      · exact hUy
    · rcases rw_cases with h | h <;> rw[h.2]
      · exact hUy
      · exact Metric.mem_ball_self hε
  have hgab : g a = 0 ∧ g b = 0 := by
    rcases rw_cases with h | h <;> rw[h.1, h.2]
    · exact ⟨hx, hy⟩
    · exact ⟨hy, hx⟩
  have hxnot : x ∉ Set.Ioo a b := by
    intro hcontra; rw [Set.mem_Ioo] at hcontra
    rcases rw_cases with h | h <;> (rw[h.1, h.2] at hcontra; linarith)
  have ⟨z,hz,hg'z⟩ := exists_hasDerivAt_eq_slope g g' hab ?_ ?_
  · rw [hgab.1, hgab.2, sub_self, zero_div] at hg'z
    use z, (hsub (Set.Ioo_subset_Icc_self hz)).1, hg'z
    intro hcontra
    rw [Set.mem_singleton_iff.1 hcontra] at hz
    exact hxnot hz
  · exact HasDerivAt.continuousOn (fun w hw  ↦ hVder _ (hsub hw).2)
  · exact (fun w hw  ↦ hVder _ (hsub (Set.Ioo_subset_Icc_self hw)).2)

lemma ContinuousAt.eq_of_frequently_eq {g : ℝ → ℝ} {a x : ℝ}
    (hZero : ∃ᶠ y in nhdsWithin x {x}ᶜ, g y = a)
    (hCont : ContinuousAt g x) :
    g x = a :=
    (tendsto_nhds_unique_of_frequently_eq
      (tendsto_nhdsWithin_of_tendsto_nhds hCont)
      tendsto_const_nhds hZero)

lemma ConvexOn.tangent_line_le (hgc : ConvexOn ℝ U g) (hx : x ∈ U) (hy : y ∈ U)
  (hg' : HasDerivAt g (g' y) y) : g y + g' y * (x - y) ≤ g x := by
  rcases lt_trichotomy x y with hxy | hxy | hxy
  · have h := hgc.slope_le_of_hasDerivAt hx hy hxy hg'
    rw [slope_def_field, div_le_iff₀ (by linarith)] at h
    linarith
  · simp only [hxy, sub_self, mul_zero, add_zero, le_refl]
  · have h := hgc.le_slope_of_hasDerivAt hy hx hxy hg'
    rw [slope_def_field, le_div_iff₀ (by linarith)] at h
    linarith

/-!
### L'Hôpital's rule
-/

-- General iterated L'Hôpital's rule
lemma ContinuousAt.lhopital_iterated (n : ℕ) (ns ds : List (ℝ → ℝ))
    (hnslen : ns.length = n + 1) (hdslen : ds.length = n + 1)
    (hnDer : ∀ k (hk : k < n), ∀ᶠ (y : ℝ) in nhds x, HasDerivAt ns[k] (ns[k + 1] y) y)
    (hdDer : ∀ k (hk : k < n), ∀ᶠ (y : ℝ) in nhds x, HasDerivAt ds[k] (ds[k + 1] y) y)
    (hnZero : ∀ k (hk : k < n), ns[k] x = 0)
    (hdZero : ∀ k (hk : k < n), ds[k] x = 0)
    (hnCont : ContinuousAt ns[n] x)
    (hdCont : ContinuousAt ds[n] x)
    (hdFinal : ds[n] x ≠ 0) :
    ContinuousAt
        (fun y ↦ if y = x
          then (ns[n] x) / (ds[n] x)
          else (ns[0] y) / (ds[0] y))
        x := by
  revert ns ds n; intro n
  induction n with
  | zero =>
    intro ns ds _ _ _ _ _ _  hnC hdC hnZ
    refine ContinuousAt.congr (ContinuousAt.div₀ hnC hdC hnZ) (Eq.eventuallyEq ?_)
    ext; split <;> simp_all only [ne_eq]
  | succ n ih =>
    intro ns ds len_ns len_ds hnDer hdDer hnZero hdZero hnC hdC hnZ
    rw [←continuousWithinAt_compl_self, ContinuousWithinAt, ite_eq_left rfl]
    apply Filter.Tendsto.congr' (f₁ := fun y ↦ (ns[0] y) / (ds[0] y) )
      (eventually_nhdsWithin_of_forall fun y hy ↦ (ite_eq_right hy).symm)
    have hn : 0 < n + 1 := Nat.zero_lt_succ _
    have hn_tail : ns.tail.length = n + 1 := by
      rw [List.length_tail, len_ns, add_tsub_cancel_right, Nat.add_left_cancel_iff]
    have hd_tail : ds.tail.length = n + 1 := by
      rw [List.length_tail, len_ds, add_tsub_cancel_right, Nat.add_left_cancel_iff]
    refine HasDerivAt.lhopital_zero_nhdsNE (f' := ns[1]) (g' := ds[1]) ?_ ?_ ?_ ?_ ?_ ?_
    · exact eventually_nhdsWithin_of_eventually_nhds (hnDer 0 hn)
    · exact eventually_nhdsWithin_of_eventually_nhds (hdDer 0 hn)
    · by_contra hcontra
      simp_rw [Filter.not_eventually, not_ne_iff] at hcontra
      have hInd : ∀ k (hk : k < n + 1), ∃ᶠ (x : ℝ) in nhdsWithin x {x}ᶜ, ds[k+1] x = 0 := by
        intro k
        induction k with
        | zero => exact fun _ ↦ hcontra
        | succ _ ih =>
          exact fun _ ↦ frequently_deriv_eq_zero_of_frequently_eq_zero (hdZero _ (by linarith))
            (hdDer _ (by linarith)) (ih (by linarith))
      specialize hInd n (by linarith)
      exact hnZ (ContinuousAt.eq_of_frequently_eq hInd hdC)
    · rw [←(hnZero 0 hn)]
      refine continuousWithinAt_compl_self.2 ?_
      exact HasDerivAt.continuousAt (hnDer 0 hn).self_of_nhds
    · rw [←(hdZero 0 hn)]
      refine continuousWithinAt_compl_self.2 ?_
      exact HasDerivAt.continuousAt (hdDer 0 hn).self_of_nhds
    · specialize ih ns.tail ds.tail hn_tail hd_tail ?_ ?_ ?_ ?_ ?_ ?_ ?_
      · intro k hk
        convert hnDer (k+1) (by linarith) using 3
        · refine List.getElem_tail (by linarith)
        · simp
      · intro k hk
        convert hdDer (k+1) (by linarith) using 3
        · refine List.getElem_tail (by linarith)
        · simp
      · exact fun k hk ↦ by convert hnZero (k + 1) (by linarith) using 1; simp
      · exact fun k hk ↦ by convert hdZero (k + 1) (by linarith) using 1; simp
      · convert hnC using 1; simp
      · convert hdC using 1; simp
      · convert hnZ using 1; simp
      · rw [←continuousWithinAt_compl_self, ContinuousWithinAt, ite_eq_left rfl] at ih
        convert Filter.Tendsto.congr' ?_ ih using 2
        · simp
        · refine eventually_nhdsWithin_of_forall ?_
          intro y hy
          rw [Set.mem_compl_iff, Set.mem_singleton_iff] at hy
          simp [ite_eq_right hy]

end General

/-!
### Function analysis and calculations
-/

noncomputable section Calculations

open Polynomial

/-!
### Main definitions
-/

-- Domain
def _root_.Tengoku.Shearertrianglefreeind.S : Set ℝ := {x | 0 < x ∧ x ≠ 1}

-- Main function `F` and its derivatives.
def _root_.Tengoku.Shearertrianglefreeind.F : ℝ → ℝ := fun x ↦
  if x = 1 then 1/2
  else          (x * Real.log x - x + 1) / (x - 1)^2

def _root_.Tengoku.Shearertrianglefreeind.F' : ℝ → ℝ := fun x ↦
  if x = 1 then -1/6
  else          (-2 + 2*x - Real.log x - x * Real.log x) / (x - 1)^3

def _root_.Tengoku.Shearertrianglefreeind.F'' : ℝ → ℝ := fun x ↦
  if x = 1 then 1/6
  else          (1 + 4*x - 5*x^2 + 4 * x * Real.log x + 2 * x^2 * Real.log x) / ((x - 1)^4 * x)

/-!
### Numerators and denominators of F, F', and F''.
-/
-- `F`
def _root_.Tengoku.Shearertrianglefreeind.nF₀ : ℝ → ℝ := fun x ↦ x * Real.log x - x + 1
def _root_.Tengoku.Shearertrianglefreeind.nF₁ : ℝ → ℝ := fun x ↦ Real.log x
def _root_.Tengoku.Shearertrianglefreeind.nF₂ : ℝ → ℝ := fun x ↦ 1/x

def _root_.Tengoku.Shearertrianglefreeind.dF₀ : ℝ → ℝ := fun x ↦ (x - 1)^2
def _root_.Tengoku.Shearertrianglefreeind.dF₁ : ℝ → ℝ := fun x ↦ 2 * (x - 1)
def _root_.Tengoku.Shearertrianglefreeind.dF₂ : ℝ → ℝ := fun _ ↦ 2

-- `F'`
def _root_.Tengoku.Shearertrianglefreeind.nF'₀ : ℝ → ℝ := fun x ↦ -2 + 2*x - Real.log x - x * Real.log x
def _root_.Tengoku.Shearertrianglefreeind.nF'₁ : ℝ → ℝ := fun x ↦ 1 - 1/x - Real.log x
def _root_.Tengoku.Shearertrianglefreeind.nF'₂ : ℝ → ℝ := fun x ↦ 1 / x^2 - 1 / x
def _root_.Tengoku.Shearertrianglefreeind.nF'₃ : ℝ → ℝ := fun x ↦ -2 / x^3 + 1 / x^2

def _root_.Tengoku.Shearertrianglefreeind.dF'₀ : ℝ → ℝ := fun x ↦ (x - 1)^3
def _root_.Tengoku.Shearertrianglefreeind.dF'₁ : ℝ → ℝ := fun x ↦ 3 * (x - 1)^2
def _root_.Tengoku.Shearertrianglefreeind.dF'₂ : ℝ → ℝ := fun x ↦ 6 * (x - 1)
def _root_.Tengoku.Shearertrianglefreeind.dF'₃ : ℝ → ℝ := fun _ ↦ 6

-- `F''`
def _root_.Tengoku.Shearertrianglefreeind.nF''₀ : ℝ → ℝ := fun x ↦ 1 + 4*x - 5*x^2 + 4 * x * Real.log x + 2 * x^2 * Real.log x
def _root_.Tengoku.Shearertrianglefreeind.nF''₁ : ℝ → ℝ := fun x ↦ 8 - 8 * x + 4 * Real.log x  + 4 * x * Real.log x
def _root_.Tengoku.Shearertrianglefreeind.nF''₂ : ℝ → ℝ := fun x ↦ -4 + 4/x + 4 * Real.log x
def _root_.Tengoku.Shearertrianglefreeind.nF''₃ : ℝ → ℝ := fun x ↦ -4 / x^2 + 4 / x
def _root_.Tengoku.Shearertrianglefreeind.nF''₄ : ℝ → ℝ := fun x ↦ 8 / x^3 - 4 / x^2

def _root_.Tengoku.Shearertrianglefreeind.dF''₀ : ℝ → ℝ := fun x ↦ (x - 1)^4 * x
def _root_.Tengoku.Shearertrianglefreeind.dF''₁ : ℝ → ℝ := fun x ↦ 1 - 8 * x + 18 * x^2 - 16 * x^3 + 5 * x^4
def _root_.Tengoku.Shearertrianglefreeind.dF''₂ : ℝ → ℝ := fun x ↦ -8 + 36 * x - 48 * x^2 + 20 * x^3
def _root_.Tengoku.Shearertrianglefreeind.dF''₃ : ℝ → ℝ := fun x ↦ 36 - 96 * x + 60 * x^2
def _root_.Tengoku.Shearertrianglefreeind.dF''₄ : ℝ → ℝ := fun x ↦ -96 + 120 * x

/-!
### Lemmas about S
-/

lemma _root_.Tengoku.Shearertrianglefreeind.S_open : IsOpen S := IsOpen.and (isOpen_lt' 0) (isOpen_ne)

lemma _root_.Tengoku.Shearertrianglefreeind.pos_not_in_S_eq_one (hx_pos : 0 < x) (hx_not_in_S : x ∉ S) : x = 1 := by
  by_contra hxn1
  exact hx_not_in_S ⟨hx_pos, hxn1⟩

/-!
### F, F', and F'' equal to rational functions on S
-/

lemma _root_.Tengoku.Shearertrianglefreeind.F_not_one (hx : x ≠ 1) : F x   = nF₀ x / dF₀ x       := ite_eq_right hx
lemma _root_.Tengoku.Shearertrianglefreeind.F'_not_one (hx : x ≠ 1) : F' x  = nF'₀ x / dF'₀ x     := ite_eq_right hx
lemma _root_.Tengoku.Shearertrianglefreeind.F''_not_one (hx : x ≠ 1) : F'' x = nF''₀ x / dF''₀ x   := ite_eq_right hx

lemma _root_.Tengoku.Shearertrianglefreeind.F_at_zero : F 0    = 1  := by simp [F]
lemma _root_.Tengoku.Shearertrianglefreeind.F_at_one : F 1    = 1/2  := ite_eq_left rfl
lemma _root_.Tengoku.Shearertrianglefreeind.F'_at_one : F' 1   = -1/6 := ite_eq_left rfl
lemma _root_.Tengoku.Shearertrianglefreeind.F''_at_one : F'' 1  = 1/6  := ite_eq_left rfl

lemma _root_.Tengoku.Shearertrianglefreeind.F_on_S : S.EqOn F    (fun x ↦ nF₀ x    / dF₀ x)    := fun _ hx ↦ ite_eq_right hx.2
lemma _root_.Tengoku.Shearertrianglefreeind.F'_on_S : S.EqOn F'   (fun x ↦ nF'₀ x   / dF'₀ x)   := fun _ hx ↦ ite_eq_right hx.2
lemma _root_.Tengoku.Shearertrianglefreeind.F''_on_S : S.EqOn F''  (fun x ↦ nF''₀ x  / dF''₀ x)  := fun _ hx ↦ ite_eq_right hx.2

/-!
### Derivatives of the numerators and denominators of F, F' and F''
-/

/-!
  Two helpful rewrite lemmas about the derivatives of `x ↦ 1/x` and `x ↦ 1/x^2`.
-/

lemma _root_.Tengoku.Shearertrianglefreeind.hasDerivAtInv (hx : 0 < x) : HasDerivAt (fun y ↦ 1 / y) (- 1 / x^2) x := by
  convert hasDerivAt_inv (ne_of_lt hx).symm using 1
  · ext _; ring
  · ring
  first
    | (all_goals grind; done)
    | (all_goals simp_all; done)
    | (all_goals aesop; done)
    | (all_goals omega; done)
    | (all_goals norm_num; done)
    | (all_goals positivity; done)
    | (all_goals linarith; done)
    | (all_goals decide; done)
    | (all_goals tauto; done)

lemma _root_.Tengoku.Shearertrianglefreeind.hasDerivAt_nF''₂ (hx : 0 < x) : HasDerivAt nF''₂ (nF''₃ x) x := by
  unfold nF''₂ nF''₃
  convert! HasDerivAt.add
    (f := fun x ↦ -4 + 4/x) (f' := -4 / x^2) ?_
    (HasDerivAt.const_mul 4 (Real.hasDerivAt_log (ne_of_lt hx).symm)) using 1
  convert! HasDerivAt.add (hasDerivAt_const x (-4))
    (HasDerivAt.const_mul 4 (hasDerivAtInv hx)) using 1
  · ext _; rw [Pi.add_apply]; ring
  · ring

/-!
### Continuity of (derivatives of) denominators and numerators
-/

lemma _root_.Tengoku.Shearertrianglefreeind.ContinuousAt_dF₀ : ContinuousAt dF₀ x := by
  unfold dF₀
  exact ContinuousAt.pow (ContinuousAt.sub (by exact fun ⦃U⦄ a ↦ a) continuousAt_const) _

lemma _root_.Tengoku.Shearertrianglefreeind.ContinuousAt_nF₀ : ContinuousAt nF₀ x  :=
  ContinuousAt.add (ContinuousAt.sub (Continuous.continuousAt Real.continuous_mul_log ) fun _ a ↦ a)
    continuousAt_const

lemma _root_.Tengoku.Shearertrianglefreeind.ContinuousAt_nF₂ (hx : 0 < x) : ContinuousAt nF₂ x := by unfold nF₂; continuity

lemma _root_.Tengoku.Shearertrianglefreeind.ContinuousAt_dF₂ : ContinuousAt dF₂ x := continuousAt_const

lemma _root_.Tengoku.Shearertrianglefreeind.ContinuousAt_nF'₃ (hx : 0 < x) : ContinuousAt nF'₃ x := by
  refine ContinuousAt.add ?_ ?_ <;>
  exact ContinuousAt.div₀ continuousAt_const
    (ContinuousAt.pow (by exact fun _ a ↦ a) _) (by positivity)

lemma _root_.Tengoku.Shearertrianglefreeind.ContinuousAt_dF'₃ : ContinuousAt dF'₃ x := continuousAt_const

lemma _root_.Tengoku.Shearertrianglefreeind.ContinuousAt_nF''₄ (hx : 0 < x) : ContinuousAt nF''₄ x := by
  refine ContinuousAt.add ?_ (ContinuousAt.neg ?_) <;>
  exact ContinuousAt.div₀ continuousAt_const
    (ContinuousAt.pow (by exact fun _ a ↦ a) _) (by positivity)

lemma _root_.Tengoku.Shearertrianglefreeind.ContinuousAt_dF''₄ : ContinuousAt dF''₄ x := by
  unfold dF''₄
  exact Continuous.continuousAt (by continuity)

/-!
### Useful (in)equalities involving the denominators and numerators
-/

lemma _root_.Tengoku.Shearertrianglefreeind.dF₀_ne_zero (hx : x ≠ 1) : dF₀ x ≠ 0      := pow_ne_zero 2 (sub_ne_zero_of_ne hx)
lemma _root_.Tengoku.Shearertrianglefreeind.dF₀_ne_zero_on_S (hx : x ∈ S) : dF₀ x ≠ 0 := dF₀_ne_zero hx.2

lemma _root_.Tengoku.Shearertrianglefreeind.dF'₀_ne_zero (hx : x ≠ 1) : dF'₀ x ≠ 0      := pow_ne_zero 3 (sub_ne_zero_of_ne hx)
lemma _root_.Tengoku.Shearertrianglefreeind.dF'₀_ne_zero_on_S (hx : x ∈ S) : dF'₀ x ≠ 0 := dF'₀_ne_zero hx.2
lemma _root_.Tengoku.Shearertrianglefreeind.dF'₀_nonneg (hx : 1 < x) : 0 ≤ dF'₀ x       := pow_nonneg (by linarith) 3

lemma _root_.Tengoku.Shearertrianglefreeind.dF''₀_nonneg (hx : 0 < x) : 0 ≤ dF''₀ x  := by unfold dF''₀; positivity

lemma _root_.Tengoku.Shearertrianglefreeind.dF''₀_ne_zero_on_S (hx : x ∈ S) : dF''₀ x ≠ 0   :=
  (mul_ne_zero_iff_right (ne_of_lt hx.1).symm).mpr (pow_ne_zero 4 (sub_ne_zero_of_ne hx.2))

/-!
  To prove that `nF''₀` is nonnegative we define two types of functions:
  `isType1`: Nonincreasing on (0,1], nondecreasing on [1,∞) and zero at x = 1.
  `isType2`: Nonpositive on (0,1] and nonnegative on [1,∞).
  We prove that a function `l` with `l 1 = 0` whose derivative is one type is itself the other type.
-/

def _root_.Tengoku.Shearertrianglefreeind.isType1 (l : ℝ → ℝ) :=  AntitoneOn l (Ioc 0 1) ∧ MonotoneOn l (Ici 1) ∧ (l 1 = 0)
def _root_.Tengoku.Shearertrianglefreeind.isType2 (l : ℝ → ℝ) :=  (∀ {x}, x ∈ Ioc 0 1 → l x ≤ 0) ∧ (∀ {x}, x ∈ Ici 1 → 0 ≤ l x)

lemma _root_.Tengoku.Shearertrianglefreeind.Type1_nonneg {l : ℝ → ℝ} (hType : isType1 l) (hx : 0 < x) : 0 ≤ l x := by
  rw [←hType.2.2]
  rcases le_or_gt x 1 with hx1 | hx1
  · exact hType.1 ⟨hx,hx1⟩ ⟨Real.zero_lt_one, le_refl 1⟩ hx1
  · exact hType.2.1 self_mem_Ici (mem_Ici_of_Ioi hx1) (le_of_lt hx1)

lemma _root_.Tengoku.Shearertrianglefreeind.Type2_mul_nonneg {l m : ℝ → ℝ} (hType : isType2 l) (hm : ∀ {x}, 0 < x → 0 ≤ m x) :
  isType2 (fun x ↦ l x * m x) :=
  ⟨ fun hx ↦ mul_nonpos_of_nonpos_of_nonneg (hType.1 hx) (hm hx.1),
    fun hx ↦ Left.mul_nonneg (hType.2 hx) (hm (by linarith [mem_Ici.1 hx]))⟩

lemma _root_.Tengoku.Shearertrianglefreeind.DerivAt_Type1_imp_Type2 {l l' : ℝ → ℝ} (hType : isType1 l')
    (hDer : ∀ {x}, 0 < x → HasDerivAt l (l' x) x)
    (h : l 1 = 0) : isType2 l := by
  have h_mon : MonotoneOn l (Ioi 0) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (f' := l')
    · exact fun _ hx ↦ ContinuousAt.continuousWithinAt (HasDerivAt.continuousAt (hDer hx))
    · rw [interior_Ioi]
      exact fun y hy ↦ HasDerivAt.hasDerivWithinAt (hDer hy)
    · rw [interior_Ioi]
      exact fun x hx ↦ Type1_nonneg hType hx
    · exact convex_Ioi 0
  refine ⟨?_,?_⟩ <;> (intro x hx; rw [←h])
  · exact h_mon (mem_of_mem_inter_left hx) (by norm_num) (by exact hx.2)
  · refine h_mon (by norm_num) ?_ (by exact hx)
    rw [mem_Ioi]; rw [mem_Ici] at hx; linarith

lemma _root_.Tengoku.Shearertrianglefreeind.DerivAt_Type2_imp_Type1 {l l' : ℝ → ℝ} (hType : isType2 l')
    (hDer : ∀ {x}, 0 < x → HasDerivAt l (l' x) x)
    (h : l 1 = 0) : isType1 l := by
  refine ⟨?_, ⟨?_, h⟩⟩
  · apply antitoneOn_of_hasDerivWithinAt_nonpos (f' := l')
    · exact fun _ hx ↦ ContinuousAt.continuousWithinAt (HasDerivAt.continuousAt (hDer hx.1))
    · rw [interior_Ioc]
      exact fun y hy ↦ HasDerivAt.hasDerivWithinAt (hDer hy.1)
    · rw [interior_Ioc]
      exact fun x hx ↦ (hType.1 (mem_Ioc_of_Ioo hx))
    · exact convex_Ioc 0 1
  · apply monotoneOn_of_hasDerivWithinAt_nonneg (f' := l')
    · exact fun _ hx ↦ ContinuousAt.continuousWithinAt
        (HasDerivAt.continuousAt (hDer (by linarith [mem_Ici.1 hx])))
    · rw [interior_Ici]
      exact fun y hy ↦ HasDerivAt.hasDerivWithinAt (hDer (by linarith [mem_Ioi.1 hy]))
    · rw [interior_Ici]
      exact fun x hx ↦ (hType.2 (mem_Ici_of_Ioi hx))
    · exact convex_Ici 1

/-!
  We prove that the first few derivatives of `nF''₀` alternate between these two types.
-/

lemma _root_.Tengoku.Shearertrianglefreeind.isType2_nF''₃ : isType2 nF''₃ := by
  convert Type2_mul_nonneg (l := fun x ↦ -4 + 4*x) (m := fun x ↦ 1 / x^2) ?_ ?_ using 1
  · unfold nF''₃; ext x;
    by_cases hx : x = 0
    · rw [hx]; simp
    · field_simp
  · refine ⟨?_,?_⟩ <;> (intro _ _; simp_all)
  · intro _ _; simp [sq_nonneg]

lemma _root_.Tengoku.Shearertrianglefreeind.isType1_nF''₂ : isType1 nF''₂ :=
  DerivAt_Type2_imp_Type1 isType2_nF''₃ hasDerivAt_nF''₂ (by norm_num [nF''₂])

/-!
  As a convenient corollary we find that nF'₀ is nonpositive.
-/

/-!
### Continuity of F, F' and F'' at x = 1.
-/

/-!
### Derivatives of F, F'.
-/

/-!
  First two auxilliary lemmas giving the derivatives on S.
-/

/-!
  Then the derivatives on (0,∞).
-/

/-!
### Continuity of F, F'.
-/

/-
### Convexity of F, nonpositivity of F' and F is at most 1.
-/

/-
### Finally the differential equation that F satisfies.
-/

lemma _root_.Tengoku.Shearertrianglefreeind.F_diff_equation : (x - x^2) * F' x - (x + 1) * F x + 1 = 0 := by
  by_cases hx : x = 1
  · rw [hx, F_at_one, F'_at_one]; norm_num
  · rw [F_not_one hx, F'_not_one hx, ←mul_right_inj' (dF₀_ne_zero hx),
        ←mul_right_inj' (dF'₀_ne_zero hx), mul_zero, mul_zero]
    field_simp [(dF₀_ne_zero hx), (dF'₀_ne_zero hx)]
    unfold dF₀ dF'₀ nF₀ nF'₀
    ring
-- Tengoku: root names of this library moved to Tengoku.Shearertrianglefreeind so they do not collide with other libraries (generated)
