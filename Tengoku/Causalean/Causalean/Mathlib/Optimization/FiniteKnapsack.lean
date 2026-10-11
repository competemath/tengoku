module
public import Tengoku.Causalean.Causalean.Mathlib.Optimization.KKT
public import Tengoku

/-!
Finite fractional-knapsack optimization. This module proves attainment on the
finite policy box, derives the KKT shadow-price identity, and packages primal
attainment with an exact dual representation.
-/

public section

open scoped BigOperators RealInnerProductSpace
open Set

namespace Causalean.Mathlib.Optimization

/-- A finite fractional knapsack with [dimension, weights, item values, budget, and a
nonnegative-budget certificate](hyp:d,p,tau,b,hb) [has a feasible policy that maximizes the
weighted value over every box-constrained policy within budget](goal). -/
lemma finite_knapsack_attains {d : ℕ} (p tau : Fin d → ℝ) (b : ℝ)
    (hb : 0 ≤ b) :
    ∃ pi : EuclideanSpace ℝ (Fin d),
      (∀ j, pi j ∈ Set.Icc (0 : ℝ) 1) ∧
      (∑ j, p j * pi j) ≤ b ∧
      ∀ rho : EuclideanSpace ℝ (Fin d),
        (∀ j, rho j ∈ Set.Icc (0 : ℝ) 1) →
        (∑ j, p j * rho j) ≤ b →
        (∑ j, p j * rho j * tau j) ≤ ∑ j, p j * pi j * tau j := by
  classical
  let box : Set (EuclideanSpace ℝ (Fin d)) :=
    WithLp.toLp 2 '' Set.pi Set.univ (fun _ : Fin d => Set.Icc (0 : ℝ) 1)
  let cost : EuclideanSpace ℝ (Fin d) → ℝ := fun x => ∑ j, p j * x j
  let value : EuclideanSpace ℝ (Fin d) → ℝ := fun x => ∑ j, p j * x j * tau j
  have hbox : IsCompact box := by
    exact (isCompact_univ_pi fun _ : Fin d => isCompact_Icc).image
      (PiLp.continuous_toLp 2 (fun _ : Fin d => ℝ))
  have hcost : Continuous cost := by
    dsimp [cost]
    fun_prop
  have hvalue : Continuous value := by
    dsimp [value]
    fun_prop
  let K := box ∩ {x | cost x ≤ b}
  have hK : IsCompact K := hbox.inter_right (isClosed_le hcost continuous_const)
  have h0box : (0 : EuclideanSpace ℝ (Fin d)) ∈ box := by
    refine ⟨0, ?_, ?_⟩
    · intro j _
      norm_num
    · rfl
  have h0K : (0 : EuclideanSpace ℝ (Fin d)) ∈ K := by
    exact ⟨h0box, by simpa [cost] using hb⟩
  obtain ⟨pi, hpiK, hpiMax⟩ := hK.exists_isMaxOn ⟨0, h0K⟩ hvalue.continuousOn
  refine ⟨pi, ?_, hpiK.2, ?_⟩
  · rintro j
    obtain ⟨x, hx, rfl⟩ := hpiK.1
    exact hx j (Set.mem_univ j)
  · intro rho hrho hcostrho
    apply hpiMax
    refine ⟨?_, hcostrho⟩
    refine ⟨fun j => rho j, ?_, ?_⟩
    intro j _
    exact hrho j
    ext j
    rfl

end Causalean.Mathlib.Optimization
