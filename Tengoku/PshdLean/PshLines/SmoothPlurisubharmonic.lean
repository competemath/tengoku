import Tengoku.PshdLean.PshLines.CircleSubmean
import Tengoku.PshdLean.PshLines.SubmeanLaplacian

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Nonnegative Levi forms give actual plurisubharmonic functions

This implication joins the actual real Hessian chain rule, the classical
Laplacian submean theorem, and the extended-real disc definition. No PSH
or current correspondence is supplied as an assumption.
-/

open Set Metric Laplacian

namespace PshLines

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E]

/-- The smooth Levi criterion implies the extended-real disc inequalities.
@isnad1 id=discpsho.2h3v.s8.360e102f7e7d from=translated src=- shape=2294cf80 vocab=5c12b342
-/
theorem discPshOn_of_levi_nonneg {u : E → ℝ} {U : Set E}
    (hu : ContDiff ℝ 2 u) (hL : ∀ x ∈ U, ∀ v : E, 0 ≤ leviForm u x v) :
    DiscPshOn (fun y => (u y : EReal)) U := by
  apply discPshOn_of_circleAverage hu.continuous
  intro x v r hr hD
  have hline : ContDiff ℝ 2 (fun z : ℂ => u (x + z • v)) := by
    exact hu.comp (contDiff_const.add (complexLineLinear v).contDiff)
  have hΔ : ∀ z ∈ closedBall (0 : ℂ) r,
      0 ≤ Δ (fun t : ℂ => u (x + t • v)) z := by
    intro z hz
    apply (laplacian_complexLine_nonneg_iff hu x v z).mpr
    exact hL _ (hD ⟨z, hz, rfl⟩) v
  simpa only [zero_smul, add_zero] using
    submean_of_laplacian_nonneg hline 0 hr.le hΔ

/--
@isnad1 id=plurisub.3h3v.s8.fd958114df7c from=translated src=- shape=5666c88d vocab=b6c76608
-/
theorem plurisubharmonicOn_of_levi_nonneg {u : E → ℝ} {U : Set E}
    (hu : ContDiff ℝ 2 u) (hU : IsOpen U)
    (hL : ∀ x ∈ U, ∀ v : E, 0 ≤ leviForm u x v) :
    PlurisubharmonicOn (fun y => (u y : EReal)) U :=
  (discPshOn_of_levi_nonneg hu hL).plurisubharmonicOn hU

section QuadraticPotential

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [NormedSpace ℂ H] [IsScalarTower ℝ ℂ H]

/-- A concrete nonconstant PSH potential, established by genuine calculus.
@isnad1 id=discpsho.0h2v.s7.4c3e56d60f7e from=translated src=- shape=85e4dd07 vocab=ec58e2f2
-/
theorem discPshOn_norm_sq (U : Set H) :
    DiscPshOn (fun y : H => ((‖y‖ ^ 2 : ℝ) : EReal)) U :=
  discPshOn_of_levi_nonneg (contDiff_norm_sq ℝ)
    (fun x _ v => leviForm_norm_sq_nonneg x v)

/--
@isnad1 id=plurisub.0h2v.s7.8c19f6fdd07a from=translated src=- shape=2b203a18 vocab=d78a3608
-/
theorem plurisubharmonicAt_norm_sq (x : H) :
    PlurisubharmonicAt (fun y : H => ((‖y‖ ^ 2 : ℝ) : EReal)) x :=
  (discPshOn_norm_sq univ).plurisubharmonicOn isOpen_univ x (mem_univ x)

end QuadraticPotential

end PshLines
