import Tengoku.Seed.Analysis.Complex.Schwarz

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # A uniformly bounded analytic divided-difference remainder

The difference quotient at zero extends analytically over zero, with value
`f' 0`.  Schwarz's lemma bounds this remainder throughout the full disk by
twice the bound for `f`, divided by the disk radius.
-/

noncomputable section

open Set Metric
open scoped Topology

namespace AbelFormalization

/-- The analytic continuation of `(f q - f 0) / q` through `q = 0`.-/
def analyticRemainder (f : ℂ → ℂ) : ℂ → ℂ := dslope f 0

/--
@isnad1 id=eq.0h1v.s5.cfc1e5df16bd from=translated src=- shape=38886ea6 vocab=dd7be0ff
-/
theorem analyticRemainder_zero (f : ℂ → ℂ) : analyticRemainder f 0 = deriv f 0 :=
  dslope_same f 0

/--
@isnad1 id=eq.1h2v.s5.2a0d0ab29313 from=translated src=- shape=ecd14b7e vocab=4cbca56d
-/
theorem analyticRemainder_eq_div (f : ℂ → ℂ) {q : ℂ} (hq : q ≠ 0) :
    analyticRemainder f q = (f q - f 0) / q := by
  simp only [analyticRemainder, dslope_of_ne f hq, slope_def_module,
    sub_zero, smul_eq_mul, div_eq_inv_mul]

/-- The remainder identity holds at every point, including zero.
@isnad1 id=eq.0h2v.s5.3902bf6149bf from=translated src=- shape=610e5336 vocab=cacada79
-/
theorem analyticRemainder_identity (f : ℂ → ℂ) (q : ℂ) :
    f q = f 0 + q * analyticRemainder f q := by
  have he := sub_smul_dslope f 0 q
  simp only [sub_zero, smul_eq_mul] at he
  dsimp only [analyticRemainder]
  rw [he]
  ring

/--
@isnad1 id=analytic.2h2v.s6.65c9d2830bf2 from=translated src=- shape=8de898e2 vocab=bce05df9
-/
theorem analyticOnNhd_analyticRemainder {f : ℂ → ℂ} {R : ℝ} (hR : 0 < R)
    (hf : AnalyticOnNhd ℂ f (ball (0 : ℂ) R)) :
    AnalyticOnNhd ℂ (analyticRemainder f) (ball (0 : ℂ) R) :=
  ((Complex.differentiableOn_dslope (ball_mem_nhds 0 hR)).mpr
    hf.differentiableOn).analyticOnNhd isOpen_ball

/-- The full-disk bound includes the derivative value at the center.
@isnad1 id=le.4h4v.s7.5f5067ac2269 from=translated src=- shape=52429e56 vocab=1311b887
-/
theorem norm_analyticRemainder_le {f : ℂ → ℂ} {R S : ℝ} (hR : 0 < R)
    (hf : AnalyticOnNhd ℂ f (ball (0 : ℂ) R))
    (hbound : ∀ q ∈ ball (0 : ℂ) R, ‖f q‖ ≤ S)
    {q : ℂ} (hq : q ∈ ball (0 : ℂ) R) :
    ‖analyticRemainder f q‖ ≤ 2 * S / R := by
  have hm : MapsTo f (ball (0 : ℂ) R) (closedBall (f 0) (2 * S)) := by
    intro z hz
    change dist (f z) (f 0) ≤ 2 * S
    calc
      dist (f z) (f 0) = ‖f z - f 0‖ := dist_eq_norm _ _
      _ ≤ ‖f z‖ + ‖f 0‖ := norm_sub_le _ _
      _ ≤ S + S := add_le_add (hbound z hz) (hbound 0 (mem_ball_self hR))
      _ = 2 * S := by ring
  exact Complex.norm_dslope_le_div_of_mapsTo_ball hf.differentiableOn hm hq

/-- A bounded analytic function has a bounded analytic first-order remainder,
uniformly on the same disk.
@isnad1 id=ex.3h3v.s8.6ba780949e65 from=translated src=- shape=c3260dc2 vocab=8aa41d9a
-/
theorem exists_bounded_analytic_remainder {f : ℂ → ℂ} {R S : ℝ} (hR : 0 < R)
    (hf : AnalyticOnNhd ℂ f (ball (0 : ℂ) R))
    (hbound : ∀ q ∈ ball (0 : ℂ) R, ‖f q‖ ≤ S) :
    ∃ H : ℂ → ℂ, AnalyticOnNhd ℂ H (ball (0 : ℂ) R) ∧
      (∀ q : ℂ, f q = f 0 + q * H q) ∧
      ∀ q ∈ ball (0 : ℂ) R, ‖H q‖ ≤ 2 * S / R :=
  ⟨analyticRemainder f, analyticOnNhd_analyticRemainder hR hf,
    analyticRemainder_identity f, fun _ hq => norm_analyticRemainder_le hR hf hbound hq⟩

end AbelFormalization
