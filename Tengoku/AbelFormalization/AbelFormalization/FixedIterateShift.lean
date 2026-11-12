import Tengoku.AbelFormalization.AbelFormalization.Inverse
import Tengoku.Seed.Algebra.Order.BigOperators.Group.Finset
import Tengoku.Seed.Analysis.SpecialFunctions.ExpDeriv
import Tengoku.Seed.Analysis.SpecialFunctions.Log.Deriv

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Quantitative calculus for a fixed iterate of `exp x - 1`

Scratch lemmas for the bounded-shift argument.  The derivative of an
iterate is written as the product along its orbit, which gives the lower
derivative and secant estimates used to locate and bound the shift.
-/

noncomputable section

open Set Function
open scoped BigOperators ContDiff

namespace AbelFormalization

/-- The derivative of `E^[d]` is the product of the derivatives of `E`
along the first `d` points of the orbit.
@isnad1 id=hasderiv.0h2v.s5.67de9adebcb1 from=translated src=- shape=0c85afcc vocab=ee06b1b4
-/
theorem hasDerivAt_E_iterate (d : ℕ) (x : ℝ) :
    HasDerivAt (E^[d])
      (Finset.prod (Finset.range d) fun k => Real.exp (E^[k] x)) x := by
  induction d with
  | zero =>
      simpa using hasDerivAt_id x
  | succ d ih =>
      have hE : HasDerivAt E (Real.exp (E^[d] x)) (E^[d] x) := by
        change HasDerivAt (fun y : ℝ => Real.exp y - 1)
          (Real.exp (E^[d] x)) (E^[d] x)
        exact (Real.hasDerivAt_exp (E^[d] x)).sub_const 1
      simpa only [Function.iterate_succ', Finset.prod_range_succ, mul_comm] using
        hE.comp x ih

/-- Formula for the derivative of a fixed iterate of `E`.
@isnad1 id=eq.0h2v.s5.0880eb812ed2 from=translated src=- shape=7e66da5f vocab=3b532758
-/
theorem deriv_E_iterate (d : ℕ) (x : ℝ) :
    deriv (E^[d]) x =
      Finset.prod (Finset.range d) fun k => Real.exp (E^[k] x) :=
  (hasDerivAt_E_iterate d x).deriv

/-! ## The bounded shift -/

/-- Iterating the one-sided inverse identity `E (L x) = x` is valid as
long as the initial argument is positive.
@isnad1 id=eq.1h2v.s4.59acaf16de69 from=translated src=- shape=c2555257 vocab=1be51c72
-/
theorem E_iterate_L_iterate {x : ℝ} (hx : 0 < x) (d : ℕ) :
    E^[d] (L^[d] x) = x := by
  induction d with
  | zero => rfl
  | succ d ih =>
      rw [Function.iterate_succ_apply (f := E),
        Function.iterate_succ_apply' (f := L),
        E_L (L_iterate_pos hx d), ih]

/-- The explicit shift obtained by applying the inverse iterate.-/
def fixedIterateShift (d : ℕ) (v c : ℝ) : ℝ :=
  L^[d] (E^[d] v + c) - v

/-! ## Smoothness -/

private theorem contDiff_E : ContDiff ℝ ∞ E := by
  change ContDiff ℝ ∞ (fun x : ℝ => Real.exp x - 1)
  exact Real.contDiff_exp.sub contDiff_const

/-- Every fixed iterate of `E` is smooth on the real line.
@isnad1 id=contdiff.0h1v.s5.c96cdbbce09b from=translated src=- shape=7ee8d25a vocab=2afc776a
-/
theorem contDiff_E_iterate (d : ℕ) : ContDiff ℝ ∞ (E^[d]) := by
  induction d with
  | zero =>
      simpa only [Function.iterate_zero] using
        (contDiff_id : ContDiff ℝ ∞ (id : ℝ → ℝ))
  | succ d ih =>
      rw [Function.iterate_succ']
      exact contDiff_E.comp ih

private theorem contDiffAt_L {x : ℝ} (hx : 0 < x) :
    ContDiffAt ℝ ∞ L x := by
  change ContDiffAt ℝ ∞ (fun y : ℝ => Real.log (1 + y)) x
  have hadd : ContDiffAt ℝ ∞ (fun y : ℝ => 1 + y) x :=
    contDiffAt_const.add contDiffAt_id
  change ContDiffAt ℝ ∞ (Real.log ∘ fun y : ℝ => 1 + y) x
  exact (Real.contDiffAt_log.2 (by linarith : 1 + x ≠ 0)).comp x hadd

/-- A fixed logarithmic iterate is smooth at every positive argument.
@isnad1 id=contdiff.1h2v.s5.4a88b6c0e637 from=translated src=- shape=390e06c4 vocab=e974fe1b
-/
theorem contDiffAt_L_iterate {x : ℝ} (hx : 0 < x) (d : ℕ) :
    ContDiffAt ℝ ∞ (L^[d]) x := by
  induction d with
  | zero =>
      simpa only [Function.iterate_zero] using
        (contDiffAt_id : ContDiffAt ℝ ∞ (id : ℝ → ℝ) x)
  | succ d ih =>
      rw [Function.iterate_succ']
      exact (contDiffAt_L (L_iterate_pos hx d)).comp x ih

/-- The fixed-iterate shift is smooth in its unbounded coordinate and its
scalar displacement whenever the input to the inverse iterate is positive.
@isnad1 id=contdiff.1h3v.s6.c6608bed3a42 from=translated src=- shape=a23451f6 vocab=c2b20c8f
-/
theorem contDiffAt_fixedIterateShift (d : ℕ) {v c : ℝ}
    (harg : 0 < E^[d] v + c) :
    ContDiffAt ℝ ∞
      (fun q : ℝ × ℝ => fixedIterateShift d q.1 q.2) (v, c) := by
  have hfirst : ContDiffAt ℝ ∞
      (fun q : ℝ × ℝ => E^[d] q.1) (v, c) := by
    change ContDiffAt ℝ ∞ ((E^[d]) ∘ Prod.fst) (v, c)
    exact (contDiff_E_iterate d).contDiffAt.comp (v, c) contDiffAt_fst
  have hinner : ContDiffAt ℝ ∞
      (fun q : ℝ × ℝ => E^[d] q.1 + q.2) (v, c) :=
    hfirst.add contDiffAt_snd
  have hreturned : ContDiffAt ℝ ∞
      (fun q : ℝ × ℝ => L^[d] (E^[d] q.1 + q.2)) (v, c) := by
    change ContDiffAt ℝ ∞
      ((L^[d]) ∘ fun q : ℝ × ℝ => E^[d] q.1 + q.2) (v, c)
    exact (contDiffAt_L_iterate harg d).comp (v, c) hinner
  change ContDiffAt ℝ ∞
    (fun q : ℝ × ℝ => L^[d] (E^[d] q.1 + q.2) - q.1) (v, c)
  exact hreturned.sub contDiffAt_fst

end AbelFormalization
