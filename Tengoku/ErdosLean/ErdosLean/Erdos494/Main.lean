import Tengoku.ErdosLean.ErdosLean.Erdos494.Defs
import Tengoku.ErdosLean.ErdosLean.Erdos494.Parts.PowerSumsDetermine
import Tengoku.ErdosLean.ErdosLean.Erdos494.Parts.KSumPowerSum
import Tengoku.ErdosLean.ErdosLean.Erdos494.Parts.Kruyt
import Tengoku.ErdosLean.ErdosLean.Erdos494.Parts.TaoNeg
import Tengoku.ErdosLean.ErdosLean.Erdos494.Parts.Divisibility
import Tengoku.ErdosLean.ErdosLean.Erdos494.Parts.BoundedJ
import Tengoku.ErdosLean.ErdosLean.Erdos494.Parts.TwoTermApprox
import Tengoku.ErdosLean.ErdosLean.Erdos494.Parts.ExactCase
import Tengoku.ErdosLean.ErdosLean.Erdos494.Parts.SmoothGap

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Erdős Problem 494 (JSP-000399): main theorem

Assembly of [GFS62]:
* algebraic layer (Selfridge–Straus): if `f_s(n,j) ≠ 0` for all `j ≥ 1` then `A_s` and `|A| = n`
  determine all power sums of `A`, hence `A`;
* number-theoretic core `GFSCore`: bounded `j` is trivial; otherwise `f = 0` forces a two-term
  near-equality between `P`-smooth numbers (`two_term_approx` + `gfs_dvd`), which the
  Ridout-type gap theorem `smooth_gap` turns into an exact equality, excluded by `exact_case`.
-/

open Filter

namespace Erdos494

/-- Selfridge–Straus: nonvanishing of `f_s(n, ·)` gives uniqueness for `|A| = n`.
@isnad1 id=erdos494.1h2v.s4.1b3381d1f7d3 from=translated src=- shape=2c3d2ad7 vocab=3f361a70
-/
theorem unique_of_gfsPoly_ne_zero (s n : ℕ) (hcore : ∀ j, 1 ≤ j → gfsPoly s n j ≠ 0) :
    Erdos494Unique s n := by
  intro A B hA hB hAB
  have hall : ∀ j, 1 ≤ j → psum A j = psum B j := by
    intro j
    induction j using Nat.strong_induction_on with
    | _ j ih =>
      intro hj
      have hlow : ∀ l, 1 ≤ l → l < j → psum A l = psum B l := fun l hl hlj => ih l hlj hl
      have key := ksum_power_sum A B n s j hA hB hj hlow
      have hk : ksumPsum A s j = ksumPsum B s j := by simp [ksumPsum, hAB]
      rw [hk, sub_self] at key
      have hne : (gfsPoly s n j : ℂ) ≠ 0 := by exact_mod_cast hcore j hj
      exact sub_eq_zero.1 ((mul_eq_zero.1 key.symm).resolve_left hne)
  exact power_sums_determine A B n hA hB fun j hj _ => hall j hj

end Erdos494
