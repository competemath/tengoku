import Tengoku.Linearhadwiger.HadwigerLean.Woven.OuterScales
import Tengoku.Seed.Tactic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The integer chromatic budget for the outer woven recursion
-/

namespace HadwigerLean
namespace Woven

/-- The costs from role normalization, fan and hub removal, inner-root
neighbors, two connectivity extractions, and two separations.-/
def outerChildLoss (a K h σ : ℕ) : ℕ :=
  (45 + 12 * K) * a + h + 2 * σ

/-- The individually tracked losses agree with the bundled child loss.
@isnad1 id=eq.0h4v.s6.d2a5254d07fb from=translated src=- shape=5f8c3680 vocab=1a1a2927
-/
theorem outerChildLoss_eq_sum (a K h σ : ℕ) :
    outerChildLoss a K h σ =
      14 * a + 28 * a + 3 * a + h + 12 * K * a + 2 * σ := by
  simp only [outerChildLoss]
  ring

/-- If a child loses at most the budgeted amount of chromatic number,
then it satisfies the induction threshold at the exact child scale.
@isnad1 id=le.4h9v.s7.977d62874ca2 from=translated src=- shape=0d9634ab vocab=6ca39830
-/
theorem outer_child_chromatic_of_budget
    (a child K B U h σ parentχ childχ : ℕ)
    (hscale : 3 * child = 2 * a)
    (hbudget : 3 * outerChildLoss a K h σ ≤ B * a)
    (hparent : U + B * a ≤ parentχ)
    (hloss : parentχ ≤ childχ + outerChildLoss a K h σ) :
    U + B * child ≤ childχ := by
  have hscaled : 3 * (B * child) = 2 * (B * a) := by
    calc
      3 * (B * child) = B * (3 * child) := by ring
      _ = B * (2 * a) := by rw [hscale]
      _ = 2 * (B * a) := by ring
  omega

/-- The same arithmetic directly at adjacent integer outer scales.
@isnad1 id=le.4h9v.s7.aa8ad13ee03e from=translated src=- shape=4bdd66c9 vocab=6c0c6ca6
-/
theorem outerScale_child_chromatic_of_budget
    (m i K B U h σ parentχ childχ : ℕ)
    (hi : i < m)
    (hbudget : 3 * outerChildLoss (outerScale m i) K h σ ≤
      B * outerScale m i)
    (hparent : U + B * outerScale m i ≤ parentχ)
    (hloss : parentχ ≤ childχ + outerChildLoss (outerScale m i) K h σ) :
    U + B * outerScale m (i + 1) ≤ childχ := by
  exact outer_child_chromatic_of_budget
    (outerScale m i) (outerScale m (i + 1)) K B U h σ parentχ childχ
    (outerScale_child m i hi) hbudget hparent hloss

/-- The explicit Corollary 24 constants satisfy the outer child budget
at every scale, even for `d = 0`.
@isnad1 id=le.0h2v.s6.3f21efcbca09 from=translated src=- shape=f9d7ec01 vocab=6ca39830
-/
theorem cor24_outer_child_budget (a d : ℕ) :
    3 * outerChildLoss a 10000 (980 * a) (14 * d * a) ≤
      (1000000 * (d + 1)) * a := by
  have hcoef : 3 * (121025 + 28 * d) ≤ 1000000 * (d + 1) := by
    omega
  have hmul := Nat.mul_le_mul_right a hcoef
  dsimp [outerChildLoss]
  nlinarith

end Woven
end HadwigerLean
