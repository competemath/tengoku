import Tengoku.RankTwoPoissonCounterexample.RankTwoPoisson.CharacteristicZero
import Tengoku.RankTwoPoissonCounterexample.RankTwoPoisson.Complex

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Exhaustive classification of the three - point fiber

The core equations are solved over every characteristic-zero field. In the
nonzero-x case, polynomial combinations give xy = -3/2, x²β = 13/2 and x² = 1.
The existing two-sided source-coordinate certificate then distinguishes points
by (x,y,β,D). This proves exhaustion in the original coordinate order (x,q,p,z),
using the original map (R,T,D,S), rather than merely evaluating three points.
-/

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace RankTwoPoisson
namespace Fiber
noncomputable section
variable {K : Type*} [Field K] [CharZero K]

/-- The normalized core first coordinate evaluated over the coefficient field.-/
def rValue (x y b : K) : K := 2 * x - 3 * x ^ 2 * y - x ^ 3 * b
/-- The normalized core third coordinate evaluated over the coefficient field.-/
def sValue (x y b : K) : K := y + 3 * x * (1 + x * y) ^ 2 * b + 3 * x * y ^ 2 * (4 + 3 * x * y)
/-- The normalized core second coordinate evaluated over the coefficient field.-/
def tValue (x y b : K) : K := -(1 / 2 : K) * ((1 + x * y) ^ 3 * b + y ^ 2 * (1 + x * y) * (4 + 3 * x * y))

/-- The entire core fiber, with the zero-x and nonzero-x cases both included.-/
theorem core_fiber (x y b : K) :
    (rValue x y b = 0 ∧ tValue x y b = 1 / 8 ∧ sValue x y b = 0) ↔
    (x = 0 ∧ y = 0 ∧ b =  -1 / 4) ∨
    (x = 1 ∧ y =  -3 / 2 ∧ b = 13 / 2) ∨
    (x =  -1 ∧ y = 3 / 2 ∧ b = 13 / 2) := by
  constructor
  · rintro ⟨hr, ht, hs⟩
    by_cases hx : x = 0
    · subst x
      have hy : y = 0 := by simpa [sValue] using hs
      subst y
      left
      refine ⟨rfl, rfl, ?_⟩
      dsimp [tValue] at ht
      linear_combination -2 * ht
    · have hprod : x * (2 - 3 * x * y - x ^ 2 * b) = 0 := by
        dsimp [rValue] at hr
        linear_combination hr
      have ha : 2 - 3 * x * y - x ^ 2 * b = 0 := (mul_eq_zero.mp hprod).resolve_left hx
      have hu : x * y = -3 / 2 := by
        dsimp [sValue] at hs
        linear_combination (1 / 4 : K) * (x * hs + 3 * (1 + x * y) ^ 2 * ha)
      have hb : x ^ 2 * b = 13 / 2 := by
        linear_combination -ha - 3 * hu
      have hx2 : x ^ 2 = 1 := by
        dsimp [tValue] at ht
        linear_combination -8 * x ^ 2 * ht - 4 * (1 + x * y) ^ 3 * hb -
          (12 * (x * y) ^ 3 + 36 * (x * y) ^ 2 + 40 * x * y + 18) * hu
      have hprod : (x - 1) * (x + 1) = 0 := by linear_combination hx2
      rcases mul_eq_zero.mp hprod with hp | hm
      · have hx1 : x = 1 := sub_eq_zero.mp hp
        subst x
        right; left
        exact ⟨rfl, by simpa using hu, by simpa using hb⟩
      · have hx1 : x =  -1 := by linear_combination hm
        subst x
        right; right
        refine ⟨rfl, ?_, ?_⟩
        · linear_combination -hu
        · simpa using hb
  · rintro (⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩) <;>
      norm_num [rValue, sValue, tValue]

/-- Evaluate a rational polynomial at an arbitrary point over K.-/
def ev (v : Var → K) (f : P) : K := MvPolynomial.aeval v f

/-- Coefficient extension followed by evaluation agrees with rational-polynomial evaluation.-/
theorem eval_map (v : Var → K) (f : P) :
    MvPolynomial.aeval v (mapK K f) = ev v f := by
  simp [mapK, ev, MvPolynomial.aeval_def, MvPolynomial.eval₂_map]

/-- The actual point map evaluates the original rational output tuple.-/
theorem pointMap_eq (v : Var → K) (i : Var) :
    pointMapK K (PhiK K) v i = ev v (output i) := by
  simp [pointMapK, PhiK, outputK, eval_map]

/-- Correspondence of the scalar core first coordinate to the existing polynomial R.-/
theorem eval_r (v : Var → K) : ev v R = rValue (v 0) (ev v y) (ev v beta) := by
  simp [ev, R, rValue, rat, x]

/-- Correspondence of the scalar core third coordinate to the existing polynomial S.-/
theorem eval_s (v : Var → K) : ev v S = sValue (v 0) (ev v y) (ev v beta) := by
  simp [ev, S, sValue, u, rat, x, mul_assoc]

/-- Correspondence of the scalar core second coordinate to the existing polynomial T.-/
theorem eval_t (v : Var → K) : ev v T = tValue (v 0) (ev v y) (ev v beta) := by
  simp [ev, T, tValue, u, rat, x, mul_assoc]
  ring

/-- The manuscript Hamiltonian correction in independent source coordinates.-/
def hValue (x y b : K) : K :=
  (1 / 20) * y ^ 4 * (18 * (x * y) ^ 2 + 78 * x * y + 125) +
  (3 / 10) * b * y ^ 2 * ((x * y) ^ 3 + 5 * (x * y) ^ 2 + 10 * x * y - 5) -
  (1 / 6) * b ^ 2 * (9 * x * y + 2) - (1 / 6) * x ^ 2 * b ^ 3

/-- The scalar correction is the evaluation of the existing polynomial H.-/
theorem eval_h (v : Var → K) : ev v H = hValue (v 0) (ev v y) (ev v beta) := by
  simp [ev, H, hValue, u, rat, x]
  ring

/-- The source-coordinate inverse recovers q over K.-/
theorem recover_q (v : Var → K) :
    ev v y + (1 / 3 : K) * v 0 * ev v beta = v 1 := by
  have h := congrArg (ev v) SourceCoordinates.Qorig_eq
  simpa [ev, SourceCoordinates.Qorig, rat, x, q] using h

/-- The source-coordinate inverse recovers p over K.-/
theorem recover_p (v : Var → K) :
    3 * (v 1) ^ 2 * (ev v beta + 9 * (v 1) ^ 2) +
      2 * (1 - 3 * v 0 * v 1) * ev v D0 = v 2 := by
  have h := congrArg (ev v) SourceCoordinates.pRecovered_eq
  simpa [ev, SourceCoordinates.pRecovered, SourceCoordinates.Morig,
    SourceCoordinates.Qorig_eq, rat, x, q, p] using h

/-- The source-coordinate inverse recovers z over K.-/
theorem recover_z (v : Var → K) :
    (1 / 2 : K) * (1 + 3 * v 0 * v 1) * (ev v beta + 9 * (v 1) ^ 2) -
      3 * (v 0) ^ 2 * ev v D0 = v 3 := by
  have h := congrArg (ev v) SourceCoordinates.zRecovered_eq
  simpa [ev, SourceCoordinates.zRecovered, SourceCoordinates.Morig,
    SourceCoordinates.Qorig_eq, rat, x, q, z] using h

/-- The corrected source coordinates (x,y,β,D) distinguish all K-points.-/
theorem source_injective (v w : Var → K)
    (hx : v 0 = w 0) (hy : ev v y = ev w y)
    (hb : ev v beta = ev w beta) (hd : ev v D = ev w D) : v = w := by
  have hq : v 1 = w 1 := by
    rw [← recover_q v, ← recover_q w, hx, hy, hb]
  have hh : ev v H = ev w H := by rw [eval_h, eval_h, hx, hy, hb]
  have hd0 : ev v D0 = ev w D0 := by
    have h : ev v D0 + ev v H = ev w D0 + ev w H := by simpa [ev, D] using hd
    rw [hh] at h
    exact add_right_cancel h
  have hp : v 2 = w 2 := by
    rw [← recover_p v, ← recover_p w, hx, hq, hb, hd0]
  have hz : v 3 = w 3 := by
    rw [← recover_z v, ← recover_z w, hx, hq, hb, hd0]
  funext i
  fin_cases i
  · exact hx
  · exact hq
  · exact hp
  · exact hz

/-- Transport the third rational point to an arbitrary characteristic-zero field.-/
theorem point2K_image :
    pointMapK K (PhiK K) (fieldPoint K point2) = targetK K := by
  rw [targetK, pointMapK_PhiK_fieldPoint, point2_image]

/-- The four coordinate equations of the specified fiber, in order (R,T,D,S).-/
theorem target_coordinates {v : Var → K}
    (hv : pointMapK K (PhiK K) v = targetK K) :
    ev v R = 0 ∧ ev v T = 1 / 8 ∧ ev v D = 0 ∧ ev v S = 0 := by
  have h0 := congrFun hv 0
  have h1 := congrFun hv 1
  have h2 := congrFun hv 2
  have h3 := congrFun hv 3
  simp only [pointMap_eq] at h0 h1 h2 h3
  simp [output, targetK, fieldPoint, target] at h0 h1 h2 h3
  exact ⟨h0, by simpa only [one_div] using h1, h2, h3⟩

/-- The displayed three points exhaust the four-dimensional fiber over K.-/
theorem exact_fiber_charZero (v : Var → K) :
    pointMapK K (PhiK K) v = targetK K ↔
    v = point0K K ∨ v = point1K K ∨ v = fieldPoint K point2 := by
  constructor
  · intro hv
    obtain ⟨hr, ht, hd, hs⟩ := target_coordinates hv
    rw [eval_r] at hr
    rw [eval_t] at ht
    rw [eval_s] at hs
    rcases (core_fiber (v 0) (ev v y) (ev v beta)).mp ⟨hr, ht, hs⟩ with
      h0 | h1 | h2
    · left
      obtain ⟨hx, hy, hb⟩ := h0
      apply source_injective v (point0K K)
      · simpa [point0K, fieldPoint, point0] using hx
      · rw [hy]; norm_num [ev, point0K, fieldPoint, point0, y, beta, B, a, rat, x, q, p, z, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
      · rw [hb]; norm_num [ev, point0K, fieldPoint, point0, beta, B, a, rat, x, q, p, z, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
      · exact hd.trans (target_coordinates (point0K_image K)).2.2.1.symm
    · right; left
      obtain ⟨hx, hy, hb⟩ := h1
      apply source_injective v (point1K K)
      · simpa [point1K, fieldPoint, point1] using hx
      · rw [hy]; norm_num [ev, point1K, fieldPoint, point1, y, beta, B, a, rat, x, q, p, z, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
      · rw [hb]; norm_num [ev, point1K, fieldPoint, point1, beta, B, a, rat, x, q, p, z, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
      · exact hd.trans (target_coordinates (point1K_image K)).2.2.1.symm
    · right; right
      obtain ⟨hx, hy, hb⟩ := h2
      apply source_injective v (fieldPoint K point2)
      · simpa [fieldPoint, point2] using hx
      · rw [hy]; norm_num [ev, fieldPoint, point2, y, beta, B, a, rat, x, q, p, z, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
      · rw [hb]; norm_num [ev, fieldPoint, point2, beta, B, a, rat, x, q, p, z, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
      · exact hd.trans (target_coordinates (point2K_image (K:=K))).2.2.1.symm
  · rintro (rfl | rfl | rfl)
    · exact point0K_image K
    · exact point1K_image K
    · exact point2K_image

/-- The exact complex fiber in the manuscript, including its reverse implication.-/
theorem exact_fiber_complex (v : Var → ℂ) :
    pointMapC PhiC v = targetC ↔
    v = point0C ∨ v = point1C ∨ v = complexPoint point2 := by
  exact exact_fiber_charZero v

/-- The same exact fiber for the original rational point map.-/
theorem exact_fiber_rational (v : Var → ℚ) :
    pointMap Phi v = target ↔ v = point0 ∨ v = point1 ∨ v = point2 := by
  have hmap : pointMapK ℚ (PhiK ℚ) v = pointMap Phi v := by
    funext i
    rw [pointMap_eq]
    simp [ev, pointMap, Phi, MvPolynomial.aeval_eq_eval]
    change MvPolynomial.eval₂ _ v (output i) = MvPolynomial.eval₂ _ v (output i)
    congr 1
  have hfield (w : Var → ℚ) : fieldPoint ℚ w = w := by
    funext i
    simp [fieldPoint]
  have h := exact_fiber_charZero v
  rw [hmap, targetK, point0K, point1K, hfield, hfield, hfield, hfield] at h
  exact h

/-- The three correction values in equation (H-fiber-values).-/
theorem hValue_points :
    hValue (0:K) 0 (-1 / 4) = -1 / 48 ∧
    hValue (1:K) (-3 / 2) (13 / 2) = -1097 / 192 ∧
    hValue (-1:K) (3 / 2) (13 / 2) = -1097 / 192 := by
  norm_num [hValue]

/-- The three listed points are pairwise distinct in every characteristic-zero field.-/
theorem fiber_points_distinct :
    point0K K ≠ point1K K ∧ point0K K ≠ fieldPoint K point2 ∧
    point1K K ≠ fieldPoint K point2 := by
  refine ⟨point0K_ne_point1K K, ?_, ?_⟩
  · intro h
    have h0 := congrFun h 0
    norm_num [point0K, fieldPoint, point0, point2] at h0
  · intro h
    have h0 := congrFun h 0
    norm_num [point1K, fieldPoint, point1, point2] at h0

/-- The localized formulas of the manuscript, with the necessary x ≠ 0 hypothesis.-/
theorem localized_core (x y b : K) (hx : x ≠ 0) :
    let w := 1 + x * y
    let a := 2 - 3 * x * y - x ^ 2 * b
    rValue x y b = x * a ∧
    sValue x y b = (2 + 4 * w - 3 * a * w ^ 2) / x ∧
    tValue x y b = (a * w ^ 3 - w ^ 2 - w) / (2 * x ^ 2) := by
  dsimp [rValue, sValue, tValue]
  constructor
  · ring
  constructor <;> field_simp <;> ring

/-- Point-map noninjectivity, distinct from nonautomorphism of the algebra map.-/
theorem pointMap_not_injective : ¬ Function.Injective (pointMapK K (PhiK K)) := by
  intro h
  exact point0K_ne_point1K K (h ((point0K_image K).trans (point1K_image K).symm))

/-- Noninjectivity of the original rational point map.-/
theorem rational_pointMap_not_injective : ¬ Function.Injective (pointMap Phi) := by
  intro h
  exact point0_ne_point1 (h (point0_image.trans point1_image.symm))

/-- Noninjectivity of the original complex point map.-/
theorem complex_pointMap_not_injective : ¬ Function.Injective (pointMapC PhiC) := by
  intro h
  exact point0C_ne_point1C (h (point0C_image.trans point1C_image.symm))

end
end Fiber
end RankTwoPoisson
