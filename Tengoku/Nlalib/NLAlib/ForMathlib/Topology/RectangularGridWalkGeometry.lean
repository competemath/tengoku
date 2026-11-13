import Tengoku.Nlalib.NLAlib.ForMathlib.Topology.CubicalGridWalk
import Tengoku.Nlalib.NLAlib.ForMathlib.Topology.RectangularGrid

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # Geometric control of actual canonical rectangular grid walks

Every active straight edge of the finite L-shaped walk stays in the
coordinate rectangle between its two endpoint vertices. A uniform distance
bound on those two vertices therefore controls the whole actual grid walk.
-/

noncomputable section
open Set AffineMap
open scoped unitInterval
namespace Cubical.RectangularGrid
variable {m n : ℕ}

/-- Horizontal canonical edges have one affine and one constant coordinate.
@isnad1 id=eq.0h7v.s8.37c502e61365 from=translated src=- shape=d6706b06 vocab=7a576653
-/
theorem horizontal_apply (x : Fin (m + 1) → ℝ) (y : Fin (n + 1) → ℝ)
    (i : Fin m) (j : Fin (n + 1)) (t : I) :
    Grid.horizontal (vertex x y) i j t =
      (lineMap (x i.castSucc) (x i.succ) (t : ℝ) : ℝ) + y j * Complex.I := by
  apply Complex.ext <;>
    simp [Grid.horizontal, vertex, Path.segment_apply, lineMap_apply_module]
  ring

/-- Vertical canonical edges have one constant and one affine coordinate.
@isnad1 id=eq.0h7v.s8.f28bbe64e5e1 from=translated src=- shape=515bd11e vocab=8d32f156
-/
theorem vertical_apply (x : Fin (m + 1) → ℝ) (y : Fin (n + 1) → ℝ)
    (i : Fin (m + 1)) (j : Fin n) (t : I) :
    Grid.vertical (vertex x y) i j t =
      (x i : ℂ) + (lineMap (y j.castSucc) (y j.succ) (t : ℝ) : ℝ) * Complex.I := by
  apply Complex.ext <;>
    simp [Grid.vertical, vertex, Path.segment_apply, lineMap_apply_module]
  ring

/-- A horizontal edge active in the L-shaped walk stays in its actual
endpoint coordinate rectangle.
@isnad1 id=and.2h9v.s9.785567991c1c from=translated src=- shape=ce4087f5 vocab=2168af28
-/
theorem horizontal_mem_rectangle_of_walkCoefficient_ne_zero
    (x : Fin (m + 1) → ℝ) (y : Fin (n + 1) → ℝ) (hx : Monotone x)
    (p q : Fin (m + 1) × Fin (n + 1)) (i : Fin m) (j : Fin (n + 1))
    (hc : Grid.walkHorizontalCoefficients p q i j ≠ 0) (t : I) :
    (Grid.horizontal (vertex x y) i j t).re ∈ uIcc (x p.1) (x q.1) ∧
      (Grid.horizontal (vertex x y) i j t).im ∈ uIcc (y p.2) (y q.2) := by
  classical
  have hj : j = p.2 := by
    by_contra hne
    exact hc (by simp [Grid.walkHorizontalCoefficients, hne])
  subst j
  have hi : Grid.intervalCoefficients p.1 q.1 i ≠ 0 := by
    simpa [Grid.walkHorizontalCoefficients] using hc
  obtain ⟨hlo, hhi⟩ := Grid.intervalCoefficients_ne_zero_bounds p.1 q.1 i hi
  have hl : min (x p.1) (x q.1) ≤ x i.castSucc := by
    rw [← hx.map_min]
    exact hx hlo
  have hh : x i.succ ≤ max (x p.1) (x q.1) := by
    rw [← hx.map_max]
    exact hx hhi
  have hm := hx i.castSucc_lt_succ.le
  rw [horizontal_apply]
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, mul_zero, sub_zero, add_zero,
    Complex.add_im, Complex.mul_im, mul_one, zero_add]
  exact ⟨(convex_Icc _ _).lineMap_mem ⟨hl, hm.trans hh⟩ ⟨hl.trans hm, hh⟩ t.property,
    left_mem_uIcc⟩

/-- A vertical edge active in the L-shaped walk stays in its actual
endpoint coordinate rectangle.
@isnad1 id=and.2h9v.s9.7ae876a23d16 from=translated src=- shape=a467c258 vocab=ba132851
-/
theorem vertical_mem_rectangle_of_walkCoefficient_ne_zero
    (x : Fin (m + 1) → ℝ) (y : Fin (n + 1) → ℝ) (hy : Monotone y)
    (p q : Fin (m + 1) × Fin (n + 1)) (i : Fin (m + 1)) (j : Fin n)
    (hc : Grid.walkVerticalCoefficients p q i j ≠ 0) (t : I) :
    (Grid.vertical (vertex x y) i j t).re ∈ uIcc (x p.1) (x q.1) ∧
      (Grid.vertical (vertex x y) i j t).im ∈ uIcc (y p.2) (y q.2) := by
  classical
  have hi : i = q.1 := by
    by_contra hne
    exact hc (by simp [Grid.walkVerticalCoefficients, hne])
  subst i
  have hj : Grid.intervalCoefficients p.2 q.2 j ≠ 0 := by
    simpa [Grid.walkVerticalCoefficients] using hc
  obtain ⟨hlo, hhi⟩ := Grid.intervalCoefficients_ne_zero_bounds p.2 q.2 j hj
  have hl : min (y p.2) (y q.2) ≤ y j.castSucc := by
    rw [← hy.map_min]
    exact hy hlo
  have hh : y j.succ ≤ max (y p.2) (y q.2) := by
    rw [← hy.map_max]
    exact hy hhi
  have hm := hy j.castSucc_lt_succ.le
  rw [vertical_apply]
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, mul_zero, sub_zero, add_zero,
    Complex.add_im, Complex.mul_im, mul_one, zero_add]
  exact ⟨right_mem_uIcc,
    (convex_Icc _ _).lineMap_mem ⟨hl, hm.trans hh⟩ ⟨hl.trans hm, hh⟩ t.property⟩

/-- Every active edge of the actual finite L-shaped walk stays in the
coordinate rectangle between its two specified endpoint vertices.
@isnad1 id=and.3h8v.s9.4d5ecab3a4ff from=translated src=- shape=c8b3e5b5 vocab=a43758f1
-/
theorem walkChain_mem_rectangle
    (x : Fin (m + 1) → ℝ) (y : Fin (n + 1) → ℝ) (hx : Monotone x) (hy : Monotone y)
    (p q : Fin (m + 1) × Fin (n + 1)) :
    ∀ γ ∈ (Grid.walkChain (vertex x y) p q).support, ∀ t,
      (γ t).re ∈ uIcc (x p.1) (x q.1) ∧ (γ t).im ∈ uIcc (y p.2) (y q.2) := by
  exact Grid.edgeChain_mapsTo_of_nonzero_edges_mapsTo (vertex x y)
    (Grid.walkHorizontalCoefficients p q) (Grid.walkVerticalCoefficients p q)
    {z : ℂ | z.re ∈ uIcc (x p.1) (x q.1) ∧ z.im ∈ uIcc (y p.2) (y q.2)}
    (horizontal_mem_rectangle_of_walkCoefficient_ne_zero x y hx p q)
    (vertical_mem_rectangle_of_walkCoefficient_ne_zero x y hy p q)

end Cubical.RectangularGrid

namespace Complex

/-- A coordinate rectangle spanned by two points within distance `r` of a
point lies within distance `2r` of that point. No assertion about a straight
line parameterization or smoothness is needed.
@isnad1 id=lt.4h5v.s6.70c76e73ced8 from=translated src=- shape=6496646f vocab=f8aecd28
-/
theorem norm_sub_lt_two_mul_of_mem_coordinate_rectangle
    {a b c z : ℂ} {r : ℝ} (ha : ‖a - z‖ < r) (hb : ‖b - z‖ < r)
    (hr : c.re ∈ Set.uIcc a.re b.re) (hi : c.im ∈ Set.uIcc a.im b.im) :
    ‖c - z‖ < 2 * r := by
  have hra : |a.re - z.re| < r := by
    simpa only [sub_re] using (abs_re_le_norm (a - z)).trans_lt ha
  have hrb : |b.re - z.re| < r := by
    simpa only [sub_re] using (abs_re_le_norm (b - z)).trans_lt hb
  have hia : |a.im - z.im| < r := by
    simpa only [sub_im] using (abs_im_le_norm (a - z)).trans_lt ha
  have hib : |b.im - z.im| < r := by
    simpa only [sub_im] using (abs_im_le_norm (b - z)).trans_lt hb
  have hrc : |c.re - z.re| < r := by
    rw [abs_lt] at hra hrb ⊢
    rcases Set.mem_uIcc.mp hr with h | h <;> constructor <;> linarith [h.1, h.2]
  have hic : |c.im - z.im| < r := by
    rw [abs_lt] at hia hib ⊢
    rcases Set.mem_uIcc.mp hi with h | h <;> constructor <;> linarith [h.1, h.2]
  apply (norm_le_abs_re_add_abs_im _).trans_lt
  simpa only [sub_re, sub_im] using (show |c.re - z.re| + |c.im - z.im| < 2 * r by linarith)

end Complex

namespace Cubical.RectangularGrid

/-- Uniform endpoint distance control bounds every point on every active
canonical edge of the actual finite grid walk.
@isnad1 id=lt.5h10v.s9.c858e2b1e34d from=translated src=- shape=be10b455 vocab=d6656387
-/
theorem walkChain_norm_sub_lt
    {m n : ℕ} (x : Fin (m + 1) → ℝ) (y : Fin (n + 1) → ℝ)
    (hx : Monotone x) (hy : Monotone y) (p q : Fin (m + 1) × Fin (n + 1))
    {z : ℂ} {r : ℝ} (hp : ‖vertex x y p.1 p.2 - z‖ < r)
    (hq : ‖vertex x y q.1 q.2 - z‖ < r) :
    ∀ γ ∈ (Grid.walkChain (vertex x y) p q).support, ∀ t, ‖γ t - z‖ < 2 * r := by
  intro γ hγ t
  obtain ⟨hr, hi⟩ := walkChain_mem_rectangle x y hx hy p q γ hγ t
  exact Complex.norm_sub_lt_two_mul_of_mem_coordinate_rectangle hp hq
    (by simpa only [vertex_re] using hr) (by simpa only [vertex_im] using hi)

end Cubical.RectangularGrid
