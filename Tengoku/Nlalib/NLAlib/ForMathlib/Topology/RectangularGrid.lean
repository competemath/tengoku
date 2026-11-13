import Tengoku.Nlalib.NLAlib.ForMathlib.Topology.CubicalGrid
import Tengoku.Seed.Analysis.Complex.Basic
import Tengoku.Seed.Data.Fin.SuccPred
import Tengoku.Seed.Tactic.Linarith
import Tengoku.Seed.Tactic.Ring

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # Rectangular complex grids as actual cubical chains

Real coordinate arrays give the native complex vertices, segment edges and
continuous filled cells. Strictly increasing arrays give distinct vertices
and place each cell center strictly inside its own rectangle and strictly
outside every other cell rectangle.
-/

noncomputable section
open AffineMap Set
open scoped unitInterval
namespace Cubical.RectangularGrid

variable {m n : ℕ}

/-- The actual complex vertex with the two specified real coordinates.-/
def vertex (x : Fin (m + 1) → ℝ) (y : Fin (n + 1) → ℝ)
    (i : Fin (m + 1)) (j : Fin (n + 1)) : ℂ :=
  x i + y j * Complex.I

/--
@isnad1 id=eq.0h6v.s6.604847ec985b from=translated src=- shape=48c33457 vocab=81de42c6
-/
@[simp]
theorem vertex_re (x : Fin (m + 1) → ℝ) (y : Fin (n + 1) → ℝ)
    (i : Fin (m + 1)) (j : Fin (n + 1)) : (vertex x y i j).re = x i := by
  simp [vertex]

/--
@isnad1 id=eq.0h6v.s6.80bdd36f876b from=translated src=- shape=f1c7bfef vocab=0e4a02d7
-/
@[simp]
theorem vertex_im (x : Fin (m + 1) → ℝ) (y : Fin (n + 1) → ℝ)
    (i : Fin (m + 1)) (j : Fin (n + 1)) : (vertex x y i j).im = y j := by
  simp [vertex]

/-- Strict coordinate arrays give genuinely distinct grid vertices.
@isnad1 id=injectiv.2h4v.s8.046b7622ff55 from=translated src=- shape=ceaff0dd vocab=a12d1fe7
-/
theorem vertex_injective (x : Fin (m + 1) → ℝ) (y : Fin (n + 1) → ℝ)
    (hx : StrictMono x) (hy : StrictMono y) :
    Function.Injective (fun p : Fin (m + 1) × Fin (n + 1) => vertex x y p.1 p.2) := by
  intro p q h
  apply Prod.ext
  · apply hx.injective
    simpa only [vertex_re] using congrArg Complex.re h
  · apply hy.injective
    simpa only [vertex_im] using congrArg Complex.im h

/-- A bilinear cell in a rectangular complex grid has the expected two
independent affine coordinates.
@isnad1 id=eq.0h7v.s8.50626fa71161 from=translated src=- shape=a0454325 vocab=32b65842
-/
theorem cell_apply (x : Fin (m + 1) → ℝ) (y : Fin (n + 1) → ℝ)
    (i : Fin m) (j : Fin n) (p : I × I) :
    Grid.cell (vertex x y) i j p =
      (lineMap (x i.castSucc) (x i.succ) (p.1 : ℝ) : ℝ) +
        (lineMap (y j.castSucc) (y j.succ) (p.2 : ℝ) : ℝ) * Complex.I := by
  apply Complex.ext <;>
    simp [Grid.cell, vertex, lineMap_apply_module] <;> ring

/-- Every point of the actual filled cell lies in its closed coordinate rectangle.
@isnad1 id=and.2h7v.s9.e97484cb2a31 from=translated src=- shape=cf3aa567 vocab=f0dcaf2c
-/
theorem cell_mem_rectangle (x : Fin (m + 1) → ℝ) (y : Fin (n + 1) → ℝ)
    (hx : Monotone x) (hy : Monotone y) (i : Fin m) (j : Fin n) (p : I × I) :
    (Grid.cell (vertex x y) i j p).re ∈ Icc (x i.castSucc) (x i.succ) ∧
      (Grid.cell (vertex x y) i j p).im ∈ Icc (y j.castSucc) (y j.succ) := by
  have hi : i.castSucc ≤ i.succ := i.castSucc_lt_succ.le
  have hj : j.castSucc ≤ j.succ := j.castSucc_lt_succ.le
  rw [cell_apply]
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, mul_zero, sub_zero, add_zero,
    Complex.add_im, Complex.mul_im, mul_one, zero_add]
  exact ⟨(convex_Icc _ _).lineMap_mem ⟨le_rfl, hx hi⟩ ⟨hx hi, le_rfl⟩ p.1.property,
    (convex_Icc _ _).lineMap_mem ⟨le_rfl, hy hj⟩ ⟨hy hj, le_rfl⟩ p.2.property⟩

/-- The actual geometric center of a grid cell.-/
def center (x : Fin (m + 1) → ℝ) (y : Fin (n + 1) → ℝ)
    (i : Fin m) (j : Fin n) : ℂ :=
  ((x i.castSucc + x i.succ) / 2 : ℝ) +
    ((y j.castSucc + y j.succ) / 2 : ℝ) * Complex.I

/--
@isnad1 id=eq.0h6v.s6.ae56c23f17de from=translated src=- shape=5b9cfbaa vocab=5523d65f
-/
@[simp]
theorem center_re (x : Fin (m + 1) → ℝ) (y : Fin (n + 1) → ℝ)
    (i : Fin m) (j : Fin n) :
    (center x y i j).re = (x i.castSucc + x i.succ) / 2 := by
  simp [center]

/--
@isnad1 id=eq.0h6v.s6.34196c673a92 from=translated src=- shape=3914ff49 vocab=19dba0ff
-/
@[simp]
theorem center_im (x : Fin (m + 1) → ℝ) (y : Fin (n + 1) → ℝ)
    (i : Fin m) (j : Fin n) :
    (center x y i j).im = (y j.castSucc + y j.succ) / 2 := by
  simp [center]

/-- Strict coordinates put the center strictly inside its own cell.
@isnad1 id=and.2h6v.s7.a12bd8b62749 from=translated src=- shape=a0079607 vocab=936d3f9d
-/
theorem center_mem_open_rectangle (x : Fin (m + 1) → ℝ) (y : Fin (n + 1) → ℝ)
    (hx : StrictMono x) (hy : StrictMono y) (i : Fin m) (j : Fin n) :
    x i.castSucc < (center x y i j).re ∧ (center x y i j).re < x i.succ ∧
      y j.castSucc < (center x y i j).im ∧ (center x y i j).im < y j.succ := by
  have hi := hx i.castSucc_lt_succ
  have hj := hy j.castSucc_lt_succ
  simp only [center_re, center_im]
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

/-- A different grid cell places the specified center strictly outside its
closed rectangle, including cells sharing a side or a corner.
@isnad1 id=or.3h8v.s7.a6a51ae5d0b4 from=translated src=- shape=3dd4157f vocab=0c69cae3
-/
theorem center_strictly_outside_other_rectangle
    (x : Fin (m + 1) → ℝ) (y : Fin (n + 1) → ℝ)
    (hx : StrictMono x) (hy : StrictMono y)
    (i k : Fin m) (j l : Fin n) (hne : (i, j) ≠ (k, l)) :
    (center x y i j).re < x k.castSucc ∨ x k.succ < (center x y i j).re ∨
      (center x y i j).im < y l.castSucc ∨ y l.succ < (center x y i j).im := by
  have hcenter := center_mem_open_rectangle x y hx hy i j
  rcases lt_trichotomy i k with hik | rfl | hki
  · exact Or.inl (hcenter.2.1.trans_le (hx.monotone (Fin.succ_le_castSucc_iff.mpr hik)))
  · rcases lt_trichotomy j l with hjl | rfl | hlj
    · exact Or.inr (Or.inr (Or.inl
        (hcenter.2.2.2.trans_le (hy.monotone (Fin.succ_le_castSucc_iff.mpr hjl)))))
    · exact False.elim (hne rfl)
    · exact Or.inr (Or.inr (Or.inr
        ((hy.monotone (Fin.succ_le_castSucc_iff.mpr hlj)).trans_lt hcenter.2.2.1)))
  · exact Or.inr (Or.inl ((hx.monotone (Fin.succ_le_castSucc_iff.mpr hki)).trans_lt hcenter.1))

end Cubical.RectangularGrid
