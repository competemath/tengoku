import Tengoku.Linearhadwiger.HadwigerLean.Coloring.Fractional

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Integral colorings as fractional colorings

Every ordinary coloring yields a feasible fractional coloring by assigning unit
weight to its nonempty color classes. The construction below keeps only colors
actually used by vertices, so it also works on the empty graph.
-/

namespace HadwigerLean

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

private def finiteColorClass {G : SimpleGraph V} {n : ℕ}
    (C : G.Coloring (Fin n)) (i : Fin n) : Finset V :=
  Finset.univ.filter (fun v => C v = i)

omit [DecidableEq V] in
private theorem mem_finiteColorClass {G : SimpleGraph V} {n : ℕ}
    (C : G.Coloring (Fin n)) (i : Fin n) (v : V) :
    v ∈ finiteColorClass C i ↔ C v = i := by
  simp [finiteColorClass]

omit [DecidableEq V] in
private theorem finiteColorClass_indep {G : SimpleGraph V} {n : ℕ}
    (C : G.Coloring (Fin n)) (i : Fin n) :
    G.IsIndepSet ((finiteColorClass C i : Finset V) : Set V) := by
  simpa [finiteColorClass, SimpleGraph.Coloring.colorClass] using
    C.isIndepSet_colorClass i

private noncomputable def usedColors {G : SimpleGraph V} {n : ℕ}
    (C : G.Coloring (Fin n)) : Finset (Fin n) := by
  classical
  exact Finset.univ.image C

omit [DecidableEq V] in
private theorem color_mem_usedColors {G : SimpleGraph V} {n : ℕ}
    (C : G.Coloring (Fin n)) (v : V) : C v ∈ usedColors C := by
  classical
  simp [usedColors]

private def stableColorClass {G : SimpleGraph V} {n : ℕ}
    (C : G.Coloring (Fin n)) (i : {i : Fin n // i ∈ usedColors C}) : StableSet G := by
  have hne : (finiteColorClass C i.1).Nonempty := by
    classical
    obtain ⟨v, _, hv⟩ := Finset.mem_image.mp i.2
    exact ⟨v, (mem_finiteColorClass C i.1 v).2 hv⟩
  exact ⟨finiteColorClass C i.1, hne, finiteColorClass_indep C i.1⟩

private noncomputable def colorClassFamily {G : SimpleGraph V} {n : ℕ}
    (C : G.Coloring (Fin n)) : Finset (StableSet G) := by
  classical
  exact (usedColors C).attach.image (stableColorClass C)

private theorem colorClassFamily_card_le {G : SimpleGraph V} {n : ℕ}
    (C : G.Coloring (Fin n)) : (colorClassFamily C).card ≤ n := by
  classical
  calc
    (colorClassFamily C).card ≤ (usedColors C).card := by
      unfold colorClassFamily
      simpa only [Finset.card_attach] using
        (Finset.card_image_le (s := (usedColors C).attach)
          (f := stableColorClass C))
    _ ≤ n := by
      simpa using Finset.card_le_card (Finset.subset_univ (usedColors C))

/-- Unit weight on each distinct nonempty color class of `C`.-/
noncomputable def coloringFractionalWeight {G : SimpleGraph V} {n : ℕ}
    (C : G.Coloring (Fin n)) : StableSet G → ℝ :=
  fun S => if S ∈ colorClassFamily C then 1 else 0

/--
@isnad1 id=isfracti.0h4v.s4.32db60e6ecf6 from=translated src=- shape=155be71e vocab=c1d7ff66
-/
theorem coloringFractionalWeight_feasible {G : SimpleGraph V} {n : ℕ}
    (C : G.Coloring (Fin n)) :
    IsFractionalColoring G (coloringFractionalWeight C) := by
  classical
  constructor
  · intro S
    simp only [coloringFractionalWeight]
    split_ifs <;> norm_num
  · intro v
    let i : {i : Fin n // i ∈ usedColors C} := ⟨C v, color_mem_usedColors C v⟩
    have hi : stableColorClass C i ∈ colorClassFamily C := by
      unfold colorClassFamily
      exact Finset.mem_image.mpr ⟨i, Finset.mem_attach _ _, rfl⟩
    have hv : v ∈ (stableColorClass C i).1 := by
      exact (mem_finiteColorClass C i.1 v).2 rfl
    have hnonneg : ∀ S ∈ (Finset.univ : Finset (StableSet G)),
        0 ≤ if v ∈ S.1 then coloringFractionalWeight C S else 0 := by
      intro S _
      simp only [coloringFractionalWeight]
      split_ifs <;> norm_num
    change 1 ≤ ∑ S : StableSet G,
      if v ∈ S.1 then coloringFractionalWeight C S else 0
    calc
      1 = (if v ∈ (stableColorClass C i).1 then
            coloringFractionalWeight C (stableColorClass C i) else 0) := by
          simp [hv, coloringFractionalWeight, hi]
      _ ≤ ∑ S : StableSet G,
            if v ∈ S.1 then coloringFractionalWeight C S else 0 :=
          Finset.single_le_sum hnonneg (Finset.mem_univ _)

/--
@isnad1 id=eq.0h4v.s5.c13cedeb1f33 from=translated src=- shape=34906db7 vocab=3de7e12d
-/
theorem coloringFractionalWeight_cost {G : SimpleGraph V} {n : ℕ}
    (C : G.Coloring (Fin n)) :
    fractionalCost G (coloringFractionalWeight C) =
      ((colorClassFamily C).card : ℝ) := by
  classical
  simp [fractionalCost, coloringFractionalWeight]

/-- A coloring with `n` colors gives a fractional coloring of cost at most `n`.
@isnad1 id=le.1h3v.s4.60e49b7c4a47 from=translated src=- shape=be52274e vocab=33cac738
-/
theorem fractionalChromaticNumber_le_colorable (G : SimpleGraph V) {n : ℕ}
    (h : G.Colorable n) : fractionalChromaticNumber G ≤ (n : ℝ) := by
  let C : G.Coloring (Fin n) := h.some
  calc
    fractionalChromaticNumber G ≤ fractionalCost G (coloringFractionalWeight C) :=
      fractionalChromaticNumber_le_cost G (coloringFractionalWeight_feasible C)
    _ = ((colorClassFamily C).card : ℝ) := coloringFractionalWeight_cost C
    _ ≤ n := by exact_mod_cast colorClassFamily_card_le C

/-- Fractional chromatic number is at most ordinary chromatic number.
@isnad1 id=le.0h2v.s4.24236062ef12 from=translated src=- shape=4fc5e85e vocab=9aaad485
-/
theorem fractionalChromaticNumber_le_chromatic (G : SimpleGraph V) :
    fractionalChromaticNumber G ≤ (chromatic G : ℝ) :=
  fractionalChromaticNumber_le_colorable G (colorable_chromatic G)

end HadwigerLean
