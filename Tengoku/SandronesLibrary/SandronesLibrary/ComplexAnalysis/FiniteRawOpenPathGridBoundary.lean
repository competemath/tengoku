/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.SandronesLibrary.SandronesLibrary.ComplexAnalysis.DyadicPathIntegralAssembly
import Tengoku.SandronesLibrary.SandronesLibrary.Topology.FiniteRawOpenPathGrid
import Tengoku.Seed.Analysis.Complex.HasPrimitives

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Local-primitive assembly and cancellation on a finite raw path grid.

> **Entry**: complex-analysis.path-integral.finite-raw-grid-boundary -/

open Set Metric MeasureTheory
open scoped unitInterval

noncomputable section

namespace SandronesLibrary.ComplexAnalysis

open SandronesLibrary.Topology

/-- Telescoping along a function on the `n+1` vertices of a finite interval.-/
private theorem fin_sum_adjacent_sub {G : Type*} [AddCommGroup G] {n : ℕ}
    (value : Fin (n + 1) → G) :
    (∑ i : Fin n, (value i.castSucc - value i.succ)) =
      value 0 - value (Fin.last n) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Fin.sum_univ_castSucc]
      have hfirst := ih (fun j : Fin (n + 1) ↦ value j.castSucc)
      rw [show (∑ i : Fin n,
          (value i.castSucc.castSucc - value i.castSucc.succ)) =
          value 0 - value (Fin.last n).castSucc by
        simpa only [Fin.succ_castSucc, Fin.castSucc_zero] using hfirst]
      simp only [Fin.succ_last]
      abel

private theorem fin_sum_adjacent_sub_rev {G : Type*} [AddCommGroup G] {n : ℕ}
    (value : Fin (n + 1) → G) :
    (∑ i : Fin n, (value i.succ - value i.castSucc)) =
      value (Fin.last n) - value 0 := by
  calc
    (∑ i : Fin n, (value i.succ - value i.castSucc)) =
        -(∑ i : Fin n, (value i.castSucc - value i.succ)) := by
          rw [← Finset.sum_neg_distrib]
          apply Finset.sum_congr rfl
          intro i hi
          abel
    _ = -(value 0 - value (Fin.last n)) := by
      rw [fin_sum_adjacent_sub]
    _ = value (Fin.last n) - value 0 := by abel

/-- Native-`Fin` version of finite square-grid cancellation.-/
private theorem sum_finSquareCellBoundaries_eq_outerBoundary
    {G : Type*} [AddCommGroup G] (n : ℕ)
    (horizontal : Fin n → Fin (n + 1) → G)
    (vertical : Fin (n + 1) → Fin n → G) :
    (∑ i : Fin n, ∑ j : Fin n,
      ((horizontal i j.castSucc - horizontal i j.succ) +
        (vertical i.succ j - vertical i.castSucc j))) =
      (∑ i : Fin n,
        (horizontal i 0 - horizontal i (Fin.last n))) +
      ∑ j : Fin n,
        (vertical (Fin.last n) j - vertical 0 j) := by
  have hhorizontal :
      (∑ i : Fin n, ∑ j : Fin n,
        (horizontal i j.castSucc - horizontal i j.succ)) =
      ∑ i : Fin n, (horizontal i 0 - horizontal i (Fin.last n)) := by
    apply Finset.sum_congr rfl
    intro i hi
    exact fin_sum_adjacent_sub (horizontal i)
  have hvertical :
      (∑ i : Fin n, ∑ j : Fin n,
        (vertical i.succ j - vertical i.castSucc j)) =
      ∑ j : Fin n, (vertical (Fin.last n) j - vertical 0 j) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j hj
    exact fin_sum_adjacent_sub_rev (fun i ↦ vertical i j)
  rw [Finset.sum_congr rfl (fun i hi ↦ Finset.sum_add_distrib),
    Finset.sum_add_distrib, hhorizontal, hvertical]

/-- Preferred finite-index analytic grid carrier matching the native index
types of `IndexedOpenCoverSquareSubdivision`.-/
private structure FiniteLocalPrimitivePathGrid (f : ℂ → ℂ) where
  steps : ℕ
  vertex : Fin (steps + 1) → Fin (steps + 1) → ℂ
  horizontal : (i : Fin steps) → (j : Fin (steps + 1)) →
    Path (vertex i.castSucc j) (vertex i.succ j)
  vertical : (i : Fin (steps + 1)) → (j : Fin steps) →
    Path (vertex i j.castSucc) (vertex i j.succ)
  horizontal_piecewiseC1 : ∀ i j, Path.PiecewiseC1 (horizontal i j)
  vertical_piecewiseC1 : ∀ i j, Path.PiecewiseC1 (vertical i j)
  cellSet : Fin steps → Fin steps → Set ℂ
  cellSet_open : ∀ i j, IsOpen (cellSet i j)
  cell_exact : ∀ i j, Complex.IsExactOn f (cellSet i j)
  bottom_mem : ∀ i j, Set.range (horizontal i j.castSucc) ⊆ cellSet i j
  right_mem : ∀ i j, Set.range (vertical i.succ j) ⊆ cellSet i j
  top_mem : ∀ i j, Set.range (horizontal i j.succ) ⊆ cellSet i j
  left_mem : ∀ i j, Set.range (vertical i.castSucc j) ⊆ cellSet i j

end SandronesLibrary.ComplexAnalysis

namespace SandronesLibrary.Topology

private def FiniteHorizontalReplacementExists
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (R : FiniteRawOpenPathGrid E) : Prop :=
  ∀ i j, ∃ q : Path (R.vertex i.castSucc j) (R.vertex i.succ j),
    Path.PiecewiseC1 q ∧
      (∀ k, j = k.castSucc → Set.range q ⊆ R.cellSet i k) ∧
      (∀ k, j = k.succ → Set.range q ⊆ R.cellSet i k) ∧
      (j = 0 ∨ j = Fin.last R.steps → q = R.horizontalRaw i j)

private theorem FiniteRawOpenPathGrid.horizontalReplacementExists
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (R : FiniteRawOpenPathGrid E) : FiniteHorizontalReplacementExists R := by
  intro i j
  by_cases hj0 : j = 0
  · subst j
    refine ⟨R.horizontalRaw i 0, R.horizontal_zero_piecewiseC1 i, ?_, ?_, ?_⟩
    · intro k hk
      rw [hk]
      exact R.bottom_mem i k
    · intro k hk
      exfalso
      have : (0 : ℕ) = k.val + 1 := congrArg Fin.val hk
      omega
    · intro hboundary
      rfl
  · by_cases hjlast : j = Fin.last R.steps
    · subst j
      refine ⟨R.horizontalRaw i (Fin.last R.steps),
        R.horizontal_last_piecewiseC1 i, ?_, ?_, ?_⟩
      · intro k hk
        exfalso
        have hval : R.steps = k.val := congrArg Fin.val hk
        omega
      · intro k hk
        rw [hk]
        exact R.top_mem i k
      · intro hboundary
        rfl
    · have hjpos : 0 < j.val := by
        have : j.val ≠ 0 := by
          intro h
          apply hj0
          apply Fin.ext
          simpa using h
        omega
      have hjlt : j.val < R.steps := by
        have hjle : j.val ≤ R.steps := Nat.le_of_lt_succ j.isLt
        have hjne : j.val ≠ R.steps := by
          intro h
          apply hjlast
          apply Fin.ext
          simpa using h
        omega
      let below : Fin R.steps := ⟨j.val - 1, by omega⟩
      let above : Fin R.steps := ⟨j.val, hjlt⟩
      have hbelow : below.succ = j := by
        apply Fin.ext
        simp [below]
        omega
      have habove : above.castSucc = j := by
        apply Fin.ext
        rfl
      have hraw : Set.range (R.horizontalRaw i j) ⊆
          R.cellSet i below ∩ R.cellSet i above := by
        intro z hz
        constructor
        · rw [← hbelow] at hz
          exact R.top_mem i below hz
        · rw [← habove] at hz
          exact R.bottom_mem i above hz
      obtain ⟨q, hqrange, hqpiece, K, hK⟩ :=
        Path.exists_piecewiseC1_range_subset_open_and_homotopyWithin
          (R.horizontalRaw i j)
          ((R.cellSet_open i below).inter (R.cellSet_open i above))
          (fun t ↦ hraw (Set.mem_range_self t))
      refine ⟨q, hqpiece, ?_, ?_, ?_⟩
      · intro k hk
        have : k = above := by
          apply Fin.ext
          have := congrArg Fin.val (hk.symm.trans habove.symm)
          simpa [above] using this
        subst k
        exact fun z hz ↦ (hqrange hz).2
      · intro k hk
        have : k = below := by
          apply Fin.ext
          have := congrArg Fin.val (hk.symm.trans hbelow.symm)
          simp [below] at this ⊢
          omega
        subst k
        exact fun z hz ↦ (hqrange hz).1
      · intro hboundary
        rcases hboundary with hjzero | hjlast'
        · exact (hj0 hjzero).elim
        · exact (hjlast hjlast').elim

private def FiniteVerticalReplacementExists
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (R : FiniteRawOpenPathGrid E) : Prop :=
  ∀ i j, ∃ q : Path (R.vertex i j.castSucc) (R.vertex i j.succ),
    Path.PiecewiseC1 q ∧
      (∀ k, i = k.castSucc → Set.range q ⊆ R.cellSet k j) ∧
      (∀ k, i = k.succ → Set.range q ⊆ R.cellSet k j) ∧
      (i = 0 ∨ i = Fin.last R.steps → q = R.verticalRaw i j)

private theorem FiniteRawOpenPathGrid.verticalReplacementExists
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (R : FiniteRawOpenPathGrid E) : FiniteVerticalReplacementExists R := by
  intro i j
  by_cases hi0 : i = 0
  · subst i
    refine ⟨R.verticalRaw 0 j, R.vertical_zero_piecewiseC1 j, ?_, ?_, ?_⟩
    · intro k hk
      rw [hk]
      exact R.left_mem k j
    · intro k hk
      exfalso
      have : (0 : ℕ) = k.val + 1 := congrArg Fin.val hk
      omega
    · intro hboundary
      rfl
  · by_cases hilast : i = Fin.last R.steps
    · subst i
      refine ⟨R.verticalRaw (Fin.last R.steps) j,
        R.vertical_last_piecewiseC1 j, ?_, ?_, ?_⟩
      · intro k hk
        exfalso
        have hval : R.steps = k.val := congrArg Fin.val hk
        omega
      · intro k hk
        rw [hk]
        exact R.right_mem k j
      · intro hboundary
        rfl
    · have hipos : 0 < i.val := by
        have : i.val ≠ 0 := by
          intro h
          apply hi0
          apply Fin.ext
          simpa using h
        omega
      have hilt : i.val < R.steps := by
        have hile : i.val ≤ R.steps := Nat.le_of_lt_succ i.isLt
        have hine : i.val ≠ R.steps := by
          intro h
          apply hilast
          apply Fin.ext
          simpa using h
        omega
      let left : Fin R.steps := ⟨i.val - 1, by omega⟩
      let right : Fin R.steps := ⟨i.val, hilt⟩
      have hleft : left.succ = i := by
        apply Fin.ext
        simp [left]
        omega
      have hright : right.castSucc = i := by
        apply Fin.ext
        rfl
      have hraw : Set.range (R.verticalRaw i j) ⊆
          R.cellSet left j ∩ R.cellSet right j := by
        intro z hz
        constructor
        · rw [← hleft] at hz
          exact R.right_mem left j hz
        · rw [← hright] at hz
          exact R.left_mem right j hz
      obtain ⟨q, hqrange, hqpiece, K, hK⟩ :=
        Path.exists_piecewiseC1_range_subset_open_and_homotopyWithin
          (R.verticalRaw i j)
          ((R.cellSet_open left j).inter (R.cellSet_open right j))
          (fun t ↦ hraw (Set.mem_range_self t))
      refine ⟨q, hqpiece, ?_, ?_, ?_⟩
      · intro k hk
        have : k = right := by
          apply Fin.ext
          have := congrArg Fin.val (hk.symm.trans hright.symm)
          simpa [right] using this
        subst k
        exact fun z hz ↦ (hqrange hz).2
      · intro k hk
        have : k = left := by
          apply Fin.ext
          have := congrArg Fin.val (hk.symm.trans hleft.symm)
          simp [left] at this ⊢
          omega
        subst k
        exact fun z hz ↦ (hqrange hz).1
      · intro hboundary
        rcases hboundary with hizero | hilast'
        · exact (hi0 hizero).elim
        · exact (hilast hilast').elim

end SandronesLibrary.Topology

namespace SandronesLibrary.ComplexAnalysis

open SandronesLibrary.Topology

/-- A local primitive evaluates the path integral of every topology-owned
piecewise-C1 path by its endpoints.-/
private theorem pathIntegral_eq_sub_of_isExactOn_of_piecewiseC1
    {f : ℂ → ℂ} {U : Set ℂ} {a b : ℂ} {gamma : Path a b}
    (hexact : Complex.IsExactOn f U) (hU : IsOpen U)
    (hgamma : Path.PiecewiseC1 gamma) (hrange : Set.range gamma ⊆ U) :
    pathIntegral f gamma = Classical.choose hexact b - Classical.choose hexact a := by
  let g : ℂ → ℂ := Classical.choose hexact
  have hg : ∀ z ∈ U, HasDerivAt g (f z) z := Classical.choose_spec hexact
  have hf : ContinuousOn f U := by
    exact (hexact.differentiableOn hU).continuousOn
  exact pathIntegral_eq_sub_of_primitive_of_admissiblePath
    (admissiblePath_of_piecewiseC1 hgamma hrange hf) hg

/-- The four oriented edges of one cell have total integral zero whenever one
local primitive is available on a set containing all four paths.-/
private theorem pathIntegral_fourEdgeBoundary_eq_zero_of_isExactOn
    {f : ℂ → ℂ} {U : Set ℂ} {a b c d : ℂ}
    (bottom : Path a b) (right : Path b c)
    (top : Path c d) (left : Path d a)
    (hexact : Complex.IsExactOn f U) (hU : IsOpen U)
    (hbottom : Path.PiecewiseC1 bottom) (hright : Path.PiecewiseC1 right)
    (htop : Path.PiecewiseC1 top) (hleft : Path.PiecewiseC1 left)
    (bottom_mem : Set.range bottom ⊆ U) (right_mem : Set.range right ⊆ U)
    (top_mem : Set.range top ⊆ U) (left_mem : Set.range left ⊆ U) :
    pathIntegral f bottom + pathIntegral f right +
        pathIntegral f top + pathIntegral f left = 0 := by
  rw [pathIntegral_eq_sub_of_isExactOn_of_piecewiseC1
      hexact hU hbottom bottom_mem,
    pathIntegral_eq_sub_of_isExactOn_of_piecewiseC1
      hexact hU hright right_mem,
    pathIntegral_eq_sub_of_isExactOn_of_piecewiseC1
      hexact hU htop top_mem,
    pathIntegral_eq_sub_of_isExactOn_of_piecewiseC1
      hexact hU hleft left_mem]
  abel

end SandronesLibrary.ComplexAnalysis
namespace SandronesLibrary.ComplexAnalysis

open SandronesLibrary.Topology

/-- Native-`Fin` cellwise primitive assembly and internal-edge cancellation.-/
private theorem FiniteLocalPrimitivePathGrid.outerBoundaryIntegral_eq_zero
    {f : ℂ → ℂ} (G : FiniteLocalPrimitivePathGrid f) :
    (∑ i : Fin G.steps,
        (pathIntegral f (G.horizontal i 0) -
          pathIntegral f (G.horizontal i (Fin.last G.steps)))) +
      ∑ j : Fin G.steps,
        (pathIntegral f (G.vertical (Fin.last G.steps) j) -
          pathIntegral f (G.vertical 0 j)) = 0 := by
  let horizontalIntegral := fun i j ↦ pathIntegral f (G.horizontal i j)
  let verticalIntegral := fun i j ↦ pathIntegral f (G.vertical i j)
  have hcell : ∀ i j,
      (horizontalIntegral i j.castSucc - horizontalIntegral i j.succ) +
        (verticalIntegral i.succ j - verticalIntegral i.castSucc j) = 0 := by
    intro i j
    have hboundary := pathIntegral_fourEdgeBoundary_eq_zero_of_isExactOn
      (G.horizontal i j.castSucc) (G.vertical i.succ j)
      (G.horizontal i j.succ).symm (G.vertical i.castSucc j).symm
      (G.cell_exact i j) (G.cellSet_open i j)
      (G.horizontal_piecewiseC1 i j.castSucc)
      (G.vertical_piecewiseC1 i.succ j)
      (G.horizontal_piecewiseC1 i j.succ).symm
      (G.vertical_piecewiseC1 i.castSucc j).symm
      (G.bottom_mem i j) (G.right_mem i j)
      (by simpa only [Path.symm_range] using G.top_mem i j)
      (by simpa only [Path.symm_range] using G.left_mem i j)
    simp only [pathIntegral_symm] at hboundary
    dsimp [horizontalIntegral, verticalIntegral]
    calc
      _ = pathIntegral f (G.horizontal i j.castSucc) +
          pathIntegral f (G.vertical i.succ j) +
          -pathIntegral f (G.horizontal i j.succ) +
          -pathIntegral f (G.vertical i.castSucc j) := by abel
      _ = 0 := hboundary
  have hsum :
      (∑ i : Fin G.steps, ∑ j : Fin G.steps,
        ((horizontalIntegral i j.castSucc - horizontalIntegral i j.succ) +
          (verticalIntegral i.succ j - verticalIntegral i.castSucc j))) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    apply Finset.sum_eq_zero
    intro j hj
    exact hcell i j
  rw [sum_finSquareCellBoundaries_eq_outerBoundary] at hsum
  exact hsum

end SandronesLibrary.ComplexAnalysis

namespace SandronesLibrary.ComplexAnalysis

open SandronesLibrary.Topology

/-- Cellwise exactness on a finite raw open grid forces the integral along its
four original outer sides to vanish. Internal raw edges may be regularized,
but the four boundary families are retained definitionally by their chosen
replacements.-/
theorem finiteRawOpenPathGrid_outerBoundaryIntegral_eq_zero
    {f : ℂ → ℂ} (R : FiniteRawOpenPathGrid ℂ)
    (hexact : ∀ i j, Complex.IsExactOn f (R.cellSet i j)) :
    (∑ i : Fin R.steps,
        (pathIntegral f (R.horizontalRaw i 0) -
          pathIntegral f (R.horizontalRaw i (Fin.last R.steps)))) +
      ∑ j : Fin R.steps,
        (pathIntegral f (R.verticalRaw (Fin.last R.steps) j) -
          pathIntegral f (R.verticalRaw 0 j)) = 0 := by
  classical
  let horizontal := fun i j ↦
    Classical.choose (R.horizontalReplacementExists i j)
  have horizontal_spec := fun i j ↦
    Classical.choose_spec (R.horizontalReplacementExists i j)
  let vertical := fun i j ↦
    Classical.choose (R.verticalReplacementExists i j)
  have vertical_spec := fun i j ↦
    Classical.choose_spec (R.verticalReplacementExists i j)
  let G : FiniteLocalPrimitivePathGrid f := {
    steps := R.steps
    vertex := R.vertex
    horizontal := horizontal
    vertical := vertical
    horizontal_piecewiseC1 := fun i j ↦ (horizontal_spec i j).1
    vertical_piecewiseC1 := fun i j ↦ (vertical_spec i j).1
    cellSet := R.cellSet
    cellSet_open := R.cellSet_open
    cell_exact := hexact
    bottom_mem := fun i j ↦ (horizontal_spec i j.castSucc).2.1 j rfl
    right_mem := fun i j ↦ (vertical_spec i.succ j).2.2.1 i rfl
    top_mem := fun i j ↦ (horizontal_spec i j.succ).2.2.1 j rfl
    left_mem := fun i j ↦ (vertical_spec i.castSucc j).2.1 i rfl }
  have houter := G.outerBoundaryIntegral_eq_zero
  have horizontal_zero : ∀ i, horizontal i 0 = R.horizontalRaw i 0 :=
    fun i ↦ (horizontal_spec i 0).2.2.2 (Or.inl rfl)
  have horizontal_last : ∀ i,
      horizontal i (Fin.last R.steps) =
        R.horizontalRaw i (Fin.last R.steps) :=
    fun i ↦ (horizontal_spec i (Fin.last R.steps)).2.2.2 (Or.inr rfl)
  have vertical_zero : ∀ j, vertical 0 j = R.verticalRaw 0 j :=
    fun j ↦ (vertical_spec 0 j).2.2.2 (Or.inl rfl)
  have vertical_last : ∀ j,
      vertical (Fin.last R.steps) j =
        R.verticalRaw (Fin.last R.steps) j :=
    fun j ↦ (vertical_spec (Fin.last R.steps) j).2.2.2 (Or.inr rfl)
  dsimp only [G] at houter
  simp_rw [horizontal_zero, horizontal_last, vertical_zero, vertical_last] at houter
  exact houter

end SandronesLibrary.ComplexAnalysis
