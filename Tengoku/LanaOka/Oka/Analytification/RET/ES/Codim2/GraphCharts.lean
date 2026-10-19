/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Tengoku.LanaOka.Oka.Analytification.RET.ES.Codim2.BlowupChart

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Normal crossings coordinates for resolved families of graphs

Keep the notation of `Oka/Analytification/RET/ES/Codim2/BlowupChart.lean`: points of
`(E × ℂ) × ℂ` are written `((y, t), w)`. After the blow-ups of
`Codim2.IsContactFamily.blowup`, the total transform of a family of graphs is locally of one of
the following forms, and each is a normal crossings divisor in explicit holomorphic coordinates
`Φ` with explicit holomorphic inverse `Φ'`:

* a single graph `w = ψ(y, t)`: `Φ((y, t), w) = ((y, t), w - ψ(y, t))`
  (`Codim2.smoothChart`);
* the hyperplane `t = 0` and a graph `w = χ(y, t)`:
  `Φ((y, t), w) = (y, (t, w - χ(y, t)))` (`Codim2.verticalChart`);
* two graphs `w = ψ₁` and `w = ψ₁ + t u` with `u` without zeros, i.e. contact order `1`:
  `Φ((y, t), w) = (y, (v, v - t))` with `v = (w - ψ₁) / u` (`Codim2.transversalChart`).

In each case `x` lies on the divisor if and only if some coordinate of the second component of
`Φ(x)` vanishes (`Codim2.mem_graphs_iff_smoothChart`, `Codim2.mem_iff_verticalChart`,
`Codim2.mem_iff_transversalChart`). Together with
`ComplexAnalytic.BoundedSections.exists_isFreeSpanAt_of_local` this shows that the sheaf of
bounded sections is locally free at such points.

## Main definitions

- `Codim2.smoothChart`, `Codim2.verticalChart`, `Codim2.transversalChart` and their inverses.
-/

open Set Filter Topology

namespace Codim2

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-! ### A single graph -/

/-- The coordinates `((y, t), w) ↦ ((y, t), w - ψ(y, t))` along the graph of `ψ`. -/
def smoothChart (ψ : E × ℂ → ℂ) (x : (E × ℂ) × ℂ) : (E × ℂ) × (Fin 1 → ℂ) :=
  (x.1, fun _ ↦ x.2 - ψ x.1)

/-- The inverse `((y, t), z) ↦ ((y, t), z + ψ(y, t))` of `Codim2.smoothChart ψ`. -/
def smoothChartInv (ψ : E × ℂ → ℂ) (z : (E × ℂ) × (Fin 1 → ℂ)) : (E × ℂ) × ℂ :=
  (z.1, z.2 0 + ψ z.1)

omit [NormedAddCommGroup E] [NormedSpace ℂ E] in
lemma smoothChartInv_smoothChart (ψ : E × ℂ → ℂ) (x : (E × ℂ) × ℂ) :
    smoothChartInv ψ (smoothChart ψ x) = x :=
  Prod.ext rfl (sub_add_cancel _ _)

omit [NormedAddCommGroup E] [NormedSpace ℂ E] in
lemma smoothChart_smoothChartInv (ψ : E × ℂ → ℂ) (z : (E × ℂ) × (Fin 1 → ℂ)) :
    smoothChart ψ (smoothChartInv ψ z) = z := by
  refine Prod.ext rfl (funext fun i ↦ ?_)
  rw [Subsingleton.elim i 0]
  exact add_sub_cancel_right _ _

lemma differentiableOn_smoothChart {ψ : E × ℂ → ℂ} {V : Set (E × ℂ)}
    (hψ : DifferentiableOn ℂ ψ V) : DifferentiableOn ℂ (smoothChart ψ) (Prod.fst ⁻¹' V) := by
  have h : DifferentiableOn ℂ (fun x : (E × ℂ) × ℂ ↦ ψ x.1) (Prod.fst ⁻¹' V) :=
    hψ.comp differentiableOn_fst fun _ hx ↦ hx
  exact differentiableOn_fst.prodMk (differentiableOn_pi.2 fun _ ↦ differentiableOn_snd.sub h)

lemma differentiableOn_smoothChartInv {ψ : E × ℂ → ℂ} {V : Set (E × ℂ)}
    (hψ : DifferentiableOn ℂ ψ V) : DifferentiableOn ℂ (smoothChartInv ψ) (Prod.fst ⁻¹' V) := by
  have h : DifferentiableOn ℂ (fun z : (E × ℂ) × (Fin 1 → ℂ) ↦ ψ z.1) (Prod.fst ⁻¹' V) :=
    hψ.comp differentiableOn_fst fun _ hx ↦ hx
  exact differentiableOn_fst.prodMk
    ((by fun_prop : Differentiable ℂ fun z : (E × ℂ) × (Fin 1 → ℂ) ↦ z.2 0).differentiableOn.add h)

omit [NormedAddCommGroup E] [NormedSpace ℂ E] in
/-- A point lies on the graph of `ψ` if and only if its last coordinate in
`Codim2.smoothChart ψ` vanishes. -/
lemma mem_graphs_iff_smoothChart {ψ : E × ℂ → ℂ} {V : Set (E × ℂ)} {x : (E × ℂ) × ℂ}
    (hx : x.1 ∈ V) : x ∈ graphs V (fun _ : Unit ↦ ψ) ↔ ∃ i, (smoothChart ψ x).2 i = 0 := by
  simp [mem_graphs, smoothChart, hx, sub_eq_zero]

/-! ### The hyperplane `t = 0` and a graph -/

/-- The coordinates `((y, t), w) ↦ (y, (t, w - χ(y, t)))`. -/
def verticalChart (χ : E × ℂ → ℂ) (x : (E × ℂ) × ℂ) : E × (Fin 2 → ℂ) :=
  (x.1.1, ![x.1.2, x.2 - χ x.1])

/-- The inverse `(y, (s, z)) ↦ ((y, s), z + χ(y, s))` of `Codim2.verticalChart χ`. -/
def verticalChartInv (χ : E × ℂ → ℂ) (z : E × (Fin 2 → ℂ)) : (E × ℂ) × ℂ :=
  ((z.1, z.2 0), z.2 1 + χ (z.1, z.2 0))

omit [NormedAddCommGroup E] [NormedSpace ℂ E] in
lemma verticalChartInv_verticalChart (χ : E × ℂ → ℂ) (x : (E × ℂ) × ℂ) :
    verticalChartInv χ (verticalChart χ x) = x := by
  simp [verticalChart, verticalChartInv]

omit [NormedAddCommGroup E] [NormedSpace ℂ E] in
lemma verticalChart_verticalChartInv (χ : E × ℂ → ℂ) (z : E × (Fin 2 → ℂ)) :
    verticalChart χ (verticalChartInv χ z) = z := by
  refine Prod.ext rfl (funext fun i ↦ ?_)
  fin_cases i <;> simp [verticalChart, verticalChartInv]

lemma differentiableOn_verticalChart {χ : E × ℂ → ℂ} {V : Set (E × ℂ)}
    (hχ : DifferentiableOn ℂ χ V) : DifferentiableOn ℂ (verticalChart χ) (Prod.fst ⁻¹' V) := by
  have h : DifferentiableOn ℂ (fun x : (E × ℂ) × ℂ ↦ χ x.1) (Prod.fst ⁻¹' V) :=
    hχ.comp differentiableOn_fst fun _ hx ↦ hx
  refine (differentiable_fst.comp differentiable_fst).differentiableOn.prodMk
    (differentiableOn_pi.2 fun i ↦ ?_)
  fin_cases i
  · simp only [Fin.zero_eta, Matrix.cons_val_zero]
    fun_prop
  · simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    exact differentiableOn_snd.sub h

lemma differentiableOn_verticalChartInv {χ : E × ℂ → ℂ} {V : Set (E × ℂ)}
    (hχ : DifferentiableOn ℂ χ V) :
    DifferentiableOn ℂ (verticalChartInv χ) {z | (z.1, z.2 0) ∈ V} := by
  have hm : Differentiable ℂ fun z : E × (Fin 2 → ℂ) ↦ ((z.1, z.2 0) : E × ℂ) := by fun_prop
  have h : DifferentiableOn ℂ (fun z : E × (Fin 2 → ℂ) ↦ χ (z.1, z.2 0))
      {z | (z.1, z.2 0) ∈ V} := hχ.comp hm.differentiableOn fun _ hz ↦ hz
  exact hm.differentiableOn.prodMk
    ((by fun_prop : Differentiable ℂ fun z : E × (Fin 2 → ℂ) ↦ z.2 1).differentiableOn.add h)

omit [NormedAddCommGroup E] [NormedSpace ℂ E] in
/-- A point lies on `{t = 0} ∪ {w = χ}` if and only if a coordinate of the second component of
`Codim2.verticalChart χ` vanishes. -/
lemma mem_iff_verticalChart {χ : E × ℂ → ℂ} {V : Set (E × ℂ)} {x : (E × ℂ) × ℂ}
    (hx : x.1 ∈ V) : x ∈ vertical V ∪ graphs V (fun _ : Unit ↦ χ) ↔
      ∃ i, (verticalChart χ x).2 i = 0 := by
  simp only [mem_union, mem_vertical, mem_graphs, hx, true_and, exists_const, Fin.exists_fin_two,
    verticalChart, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
    sub_eq_zero]

/-! ### Two graphs of contact order one -/

/-- The coordinates `((y, t), w) ↦ (y, (v, v - t))`, `v = (w - ψ(y, t)) / u(y, t)`, in which the
graphs of `ψ` and `ψ + t u` become the coordinate hyperplanes. -/
noncomputable def transversalChart (ψ u : E × ℂ → ℂ) (x : (E × ℂ) × ℂ) : E × (Fin 2 → ℂ) :=
  (x.1.1, ![(x.2 - ψ x.1) / u x.1, (x.2 - ψ x.1) / u x.1 - x.1.2])

/-- The inverse `(y, (a, b)) ↦ ((y, a - b), ψ(y, a - b) + u(y, a - b) a)` of
`Codim2.transversalChart ψ u`. -/
def transversalChartInv (ψ u : E × ℂ → ℂ) (z : E × (Fin 2 → ℂ)) : (E × ℂ) × ℂ :=
  ((z.1, z.2 0 - z.2 1), ψ (z.1, z.2 0 - z.2 1) + u (z.1, z.2 0 - z.2 1) * z.2 0)

omit [NormedAddCommGroup E] [NormedSpace ℂ E] in
lemma transversalChartInv_transversalChart (ψ u : E × ℂ → ℂ) {x : (E × ℂ) × ℂ}
    (hx : u x.1 ≠ 0) : transversalChartInv ψ u (transversalChart ψ u x) = x := by
  have h₁ : ((x.1.1, (x.2 - ψ x.1) / u x.1 - ((x.2 - ψ x.1) / u x.1 - x.1.2)) : E × ℂ) = x.1 :=
    Prod.ext rfl (sub_sub_cancel _ _)
  simp only [transversalChart, transversalChartInv, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, h₁]
  rw [mul_div_cancel₀ _ hx, add_sub_cancel]

omit [NormedAddCommGroup E] [NormedSpace ℂ E] in
lemma transversalChart_transversalChartInv (ψ u : E × ℂ → ℂ) {z : E × (Fin 2 → ℂ)}
    (hz : u (z.1, z.2 0 - z.2 1) ≠ 0) :
    transversalChart ψ u (transversalChartInv ψ u z) = z := by
  refine Prod.ext rfl (funext fun i ↦ ?_)
  fin_cases i
  · simp [transversalChart, transversalChartInv, mul_div_cancel_left₀ _ hz]
  · simp [transversalChart, transversalChartInv, mul_div_cancel_left₀ _ hz]

lemma differentiableOn_transversalChart {ψ u : E × ℂ → ℂ} {V : Set (E × ℂ)}
    (hψ : DifferentiableOn ℂ ψ V) (hu : DifferentiableOn ℂ u V) (hu0 : ∀ z ∈ V, u z ≠ 0) :
    DifferentiableOn ℂ (transversalChart ψ u) (Prod.fst ⁻¹' V) := by
  have hψ' : DifferentiableOn ℂ (fun x : (E × ℂ) × ℂ ↦ ψ x.1) (Prod.fst ⁻¹' V) :=
    hψ.comp differentiableOn_fst fun _ hx ↦ hx
  have hq : DifferentiableOn ℂ (fun x : (E × ℂ) × ℂ ↦ (x.2 - ψ x.1) / u x.1)
      (Prod.fst ⁻¹' V) := by
    have hu' : DifferentiableOn ℂ (fun x : (E × ℂ) × ℂ ↦ u x.1) (Prod.fst ⁻¹' V) :=
      hu.comp differentiableOn_fst fun _ hx ↦ hx
    simp only [div_eq_mul_inv]
    exact (differentiableOn_snd.sub hψ').mul (hu'.inv fun x hx ↦ hu0 _ hx)
  refine (differentiable_fst.comp differentiable_fst).differentiableOn.prodMk
    (differentiableOn_pi.2 fun i ↦ ?_)
  fin_cases i
  · simpa [transversalChart] using hq
  · simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    exact hq.sub (by fun_prop)

lemma differentiableOn_transversalChartInv {ψ u : E × ℂ → ℂ} {V : Set (E × ℂ)}
    (hψ : DifferentiableOn ℂ ψ V) (hu : DifferentiableOn ℂ u V) :
    DifferentiableOn ℂ (transversalChartInv ψ u) {z | (z.1, z.2 0 - z.2 1) ∈ V} := by
  have hm : Differentiable ℂ fun z : E × (Fin 2 → ℂ) ↦ ((z.1, z.2 0 - z.2 1) : E × ℂ) := by
    fun_prop
  have h₁ : DifferentiableOn ℂ (fun z : E × (Fin 2 → ℂ) ↦ ψ (z.1, z.2 0 - z.2 1))
      {z | (z.1, z.2 0 - z.2 1) ∈ V} := hψ.comp hm.differentiableOn fun _ hz ↦ hz
  have h₂ : DifferentiableOn ℂ (fun z : E × (Fin 2 → ℂ) ↦ u (z.1, z.2 0 - z.2 1))
      {z | (z.1, z.2 0 - z.2 1) ∈ V} := hu.comp hm.differentiableOn fun _ hz ↦ hz
  exact hm.differentiableOn.prodMk (h₁.add (h₂.mul
    (by fun_prop : Differentiable ℂ fun z : E × (Fin 2 → ℂ) ↦ z.2 0).differentiableOn))

omit [NormedAddCommGroup E] [NormedSpace ℂ E] in
/-- A point lies on the union of the graphs of `ψ` and `ψ + t u` if and only if a coordinate of
the second component of `Codim2.transversalChart ψ u` vanishes. -/
lemma mem_iff_transversalChart {ψ u : E × ℂ → ℂ} {V : Set (E × ℂ)} {x : (E × ℂ) × ℂ}
    (hx : x.1 ∈ V) (hu : u x.1 ≠ 0) :
    x ∈ graphs V ![ψ, fun z ↦ ψ z + z.2 * u z] ↔ ∃ i, (transversalChart ψ u x).2 i = 0 := by
  simp only [mem_graphs, hx, true_and, Fin.exists_fin_two, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one, transversalChart, div_eq_zero_iff, hu,
    or_false, sub_eq_zero]
  refine or_congr Iff.rfl ?_
  rw [div_eq_iff hu, eq_comm (b := x.1.2 * u x.1), ← sub_eq_iff_eq_add', eq_comm]

end Codim2
