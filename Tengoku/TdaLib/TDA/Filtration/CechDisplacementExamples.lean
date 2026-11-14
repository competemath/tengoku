import Tengoku.TdaLib.TDA.Filtration.CechDisplacement

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

/-!
# Same-label Čech displacement fixtures

The fixtures test the `Cech.radiusAt`, `Cech.filter`, `Cech.displacement` and
`Rips` definitions: three points on the line where the Čech change attains the
displacement and the Rips change attains twice it, two labellings of the same image with
positive displacement, and the failure of the radius estimate on the empty set for a
negative bound.
-/

universe w v

namespace TDA.Filtration.Cech.DisplacementExamples

open TDA.Simplicial

/-! ### Three points: Čech moves by exactly `δ`, Rips by exactly `2 * δ` -/

namespace ThreePoints

/-- The labelled points `0, 1, 2` on the real line.-/
def p : Fin 3 → ℝ := ![0, 1, 2]

/-- The outer points moved outward by one: `-1, 1, 3`.-/
def q : Fin 3 → ℝ := ![-1, 1, 3]

/--
@isnad1 id=eq.0h0v.s4.e115c77216cd from=translated src=- shape=012516b9 vocab=3a6ad601
-/
@[simp] theorem p_zero : p 0 = 0 := rfl
/--
@isnad1 id=eq.0h0v.s4.8321b053c991 from=translated src=- shape=012516b9 vocab=3a6ad601
-/
@[simp] theorem p_two : p 2 = 2 := rfl
/--
@isnad1 id=eq.0h0v.s4.88bfb81ba114 from=translated src=- shape=f05c4898 vocab=0b75d394
-/
@[simp] theorem q_zero : q 0 = -1 := rfl
/--
@isnad1 id=eq.0h0v.s4.50ead3758c0e from=translated src=- shape=012516b9 vocab=b8395d6e
-/
@[simp] theorem q_two : q 2 = 3 := rfl

/--
@isnad1 id=injectiv.0h0v.s3.9e400b3bc923 from=translated src=- shape=bfe16b09 vocab=4359e0d4
-/
theorem p_injective : Function.Injective p := by
  intro i j h
  fin_cases i <;> fin_cases j <;> first | rfl | norm_num [p] at h

/--
@isnad1 id=injectiv.0h0v.s3.d471faecf238 from=translated src=- shape=bfe16b09 vocab=fee16af8
-/
theorem q_injective : Function.Injective q := by
  intro i j h
  fin_cases i <;> fin_cases j <;> first | rfl | norm_num [q] at h

/-- The label metric induced by `p`.-/
noncomputable abbrev metricP : MetricSpace (Fin 3) :=
  MetricSpace.induced p p_injective inferInstance

/-- The label metric induced by `q`.-/
noncomputable abbrev metricQ : MetricSpace (Fin 3) :=
  MetricSpace.induced q q_injective inferInstance

/--
@isnad1 id=eq.0h2v.s5.24314f9a547c from=translated src=- shape=0e1f8095 vocab=9105aa2d
-/
theorem metricP_dist (v w : Fin 3) : metricP.dist v w = dist (p v) (p w) := rfl

/--
@isnad1 id=eq.0h2v.s5.c4d055001ce8 from=translated src=- shape=0e1f8095 vocab=358a4652
-/
theorem metricQ_dist (v w : Fin 3) : metricQ.dist v w = dist (q v) (q w) := rfl

/--
@isnad1 id=eq.0h0v.s4.cdee9df720d8 from=translated src=- shape=ac4cafab vocab=210dadd3
-/
theorem displacement_eq : displacement p q = 1 := by
  apply le_antisymm
  · refine (displacement_le_iff p q 1).2 ⟨zero_le_one, fun v => ?_⟩
    fin_cases v <;> norm_num [p, q, Real.dist_eq]
  · have h := dist_le_displacement p q 0
    norm_num [p, q, Real.dist_eq] at h
    exact h

/-- The triangle on all three labels.-/
def tri : TotalFace (Rips.fullComplex (Fin 3)) := ⟨Finset.univ, Finset.univ_nonempty⟩

/--
@isnad1 id=eq.0h0v.s5.6b60a392c73a from=translated src=- shape=5d4dcd9b vocab=f59dd648
-/
theorem cech_value_p : (filter p).value tri = 1 := by
  apply le_antisymm
  · refine (filter_value_le_radiusAt p tri 1).trans
      ((radiusAt_le_iff p 1 _ 1).2 ⟨zero_le_one, fun v _ => ?_⟩)
    fin_cases v <;> norm_num [p, Real.dist_eq]
  · have h := rips_le_two_mul_filter_value metricP p metricP_dist tri
    have hd : metricP.dist 0 2 ≤ (Rips.filter metricP).value tri :=
      Rips.dist_le_diameter metricP (Finset.mem_univ _) (Finset.mem_univ _)
    rw [metricP_dist, p_zero, p_two, Real.dist_eq] at hd
    rw [Rips.filter_value] at h
    norm_num at hd
    linarith

/--
@isnad1 id=eq.0h0v.s5.323f55cbce8d from=translated src=- shape=5d4dcd9b vocab=da8dc4b4
-/
theorem cech_value_q : (filter q).value tri = 2 := by
  apply le_antisymm
  · refine (filter_value_le_radiusAt q tri 1).trans
      ((radiusAt_le_iff q 1 _ 2).2 ⟨zero_le_two, fun v _ => ?_⟩)
    fin_cases v <;> norm_num [q, Real.dist_eq]
  · have h := rips_le_two_mul_filter_value metricQ q metricQ_dist tri
    have hd : metricQ.dist 0 2 ≤ (Rips.filter metricQ).value tri :=
      Rips.dist_le_diameter metricQ (Finset.mem_univ _) (Finset.mem_univ _)
    rw [metricQ_dist, q_zero, q_two, Real.dist_eq] at hd
    rw [Rips.filter_value] at h
    norm_num at hd
    linarith

/-- The displacement-form Čech face estimate is attained.
@isnad1 id=eq.0h0v.s6.5c6d8f3e3ca0 from=translated src=- shape=f827ffd1 vocab=7e977c02
-/
theorem abs_cech_value_sub_eq_displacement :
    |(filter p).value tri - (filter q).value tri| = displacement p q := by
  rw [cech_value_p, cech_value_q, displacement_eq]
  norm_num

/--
@isnad1 id=eq.0h0v.s4.29efbeefe412 from=translated src=- shape=0cc44dab vocab=c5da9103
-/
theorem rips_value_p : Rips.diameter metricP Finset.univ = 2 := by
  apply le_antisymm
  · refine (Rips.diameter_le_iff metricP _ 2).2 ⟨zero_le_two, fun v _ w _ => ?_⟩
    rw [metricP_dist]
    fin_cases v <;> fin_cases w <;> norm_num [p, Real.dist_eq]
  · have hd := Rips.dist_le_diameter metricP (Finset.mem_univ (0 : Fin 3))
      (Finset.mem_univ (2 : Fin 3))
    rw [metricP_dist, p_zero, p_two, Real.dist_eq] at hd
    norm_num at hd
    exact hd

/--
@isnad1 id=eq.0h0v.s4.23bd56f1b1c2 from=translated src=- shape=0cc44dab vocab=61e1bfe7
-/
theorem rips_value_q : Rips.diameter metricQ Finset.univ = 4 := by
  apply le_antisymm
  · refine (Rips.diameter_le_iff metricQ _ 4).2 ⟨by norm_num, fun v _ w _ => ?_⟩
    rw [metricQ_dist]
    fin_cases v <;> fin_cases w <;> norm_num [q, Real.dist_eq]
  · have hd := Rips.dist_le_diameter metricQ (Finset.mem_univ (0 : Fin 3))
      (Finset.mem_univ (2 : Fin 3))
    rw [metricQ_dist, q_zero, q_two, Real.dist_eq] at hd
    norm_num at hd
    exact hd

/-- The Rips face estimate in displacement form is attained.
@isnad1 id=eq.0h0v.s6.cebeaadf7187 from=translated src=- shape=5201b8c6 vocab=f3d54248
-/
theorem abs_rips_value_sub_eq_two_mul_displacement :
    |Rips.diameter metricP Finset.univ - Rips.diameter metricQ Finset.univ| =
      2 * displacement p q := by
  rw [rips_value_p, rips_value_q, displacement_eq]
  norm_num

/-- The Rips comparison `pairwiseDiscrepancy ≤ 2 * displacement` is attained.
@isnad1 id=eq.0h0v.s4.6f81838a13e9 from=translated src=- shape=36e22f2b vocab=9c295919
-/
theorem pairwiseDiscrepancy_eq : Rips.pairwiseDiscrepancy metricP metricQ = 2 := by
  apply le_antisymm
  · have h := pairwiseDiscrepancy_le_two_mul_displacement metricP metricQ p q
      metricP_dist metricQ_dist
    rw [displacement_eq] at h
    linarith
  · have h := Rips.abs_dist_sub_le_pairwiseDiscrepancy metricP metricQ 0 2
    rw [metricP_dist, metricQ_dist, p_zero, p_two, q_zero, q_two, Real.dist_eq,
      Real.dist_eq] at h
    norm_num at h
    exact h

/--
@isnad1 id=eq.0h0v.s5.7fb2461363f5 from=translated src=- shape=7057ba55 vocab=06a0c507
-/
theorem pairwiseDiscrepancy_eq_two_mul_displacement :
    Rips.pairwiseDiscrepancy metricP metricQ = 2 * displacement p q := by
  rw [pairwiseDiscrepancy_eq, displacement_eq]
  norm_num

/-- On this family Čech values are strictly more stable than Rips values.
@isnad1 id=lt.0h0v.s7.3c87cf59bc0a from=translated src=- shape=f6415fbc vocab=9f16f429
-/
theorem cech_change_lt_rips_change :
    |(filter p).value tri - (filter q).value tri| <
      |(Rips.filter metricP).value tri - (Rips.filter metricQ).value tri| := by
  rw [Rips.filter_value, Rips.filter_value]
  change _ < |Rips.diameter metricP Finset.univ - Rips.diameter metricQ Finset.univ|
  rw [cech_value_p, cech_value_q, rips_value_p, rips_value_q]
  norm_num

end ThreePoints

/-! ### Same image, positive displacement -/

namespace Swap

/-- The labelled points `0, 2`.-/
def p : Fin 2 → ℝ := ![0, 2]

/-- The same two points with the labels exchanged.-/
def q : Fin 2 → ℝ := ![2, 0]

/--
@isnad1 id=eq.0h0v.s4.7433eb807827 from=translated src=- shape=eff7bada vocab=023ce1db
-/
theorem range_eq : Set.range p = Set.range q := by
  ext x
  simp only [Set.mem_range, Fin.exists_fin_two, p, q, Matrix.cons_val_zero,
    Matrix.cons_val_one]
  tauto

/-- The images agree, yet the same-label displacement is positive.
@isnad1 id=eq.0h0v.s4.aaeb0fd8e131 from=translated src=- shape=ac4cafab vocab=56429054
-/
theorem displacement_eq : displacement p q = 2 := by
  apply le_antisymm
  · refine (displacement_le_iff p q 2).2 ⟨zero_le_two, fun v => ?_⟩
    fin_cases v <;> norm_num [p, q, Real.dist_eq]
  · have h := dist_le_displacement p q 0
    norm_num [p, q, Real.dist_eq] at h
    exact h

end Swap

/-! ### The sign condition of the radius estimate cannot be dropped -/

section EmptySeed

variable {X : Type w} {V : Type v} [PseudoMetricSpace X]

/--
@isnad1 id=eq.0h4v.s5.c8ba104938f9 from=translated src=- shape=f820d4f4 vocab=2c5c9859
-/
@[simp] theorem radiusAt_empty (p : V → X) (x : X) : radiusAt p x ∅ = 0 := by
  rw [radiusAt, Finset.fold_empty]

/-- On the empty set the displacement hypothesis holds vacuously for `ε = -1`, but the radius
estimate fails.
@isnad1 id=and.0h5v.s6.8178cf3b1240 from=translated src=- shape=ec6fa766 vocab=49e05838
-/
theorem radiusAt_estimate_fails_of_neg (p q : V → X) (x : X) :
    (∀ v ∈ (∅ : Finset V), dist (p v) (q v) ≤ -1) ∧
      ¬ radiusAt p x ∅ ≤ radiusAt q x ∅ + -1 := by
  refine ⟨fun v hv => absurd hv (Finset.notMem_empty v), ?_⟩
  rw [radiusAt_empty, radiusAt_empty]
  norm_num

end EmptySeed

end TDA.Filtration.Cech.DisplacementExamples
