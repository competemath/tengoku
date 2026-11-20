import Tengoku.Seed.Analysis.InnerProductSpace.Adjoint
import Tengoku.Seed.Tactic.Ring

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Geometric Brascamp–Lieb data and the quadratic defect

The linear algebra is stated for real Hilbert spaces with arbitrary target spaces.
It will serve both real scalar targets and realifications of complex scalar targets.
-/

noncomputable section

open scoped BigOperators InnerProduct

namespace GeometricBrascampLieb

variable {ι E : Type*} {F : ι → Type*} [Fintype ι]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [∀ i, NormedAddCommGroup (F i)] [∀ i, InnerProductSpace ℝ (F i)]
  [∀ i, CompleteSpace (F i)]

/-- The two geometric normalization identities, with nonnegative weights.-/
structure Datum (ι E : Type*) (F : ι → Type*) [Fintype ι]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [∀ i, NormedAddCommGroup (F i)] [∀ i, InnerProductSpace ℝ (F i)]
    [∀ i, CompleteSpace (F i)] where
  weight : ι → ℝ
  weight_nonneg : ∀ i, 0 ≤ weight i
  map : ∀ i, E →L[ℝ] F i
  coisometry : ∀ i, (map i).comp (map i).adjoint = ContinuousLinearMap.id ℝ (F i)
  resolution : ∑ i, weight i • (map i).adjoint.comp (map i) = ContinuousLinearMap.id ℝ E

namespace Datum

variable (D : Datum ι E F)

def synthesis (v : ∀ i, F i) : E := ∑ i, D.weight i • (D.map i).adjoint (v i)

/--
@isnad1 id=eq.0h5v.s12.da3c61aa9216 from=translated src=- shape=c699e373 vocab=5a010f59
-/
theorem resolution_apply (x : E) :
    ∑ i, D.weight i • (D.map i).adjoint (D.map i x) = x := by
  simpa using congrArg (fun A : E →L[ℝ] E => A x) D.resolution

/--
@isnad1 id=eq.0h6v.s9.d4f300a3416c from=translated src=- shape=d4781df2 vocab=c06831a3
-/
theorem sum_weight_inner (x y : E) :
    ∑ i, D.weight i * inner ℝ (D.map i x) (D.map i y) = inner ℝ x y := by
  have h := congrArg (fun z : E => inner ℝ z y) (D.resolution_apply x)
  simpa only [sum_inner, real_inner_smul_left, ContinuousLinearMap.adjoint_inner_left] using h

/--
@isnad1 id=eq.0h5v.s8.5bc063ef653f from=translated src=- shape=c8f17807 vocab=4fcb84d4
-/
theorem sum_weight_norm_sq (x : E) :
    ∑ i, D.weight i * ‖D.map i x‖ ^ 2 = ‖x‖ ^ 2 := by
  simpa only [real_inner_self_eq_norm_sq] using D.sum_weight_inner x x

/--
@isnad1 id=eq.0h6v.s8.18d8fc2dda55 from=translated src=- shape=3ca26efd vocab=c79a3209
-/
theorem synthesis_inner (v : ∀ i, F i) (x : E) :
    inner ℝ (D.synthesis v) x = ∑ i, D.weight i * inner ℝ (v i) (D.map i x) := by
  simp only [synthesis, sum_inner, real_inner_smul_left,
    ContinuousLinearMap.adjoint_inner_left]

/-- An exact sum-of-squares identity for the defect in the heat-flow calculation.
@isnad1 id=eq.0h5v.s9.dea93ebb92e1 from=translated src=- shape=c8800270 vocab=4c9bda5c
-/
theorem defect_eq_sum_sq (v : ∀ i, F i) :
    (∑ i, D.weight i * ‖v i‖ ^ 2) - ‖D.synthesis v‖ ^ 2 =
      ∑ i, D.weight i * ‖v i - D.map i (D.synthesis v)‖ ^ 2 := by
  simp_rw [norm_sub_sq_real, mul_add, mul_sub, Finset.sum_add_distrib,
    Finset.sum_sub_distrib]
  rw [D.sum_weight_norm_sq]
  have hcross : (∑ i, D.weight i * (2 * inner ℝ (v i) (D.map i (D.synthesis v)))) =
      2 * ‖D.synthesis v‖ ^ 2 := by
    calc
      _ = 2 * ∑ i, D.weight i * inner ℝ (v i) (D.map i (D.synthesis v)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = _ := by rw [← D.synthesis_inner, real_inner_self_eq_norm_sq]
  rw [hcross]
  ring

/--
@isnad1 id=le.0h5v.s7.48f7a04d8775 from=translated src=- shape=5854fef4 vocab=202346a3
-/
theorem defect_nonneg (v : ∀ i, F i) :
    0 ≤ (∑ i, D.weight i * ‖v i‖ ^ 2) - ‖D.synthesis v‖ ^ 2 := by
  rw [D.defect_eq_sum_sq]
  exact Finset.sum_nonneg fun i _ => mul_nonneg (D.weight_nonneg i) (sq_nonneg _)

/--
@isnad1 id=le.0h5v.s7.149960c14936 from=translated src=- shape=0ddaf240 vocab=29074924
-/
theorem synthesis_norm_sq_le (v : ∀ i, F i) :
    ‖D.synthesis v‖ ^ 2 ≤ ∑ i, D.weight i * ‖v i‖ ^ 2 :=
  sub_nonneg.mp (D.defect_nonneg v)

/--
@isnad1 id=eq.0h6v.s11.616c45f1c049 from=translated src=- shape=42cabb09 vocab=8f81ca85
-/
theorem coisometry_apply (i : ι) (y : F i) :
    D.map i ((D.map i).adjoint y) = y := by
  simpa using congrArg (fun A : F i →L[ℝ] F i => A y) (D.coisometry i)

/--
@isnad1 id=eq.0h6v.s11.0b501eabda81 from=translated src=- shape=a4318af3 vocab=a20ae476
-/
theorem adjoint_norm_sq (i : ι) (y : F i) : ‖(D.map i).adjoint y‖ ^ 2 = ‖y‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, ContinuousLinearMap.adjoint_inner_left,
    D.coisometry_apply, real_inner_self_eq_norm_sq]

/--
@isnad1 id=surjecti.0h5v.s8.1879b8cfb7b2 from=translated src=- shape=fa292f4d vocab=fc3812df
-/
theorem map_surjective (i : ι) : Function.Surjective (D.map i) :=
  fun y => ⟨(D.map i).adjoint y, D.coisometry_apply i y⟩

end Datum
end GeometricBrascampLieb
