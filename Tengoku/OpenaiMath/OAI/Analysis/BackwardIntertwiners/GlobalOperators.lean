import Tengoku.OpenaiMath.OAI.Analysis.BackwardIntertwiners.BackwardWeights

namespace OAI

namespace BackwardIntertwiners
open Filter
open scoped Topology
noncomputable section

open Topology MeasureTheory Set
open scoped ENNReal

section Fields
variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

/--
@isnad1 id=strongly.4h5v.s12.e163c7b3e7d4 from=translated src=- shape=1fccf33e vocab=93961dda
-/
lemma weightedPermutation_stronglyMeasurable (e : ℤ ≃ ℤ) (a : X → ℤ → ℂ)
    (C : ℝ) (hC : 0 ≤ C) (ha : ∀ x j, ‖a x j‖ ≤ C)
    (hm : ∀ j, Measurable (fun x => a x j))
    {f : X → Fiber} (hf : StronglyMeasurable f) :
    StronglyMeasurable (fun x => fiberWeightedPermutation e (a x) C hC (ha x) (f x)) := by
  apply fiberCoordinates_stronglyMeasurable
  intro j
  exact (hm (e j)).mul (((lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 (e j)).continuous.comp_stronglyMeasurable hf).measurable)

/--
@isnad1 id=aestrong.4h6v.s12.7600a5b126a8 from=translated src=- shape=f0acdbae vocab=7d4d3660
-/
lemma weightedPermutation_aestronglyMeasurable (e : ℤ ≃ ℤ) (a : X → ℤ → ℂ)
    (C : ℝ) (hC : 0 ≤ C) (ha : ∀ x j, ‖a x j‖ ≤ C)
    (hm : ∀ j, Measurable (fun x => a x j))
    {f : X → Fiber} (hf : AEStronglyMeasurable f μ) :
    AEStronglyMeasurable (fun x => fiberWeightedPermutation e (a x) C hC (ha x) (f x)) μ := by
  apply (weightedPermutation_stronglyMeasurable e a C hC ha hm hf.stronglyMeasurable_mk).aestronglyMeasurable.congr
  filter_upwards [hf.ae_eq_mk] with x hx
  rw [hx]

def scalarMultiplier (g : Lp ℂ ∞ μ) : Lp Fiber 2 μ →L[ℂ] Lp Fiber 2 μ :=
  LinearMap.mkContinuous
    { toFun := fun f => g • f
      map_add' := Lp.add_smul g
      map_smul' := fun c f => (Lp.smul_comm c g f).symm }
    ‖g‖ (Lp.norm_smul_le g)

def fieldVector (A : X → Fiber →L[ℂ] Fiber) (C : ℝ)
    (hA : ∀ x, ‖A x‖ ≤ C)
    (hm : ∀ f : X → Fiber, AEStronglyMeasurable f μ → AEStronglyMeasurable (fun x => A x (f x)) μ)
    (f : Lp Fiber 2 μ) : Lp Fiber 2 μ :=
  ((Lp.memLp f).of_le_mul (hm f (Lp.aestronglyMeasurable f))
    (Filter.Eventually.of_forall fun x =>
      (A x).le_opNorm (f x) |>.trans (mul_le_mul_of_nonneg_right (hA x) (norm_nonneg _)))).toLp _

/--
@isnad1 id=eventual.2h5v.s15.ffcee2150dcf from=translated src=- shape=82d3c1e9 vocab=feb38d59
-/
lemma fieldVector_ae (A : X → Fiber →L[ℂ] Fiber) (C : ℝ)
    (hA : ∀ x, ‖A x‖ ≤ C)
    (hm : ∀ f : X → Fiber, AEStronglyMeasurable f μ → AEStronglyMeasurable (fun x => A x (f x)) μ)
    (f : Lp Fiber 2 μ) : fieldVector A C hA hm f =ᵐ[μ] fun x => A x (f x) :=
  MemLp.coeFn_toLp _

/--
@isnad1 id=le.3h5v.s14.32d27a1b776c from=translated src=- shape=4e37e0e1 vocab=de7addda
-/
lemma fieldVector_norm (A : X → Fiber →L[ℂ] Fiber) (C : ℝ) (hC : 0 ≤ C)
    (hA : ∀ x, ‖A x‖ ≤ C)
    (hm : ∀ f : X → Fiber, AEStronglyMeasurable f μ → AEStronglyMeasurable (fun x => A x (f x)) μ)
    (f : Lp Fiber 2 μ) : ‖fieldVector A C hA hm f‖ ≤ C*‖f‖ := by
  calc
    _ ≤ ‖(C:ℂ) • f‖ := by
      apply Lp.norm_le_norm_of_ae_le
      filter_upwards [fieldVector_ae A C hA hm f, Lp.coeFn_smul (C:ℂ) f] with x hx hs
      rw [hx, hs, Pi.smul_apply, norm_smul, Complex.norm_real, Real.norm_of_nonneg hC]
      exact (A x).le_opNorm (f x) |>.trans (mul_le_mul_of_nonneg_right (hA x) (norm_nonneg _))
    _ = C*‖f‖ := by rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg hC]

def fieldOperator (A : X → Fiber →L[ℂ] Fiber) (C : ℝ) (hC : 0 ≤ C)
    (hA : ∀ x, ‖A x‖ ≤ C)
    (hm : ∀ f : X → Fiber, AEStronglyMeasurable f μ → AEStronglyMeasurable (fun x => A x (f x)) μ) :
    Lp Fiber 2 μ →L[ℂ] Lp Fiber 2 μ :=
  LinearMap.mkContinuous
    { toFun := fieldVector A C hA hm
      map_add' := by
        intro f g
        apply Lp.ext
        filter_upwards [fieldVector_ae A C hA hm (f+g), fieldVector_ae A C hA hm f,
          fieldVector_ae A C hA hm g, Lp.coeFn_add f g,
          Lp.coeFn_add (fieldVector A C hA hm f) (fieldVector A C hA hm g)] with x h₁ h₂ h₃ h₄ h₅
        simp only [h₁,h₂,h₃,h₄,h₅,Pi.add_apply,map_add]
      map_smul' := by
        intro c f
        apply Lp.ext
        filter_upwards [fieldVector_ae A C hA hm (c • f), fieldVector_ae A C hA hm f,
          Lp.coeFn_smul c f, Lp.coeFn_smul c (fieldVector A C hA hm f)] with x h₁ h₂ h₃ h₄
        simp only [RingHom.id_apply, h₁,h₂,h₃,h₄,Pi.smul_apply,map_smul] }
    C (fieldVector_norm A C hC hA hm)

/--
@isnad1 id=eventual.3h5v.s17.d4bbb6106d84 from=translated src=- shape=ae81210d vocab=b9a4827b
-/
lemma fieldOperator_ae (A : X → Fiber →L[ℂ] Fiber) (C : ℝ) (hC : 0 ≤ C)
    (hA : ∀ x, ‖A x‖ ≤ C)
    (hm : ∀ f : X → Fiber, AEStronglyMeasurable f μ → AEStronglyMeasurable (fun x => A x (f x)) μ)
    (f : Lp Fiber 2 μ) : fieldOperator A C hC hA hm f =ᵐ[μ] fun x => A x (f x) :=
  fieldVector_ae A C hA hm f

/--
@isnad1 id=le.3h4v.s16.2642ca080b71 from=translated src=- shape=67ad95ae vocab=4e429734
-/
lemma fieldOperator_norm (A : X → Fiber →L[ℂ] Fiber) (C : ℝ) (hC : 0 ≤ C)
    (hA : ∀ x, ‖A x‖ ≤ C)
    (hm : ∀ f : X → Fiber, AEStronglyMeasurable f μ → AEStronglyMeasurable (fun x => A x (f x)) μ) :
    ‖fieldOperator A C hC hA hm‖ ≤ C :=
  ContinuousLinearMap.opNorm_le_bound _ hC (fieldVector_norm A C hC hA hm)

/--
@isnad1 id=eventual.0h4v.s17.16d072e28c7f from=translated src=- shape=071fe18a vocab=8959e046
-/
lemma scalarMultiplier_ae (g : Lp ℂ ∞ μ) (f : Lp Fiber 2 μ) :
    scalarMultiplier g f =ᵐ[μ] fun x => g x • f x := Lp.coeFn_lpSMul g f
end Fields

abbrev GlobalHilbert := Lp Fiber 2 baseMeasure

def OperatorInvariant {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    (L : Submodule ℂ H) (T : H →L[ℂ] H) : Prop := ∀ v ∈ L, T v ∈ L

def generatedAlgebra (S V : GlobalHilbert →L[ℂ] GlobalHilbert) :
    Subalgebra ℂ (GlobalHilbert →L[ℂ] GlobalHilbert) :=
  Algebra.adjoin ℂ ({S,V} ∪ Set.range (scalarMultiplier (μ := baseMeasure)))

def AlgebraTransitive (A : Subalgebra ℂ (GlobalHilbert →L[ℂ] GlobalHilbert)) : Prop :=
  ∀ L : Submodule ℂ GlobalHilbert, IsClosed (L : Set GlobalHilbert) →
    (∀ T ∈ A, OperatorInvariant L T) → L = ⊥ ∨ L = ⊤

structure DirectModelData where
  Sx : Base → Fiber →L[ℂ] Fiber
  S : GlobalHilbert →L[ℂ] GlobalHilbert
  b : Base → ℤ → ℝ
  Vx : Base → Fiber →L[ℂ] Fiber
  V : GlobalHilbert →L[ℂ] GlobalHilbert

structure DirectModelProperties (D : DirectModelData) : Prop where
  beta_measurable : ∀ j, Measurable (fun x => explicitBeta x j)
  beta_positive : ∀ x j, 0 < explicitBeta x j
  forward_coordinates : ∀ x v j, D.Sx x v j = (explicitBeta x (j-1):ℂ)*v (j-1)
  forward_field : ∀ f, D.S f =ᵐ[baseMeasure] fun x => D.Sx x (f x)
  fiber_lattice : ∀ x (L : Submodule ℂ Fiber),
    (IsClosed (L : Set Fiber) ∧ OperatorInvariant L (D.Sx x)) ↔
      L = ⊥ ∨ L = ⊤ ∨ ∃ h : ℤ, L = coordinateTail h
  S_nonzero : D.S ≠ 0
  S_norm : ‖D.S‖ = Real.exp (-10)
  power_bound : ∀ n : ℕ, 1 ≤ n → ‖D.S^n‖ ≤ Real.exp (-10*(((n+1)^2/4:ℕ):ℝ))
  V_contraction : ‖D.V‖ ≤ 1
  commute : D.S * D.V = D.V * D.S
  backward_measurable : ∀ j, Measurable (fun x => D.b x j)
  backward_bounds : ∀ x j, 0 ≤ D.b x j ∧ D.b x j ≤ 1
  backward_coordinates : ∀ x v j, D.Vx x v j = (D.b x (j+1):ℂ)*v (j+1)
  backward_field : ∀ f, ∀ᵐ x ∂baseMeasure, D.V f (odometer x) = D.Vx x (f x)
  common_conull : ∃ Xstar : Set Base, MeasurableSet Xstar ∧ baseMeasure Xstarᶜ = 0 ∧
    odometer ⁻¹' Xstar = Xstar ∧ ∀ x ∈ Xstar,
      (∀ j, 0 < D.b x j) ∧
      (∀ h : ℤ, ((coordinateTail h).map (D.Vx x).toLinearMap).topologicalClosure = coordinateTail (h-1)) ∧
      DenseRange (D.Vx x)
  transitive : AlgebraTransitive (generatedAlgebra D.S D.V)

def forwardFiber (x : Base) : Fiber →L[ℂ] Fiber :=
  fiberWeightedPermutation (Equiv.subRight 1) (fun j => (explicitBeta x j:ℂ))
    (Real.exp (-10)) (Real.exp_pos _).le
    (fun j => by simpa only [Complex.norm_real, Real.norm_of_nonneg (explicitBeta_pos x j).le] using explicitBeta_le x j)
def backwardFiber (x : Base) : Fiber →L[ℂ] Fiber :=
  fiberWeightedPermutation (Equiv.addRight 1) (fun j => (backwardCoeff x j:ℂ)) 1 (by norm_num)
    (fun j => by simpa only [Complex.norm_real, Real.norm_of_nonneg (backwardCoeff_bounds x j).1] using (backwardCoeff_bounds x j).2)
/--
@isnad1 id=eq.0h3v.s11.916552393b96 from=translated src=- shape=673fc28a vocab=241b7d29
-/
@[simp] lemma forwardFiber_apply (x : Base) (v : Fiber) (j : ℤ) :
    forwardFiber x v j = (explicitBeta x (j-1):ℂ) * v (j-1) := rfl
/--
@isnad1 id=eq.0h3v.s11.794704f5983e from=translated src=- shape=673fc28a vocab=e65d5de0
-/
@[simp] lemma backwardFiber_apply (x : Base) (v : Fiber) (j : ℤ) :
    backwardFiber x v j = (backwardCoeff x (j+1):ℂ) * v (j+1) := rfl
/--
@isnad1 id=le.0h1v.s11.b211db6ef640 from=translated src=- shape=88426b10 vocab=b04802e1
-/
lemma forwardFiber_norm_le (x : Base) : ‖forwardFiber x‖ ≤ Real.exp (-10) :=
  fiberWeightedPermutation_norm_le _ _ _ _ _
/--
@isnad1 id=le.0h1v.s11.1bfc36c5ee1a from=translated src=- shape=85b09406 vocab=8d55ffb0
-/
lemma backwardFiber_norm_le (x : Base) : ‖backwardFiber x‖ ≤ 1 :=
  fiberWeightedPermutation_norm_le _ _ _ _ _
/--
@isnad1 id=eq.0h3v.s11.e87824c0ff89 from=translated src=- shape=24f483fb vocab=d9b4351f
-/
lemma forwardFiber_single (x : Base) (j : ℤ) (c : ℂ) :
    forwardFiber x (lp.single 2 j c) = lp.single 2 (j+1) ((explicitBeta x j:ℂ)*c) := by
  ext k
  rw [forwardFiber_apply]
  by_cases hk : k = j+1
  · subst k
    simp
  · have hj : k-1 ≠ j := by omega
    simp only [lp.single_apply_ne _ _ _ hk, lp.single_apply_ne _ _ _ hj, mul_zero]

/--
@isnad1 id=eq.0h1v.s13.fce9ea43919f from=translated src=- shape=251eceb9 vocab=ded694a1
-/
lemma backwardFiber_intertwines (x : Base) :
    forwardFiber (odometer x) * backwardFiber x = backwardFiber x * forwardFiber x := by
  ext v j
  simp only [mul_apply_eq_comp, forwardFiber_apply, backwardFiber_apply,
    sub_add_cancel, add_sub_cancel_right]
  have hc := congrArg (fun r : ℝ => (r:ℂ)) (backwardCoeff_recurrence x j)
  push_cast at hc
  linear_combination -hc * v j

/--
@isnad1 id=le.0h2v.s4.1177402fc437 from=translated src=- shape=9523cf6c vocab=3f1fd6cd
-/
lemma explicitExponent_distance (x : Base) (j : ℤ) :
    10*(coordinateDistance j:ℝ) ≤ explicitExponent x j := by
  cases j with
  | ofNat n =>
    have hd : coordinateDistance (n:ℤ) = (n:ℤ)+1 := by
      unfold coordinateDistance
      omega
    change 10*(coordinateDistance (n:ℤ):ℝ) ≤ halfExponent (plusResidue x) n
    rw [hd]
    simpa only [Int.cast_add, Int.cast_one, Int.cast_natCast] using halfExponent_lower (plusResidue x) n
  | negSucc n =>
    have hd : coordinateDistance (Int.negSucc n) = (n:ℤ)+1 := by
      unfold coordinateDistance
      omega
    rw [hd]
    change _ ≤ halfExponent (minusResidue x) n
    simpa only [Int.cast_add, Int.cast_one, Int.cast_natCast] using halfExponent_lower (minusResidue x) n

/--
@isnad1 id=le.0h3v.s5.772e76854c1b from=translated src=- shape=14e89762 vocab=e9c3cd30
-/
lemma interval_exponent_lower (x : Base) (n : ℕ) (j : ℤ) :
    10*(powerCost n:ℝ) ≤ ∑ r ∈ Finset.range n, explicitExponent x (j+(r:ℤ)) := by
  have hc : (powerCost n:ℝ) ≤ ∑ r ∈ Finset.range n, (coordinateDistance (j+(r:ℤ)):ℝ) := by
    exact_mod_cast sum_coordinateDistance_lower n j
  calc
    _ ≤ 10*(∑ r ∈ Finset.range n, (coordinateDistance (j+(r:ℤ)):ℝ)) := by linarith
    _ = ∑ r ∈ Finset.range n, 10*(coordinateDistance (j+(r:ℤ)):ℝ) := by rw [Finset.mul_sum]
    _ ≤ _ := Finset.sum_le_sum fun _ _ => explicitExponent_distance x _

/--
@isnad1 id=eq.0h4v.s13.ec35112c38e6 from=translated src=- shape=b8877fc6 vocab=719ee0bb
-/
lemma forwardFiber_power_input (x : Base) (n : ℕ) (v : Fiber) (j : ℤ) :
    (forwardFiber x ^ n) v (j+(n:ℤ)) =
      (Real.exp (-(∑ r ∈ Finset.range n, explicitExponent x (j+(r:ℤ)))):ℂ)*v j := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', mul_apply_eq_comp, forwardFiber_apply]
    have hi : j+((n+1:ℕ):ℤ)-1 = j+(n:ℤ) := by omega
    rw [hi, ih, Finset.sum_range_succ]
    change (Real.exp (-explicitExponent x (j+(n:ℤ))):ℂ)*
      ((Real.exp (-(∑ r ∈ Finset.range n, explicitExponent x (j+(r:ℤ)))):ℂ)*v j) = _
    rw [← mul_assoc, ← Complex.ofReal_mul, ← Real.exp_add]
    rw [neg_add_rev]

/--
@isnad1 id=le.0h2v.s13.f50f45795eea from=translated src=- shape=5b96402a vocab=e6447b76
-/
lemma forwardFiber_power_norm (x : Base) (n : ℕ) :
    ‖forwardFiber x ^ n‖ ≤ Real.exp (-10*(powerCost n:ℝ)) := by
  let C := Real.exp (-10*(powerCost n:ℝ))
  have hC : 0 ≤ C := (Real.exp_pos _).le
  apply ContinuousLinearMap.opNorm_le_bound _ (Real.exp_pos _).le
  intro v
  calc
    _ ≤ ‖(C:ℂ) • fiberReindex (Equiv.subRight (n:ℤ)) v‖ := by
      apply lp.norm_mono (by norm_num : (2:ENNReal) ≠ 0)
      intro j
      have hi : j = (j-(n:ℤ))+(n:ℤ) := by omega
      conv_lhs => rw [hi, forwardFiber_power_input]
      simp only [lp.coeFn_smul, Pi.smul_apply, norm_smul, fiberReindex_apply, Equiv.subRight_apply,
        norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le, Real.norm_of_nonneg hC]
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      apply Real.exp_le_exp.mpr
      simpa only [neg_mul] using neg_le_neg (interval_exponent_lower x n (j-(n:ℤ)))
    _ = C*‖v‖ := by
      rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le, (fiberReindex _).norm_map]

/--
@isnad1 id=aestrong.1h1v.s12.01108c46f8e9 from=translated src=- shape=84c4a16b vocab=579ea55b
-/
lemma forwardFiber_aestronglyMeasurable (f : Base → Fiber) (hf : AEStronglyMeasurable f baseMeasure) :
    AEStronglyMeasurable (fun x => forwardFiber x (f x)) baseMeasure := by
  apply weightedPermutation_aestronglyMeasurable
  · exact fun j => Complex.measurable_ofReal.comp (measurable_explicitBeta j)
  · exact hf
/--
@isnad1 id=aestrong.1h1v.s12.3e6ea9f67358 from=translated src=- shape=84c4a16b vocab=bd11ac79
-/
lemma backwardFiber_aestronglyMeasurable (f : Base → Fiber) (hf : AEStronglyMeasurable f baseMeasure) :
    AEStronglyMeasurable (fun x => backwardFiber x (f x)) baseMeasure := by
  apply weightedPermutation_aestronglyMeasurable
  · exact fun j => Complex.measurable_ofReal.comp (measurable_backwardCoeff j)
  · exact hf

def forwardOperator : GlobalHilbert →L[ℂ] GlobalHilbert :=
  fieldOperator forwardFiber (Real.exp (-10)) (Real.exp_pos _).le
    forwardFiber_norm_le forwardFiber_aestronglyMeasurable
/--
@isnad1 id=eventual.0h1v.s17.c932c342e347 from=translated src=- shape=9b255324 vocab=90d6a3d1
-/
lemma forwardOperator_ae (f : GlobalHilbert) :
    forwardOperator f =ᵐ[baseMeasure] fun x => forwardFiber x (f x) :=
  fieldOperator_ae _ _ _ _ _ f
/--
@isnad1 id=le.0h0v.s16.8287abbcbf34 from=translated src=- shape=68fa3aaf vocab=8cb747b7
-/
lemma forwardOperator_norm_le : ‖forwardOperator‖ ≤ Real.exp (-10) :=
  fieldOperator_norm _ _ _ _ _

def inverseOdometer (x : Base) : Base := (show PadicInt 2 from x)-1
/--
@isnad1 id=eq.0h1v.s3.2ee1bc28d54f from=translated src=- shape=47dcad53 vocab=d17d8708
-/
@[simp] lemma inverseOdometer_odometer (x : Base) : inverseOdometer (odometer x) = x := by
  change ((show PadicInt 2 from x)+1)-1 = _
  exact add_sub_cancel_right _ _
/--
@isnad1 id=eq.0h1v.s3.1188645423a9 from=translated src=- shape=47dcad53 vocab=d17d8708
-/
@[simp] lemma odometer_inverseOdometer (x : Base) : odometer (inverseOdometer x) = x := by
  change ((show PadicInt 2 from x)-1)+1 = _
  exact sub_add_cancel _ _
/--
@isnad1 id=measurep.0h0v.s4.e47032e2bdda from=translated src=- shape=359c1e0e vocab=b6e3eb82
-/
lemma inverseOdometer_preserving : MeasurePreserving inverseOdometer baseMeasure baseMeasure := by
  have hh := measurePreserving_completion (α := PadicInt 2) (measurePreserving_add_right baseHaar (-1))
  have he : inverseOdometer = (show Base → Base from fun x : PadicInt 2 => x + (-1)) := by
    funext x
    exact @sub_eq_add_neg (PadicInt 2) _ (show PadicInt 2 from x) 1
  rw [he]
  exact hh

def odometerMeasurableEquiv : Base ≃ᵐ Base where
  toFun := odometer
  invFun := inverseOdometer
  left_inv := inverseOdometer_odometer
  right_inv := odometer_inverseOdometer
  measurable_toFun := odometer_ergodic.measurable
  measurable_invFun := inverseOdometer_preserving.measurable

def backwardFieldOperator : GlobalHilbert →L[ℂ] GlobalHilbert :=
  fieldOperator backwardFiber 1 (by norm_num) backwardFiber_norm_le backwardFiber_aestronglyMeasurable

def backwardOperator : GlobalHilbert →L[ℂ] GlobalHilbert :=
  (Lp.compMeasurePreservingₗᵢ ℂ inverseOdometer inverseOdometer_preserving).toContinuousLinearMap.comp backwardFieldOperator

/--
@isnad1 id=eventual.0h1v.s17.751f4a9e86b4 from=translated src=- shape=ac4a3550 vocab=a3ddda5e
-/
lemma backwardOperator_ae_inverse (f : GlobalHilbert) :
    backwardOperator f =ᵐ[baseMeasure] fun x => backwardFiber (inverseOdometer x) (f (inverseOdometer x)) := by
  have h₁ := Lp.coeFn_compMeasurePreserving (backwardFieldOperator f) inverseOdometer_preserving
  have h₂ := (fieldOperator_ae backwardFiber 1 (by norm_num) backwardFiber_norm_le
    backwardFiber_aestronglyMeasurable f).comp_tendsto inverseOdometer_preserving.quasiMeasurePreserving.tendsto_ae
  exact h₁.trans h₂

/--
@isnad1 id=eq.0h0v.s19.aa0b0c2ce9dc from=translated src=- shape=98813381 vocab=f9547070
-/
lemma forward_backward_commute : forwardOperator * backwardOperator = backwardOperator * forwardOperator := by
  ext1 f
  apply Lp.ext
  filter_upwards [forwardOperator_ae (backwardOperator f), backwardOperator_ae_inverse f,
    backwardOperator_ae_inverse (forwardOperator f),
    (forwardOperator_ae f).comp_tendsto inverseOdometer_preserving.quasiMeasurePreserving.tendsto_ae] with x h₁ h₂ h₃ h₄
  change forwardOperator (backwardOperator f) x = backwardOperator (forwardOperator f) x
  rw [h₁,h₂,h₃]

  dsimp only [Function.comp_def] at h₄
  rw [h₄]
  have hh := congrArg (fun A : Fiber →L[ℂ] Fiber => A (f (inverseOdometer x))) (backwardFiber_intertwines (inverseOdometer x))
  simpa only [mul_apply_eq_comp, odometer_inverseOdometer] using hh

/--
@isnad1 id=eq.0h1v.s19.b5c62efa482f from=translated src=- shape=c9814651 vocab=cf4e40d2
-/
lemma forward_scalar_commute (g : Lp ℂ ∞ baseMeasure) :
    forwardOperator * scalarMultiplier g = scalarMultiplier g * forwardOperator := by
  ext1 f
  apply Lp.ext
  filter_upwards [forwardOperator_ae (scalarMultiplier g f), scalarMultiplier_ae g f,
    scalarMultiplier_ae g (forwardOperator f), forwardOperator_ae f] with x h₁ h₂ h₃ h₄
  change forwardOperator (scalarMultiplier g f) x = scalarMultiplier g (forwardOperator f) x
  simp only [h₁,h₂,h₃,h₄,map_smul]

def constantBasis (j : ℤ) : GlobalHilbert := Lp.const 2 baseMeasure (lp.single 2 j (1:ℂ))
/--
@isnad1 id=eq.0h1v.s12.71a66fbea11f from=translated src=- shape=86b685fa vocab=d7d25cda
-/
lemma constantBasis_norm (j : ℤ) : ‖constantBasis j‖ = 1 := by
  rw [constantBasis, Lp.norm_const 2 baseMeasure _ (by norm_num), lp.norm_single (by norm_num : (0:ENNReal)<2)]
  simp
/--
@isnad1 id=eventual.0h1v.s12.734c9617c8df from=translated src=- shape=ed869286 vocab=f28b7ca9
-/
lemma constantBasis_ae (j : ℤ) : constantBasis j =ᵐ[baseMeasure] fun _ => lp.single 2 j (1:ℂ) :=
  Lp.coeFn_const _ _ _
/--
@isnad1 id=eq.0h0v.s18.b3023f79db65 from=translated src=- shape=2f458983 vocab=3d119070
-/
lemma forwardOperator_constantBasis_zero :
    forwardOperator (constantBasis 0) = (Real.exp (-10):ℂ) • constantBasis 1 := by
  apply Lp.ext
  filter_upwards [forwardOperator_ae (constantBasis 0), constantBasis_ae 0, constantBasis_ae 1,
    Lp.coeFn_smul (Real.exp (-10):ℂ) (constantBasis 1)] with x h₁ h₂ h₃ h₄
  rw [h₁,h₂,h₄,Pi.smul_apply,h₃,forwardFiber_single,explicitBeta_zero,mul_one]
  rw [← lp.single_smul]
  simp
/--
@isnad1 id=eq.0h0v.s16.ddaa8c902d78 from=translated src=- shape=68fa3aaf vocab=a568c535
-/
lemma forwardOperator_norm : ‖forwardOperator‖ = Real.exp (-10) := by
  apply le_antisymm forwardOperator_norm_le
  have h := forwardOperator.le_opNorm (constantBasis 0)
  rw [forwardOperator_constantBasis_zero, norm_smul, constantBasis_norm, constantBasis_norm,
    mul_one, mul_one, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le] at h
  exact h
/--
@isnad1 id=ne.0h0v.s18.c1e851444f05 from=translated src=- shape=6f78b769 vocab=f762fd62
-/
lemma forwardOperator_ne_zero : forwardOperator ≠ 0 := by
  intro h
  have hh := forwardOperator_norm
  rw [h, norm_zero] at hh
  exact (Real.exp_ne_zero (-10)) hh.symm

/--
@isnad1 id=eventual.0h2v.s19.162f8a4cc894 from=translated src=- shape=18ac1c38 vocab=f5f03d83
-/
lemma forwardOperator_power_ae (n : ℕ) (f : GlobalHilbert) :
    (forwardOperator^n) f =ᵐ[baseMeasure] fun x => (forwardFiber x ^ n) (f x) := by
  induction n with
  | zero => filter_upwards [] with x; rfl
  | succ n ih =>
    rw [pow_succ', mul_apply_eq_comp]
    filter_upwards [forwardOperator_ae ((forwardOperator^n) f), ih] with x h₁ h₂
    simp only [h₁,h₂,pow_succ',mul_apply_eq_comp]
/--
@isnad1 id=le.0h1v.s19.995dc99e4969 from=translated src=- shape=3553e7c7 vocab=a1ae8b6d
-/
lemma forwardOperator_power_norm (n : ℕ) :
    ‖forwardOperator^n‖ ≤ Real.exp (-10*(powerCost n:ℝ)) := by
  let C := Real.exp (-10*(powerCost n:ℝ))
  have hC : 0 ≤ C := (Real.exp_pos _).le
  apply ContinuousLinearMap.opNorm_le_bound _ hC
  intro f
  calc
    _ ≤ ‖(C:ℂ) • f‖ := by
      apply Lp.norm_le_norm_of_ae_le
      filter_upwards [forwardOperator_power_ae n f, Lp.coeFn_smul (C:ℂ) f] with x h₁ h₂
      rw [h₁,h₂,Pi.smul_apply,norm_smul,Complex.norm_real,Real.norm_of_nonneg hC]
      exact (forwardFiber x ^ n).le_opNorm (f x) |>.trans
        (mul_le_mul_of_nonneg_right (forwardFiber_power_norm x n) (norm_nonneg _))
    _ = C*‖f‖ := by rw [norm_smul,Complex.norm_real,Real.norm_of_nonneg hC]

end
end BackwardIntertwiners

end OAI
