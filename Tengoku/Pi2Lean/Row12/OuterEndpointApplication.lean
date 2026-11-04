import Tengoku.Pi2Lean.Row12.OuterPrimitive
import Tengoku.Seed.Analysis.Complex.RealDeriv

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms Row12.outer_primitive_flux_zero` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Row12.outer_primitive_flux_continuousAt_zero` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Row12.outer_primitive_flux_tendsto_zero` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Row12.outer_endpoint_coefficient3_one` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Row12.outer_endpoint_tail_majorant_summable` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Row12.outer_endpoint_tail_radius` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Row12.outer_endpoint_tail_series_sum` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Row12.outer_endpoint_tail_analyticAt_zero` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Row12.squared_native_euler_two_term` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Row12.outer_endpoint_state0_inverse` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Row12.outer_endpoint_state1_inverse` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Row12.sixth_state_two_term` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Row12.sixth_normal_state_two_term` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Row12.sixth_normal_state_lambda_expansion` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Row12.outer_endpoint_lambda_tendsto_zero` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Row12.outer_endpoint_remainder_continuousAt_zero` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Row12.outer_endpoint_row_decomposition` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Row12.outer_endpoint_regular_basis_continuousAt_zero` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Row12.outer_endpoint_regular_row_continuousAt_zero` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Row12.outer_endpoint_pole_rows` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Row12.outer_endpoint_regular_zero` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Row12.outer_endpoint_map_dot` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Row12.outer_endpoint_pole_cancellations` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Row12.outer_endpoint_scaled_row_eq` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Row12.outer_endpoint_scaled_row_continuousAt_zero` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Row12.outer_endpoint_scaled_row_zero` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Row12.outer_endpoint_row_dot_decomposition` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Row12.outer_endpoint_jet_pairing` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Row12.outer_endpoint_actual_pairing_eq` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Row12.outer_endpoint_regular_dot_continuousAt_zero` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Row12.outer_endpoint_remainder_pair_continuousAt_zero` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Row12.outer_endpoint_regularized_pair_continuousAt_zero` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Row12.outer_endpoint_regularized_pair_zero` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Row12.outer_endpoint_scaled_row_tendsto_zero` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Row12.outer_endpoint_path_tendsto_zero` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Row12.outer_primitive_flux_upperEndpoint` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Row12.outer_primitive_flux_tendsto_zero_right` (it only prints; the queue checks the axioms of every declaration). -/

open Filter Matrix
open scoped ENNReal NNReal

namespace Row12

/--
@isnad1 id=eq.0h0v.s3.650e454385b2 from=translated src=- shape=3c26ae4f vocab=09c8db24
-/
theorem outer_primitive_flux_zero : outerPrimitiveFlux 0 = 0 := by
  simp [outerPrimitiveFlux]

/--
@isnad1 id=continuo.0h0v.s5.ccfed344bb3a from=translated src=- shape=5446e38f vocab=2558936f
-/
theorem outer_primitive_flux_continuousAt_zero : ContinuousAt outerPrimitiveFlux 0 := by
  apply (outer_primitive_flux_hasDerivAt 0 (by norm_num) (by norm_num) ?_).continuousAt
  norm_num [outerPrimitiveLambda,norm_div]

/--
@isnad1 id=tendsto.0h0v.s5.8b9747ce6be7 from=translated src=- shape=c9bb50cf vocab=294cf310
-/
theorem outer_primitive_flux_tendsto_zero :
    Tendsto (fun U : ℝ => outerPrimitiveFlux (U : ℂ)) (nhds 0) (nhds 0) := by
  have ho : Tendsto (fun U : ℝ => (U : ℂ)) (nhds 0) (nhds 0) :=
    Complex.continuous_ofReal.continuousAt (x := (0 : ℝ))
  have hc := outer_primitive_flux_continuousAt_zero.tendsto.comp ho
  simpa only [Function.comp_def,Complex.ofReal_zero,outer_primitive_flux_zero] using hc

/--
@isnad1 id=eq.0h0v.s5.dd8c6e0b3495 from=translated src=- shape=4683683d vocab=f5564a90
-/
theorem outer_endpoint_coefficient3_one : coefficient3 1 = 5/72 := by
  norm_num [coefficient3,Nat.factorial]

noncomputable def outerEndpointTail (k : ℕ) (q : ℂ) : ℂ :=
  ∑' n : ℕ, (coefficient3 (n+2) : ℂ)^2*((n+2 : ℕ) : ℂ)^k*q^n

noncomputable def outerEndpointTailSeries (k : ℕ) : FormalMultilinearSeries ℂ ℂ ℂ :=
  FormalMultilinearSeries.ofScalars ℂ
    (fun n => (coefficient3 (n+2) : ℂ)^2*((n+2 : ℕ) : ℂ)^k)

/--
@isnad1 id=summable.0h1v.s6.c54d8ed99298 from=translated src=- shape=9e4946f9 vocab=cb1f9b7c
-/
theorem outer_endpoint_tail_majorant_summable (k : ℕ) :
    Summable (fun n : ℕ => ((n+2 : ℕ) : ℝ)^k*(1/2 : ℝ)^n) := by
  have hs := summable_pow_mul_geometric_of_norm_lt_one k
    (r := (1/2 : ℝ)) (by norm_num)
  have ht := (summable_nat_add_iff 2).2 hs
  have hb := ht.mul_left (4 : ℝ)
  apply hb.congr
  intro n
  simp only [pow_add]
  norm_num
  ring

/--
@isnad1 id=le.0h1v.s5.ba193f685428 from=translated src=- shape=474f00f4 vocab=ffb3e09a
-/
theorem outer_endpoint_tail_radius (k : ℕ) :
    (1/2 : ℝ≥0∞) ≤ (outerEndpointTailSeries k).radius := by
  have hr : (↑(1/2 : ℝ≥0) : ℝ≥0∞) ≤ (outerEndpointTailSeries k).radius := by
    apply (outerEndpointTailSeries k).le_radius_of_summable (r := (1/2 : ℝ≥0))
    apply (outer_endpoint_tail_majorant_summable k).of_norm_bounded
    intro n
    rw [Real.norm_eq_abs,abs_of_nonneg (by positivity)]
    simp only [outerEndpointTailSeries,FormalMultilinearSeries.ofScalars_norm,
      norm_mul,norm_pow,Complex.norm_of_nonneg (coefficient3_nonneg (n+2)),
      RCLike.norm_natCast,NNReal.coe_div,NNReal.coe_one]
    calc
      coefficient3 (n+2)^2*((n+2 : ℕ) : ℝ)^k*(1/2 : ℝ)^n ≤
          1*((n+2 : ℕ) : ℝ)^k*(1/2 : ℝ)^n := by
        gcongr
        exact coefficient3_sq_le_one (n+2)
      _ = _ := by ring
  simpa only [ENNReal.coe_div',ENNReal.coe_one,ENNReal.coe_ofNat] using hr

/--
@isnad1 id=eq.0h1v.s5.481cba9f8df3 from=translated src=- shape=d520654d vocab=67875318
-/
theorem outer_endpoint_tail_series_sum (k : ℕ) :
    (outerEndpointTailSeries k).sum = outerEndpointTail k := by
  funext q
  unfold outerEndpointTail
  apply tsum_congr
  intro n
  simp [outerEndpointTailSeries,smul_eq_mul,mul_comm]

/--
@isnad1 id=analytic.0h1v.s5.ea89e07bac5f from=translated src=- shape=7d7cbb3d vocab=28465fa1
-/
theorem outer_endpoint_tail_analyticAt_zero (k : ℕ) :
    AnalyticAt ℂ (outerEndpointTail k) 0 := by
  have hp : 0 < (outerEndpointTailSeries k).radius :=
    lt_of_lt_of_le (by norm_num) (outer_endpoint_tail_radius k)
  have ha := ((outerEndpointTailSeries k).hasFPowerSeriesOnBall hp).analyticAt_of_mem
    (show (0 : ℂ) ∈ Metric.eball 0 (outerEndpointTailSeries k).radius by simpa using hp)
  rw [outer_endpoint_tail_series_sum] at ha
  exact ha

/--
@isnad1 id=eq.1h2v.s6.1b9e22c0f099 from=translated src=- shape=f273e928 vocab=2f9ddc39
-/
theorem squared_native_euler_two_term (k : ℕ) (q : ℂ) (hq : ‖q‖ < 1) :
    squaredNativeEuler k q = (0 : ℂ)^k+(25/5184 : ℂ)*q+q^2*outerEndpointTail k q := by
  have hs := squaredNativeEuler_summable k q hq
  have he := hs.sum_add_tsum_nat_add 2
  have ht : (∑' n : ℕ, (coefficient3 (n+2) : ℂ)^2*((n+2 : ℕ) : ℂ)^k*q^(n+2)) =
      q^2*outerEndpointTail k q := by
    rw [outerEndpointTail,← tsum_mul_left]
    apply tsum_congr
    intro n
    rw [pow_add]
    ring
  rw [ht] at he
  have hp : (5/72 : ℂ)^2 = 25/5184 := by norm_num
  simpa [Finset.sum_range_succ,coefficient3_zero,outer_endpoint_coefficient3_one,
    squaredNativeEuler,hp] using he.symm

noncomputable def outerEndpointV0Complex : Fin 6 → ℂ :=
  fun i => (outerEndpointV0 i : ℂ)

noncomputable def outerEndpointV1Complex : Fin 6 → ℂ :=
  fun i => (outerEndpointV1 i : ℂ)

noncomputable def outerEndpointStateZero : Fin 6 → ℂ := ![1,0,0,0,0,0]

noncomputable def outerEndpointRemainder (x : ℂ) (j : Fin 6) : ℂ :=
  (729/15625 : ℂ)^2*(sixthCyclicInverse.mulVec
    (fun i => outerEndpointTail i.val (outerPrimitiveLambda x))) j

/--
@isnad1 id=eq.0h0v.s5.b27af8849885 from=translated src=- shape=6595ee65 vocab=2412cf8b
-/
theorem outer_endpoint_state0_inverse :
    sixthCyclicInverse.mulVec outerEndpointStateZero = outerEndpointV0Complex := by
  ext i
  fin_cases i <;> norm_num [sixthCyclicInverse,outerEndpointStateZero,outerEndpointV0Complex,
    outerEndpointV0,Matrix.mulVec,dotProduct,Fin.sum_univ_succ,Matrix.of_apply,
    Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,Matrix.head_cons,Matrix.tail_cons]

/--
@isnad1 id=eq.0h0v.s5.94bf872fe2b2 from=translated src=- shape=98c7ad63 vocab=2f595316
-/
theorem outer_endpoint_state1_inverse :
    sixthCyclicInverse.mulVec (fun _ => 1) = outerEndpointV1Complex := by
  ext i
  fin_cases i <;> norm_num [sixthCyclicInverse,outerEndpointV1Complex,
    outerEndpointV1,Matrix.mulVec,dotProduct,Fin.sum_univ_succ,Matrix.of_apply,
    Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,Matrix.head_cons,Matrix.tail_cons]

/--
@isnad1 id=eq.1h1v.s6.66ffc3b5c870 from=translated src=- shape=96cb0c47 vocab=9520edb5
-/
theorem sixth_state_two_term (q : ℂ) (hq : ‖q‖ < 1) :
    sixthState q = fun i => outerEndpointStateZero i+(25/5184 : ℂ)*q+
      q^2*outerEndpointTail i.val q := by
  ext i
  have he := squared_native_euler_two_term i.val q hq
  fin_cases i <;> simpa [sixthState,outerEndpointStateZero,
    Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
    Matrix.cons_val_succ',Matrix.head_cons,Matrix.tail_cons] using he

/--
@isnad1 id=eq.1h2v.s7.ecd8902312d0 from=translated src=- shape=09b7ffcf vocab=0a4c5b32
-/
theorem sixth_normal_state_two_term (q : ℂ) (hq : ‖q‖ < 1) (j : Fin 6) :
    sixthNormalState q j = outerEndpointV0Complex j+
      (25/5184 : ℂ)*q*outerEndpointV1Complex j+
      q^2*(sixthCyclicInverse.mulVec (fun i => outerEndpointTail i.val q)) j := by
  unfold sixthNormalState
  rw [sixth_state_two_term q hq]
  calc
    _ = (sixthCyclicInverse.mulVec outerEndpointStateZero) j+
        (25/5184 : ℂ)*q*(sixthCyclicInverse.mulVec (fun _ => 1)) j+
        q^2*(sixthCyclicInverse.mulVec (fun i => outerEndpointTail i.val q)) j := by
      simp only [Matrix.mulVec,dotProduct,Fin.sum_univ_succ]
      ring
    _ = _ := by rw [outer_endpoint_state0_inverse,outer_endpoint_state1_inverse]

/--
@isnad1 id=eq.1h2v.s7.2bbb487a6222 from=translated src=- shape=f325d71b vocab=68b6dc63
-/
theorem sixth_normal_state_lambda_expansion (x : ℂ)
    (hx : ‖outerPrimitiveLambda x‖ < 1) (j : Fin 6) :
    sixthNormalState (outerPrimitiveLambda x) j =
      outerEndpointV0Complex j+(9/40000 : ℂ)*x^3*outerEndpointV1Complex j+
        x^6*outerEndpointRemainder x j := by
  rw [sixth_normal_state_two_term _ hx j]
  unfold outerEndpointRemainder outerPrimitiveLambda
  norm_num
  ring

/--
@isnad1 id=tendsto.0h0v.s5.e9fdb525fed2 from=translated src=- shape=1ec14745 vocab=c4335854
-/
theorem outer_endpoint_lambda_tendsto_zero :
    Tendsto outerPrimitiveLambda (nhds (0 : ℂ)) (nhds 0) := by
  have hc : ContinuousAt outerPrimitiveLambda 0 := by
    unfold outerPrimitiveLambda
    fun_prop
  simpa [outerPrimitiveLambda] using hc.tendsto

/--
@isnad1 id=continuo.0h1v.s5.61db4065438f from=translated src=- shape=f7197d8f vocab=80e595f1
-/
theorem outer_endpoint_remainder_continuousAt_zero (j : Fin 6) :
    ContinuousAt (fun x => outerEndpointRemainder x j) 0 := by
  have ht (i : Fin 6) : Tendsto (fun x => outerEndpointTail i.val (outerPrimitiveLambda x))
      (nhds (0 : ℂ)) (nhds (outerEndpointTail i.val 0)) := by
    simpa only [Function.comp_def] using
      (outer_endpoint_tail_analyticAt_zero i.val).continuousAt.tendsto.comp
        outer_endpoint_lambda_tendsto_zero
  have hs := tendsto_finsetSum (Finset.univ : Finset (Fin 6))
    (fun i _ => tendsto_const_nhds.mul (ht i) (a := sixthCyclicInverse j i))
  have hr := tendsto_const_nhds.mul hs (a := (729/15625 : ℂ)^2)
  change Tendsto (fun x => outerEndpointRemainder x j) (nhds (0 : ℂ))
    (nhds (outerEndpointRemainder 0 j))
  simpa only [outerEndpointRemainder,Matrix.mulVec,dotProduct,
    outerPrimitiveLambda,mul_zero,zero_pow (by norm_num : (3 : ℕ) ≠ 0)] using hr

noncomputable def outerEndpointPoleRow (k : Fin 4) : Fin 6 → ℂ :=
  outerPrimitiveCoefficients ⟨k.val, by omega⟩

noncomputable def outerEndpointRegularBasis (x : ℂ) : Fin 11 → ℂ :=
  ![1/(99*x-50),1/(99*x-50)^2,1,x,x^2,x^3,x^4,x^5,x^6,x^7,x^8]

noncomputable def outerEndpointRegularRow (x : ℂ) (j : Fin 6) : ℂ :=
  ∑ k : Fin 11, outerPrimitiveCoefficients ⟨k.val+4, by omega⟩ j*
    outerEndpointRegularBasis x k

/--
@isnad1 id=eq.0h2v.s7.3044392f8970 from=translated src=- shape=06d0e0f3 vocab=df42b7ee
-/
theorem outer_endpoint_row_decomposition (x : ℂ) (j : Fin 6) :
    outerPrimitiveRow x j = outerEndpointPoleRow 0 j/x+
      outerEndpointPoleRow 1 j/x^2+outerEndpointPoleRow 2 j/x^3+
      outerEndpointPoleRow 3 j/x^4+outerEndpointRegularRow x j := by
  fin_cases j <;> norm_num [outerPrimitiveRow,outerPrimitiveBasis,outerEndpointPoleRow,
    outerEndpointRegularRow,outerEndpointRegularBasis,Fin.sum_univ_succ,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
    Matrix.cons_val_three,Matrix.cons_val_four,Matrix.cons_val_succ,
    Matrix.cons_val_succ',Matrix.head_cons,Matrix.tail_cons,Fin.sum_univ_zero,
    outerPrimitiveCoefficients,Matrix.of_apply] <;> ring

/--
@isnad1 id=continuo.0h1v.s5.53c70552fb24 from=translated src=- shape=f7197d8f vocab=7aa42324
-/
theorem outer_endpoint_regular_basis_continuousAt_zero (k : Fin 11) :
    ContinuousAt (fun x => outerEndpointRegularBasis x k) 0 := by
  fin_cases k
  all_goals norm_num only [outerEndpointRegularBasis,Matrix.cons_val_zero,
    Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
    Matrix.cons_val_succ,Matrix.cons_val_succ',Matrix.head_cons,Matrix.tail_cons]
  all_goals fun_prop (disch := norm_num)

/--
@isnad1 id=continuo.0h1v.s5.d276228010ed from=translated src=- shape=f7197d8f vocab=47f491ef
-/
theorem outer_endpoint_regular_row_continuousAt_zero (j : Fin 6) :
    ContinuousAt (fun x => outerEndpointRegularRow x j) 0 := by
  change Tendsto (fun x => outerEndpointRegularRow x j) (nhds (0 : ℂ))
    (nhds (outerEndpointRegularRow 0 j))
  exact tendsto_finsetSum (Finset.univ : Finset (Fin 11))
    (fun k _ => tendsto_const_nhds.mul
      (outer_endpoint_regular_basis_continuousAt_zero k).tendsto
      (a := outerPrimitiveCoefficients ⟨k.val+4, by omega⟩ j))

/--
@isnad1 id=and.0h0v.s7.7c09a2605936 from=translated src=- shape=c38c1cb9 vocab=82594120
-/
theorem outer_endpoint_pole_rows :
    outerEndpointPoleRow 0 = (fun i => (outerXiNegOne i : ℂ)) ∧
    outerEndpointPoleRow 1 = (fun i => (outerXiNegTwo i : ℂ)) ∧
    outerEndpointPoleRow 2 = (fun i => (outerXiNegThree i : ℂ)) ∧
    outerEndpointPoleRow 3 = (fun i => (outerXiNegFour i : ℂ)) := by
  refine ⟨?_,?_,?_,?_⟩
  all_goals ext i
  all_goals fin_cases i <;> norm_num [outerEndpointPoleRow,outerPrimitiveCoefficients,
    outerXiNegOne,outerXiNegTwo,outerXiNegThree,outerXiNegFour,Matrix.of_apply,
    Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,Matrix.cons_val_succ',
    Matrix.head_cons,Matrix.tail_cons]

/--
@isnad1 id=eq.0h0v.s4.ea310216ba54 from=translated src=- shape=f6ac09c5 vocab=35ed7851
-/
theorem outer_endpoint_regular_zero :
    outerEndpointRegularRow 0 = fun i => (outerXiZero i : ℂ) := by
  ext i
  fin_cases i <;> norm_num [outerEndpointRegularRow,outerEndpointRegularBasis,
    outerPrimitiveCoefficients,outerXiZero,outerEscapeOne,outerEscapeTwo,
    outerPolynomialZero,Fin.sum_univ_succ,Matrix.of_apply,Matrix.cons_val_two,
    Matrix.cons_val_three,Matrix.cons_val_four,Matrix.cons_val_succ',
    Matrix.head_cons,Matrix.tail_cons]

/--
@isnad1 id=eq.0h2v.s6.0ef269914af8 from=translated src=- shape=e762932d vocab=3a48612c
-/
theorem outer_endpoint_map_dot (v w : Fin 6 → ℚ) :
    dotProduct (fun i => (v i : ℂ)) (fun i => (w i : ℂ)) = (↑(dotProduct v w : ℚ) : ℂ) := by
  simp only [dotProduct,Fin.sum_univ_succ,Fin.sum_univ_zero]
  push_cast
  rfl

/--
@isnad1 id=and.0h0v.s8.b1c29500df64 from=translated src=- shape=77e20b37 vocab=f0245a64
-/
theorem outer_endpoint_pole_cancellations :
    dotProduct (outerEndpointPoleRow 3) outerEndpointV0Complex = 0 ∧
    dotProduct (outerEndpointPoleRow 2) outerEndpointV0Complex = 0 ∧
    dotProduct (outerEndpointPoleRow 1) outerEndpointV0Complex = 0 ∧
    dotProduct (outerEndpointPoleRow 0) outerEndpointV0Complex+
      (9/40000 : ℂ)*dotProduct (outerEndpointPoleRow 3) outerEndpointV1Complex = 0 ∧
    dotProduct (outerEndpointRegularRow 0) outerEndpointV0Complex+
      (9/40000 : ℂ)*dotProduct (outerEndpointPoleRow 2) outerEndpointV1Complex = 0 := by
  rcases outer_endpoint_pole_rows with ⟨h0,h1,h2,h3⟩
  rw [h0,h1,h2,h3,outer_endpoint_regular_zero]
  unfold outerEndpointV0Complex outerEndpointV1Complex
  simp only [outer_endpoint_map_dot]
  refine ⟨?_,?_,?_,?_,?_⟩
  · exact_mod_cast outer_xi_neg_four_v0
  · exact_mod_cast outer_xi_neg_three_v0
  · exact_mod_cast outer_xi_neg_two_v0
  · have he := congrArg (fun r : ℚ => (r : ℂ)) outer_pole_one_cancellation
    norm_num at he
    exact he
  · have he := congrArg (fun r : ℚ => (r : ℂ)) outer_zero_cancellation
    norm_num at he
    exact he

noncomputable def outerEndpointScaledRow (x : ℂ) (j : Fin 6) : ℂ :=
  outerEndpointPoleRow 0 j*x^4+outerEndpointPoleRow 1 j*x^3+
    outerEndpointPoleRow 2 j*x^2+outerEndpointPoleRow 3 j*x+
      x^5*outerEndpointRegularRow x j

/--
@isnad1 id=eq.1h2v.s5.e9874ee269ac from=translated src=- shape=f29972e9 vocab=dbaab07d
-/
theorem outer_endpoint_scaled_row_eq (x : ℂ) (hx : x ≠ 0) (j : Fin 6) :
    x^5*outerPrimitiveRow x j = outerEndpointScaledRow x j := by
  rw [outer_endpoint_row_decomposition]
  unfold outerEndpointScaledRow
  field_simp [hx]

/--
@isnad1 id=continuo.0h1v.s5.66a68ca66884 from=translated src=- shape=f7197d8f vocab=078461a7
-/
theorem outer_endpoint_scaled_row_continuousAt_zero (j : Fin 6) :
    ContinuousAt (fun x => outerEndpointScaledRow x j) 0 := by
  have hr := outer_endpoint_regular_row_continuousAt_zero j
  unfold outerEndpointScaledRow
  fun_prop

/--
@isnad1 id=eq.0h1v.s4.7465a799fffa from=translated src=- shape=60b34eea vocab=81c38e11
-/
theorem outer_endpoint_scaled_row_zero (j : Fin 6) : outerEndpointScaledRow 0 j = 0 := by
  simp [outerEndpointScaledRow]
/--
@isnad1 id=eq.0h2v.s8.16f9e913153e from=translated src=- shape=ce31ffc9 vocab=178baee4
-/
theorem outer_endpoint_row_dot_decomposition (x : ℂ) (v : Fin 6 → ℂ) :
    dotProduct (outerPrimitiveRow x) v = dotProduct (outerEndpointPoleRow 0) v/x+
      dotProduct (outerEndpointPoleRow 1) v/x^2+
      dotProduct (outerEndpointPoleRow 2) v/x^3+
      dotProduct (outerEndpointPoleRow 3) v/x^4+dotProduct (outerEndpointRegularRow x) v := by
  simp only [dotProduct]
  simp_rw [outer_endpoint_row_decomposition]
  simp only [add_mul,div_mul_eq_mul_div,Finset.sum_add_distrib,Finset.sum_div]

/--
@isnad1 id=eq.1h1v.s8.13b6881e6b44 from=translated src=- shape=13204e4d vocab=916f3815
-/
theorem outer_endpoint_jet_pairing (x : ℂ) (hx : x ≠ 0) :
    dotProduct (outerPrimitiveRow x) outerEndpointV0Complex+
        (9/40000 : ℂ)*x^3*dotProduct (outerPrimitiveRow x) outerEndpointV1Complex =
      (dotProduct (outerEndpointRegularRow x) outerEndpointV0Complex-
        dotProduct (outerEndpointRegularRow 0) outerEndpointV0Complex)+
      (9/40000 : ℂ)*x*dotProduct (outerEndpointPoleRow 1) outerEndpointV1Complex+
      (9/40000 : ℂ)*x^2*dotProduct (outerEndpointPoleRow 0) outerEndpointV1Complex+
      (9/40000 : ℂ)*x^3*dotProduct (outerEndpointRegularRow x) outerEndpointV1Complex := by
  rcases outer_endpoint_pole_cancellations with ⟨h3,h2,h1,hp,hz⟩
  have hp' : dotProduct (outerEndpointPoleRow 0) outerEndpointV0Complex =
      -(9/40000 : ℂ)*dotProduct (outerEndpointPoleRow 3) outerEndpointV1Complex := by
    linear_combination hp
  have hz' : dotProduct (outerEndpointRegularRow 0) outerEndpointV0Complex =
      -(9/40000 : ℂ)*dotProduct (outerEndpointPoleRow 2) outerEndpointV1Complex := by
    linear_combination hz
  rw [outer_endpoint_row_dot_decomposition,outer_endpoint_row_dot_decomposition,
    h3,h2,h1,hp',hz']
  field_simp [hx]
  ring

noncomputable def outerEndpointRegularizedPair (x : ℂ) : ℂ :=
  (dotProduct (outerEndpointRegularRow x) outerEndpointV0Complex-
    dotProduct (outerEndpointRegularRow 0) outerEndpointV0Complex)+
  (9/40000 : ℂ)*x*dotProduct (outerEndpointPoleRow 1) outerEndpointV1Complex+
  (9/40000 : ℂ)*x^2*dotProduct (outerEndpointPoleRow 0) outerEndpointV1Complex+
  (9/40000 : ℂ)*x^3*dotProduct (outerEndpointRegularRow x) outerEndpointV1Complex+
  x*dotProduct (outerEndpointScaledRow x) (outerEndpointRemainder x)

/--
@isnad1 id=eq.2h1v.s5.f40a46314d9d from=translated src=- shape=563e2204 vocab=d4768137
-/
theorem outer_endpoint_actual_pairing_eq (x : ℂ) (hx : x ≠ 0)
    (hL : ‖outerPrimitiveLambda x‖ < 1) :
    dotProduct (outerPrimitiveRow x) (sixthNormalState (outerPrimitiveLambda x)) =
      outerEndpointRegularizedPair x := by
  have he : dotProduct (outerPrimitiveRow x) (sixthNormalState (outerPrimitiveLambda x)) =
      dotProduct (outerPrimitiveRow x) outerEndpointV0Complex+
      (9/40000 : ℂ)*x^3*dotProduct (outerPrimitiveRow x) outerEndpointV1Complex+
      x*dotProduct (outerEndpointScaledRow x) (outerEndpointRemainder x) := by
    simp only [dotProduct]
    simp_rw [sixth_normal_state_lambda_expansion x hL]
    simp only [mul_add,Finset.sum_add_distrib]
    congr 1
    · rw [Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro j _
      ring
    · rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [← outer_endpoint_scaled_row_eq x hx j]
      ring
  rw [he,outer_endpoint_jet_pairing x hx]
  rfl

/--
@isnad1 id=continuo.0h1v.s6.8e80fad48372 from=translated src=- shape=2129486a vocab=0d8e27fc
-/
theorem outer_endpoint_regular_dot_continuousAt_zero (v : Fin 6 → ℂ) :
    ContinuousAt (fun x => dotProduct (outerEndpointRegularRow x) v) 0 := by
  change Tendsto (fun x => dotProduct (outerEndpointRegularRow x) v) (nhds (0 : ℂ))
    (nhds (dotProduct (outerEndpointRegularRow 0) v))
  exact tendsto_finsetSum (Finset.univ : Finset (Fin 6))
    (fun j _ => (outer_endpoint_regular_row_continuousAt_zero j).tendsto.mul
      (tendsto_const_nhds (x := v j)))

/--
@isnad1 id=continuo.0h0v.s5.21591d59d0a8 from=translated src=- shape=7ed758d4 vocab=3d1456b0
-/
theorem outer_endpoint_remainder_pair_continuousAt_zero :
    ContinuousAt (fun x => dotProduct (outerEndpointScaledRow x) (outerEndpointRemainder x)) 0 := by
  change Tendsto (fun x => dotProduct (outerEndpointScaledRow x) (outerEndpointRemainder x))
    (nhds (0 : ℂ))
    (nhds (dotProduct (outerEndpointScaledRow 0) (outerEndpointRemainder 0)))
  exact tendsto_finsetSum (Finset.univ : Finset (Fin 6))
    (fun j _ => (outer_endpoint_scaled_row_continuousAt_zero j).tendsto.mul
      (outer_endpoint_remainder_continuousAt_zero j).tendsto)

/--
@isnad1 id=continuo.0h0v.s5.eb2d2a4df56e from=translated src=- shape=5446e38f vocab=6715e6ae
-/
theorem outer_endpoint_regularized_pair_continuousAt_zero :
    ContinuousAt outerEndpointRegularizedPair 0 := by
  have h0 := outer_endpoint_regular_dot_continuousAt_zero outerEndpointV0Complex
  have h1 := outer_endpoint_regular_dot_continuousAt_zero outerEndpointV1Complex
  have hr := outer_endpoint_remainder_pair_continuousAt_zero
  unfold outerEndpointRegularizedPair
  fun_prop

/--
@isnad1 id=eq.0h0v.s3.be5e41222060 from=translated src=- shape=3c26ae4f vocab=c8ba3f6f
-/
theorem outer_endpoint_regularized_pair_zero : outerEndpointRegularizedPair 0 = 0 := by
  simp [outerEndpointRegularizedPair]

/--
@isnad1 id=tendsto.0h1v.s6.fab65c6a9e68 from=translated src=- shape=c22819c0 vocab=98ef4930
-/
theorem outer_endpoint_scaled_row_tendsto_zero (j : Fin 6) :
    Tendsto (fun x : ℂ => x^5*outerPrimitiveRow x j)
      (nhdsWithin 0 ({0}ᶜ : Set ℂ)) (nhds 0) := by
  have hc : Tendsto (fun x : ℂ => outerEndpointScaledRow x j)
      (nhdsWithin 0 ({0}ᶜ : Set ℂ)) (nhds (outerEndpointScaledRow 0 j)) :=
    (outer_endpoint_scaled_row_continuousAt_zero j).tendsto.mono_left nhdsWithin_le_nhds
  have he : (fun x : ℂ => outerEndpointScaledRow x j) =ᶠ[nhdsWithin 0 ({0}ᶜ : Set ℂ)]
      (fun x => x^5*outerPrimitiveRow x j) := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact (outer_endpoint_scaled_row_eq x (by simpa using hx) j).symm
  simpa only [outer_endpoint_scaled_row_zero] using hc.congr' he

/--
@isnad1 id=tendsto.0h0v.s6.b045106f6a65 from=translated src=- shape=4319ac71 vocab=69bdd239
-/
theorem outer_endpoint_path_tendsto_zero :
    Tendsto (fun U : ℝ => (1 : ℂ)-(U : ℂ)^2)
      (nhdsWithin 1 (Set.Iio 1)) (nhds 0) := by
  have hi : Tendsto (fun U : ℝ => (U : ℂ)) (nhdsWithin 1 (Set.Iio 1)) (nhds 1) :=
    (Complex.continuous_ofReal.continuousAt (x := (1 : ℝ))).tendsto.mono_left
      nhdsWithin_le_nhds
  simpa only [one_pow,sub_self] using tendsto_const_nhds.sub (hi.pow 2) (a := (1 : ℂ))

/--
@isnad1 id=tendsto.0h0v.s5.db1bc89cfd64 from=translated src=- shape=f0df95df vocab=7a501314
-/
theorem outer_primitive_flux_upperEndpoint :
    Tendsto (fun U : ℝ => outerPrimitiveFlux (U : ℂ))
      (nhdsWithin 1 (Set.Iio 1)) (nhds 0) := by
  have hi : Tendsto (fun U : ℝ => (U : ℂ)) (nhdsWithin 1 (Set.Iio 1)) (nhds 1) :=
    (Complex.continuous_ofReal.continuousAt (x := (1 : ℝ))).tendsto.mono_left
      nhdsWithin_le_nhds
  have hr : Tendsto (fun U : ℝ => outerEndpointRegularizedPair ((1 : ℂ)-(U : ℂ)^2))
      (nhdsWithin 1 (Set.Iio 1)) (nhds 0) := by
    simpa only [Function.comp_def,outer_endpoint_regularized_pair_zero] using
      outer_endpoint_regularized_pair_continuousAt_zero.tendsto.comp
        outer_endpoint_path_tendsto_zero
  have hf := hi.mul hr
  have hn : Tendsto (fun U : ℝ => ‖outerPrimitiveLambda ((1 : ℂ)-(U : ℂ)^2)‖)
      (nhdsWithin 1 (Set.Iio 1)) (nhds (0 : ℝ)) := by
    simpa only [Function.comp_def,norm_zero] using
      (outer_endpoint_lambda_tendsto_zero.comp outer_endpoint_path_tendsto_zero).norm
  have hL : ∀ᶠ U : ℝ in nhdsWithin 1 (Set.Iio 1),
      ‖outerPrimitiveLambda ((1 : ℂ)-(U : ℂ)^2)‖ < 1 :=
    hn.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1))
  have hmin : ∀ᶠ U : ℝ in nhdsWithin 1 (Set.Iio 1), -1 < U :=
    (eventually_gt_nhds (by norm_num : (-1 : ℝ) < 1)).filter_mono nhdsWithin_le_nhds
  have he : (fun U : ℝ => (U : ℂ)*outerEndpointRegularizedPair ((1 : ℂ)-(U : ℂ)^2))
      =ᶠ[nhdsWithin 1 (Set.Iio 1)] (fun U => outerPrimitiveFlux (U : ℂ)) := by
    filter_upwards [hL,hmin,self_mem_nhdsWithin] with U hLu hm hu
    have hp : 0 < (1 : ℝ)-U^2 := by
      have ht : 0 < (1-U)*(U+1) := mul_pos (sub_pos.mpr hu) (by linarith)
      nlinarith
    have hx : (1 : ℂ)-(U : ℂ)^2 ≠ 0 := by
      exact_mod_cast (ne_of_gt hp)
    unfold outerPrimitiveFlux
    rw [outer_endpoint_actual_pairing_eq _ hx hLu]
  simpa only [one_mul] using hf.congr' he

/--
@isnad1 id=tendsto.0h0v.s5.ab388b891af1 from=translated src=- shape=f0df95df vocab=1015ca39
-/
theorem outer_primitive_flux_tendsto_zero_right :
    Tendsto (fun U : ℝ => outerPrimitiveFlux (U : ℂ))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) :=
  outer_primitive_flux_tendsto_zero.mono_left nhdsWithin_le_nhds

end Row12

